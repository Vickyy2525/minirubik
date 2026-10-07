#include <stdint.h>
#include <stdio.h>
#include <string.h>

enum {
    CUBIES = 7,
    PERMUTATIONS = 5040,
    ORIENTATIONS = 729,
    /* Power-of-two row strides so face*row is a shift, not a mul on RV32I. */
    PERM_STRIDE = 8192,
    ORIENT_STRIDE = 1024,
    STATES = PERMUTATIONS * ORIENTATIONS,
    MOVES = 9,
    MAX_DEPTH = 11
};

typedef struct {
    uint8_t p[CUBIES], o[CUBIES];
} state_t;

/*@ predicate valid_state(state_t *state) =
      (\forall integer i; 0 <= i < CUBIES ==>
         state->p[i] < CUBIES && state->o[i] < 3) &&
      (\forall integer i, j; 0 <= i < j < CUBIES ==>
         state->p[i] != state->p[j]) &&
      (state->o[0] + state->o[1] + state->o[2] + state->o[3] +
       state->o[4] + state->o[5] + state->o[6]) % 3 == 0;
 */

static const char *const move_names[MOVES] = {"R",  "R2", "R'", "B", "B2",
                                              "B'", "D",  "D2", "D'"};
static const uint8_t inverse_move[MOVES] = {2, 1, 0, 5, 4, 3, 8, 7, 6};
/* Each destination takes a cubie from source[face][destination]. */
static const uint8_t source[3][CUBIES] = {
    {1, 4, 2, 0, 3, 5, 6},
    {0, 1, 2, 4, 5, 6, 3},
    {0, 2, 5, 3, 1, 4, 6},
};
static const uint8_t twist[3][CUBIES] = {
    {1, 2, 0, 2, 1, 0, 0},
    {0, 0, 0, 1, 2, 1, 2},
    {0, 0, 0, 0, 0, 0, 0},
};

/*
 * Factored quarter-turn transitions, rows padded to PERM_STRIDE / ORIENT_STRIDE
 * so indexing is shift+add only (3 * (8192 + 1024) uint16_t = 55,296 B of the
 * tables; live entries remain 34,614 B).  Pattern-database distances for each
 * factor supply max(h_p, h_o), an admissible heuristic for the full Cayley
 * graph: each real move advances exactly one edge in each projected graph.
 */
static uint16_t permutation[3][PERM_STRIDE];
static uint16_t orientation[3][ORIENT_STRIDE];
static uint8_t perm_dist[PERMUTATIONS];
static uint8_t orient_dist[ORIENTATIONS];

/* Factoradic place values 6! .. 0!; avoids runtime division in unrank. */
static const uint16_t factorial[CUBIES] = {720, 120, 24, 6, 2, 1, 1};
/* Powers of 3 for base-3 orientation digits: 3^5 .. 3^0. */
static const uint16_t pow3[6] = {243, 81, 27, 9, 3, 1};

/*
 * RV32I has no mul/div.  Constant products are shifts and adds:
 *   x*3 = (x<<1)+x,  x*5 = (x<<2)+x,  x*6 = (x<<2)+(x<<1),
 *   x*7 = (x<<3)-x,  x*9 = (x<<3)+x,  x*729 = x*(512+128+64+16+8+1).
 * Orientation twists add two values each at most 2, so the sum is in 0..4.
 * Branchless rem 3: t = sum-3; ASR(t) is all-ones iff sum < 3; that mask
 * adds the modulus back when no reduction was needed.
 */
static uint8_t rem3_at_most_4(uint8_t sum)
{
    int32_t t = (int32_t) sum - 3;
    int32_t mask = t >> 31;
    return (uint8_t) (t + (mask & 3));
}

/* sum in 0..14 (seven orientations): fold to 0..6, then two ASR reductions. */
static uint8_t rem3_at_most_14(uint8_t sum)
{
    uint8_t s = (uint8_t) ((sum >> 2) + (sum & 3U));
    int32_t t = (int32_t) s - 3;
    int32_t mask = t >> 31;
    s = (uint8_t) (t + (mask & 3));
    t = (int32_t) s - 3;
    mask = t >> 31;
    return (uint8_t) (t + (mask & 3));
}

static uint32_t mul3(uint32_t x)
{
    return (x << 1) + x;
}

static uint32_t mul5(uint32_t x)
{
    return (x << 2) + x;
}

static uint32_t mul6(uint32_t x)
{
    return (x << 2) + (x << 1);
}

static uint32_t mul7(uint32_t x)
{
    return (x << 3) - x;
}

/* 729 = 512+128+64+16+8+1 */
static uint32_t mul729(uint32_t p)
{
    return (p << 9) + (p << 7) + (p << 6) + (p << 4) + (p << 3) + p;
}

/* move in 0..8: face = move/3 via (move*11)>>5 with *11 = <<3 + <<1 + id. */
static uint8_t move_face(uint8_t move)
{
    uint32_t m = move;
    return (uint8_t) (((m << 3) + (m << 1) + m) >> 5);
}

static uint8_t move_turns(uint8_t move)
{
    uint8_t face = move_face(move);
    return (uint8_t) (move - (uint8_t) mul3(face) + 1U);
}

/* Quotient p/f for p < 5040 and f a factorial place; q ≤ 6. */
static uint8_t quot_by_sub(uint32_t *p, uint16_t f)
{
    uint8_t q = 0;
    while (*p >= f) {
        *p -= f;
        ++q;
    }
    return q;
}

/* Binary long division: rank = p*729 + o with o < 729. */
static void split_rank(uint32_t rank, uint16_t *p_out, uint16_t *o_out)
{
    uint32_t p = 0, rem = rank;
    for (int k = 12; k >= 0; --k) {
        uint32_t chunk = (uint32_t) ORIENTATIONS << k;
        if (rem >= chunk) {
            rem -= chunk;
            p += 1U << k;
        }
    }
    *p_out = (uint16_t) p;
    *o_out = (uint16_t) rem;
}

/* The three quarter-turns preserve the fixed front-upper-left corner. */
/*@ requires face < 3;
    assigns \nothing;
    ensures \forall integer i; 0 <= i < CUBIES ==>
              \result.p[i] == state.p[source[face][i]];
    ensures \forall integer i; 0 <= i < CUBIES ==>
              \result.o[i] == (state.o[source[face][i]] + twist[face][i]) % 3;
 */
static state_t quarter_turn(state_t state, uint8_t face)
{
    state_t result;
    /*@ loop invariant 0 <= i <= CUBIES;
        loop invariant \forall integer j; 0 <= j < i ==>
          result.p[j] == state.p[source[face][j]];
        loop invariant \forall integer j; 0 <= j < i ==>
          result.o[j] == (state.o[source[face][j]] + twist[face][j]) % 3;
        loop assigns i, result.p[0..6], result.o[0..6];
        loop variant CUBIES - i;
    */
    for (uint8_t i = 0; i < CUBIES; ++i) {
        uint8_t from = source[face][i];
        result.p[i] = state.p[from];
        result.o[i] = rem3_at_most_4(
            (uint8_t) (state.o[from] + twist[face][i]));
    }
    return result;
}

static state_t apply_move(state_t state, uint8_t move)
{
    uint8_t face = move_face(move);
    uint8_t turns = move_turns(move);
    for (uint8_t i = 0; i < turns; ++i)
        state = quarter_turn(state, face);
    return state;
}

/*@ requires \valid_read(state);
    requires \forall integer i; 0 <= i < CUBIES ==>
      0 <= state->p[i] < CUBIES;
    requires \forall integer i, j; 0 <= i < j < CUBIES ==>
      state->p[i] != state->p[j];
    requires \forall integer i; 0 <= i < CUBIES ==>
      0 <= state->o[i] < 3;
    assigns \nothing;
    ensures \result < STATES;
 */
static uint32_t rank_state(const state_t *state)
{
    uint32_t p = 0, o = 0;
    /*@ loop invariant 0 <= i <= CUBIES;
        loop invariant (i == 0 ==> p == 0) && (i == 1 ==> p <= 6) &&
          (i == 2 ==> p <= 41) && (i == 3 ==> p <= 209) &&
          (i == 4 ==> p <= 839) && (i == 5 ==> p <= 2519) &&
          (i >= 6 ==> p <= 5039);
        loop assigns i, p;
        loop variant CUBIES - i;
     */
    for (uint8_t i = 0; i < CUBIES; ++i) {
        uint8_t smaller = 0;
        uint8_t factor = (uint8_t) (CUBIES - i);
        /*@ loop invariant i + 1 <= j <= CUBIES;
            loop invariant smaller <= j - i - 1;
            loop assigns j, smaller;
            loop variant CUBIES - j;
         */
        for (uint8_t j = (uint8_t) (i + 1U); j < CUBIES; ++j)
            if (state->p[j] < state->p[i])
                ++smaller;
        /* p *= (7..1) with shift/add only. */
        switch (factor) {
        case 7:
            p = mul7(p);
            break;
        case 6:
            p = mul6(p);
            break;
        case 5:
            p = mul5(p);
            break;
        case 4:
            p <<= 2;
            break;
        case 3:
            p = mul3(p);
            break;
        case 2:
            p <<= 1;
            break;
        default:
            break;
        }
        p += smaller;
    }
    /*@ loop invariant 0 <= i <= 6;
        loop invariant (i == 0 ==> o == 0) && (i == 1 ==> o < 3) &&
          (i == 2 ==> o < 9) && (i == 3 ==> o < 27) &&
          (i == 4 ==> o < 81) && (i == 5 ==> o < 243) &&
          (i == 6 ==> o < 729);
        loop assigns i, o;
        loop variant 6 - i;
     */
    for (uint8_t i = 0; i < 6; ++i)
        o = mul3(o) + state->o[i];
    return mul729(p) + o;
}

static uint16_t rank_perm(const state_t *state)
{
    uint32_t p = 0;
    for (uint8_t i = 0; i < CUBIES; ++i) {
        uint8_t smaller = 0;
        uint8_t factor = (uint8_t) (CUBIES - i);
        for (uint8_t j = (uint8_t) (i + 1U); j < CUBIES; ++j)
            if (state->p[j] < state->p[i])
                ++smaller;
        switch (factor) {
        case 7:
            p = mul7(p);
            break;
        case 6:
            p = mul6(p);
            break;
        case 5:
            p = mul5(p);
            break;
        case 4:
            p <<= 2;
            break;
        case 3:
            p = mul3(p);
            break;
        case 2:
            p <<= 1;
            break;
        default:
            break;
        }
        p += smaller;
    }
    return (uint16_t) p;
}

static uint16_t rank_orient(const state_t *state)
{
    uint32_t o = 0;
    for (uint8_t i = 0; i < 6; ++i)
        o = mul3(o) + state->o[i];
    return (uint16_t) o;
}

static void unrank_perm(uint16_t p_in, state_t *state)
{
    uint8_t available[CUBIES] = {0, 1, 2, 3, 4, 5, 6};
    uint32_t p = p_in;
    for (uint8_t i = 0; i < CUBIES; ++i) {
        uint8_t q = quot_by_sub(&p, factorial[i]);
        state->p[i] = available[q];
        for (uint8_t j = q; j + 1U < CUBIES - i; ++j)
            available[j] = available[j + 1U];
    }
}

static void unrank_orient(uint16_t o_in, state_t *state)
{
    uint32_t o = o_in;
    uint8_t sum = 0;
    for (uint8_t i = 0; i < 6; ++i) {
        uint8_t digit = 0;
        if (o >= pow3[i]) {
            o -= pow3[i];
            digit = 1;
        }
        if (o >= pow3[i]) {
            o -= pow3[i];
            digit = 2;
        }
        state->o[i] = digit;
        sum = (uint8_t) (sum + digit);
    }
    state->o[6] = rem3_at_most_4((uint8_t) (3U - rem3_at_most_14(sum)));
}

/*@ requires \valid(state); requires rank < STATES; assigns *state; */
static void unrank_state(uint32_t rank, state_t *state)
{
    uint16_t p, o;
    split_rank(rank, &p, &o);
    unrank_perm(p, state);
    unrank_orient(o, state);
}

/*@ requires \valid_read(state);
    requires \initialized(&state->p[0..6]) && \initialized(&state->o[0..6]);
    assigns \nothing;
    ensures \result != 0 ==> \forall integer i; 0 <= i < CUBIES ==>
      state->p[i] < CUBIES && state->o[i] < 3;
    ensures \result != 0 ==> \forall integer i, j; 0 <= i < j < CUBIES ==>
      state->p[i] != state->p[j];
    ensures \result != 0 ==>
      (state->o[0] + state->o[1] + state->o[2] + state->o[3] +
       state->o[4] + state->o[5] + state->o[6]) % 3 == 0;
    ensures complete: valid_state(state) ==> \result != 0;
 */
static int valid(const state_t *state)
{
    uint8_t sum = 0;
    /*@ loop invariant 0 <= i <= CUBIES;
        loop invariant sum <= 2 * i;
        loop invariant sum == (i > 0 ? state->o[0] : 0) +
          (i > 1 ? state->o[1] : 0) + (i > 2 ? state->o[2] : 0) +
          (i > 3 ? state->o[3] : 0) + (i > 4 ? state->o[4] : 0) +
          (i > 5 ? state->o[5] : 0) + (i > 6 ? state->o[6] : 0);
        loop invariant \forall integer j; 0 <= j < i ==>
          state->p[j] < CUBIES && state->o[j] < 3;
        loop invariant \forall integer j, k; 0 <= j < k < i ==>
          state->p[j] != state->p[k];
        loop assigns i, sum;
        loop variant CUBIES - i;
    */
    for (uint8_t i = 0; i < CUBIES; ++i) {
        if (state->p[i] >= CUBIES || state->o[i] >= 3)
            return 0;
        /*@ loop invariant 0 <= j <= i;
            loop invariant \forall integer k; 0 <= k < j ==>
              state->p[k] != state->p[i];
            loop assigns j;
            loop variant i - j;
        */
        for (uint8_t j = 0; j < i; ++j)
            if (state->p[j] == state->p[i])
                return 0;
        sum = (uint8_t) (sum + state->o[i]);
    }
    return rem3_at_most_14(sum) == 0;
}

static uint8_t heuristic(uint16_t p, uint16_t o)
{
    uint8_t hp = perm_dist[p], ho = orient_dist[o];
    return hp > ho ? hp : ho;
}

static void apply_factored(uint16_t *p, uint16_t *o, uint8_t move)
{
    uint8_t face = move_face(move);
    uint8_t turns = move_turns(move);
    for (uint8_t t = 0; t < turns; ++t) {
        *p = permutation[face][*p];
        *o = orientation[face][*o];
    }
}

/* Build factored transitions, then BFS distance PDBs on each factor. */
static int build_tables(void)
{
    state_t state;
    uint16_t queue[PERMUTATIONS];
    uint32_t head, tail;

    for (uint16_t rank = 0; rank < PERMUTATIONS; ++rank) {
        unrank_perm(rank, &state);
        unrank_orient(0, &state);
        for (uint8_t face = 0; face < 3; ++face) {
            state_t next = quarter_turn(state, face);
            permutation[face][rank] = rank_perm(&next);
        }
    }
    for (uint16_t rank = 0; rank < ORIENTATIONS; ++rank) {
        unrank_perm(0, &state);
        unrank_orient(rank, &state);
        for (uint8_t face = 0; face < 3; ++face) {
            state_t next = quarter_turn(state, face);
            orientation[face][rank] = rank_orient(&next);
        }
    }

    memset(perm_dist, UINT8_MAX, sizeof perm_dist);
    queue[0] = 0;
    perm_dist[0] = 0;
    head = 0;
    tail = 1;
    while (head < tail) {
        uint16_t here = queue[head++];
        uint8_t dist = perm_dist[here];
        for (uint8_t face = 0; face < 3; ++face) {
            uint16_t next = here;
            for (uint8_t turn = 0; turn < 3; ++turn) {
                next = permutation[face][next];
                if (perm_dist[next] == UINT8_MAX) {
                    perm_dist[next] = (uint8_t) (dist + 1U);
                    queue[tail++] = next;
                }
            }
        }
    }
    if (tail != PERMUTATIONS)
        return 0;

    memset(orient_dist, UINT8_MAX, sizeof orient_dist);
    queue[0] = 0;
    orient_dist[0] = 0;
    head = 0;
    tail = 1;
    while (head < tail) {
        uint16_t here = queue[head++];
        uint8_t dist = orient_dist[here];
        for (uint8_t face = 0; face < 3; ++face) {
            uint16_t next = here;
            for (uint8_t turn = 0; turn < 3; ++turn) {
                next = orientation[face][next];
                if (orient_dist[next] == UINT8_MAX) {
                    orient_dist[next] = (uint8_t) (dist + 1U);
                    queue[tail++] = next;
                }
            }
        }
    }
    return tail == ORIENTATIONS;
}

/*
 * Non-recursive IDA*: explicit stack, face-move pruning (same face never
 * twice in a row), bound raised from h(root) to MAX_DEPTH.  First solution
 * found is optimal because the heuristic is admissible.
 */
static int ida_solve(uint16_t start_p, uint16_t start_o, uint8_t *path)
{
    struct {
        uint16_t p, o;
        uint8_t next;
    } stack[MAX_DEPTH + 1];
    uint8_t moves[MAX_DEPTH];
    uint8_t bound = heuristic(start_p, start_o);

    if (start_p == 0 && start_o == 0)
        return 0;

    for (; bound <= MAX_DEPTH; ++bound) {
        uint8_t depth = 0;
        stack[0].p = start_p;
        stack[0].o = start_o;
        stack[0].next = 0;

        for (;;) {
            uint8_t h = heuristic(stack[depth].p, stack[depth].o);

            if ((uint16_t) depth + h > bound) {
                if (depth == 0)
                    break;
                --depth;
                continue;
            }
            if (stack[depth].p == 0 && stack[depth].o == 0) {
                memcpy(path, moves, depth);
                return depth;
            }
            if (depth == bound || stack[depth].next >= MOVES) {
                if (depth == 0)
                    break;
                --depth;
                continue;
            }

            {
                uint8_t move = stack[depth].next++;
                uint8_t face = move_face(move);
                uint16_t np, no;

                if (depth > 0 && move_face(moves[depth - 1]) == face)
                    continue;

                np = stack[depth].p;
                no = stack[depth].o;
                apply_factored(&np, &no, move);
                moves[depth] = move;
                stack[depth + 1].p = np;
                stack[depth + 1].o = no;
                stack[depth + 1].next = 0;
                ++depth;
            }
        }
    }
    return -1;
}

/*@ requires valid_read_string(input);
    requires \valid(state);
    assigns state->p[0..6], state->o[0..6];
    ensures \result != 0 ==> input[14] == '\0';
    ensures \result != 0 ==> \forall integer i; 0 <= i < CUBIES ==>
      state->p[i] < CUBIES && state->o[i] < 3;
    ensures \result != 0 ==> \forall integer i, j; 0 <= i < j < CUBIES ==>
      state->p[i] != state->p[j];
    ensures \result != 0 ==>
      (state->o[0] + state->o[1] + state->o[2] + state->o[3] +
       state->o[4] + state->o[5] + state->o[6]) % 3 == 0;
    ensures \result != 0 ==> \forall integer i; 0 <= i < CUBIES ==>
      state->p[i] == input[i] - '1';
    ensures \result != 0 ==> \forall integer i; 0 <= i < CUBIES ==>
      state->o[i] == input[i + CUBIES] - '1';
 */
static int parse_state(const char *input, state_t *state)
{
    /*@ loop invariant 0 <= i <= 14;
        loop invariant i <= strlen(input);
        loop invariant i <= 7 ==> \initialized(&state->p[0..i-1]);
        loop invariant i >= 7 ==> \initialized(&state->p[0..6]);
        loop invariant i >= 7 ==> \initialized(&state->o[0..i-8]);
        loop invariant \forall integer j; 0 <= j < i && j < CUBIES ==>
          state->p[j] == input[j] - '1';
        loop invariant \forall integer j; 0 <= j < i - CUBIES ==>
          state->o[j] == input[j + CUBIES] - '1';
        loop assigns i, state->p[0..6], state->o[0..6];
        loop variant 14 - i;
     */
    for (int i = 0; i < 14; ++i) {
        int limit = i < 7 ? 7 : 3;
        uint8_t idx = (uint8_t) i;
        if (input[i] < '1' || input[i] > '0' + limit)
            return 0;
        /* i in 0..13: idx = i % 7 without a divider. */
        if (idx >= 7)
            idx = (uint8_t) (idx - 7U);
        (i < 7 ? state->p : state->o)[idx] = (uint8_t) (input[i] - '1');
    }
    return input[14] == '\0' && valid(state);
}

/* stdout is fully buffered off a terminal, so a write error surfaces at the
 * flush, not at the printf that queued the bytes. Every exit path that has
 * produced output goes through here.
 */
static int output_failed(void)
{
    return fflush(stdout) != 0 || ferror(stdout);
}

static int self_test(void)
{
    const state_t solved = {{0, 1, 2, 3, 4, 5, 6}, {0}};
    state_t state;
    uint8_t path[MAX_DEPTH];
    uint32_t rank;
    int len;

    for (uint8_t move = 0; move < MOVES; ++move) {
        state = solved;
        state = apply_move(state, move);
        state = apply_move(state, inverse_move[move]);
        if (memcmp(&solved, &state, sizeof solved))
            return 0;
    }
    for (rank = 0; rank < STATES; ++rank) {
        unrank_state(rank, &state);
        if (!valid(&state) || rank_state(&state) != rank)
            return 0;
    }
    if (!build_tables())
        return 0;
    if (perm_dist[0] != 0 || orient_dist[0] != 0)
        return 0;
    if (heuristic(0, 0) != 0)
        return 0;

    /* Distance-11 sample: path length must be 11 and must reach solved. */
    if (!parse_state("21345671111111", &state))
        return 0;
    len = ida_solve(rank_perm(&state), rank_orient(&state), path);
    if (len != 11)
        return 0;
    for (int i = 0; i < len; ++i)
        state = apply_move(state, path[i]);
    if (rank_state(&state) != 0)
        return 0;
    return 1;
}

int main(int argc, char **argv)
{
    state_t state;
    uint8_t path[MAX_DEPTH];
    int len;
    const char *separator;

    if (argc == 2 && !strcmp(argv[1], "--self-test")) {
        if (!self_test()) {
            fputs("self-test failed\n", stderr);
            return 1;
        }
        puts("3674160 states; IDA* with factored P/O heuristic");
        return output_failed();
    }
    if (argc != 2 || !parse_state(argv[1], &state)) {
        /* C99 5.1.2.2.1 lets argv[0] be null when argc is 0. */
        fprintf(stderr, "usage: %s PPPPPPPOOOOOOO\n",
                argc > 0 && argv[0] ? argv[0] : "solver");
        return 2;
    }
    if (!build_tables()) {
        fputs("could not build transition tables\n", stderr);
        return 1;
    }
    len = ida_solve(rank_perm(&state), rank_orient(&state), path);
    if (len < 0) {
        fputs("search failed\n", stderr);
        return 1;
    }
    separator = "";
    for (int i = 0; i < len; ++i) {
        printf("%s%s", separator, move_names[path[i]]);
        separator = " ";
        state = apply_move(state, path[i]);
    }
    putchar('\n');
    return output_failed();
}
