#include <stdint.h>
#include <stdio.h>
#include <string.h>

enum {
    CUBIES = 7, PERMUTATIONS = 5040, ORIENTATIONS = 729,
    PERM_STRIDE = 8192, ORIENT_STRIDE = 1024
};

typedef struct { uint8_t p[7], o[7]; } state_t;

static const uint8_t source[3][7] = {
    {1,4,2,0,3,5,6},{0,1,2,4,5,6,3},{0,2,5,3,1,4,6}};
static const uint8_t twist[3][7] = {
    {1,2,0,2,1,0,0},{0,0,0,1,2,1,2},{0,0,0,0,0,0,0}};
static const uint16_t factorial[7] = {720,120,24,6,2,1,1};
static const uint16_t pow3[6] = {243,81,27,9,3,1};

static uint16_t permutation[3][PERM_STRIDE];
static uint16_t orientation[3][ORIENT_STRIDE];
static uint8_t perm_dist[PERMUTATIONS];
static uint8_t orient_dist[ORIENTATIONS];

static uint8_t rem3_4(uint8_t s) {
    int32_t t = (int32_t)s - 3, m = t >> 31;
    return (uint8_t)(t + (m & 3));
}
static uint8_t rem3_14(uint8_t sum) {
    uint8_t s = (uint8_t)((sum >> 2) + (sum & 3U));
    int32_t t = (int32_t)s - 3, m = t >> 31;
    s = (uint8_t)(t + (m & 3));
    t = (int32_t)s - 3; m = t >> 31;
    return (uint8_t)(t + (m & 3));
}
static uint32_t mul3(uint32_t x) { return (x<<1)+x; }
static uint32_t mul5(uint32_t x) { return (x<<2)+x; }
static uint32_t mul6(uint32_t x) { return (x<<2)+(x<<1); }
static uint32_t mul7(uint32_t x) { return (x<<3)-x; }

static state_t qt(state_t st, uint8_t face) {
    state_t r;
    for (uint8_t i = 0; i < 7; ++i) {
        uint8_t f = source[face][i];
        r.p[i] = st.p[f];
        r.o[i] = rem3_4((uint8_t)(st.o[f] + twist[face][i]));
    }
    return r;
}
static uint8_t quot(uint32_t *p, uint16_t f) {
    uint8_t q = 0; while (*p >= f) { *p -= f; ++q; } return q;
}
static void unrank_perm(uint16_t pin, state_t *st) {
    uint8_t avail[7] = {0,1,2,3,4,5,6}; uint32_t p = pin;
    for (uint8_t i = 0; i < 7; ++i) {
        uint8_t q = quot(&p, factorial[i]);
        st->p[i] = avail[q];
        for (uint8_t j = q; j+1 < 7-i; ++j) avail[j] = avail[j+1];
    }
}
static void unrank_orient(uint16_t oin, state_t *st) {
    uint32_t o = oin; uint8_t sum = 0;
    for (uint8_t i = 0; i < 6; ++i) {
        uint8_t d = 0;
        if (o >= pow3[i]) { o -= pow3[i]; d = 1; }
        if (o >= pow3[i]) { o -= pow3[i]; d = 2; }
        st->o[i] = d; sum = (uint8_t)(sum + d);
    }
    st->o[6] = rem3_4((uint8_t)(3U - rem3_14(sum)));
}
static uint16_t rank_perm(const state_t *st) {
    uint32_t p = 0;
    for (uint8_t i = 0; i < 7; ++i) {
        uint8_t smaller = 0, factor = (uint8_t)(7 - i);
        for (uint8_t j = i+1; j < 7; ++j) if (st->p[j] < st->p[i]) ++smaller;
        switch (factor) {
        case 7: p = mul7(p); break; case 6: p = mul6(p); break;
        case 5: p = mul5(p); break; case 4: p <<= 2; break;
        case 3: p = mul3(p); break; case 2: p <<= 1; break;
        }
        p += smaller;
    }
    return (uint16_t)p;
}
static uint16_t rank_orient(const state_t *st) {
    uint32_t o = 0;
    for (uint8_t i = 0; i < 6; ++i) o = mul3(o) + st->o[i];
    return (uint16_t)o;
}

static void build(void) {
    state_t st; uint16_t queue[PERMUTATIONS]; uint32_t head, tail;
    for (uint16_t r = 0; r < PERMUTATIONS; ++r) {
        unrank_perm(r, &st); unrank_orient(0, &st);
        for (uint8_t f = 0; f < 3; ++f) {
            state_t n = qt(st, f);
            permutation[f][r] = rank_perm(&n);
        }
    }
    for (uint16_t r = 0; r < ORIENTATIONS; ++r) {
        unrank_perm(0, &st); unrank_orient(r, &st);
        for (uint8_t f = 0; f < 3; ++f) {
            state_t n = qt(st, f);
            orientation[f][r] = rank_orient(&n);
        }
    }
    memset(perm_dist, 0xFF, sizeof perm_dist);
    queue[0]=0; perm_dist[0]=0; head=0; tail=1;
    while (head < tail) {
        uint16_t here = queue[head++]; uint8_t d = perm_dist[here];
        for (uint8_t f = 0; f < 3; ++f) {
            uint16_t next = here;
            for (uint8_t t = 0; t < 3; ++t) {
                next = permutation[f][next];
                if (perm_dist[next] == 0xFF) {
                    perm_dist[next] = (uint8_t)(d+1); queue[tail++] = next;
                }
            }
        }
    }
    memset(orient_dist, 0xFF, sizeof orient_dist);
    queue[0]=0; orient_dist[0]=0; head=0; tail=1;
    while (head < tail) {
        uint16_t here = queue[head++]; uint8_t d = orient_dist[here];
        for (uint8_t f = 0; f < 3; ++f) {
            uint16_t next = here;
            for (uint8_t t = 0; t < 3; ++t) {
                next = orientation[f][next];
                if (orient_dist[next] == 0xFF) {
                    orient_dist[next] = (uint8_t)(d+1); queue[tail++] = next;
                }
            }
        }
    }
}

int main(void) {
    build();
    FILE *fp = fopen("tables.bin", "wb");
    /* Only live columns: write packed for asm generator */
    for (int f = 0; f < 3; ++f)
        fwrite(permutation[f], 2, PERMUTATIONS, fp);
    for (int f = 0; f < 3; ++f)
        fwrite(orientation[f], 2, ORIENTATIONS, fp);
    fwrite(perm_dist, 1, PERMUTATIONS, fp);
    fwrite(orient_dist, 1, ORIENTATIONS, fp);
    fclose(fp);
    fprintf(stderr, "wrote tables.bin\n");
    return 0;
}
