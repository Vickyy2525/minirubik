# Computer Architecture HW1 — Mini-Rubik on RV32I

This report documents the adaptation of [sysprog21/minirubik](https://github.com/sysprog21/minirubik) for NCKU Computer Architecture Homework 1: an optimal 2×2×2 solver under a **128 KiB static-data** budget and **≤ 5×10⁷ retired instructions** on a distance-11 scramble, running as handwritten **RV32I** in Ripes, with an optional **LED Matrix** visualization.

Deliverables in this tree:

| Artifact | Role |
| :--- | :--- |
| `solver.c` | Host-side IDA* + P/O pattern databases (reference / `make check`) |
| `solver.s` | Ripes RV32I assembly (main submission) |
| `tables.bin` / `tools/dump_tables.c` | Host-precomputed transition + distance tables embedded in `.data` |
| `tests/solutions.txt` | Optimal-length vectors for `make check` |

## Summary

- **State space:** $7! \times 3^6 = 3{,}674{,}160$ (one corner fixed).
- **Metric:** half-turn metric (HTM); God's number / diameter **11**.
- **Why not full BFS:** a `toward_solved[STATES]` table alone is ~3.5 MiB; with a queue the peak is ~18 MiB — far above 128 KiB.
- **Design:** factored permutation / orientation transitions + **admissible** heuristic $h = \max(h_P, h_O)$ + **non-recursive IDA\*** (explicit stack, no heap, no recursion).
- **Assembly budget (this build):** static `.data` ≈ **40,690 B (~39.7 KiB)** including LED helpers; depth-11 retired instructions ≈ **2.98×10⁷** with `RENDER=0` (under 5×10⁷).
- **Ripes switches** (no `.if` — change `.equ` and reassemble):

```asm
.equ TESTCASE, 2    # 0=solved, 1=depth-10, 2=depth-11
.equ RENDER, 1      # 0=measure, 1=LED animation
```

## Stage 1 — Baseline constraints

### Cube model (unchanged from upstream)

Eight corner cubies; fix corner 0 at FUL so the rest are 7 positions × orientations. Orientations live in $\mathbb{Z}_3$; the seventh twist is determined by $\sum o_i \equiv 0 \pmod 3$. Generators are the three faces that do not move the fixed corner: **R, B, D**, each with quarter / half / inverse → **9 moves** in HTM.

14-digit CLI / hard-coded input:

```text
PPPPPPP OOOOOOO   → e.g. 21345671111111
```

Solved code: `12345671111111`.

### Why the original BFS does not fit Ripes

Upstream `solver.c` builds a retrograde BFS table: one move byte per state plus a rank queue. Peak working set is on the order of **17–19 MiB**, which cannot live in Ripes static memory under **128 KiB**. Even discarding the queue, 3.5 MiB of `toward_solved` already exceeds the budget.

### Measurement targets

| Constraint | Limit | This project |
| :--- | ---: | :--- |
| Static data (`.data` + helpers) | ≤ 128 KiB | ~39.7 KiB |
| Retired instructions (depth 11, no LED) | ≤ 5×10⁷ | ~2.98×10⁷ |
| Optimality | HTM length | length matches BFS distance (`make check`) |
| ISA | RV32I only (no M) | no `mul`/`div`/`rem`; products via shifts/adds |

## Stage 2 — Representation and optimal search

### Factored state

A configuration is $(p, o)$ with $p \in [0, 5040)$, $o \in [0, 729)$. A face quarter-turn updates permutation and orientation **independently**, so three small transition tables replace a full-state graph:

- `permutation[3][5040]` — next perm rank after one quarter turn of R/B/D  
- `orientation[3][729]` — next orient rank  
- `perm_dist[5040]`, `orient_dist[729]` — BFS distances on each projected graph  

Half and inverse turns apply the quarter table two or three times.

### Pattern databases and admissibility

Each real cube move advances **exactly one edge** in the permutation projection and **exactly one** in the orientation projection. Therefore

$$
h(p,o) = \max\bigl(\mathrm{perm\_dist}[p],\ \mathrm{orient\_dist}[o]\bigr)
$$

never overestimates the true HTM distance (admissible). IDA\* with this $h$ returns a shortest solution.

### Non-recursive IDA\*

Recursive IDA\* would blow the Ripes stack. The assembly (and C) use an explicit depth stack: at each node try moves $0..8$, prune same-face repeats, and cut when $d + h > \mathrm{bound}$. Raise `bound` from $h(\mathrm{start})$ up to 11 until a path to $(0,0)$ is found.

```diagram
  parse 14 digits → (p,o)
        │
        ▼
  bound ← h(p,o)
        │
        ▼
  iterative deepening: DFS with cutoff d+h ≤ bound
        │
        ▼
  emit move names; optional LED animate
```

Exact BFS *paths* need not match; only **length** must be optimal.

## Stage 3 — C refinements before assembly

`solver.c` is written as a RV32I-friendly reference:

- No heap for the search; tables are `static`.
- No `%` / `/` in the hot path: `rem3_at_most_4` / `rem3_at_most_14` use ASR masks; products use shift–add (`×3`, `×9`, `×729`, …).
- Strides `PERM_STRIDE=8192`, `ORIENT_STRIDE=1024` so face×row is a shift (assembly uses packed live tables without padding to save bytes).
- Host `tools/dump_tables.c` dumps `tables.bin`; the bytes are baked into `solver.s` `.data` so Ripes never builds tables at runtime.

Host check:

```sh
make
make check          # length-optimal vs tests/solutions.txt
./solver 21345671111111
```

## Stage 4 — Handwritten RV32I (`solver.s`)

### Assembler constraints (Ripes)

| Use | Avoid |
| :--- | :--- |
| `.text` / `.data` | `.section` |
| `.zero`, `.byte`, `.word`, `.equ`, `.align` (byte boundary) | `.if` / `.elseif` / `.endif`, `.space`, `.include` |
| `lui`+`addi` for large immediates; gp-relative loads | fragile `la` across huge `.data` |
| ABI: `a0–a7` args, `s0–s11` saved, `jal`/`ret` | M-extension ops |

Entry is the **first instruction of `.text`**. `gp` is set to `0x10000000` (Ripes `.data` base).

### Memory map (approx.)

| Symbol | Offset from `.data` | Contents |
| :--- | ---: | :--- |
| `perm_dist` | 0 | 5040 B |
| `orient_dist` | 5040 | 729 B |
| `permutation` | … | 3×5040×2 |
| `orientation` | … | 3×729×2 |
| `cube_state` / `path` | 40460 / 40476 | scratch |
| `facelets` + LED tables | 40492+ | render |
| `input0`/`input1`/`input2` | 40645+ | hard-coded cases |

Total static data ≈ **40,690 bytes**.

### TESTCASE / RENDER

Ripes has no `.if`, so selection is **runtime** from `.equ` constants:

- `TESTCASE` 0 / 1 / 2 → pointers to `input0` / `input1` / `input2`
- `RENDER` 0 → skip facelet init, inverse path, `render_cube`, `frame_delay` (instruction-count runs)
- `RENDER` 1 → LED demo

Default for demo: `TESTCASE=2`, `RENDER=1`. For the depth-11 budget check: `RENDER=0`, `TESTCASE=2`.

### Representative outputs (host C; asm prints the same move *names*, length-optimal)

| TESTCASE | Input | Depth |
| :---: | :--- | ---: |
| 0 | `12345671111111` | 0 (empty line) |
| 1 | `25416373331111` | 10 |
| 2 | `21345671111111` | 11 |

## LED Matrix

- Base address `0xF0000000`, panel **35×25**, cube drawn as a cross net (U / L F R B / D).
- Each facelet is a **4×3** block; colors W/Y/G/B/R/O.
- Animation: start from solved facelets → apply **inverse** of the solution path (scramble) → render → apply each solution move with a short `frame_delay`.
- Ends on a solid solved net (U white, D yellow, F green, B blue, R red, L orange).

Facelet geometry is a visualization group action consistent with the printed path (scramble → solved). Absolute sticker colors for an arbitrary encoding may differ slightly from a physical cube photograph; the demo requirement is a clear scramble-to-solved animation.

## Five-stage pipeline (what to capture in HackMD)

Pick one hot-path instruction, e.g. a `lbu`/`lhu` from `perm_dist` or a transition table inside `ida_solve`, and screenshot Ripes **RV32_5S** for:

| Stage | Show |
| :--- | :--- |
| IF | PC, fetched instruction |
| ID | decoded opcode / rs1 / rs2 / rd |
| EX | ALU inputs and result (address add) |
| MEM | data-memory read (table byte/half) |
| WB | destination register update |

Also note a following dependent instruction (e.g. a shift that uses the loaded distance) and whether forwarding or a stall appears. These screenshots belong in the **HackMD** notes (not required to embed every image in this `report.md`).

## How to reproduce

1. Host correctness: `make && make check`
2. Open `solver.s` in Ripes (RV32I).
3. Demo: `.equ RENDER, 1` and `.equ TESTCASE, 2` → Assemble & Run → LED + stdout moves.
4. Measure: `.equ RENDER, 0`, same `TESTCASE`, read retired-instruction counter (must be &lt; 5×10⁷ for case 2).
5. Switch `TESTCASE` to 0 and 1 to show the other two hard-coded inputs.

## Development notes

- Full BFS → IDA\*+PDBs to fit 128 KiB.
- Ripes directive cleanup: `.section` / `.space` / numeric local labels / `.if` removed.
- Large immediates and table bases via `lui`/`addi` and `gp`.
- LED initially black until `0xF0000000` writes + non-zero frame delay.

## References

1. Course assignment: Mini-Rubik on RV32I (NCKU CSIE Computer Architecture).
2. Gene Cooperman and Larry Finkelstein, “New Methods for Using Cayley Graphs in Interconnection Networks,” *Discrete Applied Mathematics* 37–38 (1992).
3. Antti Valmari, “What the Small Rubik’s Cube Taught Me…,” *STTT* 8(3) (2006).
4. Korf, “Depth-First Iterative-Deepening,” *Artificial Intelligence* 27 (1985) — IDA\*.
5. Culberson & Schaeffer — pattern databases for sliding puzzles / Rubik’s Cube heuristics.
