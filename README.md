# jsp-lean

Lean 4 formalizations for Justin Sun Prize problems (Erdős problems catalog).

Toolchain: Lean `leanprover/lean4:v4.32.0`, Mathlib `v4.32.0` (pinned in `lake-manifest.json`).

| Entry | Erdős # | Main theorem | File |
|---|---|---|---|
| JSP-000759 | #915 | `JSP000759.leonard_counterexample` — a 57-vertex, 141-edge simple graph with no five internally vertex-disjoint paths between any two distinct vertices (Leonard 1973) | `JSP000759.lean` |
| JSP-000906 | #1089 | `JSP000906.catalog_statement` — for all n ≥ 2, d: C(d+1,n−1)+1 ≤ g_d(n) ≤ C(d+n−1,n−1)+1, least-cardinality specification and limit | `JSP000906.lean` |
| JSP-000625 | #763 | `JSP000625.erdos_fuchs_bounded_error` — for every A ⊆ ℕ and c > 0, Σ_{n≤N} r_A(n) − cN is not uniformly bounded (Erdős–Fuchs 1956; proof after Newman 1998) | `JSP000625.lean` (+ `JSP000625*.lean` helpers) |

All main theorems depend only on `[propext, Classical.choice, Quot.sound]`; no `sorry`, `admit`, `native_decide`, or custom axioms.

Build: `lake exe cache get && lake build`.

Mathematical notes and machine-checked certificate data are in `notes/`.
