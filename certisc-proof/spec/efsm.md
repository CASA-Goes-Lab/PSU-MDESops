# Spec: EFSMs (extended finite-state machines): syntax, meaning, flat automata

Status: **steps 2, 3 and the reader of 5 done 2026-11-12** (`DESopsProof/Efsm.lean`: syntax,
meaning, `IsFlat`, L1, Examples 1–5; `core_aut/efsm.py`; `io_aut/cif.py`); see §11. Answers to the questions: §12.

Naming (user, 2026-11-12): the model and everything done with it is **EFSM**, under
`core_aut`. **CIF** is only a file format: reading and writing `.cif` files in `io_aut`.
Nothing outside `io_aut/cif.py` mentions CIF.

Reference (user, 2026-11-12): **M. Sköldstam, K. Åkesson, M. Fabian, "Modeling of discrete
event systems using finite automata with variables", IEEE CDC 2007** (the EFA of Supremica),
cited below as [SÅF]. Our EFSM is their EFA with the small generalizations of §1.2, which
leave every [SÅF] model meaning the same thing. CIF models are a subset (§7).

Goals, in order (user):
1. **Syntax and meaning of EFSMs first** (Lean), independent of any file format;
2. flat automata with a proved meaning, unfolded in verified Rust (scale);
3. read CIF into it; later **write CIF**, so that ESCET's tools (synthesis, simulation) can be
   used on our models, even though our EFSM is more general than CIF (§7.2).

## 1. What we take from [SÅF], and what we add

### 1.1 Taken as is

- **Def. 1 (EFA).** `E = ⟨Q × V, Σ, →, (q0, v0)⟩`: locations `Q`; variables `v = (v¹,…,vⁿ)`
  with finite domains, `V = V¹ × … × Vⁿ`; events `Σ`; transitions `p --σ / g / a--> q` with
  a guard `g : V → {0,1}` and an action `a : V → V`, `a(v) = (a¹(v),…,aⁿ(v))`.
  **Every component `aⁱ` reads the whole pre-state `v`**: updates are simultaneous.
- **Ξ, "don't care".** `aⁱ = Ξ` means "`vⁱ` keeps its value, unless another automaton
  synchronizing on the same event writes it". An absent action is `(Ξ,…,Ξ)`. Ξ is not the same
  as an explicit `vⁱ := vⁱ` (§4, Example 4).
- **Def. 2 (explicit transitions).** `(p, v) --σ--> (q, w)` iff some `p --σ/g/a--> q` has
  `g(v) = 1` and `w = a(v)` (Ξ components keep `vⁱ`).
- **Def. 3 (deterministic EFA)**: at most one successor per (state, event), over **all** states.
- **Def. 4 (full synchronous composition, FSC).** All EFA share all variables (a variable an
  automaton does not use is a never-written "don't care" variable for it), with the same
  initial values. A shared event needs one transition of each automaton that has it; guards are
  conjoined; actions are merged per variable and per pre-state `v`:

      aⁱ(v) = a₁ⁱ(v)   if a₁ⁱ(v) = a₂ⁱ(v)
              a₁ⁱ(v)   if a₂ⁱ(v) = Ξ
              a₂ⁱ(v)   if a₁ⁱ(v) = Ξ
              vⁱ       otherwise (a conflict: the variable is not updated)

  An event that is not shared moves only its own automaton.
- **Def. 5 (action consistent).** No conflict ever happens: whenever both guards hold, the two
  updates of each variable agree or one is Ξ. A sufficient condition for the intended
  behaviour; [SÅF] do not require it, and neither do we (§4, Example 3).
- **Def. 6 (isomorphic FA).** The ordinary automaton with states `Q × V` and the explicit
  transitions. Our `flat` is its **reachable part** (same language).

### 1.2 Added (generalizations; a [SÅF] model keeps its meaning)

- **G1 Marking.** [SÅF] define no marking (only `L(E)`). Each EFSM gets a **marked
  predicate** over its location and the variables; a composed state is marked iff every
  component's predicate holds (as marking in `‖` for ordinary automata). This includes
  Supremica's form (marked locations, plus marked values per variable) as a special case, and
  also predicates such as `x + y ≥ 1` that per-variable marked values cannot express
  (Example 5).
- **G2 Initial locations.** [SÅF] have one initial state `(q0, v0)`. We allow a **set of
  initial locations** per EFSM (CIF's `initial` predicates can give several). Variables keep
  one initial value each (Q5); several initial values (`in any`) later.
- **G3 Actions defined only where the guard holds.** [SÅF] ask `a : V → V` to be total. In
  practice `x := x + 1` with `x ∈ [0,2]` is guarded by `x < 2` and is not a function into `V`
  at `x = 2`. We ask `a(v) ∈ V` only where `g(v) = 1`. Equivalent: extend `a` by the identity
  where `g(v) = 0`; Def. 2 never looks there, so the explicit transitions are the same
  (a one-line lemma in Lean).
- **G4 Euc, Euo.** Controllable / uncontrollable (and later observable) events, as for our
  automata. [SÅF] use them in the supervisory-control setting but do not put them in Def. 1.

## 2. Syntax (abstract)

Guards and actions are written as **expressions**. The meaning of Def. 1 (any `g`, any `a`) is
recovered as "the functions our expressions denote".

- **Expressions** `Expr` (integer valued; booleans are 0 / 1):
  literal `k ∈ ℤ`; variable `vⁱ`; location test `@A = ℓ` (true iff automaton `A` is at location
  `ℓ`); `not, and, or, =>, <=>`; `= != < <= > >=`; `- + * div mod`; `if c then e₁ else e₂`;
  `abs, min, max`. (`const` and `alg` of a source format are substituted before this point.)
- **Variable declaration**: name, domain `[lo, hi] ⊂ ℤ` (bool `[0,1]`, enum with `k`
  literals `[0, k-1]`), initial value in the domain.
- **Edge**: `(p, σ, g, u, q)`: source and target locations, event, guard (a list of `Expr`,
  a conjunction; empty = true), update `u : Var ⇀ Expr` (a **partial map**: variables not in
  `u` are Ξ; `x := x` is an explicit entry).
- **EFSM**: name; kind (`plant` / `requirement`); locations; initial locations (G2);
  alphabet `Σ_A` (must contain every edge event; may contain more: an event with no edge
  blocks); edges; marked predicate (G1, an `Expr`).
- **EfsmSystem** `M`: events with `Euc` (and `Euo`); the variable declarations (global, as Def. 4);
  the EFSMs. A guard or update of any EFSM may **read and write any variable**, and **read any
  EFSM's location** (`@A = ℓ`; CIF's `A.L`). (Reading another automaton's location is not in
  [SÅF], whose guards range over `V` only. It adds nothing new: a location can be mirrored by a
  variable written on each of that automaton's edges. We keep it because CIF uses it and it
  costs nothing in the meaning; see §3.)

## 3. Meaning

Global state `s = (ℓ, v)`: one location per EFSM and a value per variable.

- `⟦e⟧s ∈ ℤ`, or an error: division by zero, or a value outside CIF's 32-bit integers
  `[-2^31, 2^31 - 1]` (every literal and every operator result is checked, Lean `fit32`; this is
  exactly where ESCET raises "Integer overflow"). The state itself is bounded by the variable
  ranges, which must be 32-bit. `div` / `mod` follow CIF's convention (Q6): `div` rounds
  toward zero, `mod` has the sign of the left operand, `a = b·(a div b) + a mod b`.
- **Step** `s --σ--> s'`: for every EFSM `A` with `σ ∈ Σ_A`, choose one edge `(ℓ_A, σ, g_A,
  u_A, q_A)` from `A`'s current location with every conjunct of `g_A` true at `s`. Then:
  `ℓ'_A = q_A` (others keep their location); each variable's new value is the **n-ary FSC
  merge** of the values written by the chosen edges (Ξ where an edge does not write it):
  all explicit values equal → that value; none → old value (Ξ); two different explicit values →
  old value (conflict). All right-hand sides are evaluated at `s` (the pre-state).
- **Well-formed** (Def. 1 with G3): at every **reachable** state, every chosen edge's update
  values lie in their variables' domains. A value outside is a **model error** reported with the
  state, the edge and the value (Example 2). (Checked on reachable states only; unreachable
  states do not change `flat`.)
- **Initial** states: every combination of initial locations, variables at their initial
  values. **Marked**: every EFSM's marked predicate holds.
- `flat(M)` = the reachable part of this transition system, as a Lean `Automaton` with events
  `E`, `Euc`, `Euo`. Rust's result is related to it by an injective state map `φ` onto the
  reachable states preserving initial, marking and transitions (as `IsComposition` in
  Parallel.lean); so `L` and `Lm` are equal and every theorem on `Automaton` applies.

Lemmas tying this to [SÅF]:
- **L1 (n-ary merge = iterated Def. 4).** Merging the writes of `A₁,…,A_k` at once equals
  merging them two at a time with Def. 4's rule, in any order (the rule is commutative and
  associative: once two explicit values differ the result is the old value). So the system
  meaning equals `E₁ ‖ … ‖ E_k` of [SÅF].
- **L2 (G3).** Extending a partial action by the identity outside its guard does not change the
  explicit transitions.
- **L3 (location tests).** Replacing `@A = ℓ` by a mirror variable written on `A`'s edges
  gives the same `flat` (up to `φ`). So location tests are only notation over [SÅF].

## 4. Worked examples

Each example: the EFSM(s), then the explicit transitions from the initial state.

**Example 1: simultaneous updates (a swap).** `x, y ∈ [0,1]`, initially `x = 0, y = 1`.
One EFSM `S`, location `L`, edge `L --e--> L` with `x := y, y := x`.

| state | `e` leads to |
|---|---|
| `(L, x=0, y=1)` | `(L, x=1, y=0)` |
| `(L, x=1, y=0)` | `(L, x=0, y=1)` |

Both right-hand sides read the pre-state, so the values swap: 2 states. Read one after the other
(`x := y; y := x`) it would give `(L,1,1)` and then stay there; that is **not** [SÅF]'s
meaning (`a(v) = (a¹(v), a²(v))`) and not CIF's. Split over two EFSMs, `A: e do x := y` and
`B: e do y := x`, Def. 4 gives `aˣ = y` (B leaves `x` as Ξ) and `aʸ = x`: the same swap. CIF:
the same, as each automaton writes only its own variable and reads the pre-state.

**Example 2: out of range.** `x ∈ [0,2]`, `x = 0`. EFSM `C`, location `L`,
edge `L --inc--> L` with `x := x + 1`, no guard.

| state | `inc` leads to |
|---|---|
| `x=0` | `x=1` |
| `x=1` | `x=2` |
| `x=2` | `x=3 ∉ [0,2]`: **model error** |

[SÅF]: `a(x) = x + 1` is not a function `V → V`, so `C` is not an EFA. CIF: a runtime error at
`x = 2`. We report: `inc at (L, x=2): x := 3 is outside [0, 2]`. The fix is a guard
`when x < 2`: 3 states, `inc` disabled at `x = 2` (allowed by G3).

**Example 3: conflicting writes.** `x ∈ [0,2]`, `x = 0`. EFSM `A`: `L --e--> L` with `x := 1`;
EFSM `B`: `M --e--> M` with `x := 2`.

| state | `e` leads to |
|---|---|
| `(L, M, x=0)` | `(L, M, x=0)` (conflict: `1 ≠ 2`, `x` is not updated) |

Legal in [SÅF] (Def. 4, last case), and not action consistent (Def. 5). We follow Def. 4 and
**warn** (event, state, the two values). Not expressible in CIF directly (two writers of `x`);
how it is written to CIF: §7.2.

**Example 4: Ξ is not `x := x`.** `x ∈ [0,1]`, `x = 0`; `B: e do x := 1`.
- `A: e` (no update of `x`: Ξ): merge(Ξ, 1) = 1, so `x=0 --e--> x=1`.
- `A: e do x := x` (explicit): at `x = 0` merge(0, 1) is a conflict, so `x=0 --e--> x=0`.

So the syntax keeps "not written" (absent from `u`) apart from `x := x`. In CIF the two never
differ (only the owner writes `x`).

**Example 5: marking (G1).** `x, y ∈ [0,1]`, one location, marked predicate `x + y ≥ 1`:
marked states `(0,1), (1,0), (1,1)`. Not a product of per-variable marked sets (that would
need `x ∈ {0,1}` and `y ∈ {0,1}` and so also mark `(0,0)`), so Supremica's per-variable
marking cannot say it, and G1 can.

**Example 6: [SÅF]'s dosing tank** (Fig. 1–2): 5 variables in `{0,1}`, all initially 0; plant
`User, S1, S2`, supervisor `Inlet Valve, Outlet Valve`; guards read variables written by other
automata (`s2_on` needs `vin = 1 ∧ vs1 = 1`; `vin` is written by `Inlet Valve`). It is action
consistent (each variable has one writer). A test model: its `flat` must be the composition of
their Fig. 3 automata after renaming the relabelled events back (Algorithm 1, step 6).

## 5. Modularity: theorems on top of the global meaning

`rd(x)`, `wr(x)`: the EFSMs whose variables or locations an expression reads, and the
variables an edge writes. An edge of `A` is **local** if its guard and update right-hand sides
read only `A`'s own variables and location, and it writes only `A`'s own variables, where
"own" is a partition of the variables chosen by the planner (§9).

- **T1 (local systems compose).** If every edge is local, then
  `flat(M) ≅ flat(A₁) ‖ … ‖ flat(A_k)` (same states up to `φ`, same transitions, same
  marking; so the same languages). No conflicts can arise (each variable has one writer).
- **T2 (moving a conjunct).** A guard conjunct `c` on `A`'s `e`-edges with `rd(c) ⊆ B`, `B ≠ A`,
  moves to `B` (added to every `e`-edge of `B`, or as an `e` self-loop at every location of `B`
  if `e ∉ Σ_B`), provided **every** `e`-edge of `A` carries `c`. The meaning is unchanged.
- **T3 (merging).** `A·B`: locations `Q_A × Q_B`, alphabet `Σ_A ∪ Σ_B`, edges paired on
  shared events with guards conjoined and updates merged by Def. 4's rule (as an expression:
  `if a₁ = a₂ then a₁ else x`), alone otherwise. The meaning is unchanged (this is Def. 4
  itself, kept symbolic).

Pipeline: move single-owner conjuncts (T2); merge what is still coupled (T3): EFSMs linked by
multi-owner conjuncts, by updates reading another EFSM, or by writing the same variable; unfold
each group and compose (T1). Datacenter (`datacenter.cif`): groups `Load·CRAC1·CRAC2`
(8 states, carries `load_max > removed` as a self-loop guard on `heat`) and `Room`; their
composition is the flat plant (legacy: 24 states, 88 transitions).

[SÅF]'s own modular route (Algorithm 1: location and variable automata over **relabelled**
events, then rename back) also avoids the flat product. It needs guards in a per-variable
disjunctive form and changes the alphabet; T1–T3 keep the original events, so the verified
`‖` and `supervisor` apply directly. Algorithm 1 is a candidate for later.

## 6. Requirements

- `requirement` EFSMs → the specification `H` (unfolded as their own system). If they read
  plant variables, the plant EFSMs they read are merged into `H` (T3) (user, Q3).
- State predicate requirements (CIF `requirement invariant P`) → `supervisor(G, forbidden=…)`
  with the flat plant states where `P` is false.
- Event conditions (CIF `requirement e needs g`) → a one-location requirement EFSM with an `e`
  self-loop guarded by `g`.

## 7. CIF

### 7.1 Reading: CIF is a subset

A CIF model translates into an EFSM system with the same meaning because, in CIF:
- each discrete variable is written only by the automaton that declares it, so there is one
  writer per variable: no conflicts, every CIF model is action consistent (Def. 5) and Ξ vs
  `x := x` (Example 4) does not matter;
- updates are simultaneous over the pre-state (Example 1), as Def. 1;
- an update out of range is a runtime error (Example 2), as Def. 1 / G3;
- `marked` / `initial` predicates are G1 / G2; `A.L` is a location test (L3).

Construct by construct (the translation is the only place that knows CIF):

| CIF construct | finite discrete meaning? | translation |
|---|---|---|
| events, `controllable`, `uncontrollable` (plain `event` = controllable) | yes | events, `Euc` |
| `const`, `alg`, `enum` | yes | substituted / enum as `[0, k-1]` |
| `plant`, `requirement` automata; `def` + instantiation | yes | EFSMs (kind) |
| `disc int[lo..hi] / bool / enum` | yes | variable declarations |
| locations, `initial`, `marked`, `alphabet`, `edge … when … do … goto` | yes | §2 directly |
| `group`, `import`, nested `def` | yes (naming) | flatten names |
| `func` (internal, not recursive) | yes | inline |
| `if` inside `do` | yes | one edge per branch |
| `disc … in any` / `in {…}` | yes | several initial values (after Q5) |
| `plant invariant` | yes | a state predicate restricting the system (to add to §3 when needed) |
| `requirement invariant`, `requirement e needs g` | yes | §6 |
| `monitor` | yes | edges per the monitor rule |
| channels (`send`, `receive`) | yes (finite data) | to decide |
| `cont`, `der`, time, `urgent`, `real` | no (hybrid / timed) | refused |
| unranged `int`, `string`, lists, tuples | no (unbounded) | refused |
| `svg`, `print` | no meaning | ignored |

The parser port starts from the legacy subset (rows 1–5 plus expressions); the other rows are
added one by one, each with a test.

### 7.2 Writing: from the general EFSM back to CIF

Goal: write any of our systems as CIF so that ESCET's algorithms can run on it. Our EFSM is
more general than CIF only in **who writes a variable**. Per variable `x`:
1. **One writer `A`** (the CIF case): declare `x` in `A`; `A.x` elsewhere. Direct.
2. **Never written**: a `const` with its initial value.
3. **Several writers**: merge them (T3). The merged automaton is the only writer; the merged
   updates are expressions `if a₁ = a₂ then a₁ else x` (Def. 4's rule), which CIF can write.
   Always exact. (Example 3: `A·B` with `edge e do x := if 1 = 2 then 1 else x`, i.e. `x`
   unchanged.)

An alternative to 3 that keeps the writers apart: move `x` to its own variable automaton
whose edges copy the writers' guards (reading their locations). Exact only when each writer
has at most one enabled `e`-edge at a time; later, if merging turns out too large.

So writing is: plan (which EFSMs to merge), apply T3 (proved meaning-preserving), print. The
printer is trusted, like the reader.

## 8. Where each part lives

| part | where | trusted / verified |
|---|---|---|
| syntax classes `Expr`, `Var`, `Edge`, `Efsm`, `EfsmSystem` (user-facing) | `certisc-lib/src/core_aut/efsm.py` | plain data, checked on hand-off |
| `unfold(M)` → `ValidAutomaton`; `unfold(M, groups=True)` → `{name: ValidAutomaton}` | `core_aut/efsm.py` (calls Rust) | thin wrapper |
| grouping planner (moves, merges) | `core_aut/efsm.py` | **untrusted**: Rust checks its result |
| `read_cif`, `write_cif` | `certisc-lib/src/io_aut/cif.py` | trusted parser / printer |
| hand-off: system → flat arrays | `rust/binding` | trusted marshalling, like `reencode` |
| evaluator, step, unfold, T2/T3 checks | `rust/verified/src/core_aut/efsm/` (`expr.rs`, `net.rs`, `unfold.rs`, `split.rs`) | **verified** (Verus) |
| syntax, meaning, `flat`, L1–L3, T1–T3 | `certisc-proof/DESopsProof/Efsm.lean` | **proved** (Lean) |

State names in the flat automaton: one tuple component per EFSM (location, and the variables it
writes, as the legacy `Low`, `T=0`, `Room(T=1)`), built in Python from the state vectors.

## 9. The Rust core

- **Representation.** Variables numbered `0..m`, domains `lo, hi : i64`; each EFSM's location
  is one more variable (`@A`, domain `[0, |Q_A|-1]`) **in the representation only** (the
  meaning keeps locations, proved equal). Expressions as postfix arrays (spec: a recursive
  `eval` equal to Lean's); `i64` arithmetic (two 32-bit values never overflow it), each result
  checked against the 32-bit range as Lean `fit32`, so the Rust evaluation equals Lean's.
- **State keys.** Mixed-radix `u64` of the state vector (the hand-off refuses a state space of
  `2^64` or more), reachable states in a `HashMap<u64, usize>` (vstd has its spec): memory
  follows the reachable states.
- **Unfold.** BFS from the initial states; per state and event, every combination of enabled
  edges (NFA, Q2); merge writes (L1); range check (error, Example 2); conflict report (warning,
  Example 3). Contract: the result is wf and `φ`-related to `flat(M)`; proof via the reach
  certificate (`reach_eq_of_certificate`).
- **Split check.** Verified: each planned move meets T2's condition, each merge is T3, the
  result is local. T1 then makes the composition exact without trusting the planner.

## 10. Proved, and trusted

Proved: `flat` equals the meaning (Lean), the evaluator, step and BFS (Verus), L1–L3 and
T1–T3 (Lean). Trusted: the CIF parser and printer, the marshalling into Rust, and that §3 is
[SÅF]'s meaning plus G1–G4 (checked by reading; tested on Example 6) and CIF's on its subset
(tested against ESCET when installed).

## 11. Order of work

1. This note. **Done.**
2. **Done 2026-11-12** (what was built: below). **Lean `Efsm.lean`, syntax and meaning**: `Expr`, `eval`, `Edge`, `Efsm`, `EfsmSystem`, `step`
   (with the n-ary merge), `flat`; Examples 1–5 as `decide`/`rfl` checks; L1, L2, L3.
   Built: `Expr` (with `atLoc` = CIF's `A.L`), `Edge` (update as a partial map, `none` = Ξ),
   `Efsm`, `EfsmSystem`, `eval` (strict; `ite` lazy; `div`/`mod` as CIF, `Int.tdiv`/`Int.tmod`, Q6),
   `enabled`, `choices` (one enabled edge per EFSM with the event), `write`, `mergeN`,
   `newVal` (range check), `succ`, `sem` (a `TS`), `Reach`, `WF`; `IsFlat` (the unfolder's
   contract) with `IsFlat.L` / `IsFlat.Lm`. L1 proved: `merge_fold` (n-ary merge = binary
   [SÅF] merge folded left to right) and `mergeN_perm` (any order). Examples 1–5 checked by
   `decide`. L2 holds by construction (an update is evaluated only for an edge whose guard
   holds), so no separate lemma. **Deferred:** L3 (location tests as mirror variables) and
   Example 6 (dosing tank), both before the CIF reader.
3. **Done 2026-11-12.** **Python syntax classes** (`core_aut/efsm.py`) mirroring the Lean
   ones, with the well-formedness checks that need no unfolding (names, domains, alphabets).
   Built: `Lit`, `Var`, `AtLoc`, `Un`, `Bin`, `Ite` (frozen), `Variable`, `Edge`, `Efsm`,
   `EfsmSystem` (name chosen by the user; the Lean structure has the same name) with
   `check()` and `writers()`. Names instead of Lean's indices. Tests: `tests/core_aut/test_efsm.py`.
4. **Rust** evaluator and unfold of a whole system, verified against step 2; binding; `unfold`.
5. **`io_aut/cif.py` reader** (done 2026-11-12, before step 4: `read_cif`, `parse_cif` →
   checked `EfsmSystem`; tests `tests/io_aut/test_cif.py`, translation and refusals); still to
   test once step 4 exists: Examples 1–6 as CIF, the three datacenter models flat (24 / 88 for
   `datacenter.cif`).
6. T1–T3 (Lean), planner + verified split check, `unfold(M, groups=True)`.
7. Requirements (§6); `write_cif` (§7.2); cross-check against ESCET.

## 12. Questions and answers

- **Q1.** Answered (user, 2026-11-12): theory first; the EFSM follows the theory ([SÅF],
  chosen the same day) and is not changed to fit CIF; CIF is a translation (§7).
- **Q2.** Nondeterministic models: **build the NFA** (user).
- **Q3.** Requirements reading plant variables: **merge the read plant EFSMs into `H`** (user).
- **Q4.** Unobservable events: **`Euo=`**, full observation first (user).
- **Q5.** **One initial value per variable** at first (user).
- **Q6.** Integer division of negative numbers: truncating (`-7 div 2 = -3`, `-7 mod 2 = -1`;
  C, Rust) or flooring (`-7 div 2 = -4`, `-7 mod 2 = 1`; Python, the legacy evaluator). The
  Lean `eval` must use CIF's; to read in the CIF reference manual before step 2. Irrelevant
  while values stay ≥ 0.
  **Note (user, 2026-11-12: "make a note"):** open until read in the CIF manual; `eval`'s `div`
  / `mod` is written only after that, and the convention is stated in `Efsm.lean` and in the
  Rust evaluator's comments. Searched 2026-11-12 (eclipse.dev/escet): the language tutorial
  (`cif/language-tutorial/values/integers.html`) has only non-negative examples (`9 div 4 = 2`,
  `9 mod 4 = 1`) and says `/` on integers gives a **real** (`9 / 4 = 2.25`), so `/` is outside
  our integer expressions (refused by the reader). The reference manual's rules for negative
  operands, division by zero and overflow were not found (the old manual URL is gone). Until
  read: `eval` gives an error on `div`/`mod` with a negative operand or a zero divisor.
  **Answered 2026-11-12: truncating** (user: "go ahead to fix it"). The CIF manual (PDF v13.0,
  847 pages, read in full by text search) does not state it: its only `div` example is
  `9 div 4 = 2`, it says division and modulus by zero are runtime errors, and several tools
  accept only positive divisors. ESCET's evaluator does: `CifMath.div` returns Java's `x / y`
  and `CifMath.mod` Java's `x % y`, both raising "Division by zero" for `y = 0` (GitLab
  `eclipse/escet/escet`, `cif/org.eclipse.escet.cif.common/src/.../CifMath.java`, develop,
  commit `8d93ffb0`). Its tests pin it: `testDiv` 7/4 = 1, 7/−4 = −1, −7/4 = −1, −7/−4 = 1;
  `testMod` 3, 3, −3, −3; `testDiv2` "`a div b` = `if a / b >= 0: floor(a / b) else
  ceil(a / b) end`"; `testMod2` "`a mod b` = `a - b * (a div b)`". So: `-7 div 2 = -3`,
  `-7 mod 2 = -1`. Done: Lean `BinOp.apply` uses `Int.tdiv` / `Int.tmod` (Lean's own `/`, `%`
  keep the remainder ≥ 0, which is neither), with `decide` checks of ESCET's test values and
  `mod_eq_sub_mul_div`; the reader's `_static` truncates (Python's `//` floors). The Rust
  evaluator can use Rust's `/` and `%`, which truncate. The legacy DESops evaluator floors, so
  it disagreed with ESCET on negative operands. **32-bit overflow (closed 2026-11-12, user: "close
  the gap"):** CIF's `int` is Java's (manual §2.5.4: "-2,147,483,648 to 2,147,483,647 ... Using
  values outside that range results in the CIF model being invalid"); ESCET's `CifMath` raises
  "Integer overflow" for `+ - *`, unary `-`, `abs`, `MIN div -1`. Lean `eval` now applies
  `fit32` to every literal and operator result (the other operators cannot leave the range on
  in-range operands, so this is exactly CIF's rule), with `decide` checks; the reader's
  `_static` does the same, and `EfsmSystem.check` requires 32-bit variable ranges. There is no
  literal `2147483648`, so `-2147483648` is an overflow too; CIF writes it `-(2147483647) - 1`
  (manual, CIF/SVG value representation).
- **Q7.** Conflicting writes (Example 3): **follow Def. 4 and warn** (user, 2026-11-12).
- **Q8.** Location tests: **keep them**, written `A.L` as in CIF (user, 2026-11-12). §2's
  `@A = ℓ` is the same thing.
