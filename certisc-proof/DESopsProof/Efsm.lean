import DESopsProof.Parallel
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.VecNotation

/-!
# EFSMs: syntax and meaning

The definitions of `spec/efsm.md` §2 (syntax) and §3 (meaning), after the extended finite
automata (EFA) of Sköldstam, Åkesson & Fabian, CDC 2007 ([SÅF]), with the generalizations
G1–G4 of spec §1.2.

Each definition and lemma has its statement in math first, then a **Lean:** line where the Lean
is not plain, and a **Proof:** sketch for proofs.

## Notation: math ↔ Lean

| Math | Lean |
|---|---|
| EFSMs $A_0, \dots, A_{k-1}$ | `M.aut : Fin M.k → Efsm α M.k M.nv` |
| variables $v^0, \dots, v^{n-1}$ | indices `Fin M.nv` |
| domain $V^i = [lo_i, hi_i]$, initial value $v^i_0$ | `M.lo i`, `M.hi i`, `M.init i` |
| locations | natural numbers `ℕ` (EFSM $A$ uses $0, \dots, nloc_A - 1$) |
| global state $s = (\ell, v)$ | `s : State k nv`, a pair `(s.1, s.2)` |
| $\ell_A$, the location of $A$ in $s$ | `s.1 a` |
| $v^i$ in $s$ | `s.2 i` |
| $⟦e⟧s$ (value of expression $e$ at $s$, or an error) | `e.eval s : Option ℤ` (`none`: error) |
| $s \models e$ ($⟦e⟧s$ defined and $\neq 0$) | `e.holds s = true` |
| Ξ (don't care: the edge does not write $v^i$) | `edge.upd i = none` |
| transitions of the whole system | `(sem M).f s e : Finset (State …)` |

Booleans are the integers 0 (false) and 1 (true); any nonzero value counts as true.

## Design notes

- **Locations as `ℕ`**, not `Fin nloc`: keeps `State` non-dependent. The bound is a
  well-formedness fact, not part of the type.
- **Errors.** `eval` returns `none` on an error, as CIF: `div` / `mod` by zero, or a value
  outside CIF's 32-bit integers (`fit32`; the state stays bounded by the ranges). A guard
  whose evaluation fails does not hold; an update whose evaluation fails, or whose value leaves
  its domain, gives no successor. `WF` (below) says neither happens at a reachable state:
  that is what the unfolder checks, and reports as a model error otherwise (spec §3,
  Example 2).
- **G3** (actions only need to be in range where the guard holds) is built in: an update is
  evaluated only for an edge chosen because its guard holds.
-/

namespace DESopsProof

/-! ## §2 Syntax -/

/-- Unary operators: logical not, minus, absolute value. -/
inductive UnOp
  | not | neg | abs
  deriving DecidableEq, Repr

/-- Binary operators. -/
inductive BinOp
  | and | or | imp | iff
  | eq | ne | lt | le | gt | ge
  | add | sub | mul | div | mod | min | max
  deriving DecidableEq, Repr

/-- Expressions over `k` EFSMs and `nv` variables:
- `lit c`: the integer $c$;
- `var i`: the value of $v^i$;
- `atLoc a ℓ`: CIF's `A.L`, 1 if EFSM $a$ is at location $\ell$, else 0;
- `un`, `bin`: operators; `ite c t e`: if $c$ then $t$ else $e$. -/
inductive Expr (k nv : ℕ)
  | lit (c : ℤ)
  | var (i : Fin nv)
  | atLoc (a : Fin k) (l : ℕ)
  | un (op : UnOp) (e : Expr k nv)
  | bin (op : BinOp) (x y : Expr k nv)
  | ite (c t e : Expr k nv)
  deriving DecidableEq, Repr

/-- A global state: one location per EFSM, one value per variable. -/
abbrev State (k nv : ℕ) := (Fin k → ℕ) × (Fin nv → ℤ)

/-- An edge $p \xrightarrow{\sigma / g / u} q$:
- `src` $= p$, `tgt` $= q$, `ev` $= \sigma$;
- `guard`: a list of conjuncts (empty: true);
- `upd i`: `some x` writes $v^i := x$; `none` is Ξ (does not write $v^i$; spec Example 4:
  this is not the same as `some (var i)`). -/
structure Edge (α : Type) (k nv : ℕ) where
  src : ℕ
  ev : α
  guard : List (Expr k nv)
  upd : Fin nv → Option (Expr k nv)
  tgt : ℕ

/-- One EFSM: `nloc` locations, alphabet $\Sigma_A$, initial locations (G2), marked predicate
(G1), edges. (Its kind, plant or requirement, is a tag outside the meaning.) -/
structure Efsm (α : Type) (k nv : ℕ) where
  nloc : ℕ
  alphabet : Finset α
  init : Finset ℕ
  marked : Expr k nv
  edges : List (Edge α k nv)

/-- A system: `k` EFSMs sharing `nv` variables (all variables are global, as in [SÅF] Def. 4),
with domains $[lo_i, hi_i]$ and initial values, and the event sets (G4). -/
structure EfsmSystem (α : Type) where
  k : ℕ
  nv : ℕ
  aut : Fin k → Efsm α k nv
  lo : Fin nv → ℤ
  hi : Fin nv → ℤ
  init : Fin nv → ℤ
  E : Finset α
  Euc : Finset α
  Euo : Finset α

/-! ## §3 Meaning: expressions -/

/-- $b \mapsto 1$ if $b$, else 0. -/
def b2i (b : Bool) : ℤ := if b then 1 else 0

/-- Unary operators on values (`not v` is 1 iff $v = 0$). -/
def UnOp.apply : UnOp → ℤ → Option ℤ
  | .not, v => some (b2i (v == 0))
  | .neg, v => some (-v)
  | .abs, v => some ((Int.natAbs v : ℕ) : ℤ)

/-- Binary operators on values. `div`, `mod` as CIF (spec Q6, ESCET `CifMath.div` / `mod`, which
are Java's `/` and `%`): `div` rounds toward zero (`Int.tdiv`), `mod` has the sign of $a$
(`Int.tmod`), so $a = b \cdot (a \operatorname{div} b) + (a \bmod b)$; by zero: an error. Not
Lean's `/` and `%`, which keep the remainder $\ge 0$ ($-7 / 4 = -2$, but CIF gives $-1$). The
results here are exact integers; `Expr.eval` then applies CIF's 32-bit bound (`fit32`). -/
def BinOp.apply : BinOp → ℤ → ℤ → Option ℤ
  | .and, a, b => some (b2i (a != 0 && b != 0))
  | .or, a, b => some (b2i (a != 0 || b != 0))
  | .imp, a, b => some (b2i (a == 0 || b != 0))
  | .iff, a, b => some (b2i ((a != 0) == (b != 0)))
  | .eq, a, b => some (b2i (a == b))
  | .ne, a, b => some (b2i (a != b))
  | .lt, a, b => some (b2i (decide (a < b)))
  | .le, a, b => some (b2i (decide (a ≤ b)))
  | .gt, a, b => some (b2i (decide (b < a)))
  | .ge, a, b => some (b2i (decide (b ≤ a)))
  | .add, a, b => some (a + b)
  | .sub, a, b => some (a - b)
  | .mul, a, b => some (a * b)
  | .div, a, b => if b = 0 then none else some (Int.tdiv a b)
  | .mod, a, b => if b = 0 then none else some (Int.tmod a b)
  | .min, a, b => some (Min.min a b)
  | .max, a, b => some (Max.max a b)

/-- CIF's integers are 32-bit (Java `int`): $[-2^{31},\ 2^{31} - 1]$. -/
def intMin : ℤ := -2 ^ 31
/-- See `intMin`. -/
def intMax : ℤ := 2 ^ 31 - 1

/-- A value is kept only if it is a 32-bit integer; otherwise an error (`none`):
$\mathrm{fit}(v) = v$ if $v \in [-2^{31}, 2^{31} - 1]$, else undefined. ESCET's evaluator
(`CifMath`) raises "Integer overflow" for `+`, `-`, `*`, unary `-`, `abs` and `MIN div -1`;
the other operators cannot leave the range when their operands are in it. So checking every
literal and every operator result is exactly CIF's rule. -/
def fit32 (v : ℤ) : Option ℤ := if intMin ≤ v ∧ v ≤ intMax then some v else none

variable {k nv : ℕ}

/-- $⟦e⟧s$. Both operands of a binary operator are evaluated (an error in either is an error);
`ite` evaluates only the branch it takes. Every literal and operator result goes through
`fit32` (CIF's 32-bit overflow error). A variable's value needs no check: it lies in its range
(`newVal`), and ranges are 32-bit (the reader checks them). -/
def Expr.eval (s : State k nv) : Expr k nv → Option ℤ
  | .lit c => fit32 c
  | .var i => some (s.2 i)
  | .atLoc a l => some (b2i (s.1 a == l))
  | .un op e => ((e.eval s).bind op.apply).bind fit32
  | .bin op x y =>
    ((x.eval s).bind fun a => (y.eval s).bind fun b => op.apply a b).bind fit32
  | .ite c t e => (c.eval s).bind fun v => if v ≠ 0 then t.eval s else e.eval s

/-- $s \models e$: $⟦e⟧s$ is defined and nonzero. -/
def Expr.holds (s : State k nv) (e : Expr k nv) : Bool :=
  match e.eval s with
  | some v => v != 0
  | none => false

/-! ## §3 Meaning: the FSC merge of writes ([SÅF] Def. 4)

The value of one variable after a step, from the writes of the chosen edges: `none` is Ξ, `some
c` an explicit write of $c$. -/

/-- [SÅF] Def. 4, two writes $w_1, w_2$ of a variable whose old value is $old$:
$$w_1 \oplus w_2 = \begin{cases} w_2 & w_1 = Ξ \\ w_1 & w_2 = Ξ \\ w_1 & w_1 = w_2 \\
  old & \text{otherwise (a conflict)} \end{cases}$$ -/
def merge2 (old : ℤ) : Option ℤ → Option ℤ → Option ℤ
  | none, w => w
  | some a, none => some a
  | some a, some b => if a = b then some a else some old

/-- The n-ary merge used by `sem` (spec §3): with $c_1, \dots, c_m$ the explicit writes, in order,
$$\mathrm{merge}(old, ws) = \begin{cases} old & m = 0 \\ c_1 & c_2 = \dots = c_m = c_1 \\
  old & \text{otherwise.} \end{cases}$$ -/
def mergeN (old : ℤ) (ws : List (Option ℤ)) : ℤ :=
  match ws.filterMap id with
  | [] => old
  | c :: rest => if rest.all (· == c) then c else old

/-! ## §3 Meaning: one step of the system -/

section step

variable {α : Type} [DecidableEq α] (M : EfsmSystem α)

/-- The edges of EFSM $a$ enabled at $s$ for $e$: from $a$'s current location, labelled $e$,
every guard conjunct holding. **Lean:** edge indices into `(M.aut a).edges`. -/
def enabled (s : State M.k M.nv) (a : Fin M.k) (e : α) :
    Finset (Fin (M.aut a).edges.length) :=
  Finset.univ.filter fun j =>
    (M.aut a).edges[j].src = s.1 a ∧ (M.aut a).edges[j].ev = e ∧
      (M.aut a).edges[j].guard.all (·.holds s)

/-- A choice of edges for event $e$ at $s$: for each EFSM with $e \in \Sigma_A$ one enabled edge
(`some j`); `none` for the others, which do not take part. Empty if some EFSM with $e$ has no
enabled edge (the event is blocked). **Lean:** `Fintype.piFinset` is the set of all functions
$c$ with $c(a) \in S_a$ for every $a$. -/
def choices (s : State M.k M.nv) (e : α) :
    Finset ((a : Fin M.k) → Option (Fin (M.aut a).edges.length)) :=
  Fintype.piFinset fun a =>
    if e ∈ (M.aut a).alphabet then (enabled M s a e).image some else {none}

/-- The write of EFSM $a$'s chosen edge to $v^i$, evaluated at the pre-state $s$:
`some none` = Ξ (not taking part, or not writing $v^i$), `some (some c)` = writes $c$,
`none` = evaluation error. -/
def write (s : State M.k M.nv) (c : (a : Fin M.k) → Option (Fin (M.aut a).edges.length))
    (i : Fin M.nv) (a : Fin M.k) : Option (Option ℤ) :=
  match c a with
  | none => some none
  | some j =>
    match (M.aut a).edges[j].upd i with
    | none => some none
    | some x => (x.eval s).map some

/-- The new value of $v^i$: the merge of all writes (`mergeN`), if no evaluation failed and the
value is in $[lo_i, hi_i]$; else `none`. -/
def newVal (s : State M.k M.nv) (c : (a : Fin M.k) → Option (Fin (M.aut a).edges.length))
    (i : Fin M.nv) : Option ℤ :=
  ((List.ofFn (write M s c i)).mapM id).bind fun ws =>
    let v := mergeN (s.2 i) ws
    if M.lo i ≤ v ∧ v ≤ M.hi i then some v else none

/-- The new locations: the chosen edge's target, or unchanged for EFSMs not taking part. -/
def newLoc (s : State M.k M.nv) (c : (a : Fin M.k) → Option (Fin (M.aut a).edges.length))
    (a : Fin M.k) : ℕ :=
  match c a with
  | none => s.1 a
  | some j => (M.aut a).edges[j].tgt

/-- The successor of $s$ for the choice $c$, or `none` (an update failed or left its domain). -/
def succ (s : State M.k M.nv) (c : (a : Fin M.k) → Option (Fin (M.aut a).edges.length)) :
    Option (State M.k M.nv) :=
  if h : ∀ i, (newVal M s c i).isSome then
    some (newLoc M s c, fun i => (newVal M s c i).get (h i))
  else none

/-- **The meaning of the system** (spec §3), as a transition system over global states:
- $f(s, e)$ = the successors of $s$ over all choices of enabled edges for $e$ (several: an NFA);
  empty if no EFSM has $e$ in its alphabet ([SÅF] Def. 4: the composed alphabet is the union
  of the alphabets, so such an event never occurs);
- initial states: every combination of initial locations (G2), variables at their initial
  values;
- marked: every EFSM's marked predicate holds (G1). -/
def sem : TS (State M.k M.nv) α where
  f s e :=
    if ∃ a, e ∈ (M.aut a).alphabet then
      (choices M s e).biUnion fun c =>
        match succ M s c with
        | some t => {t}
        | none => ∅
    else ∅
  X0 := (Fintype.piFinset fun a => (M.aut a).init).image fun l => (l, M.init)
  marked s := decide (∀ a, (M.aut a).marked.holds s = true)

/-- The reachable global states. -/
def Reach : Set (State M.k M.nv) := reach (sem M).f (sem M).X0

/-- **Well-formed** ([SÅF] Def. 1 with G3, spec §3): initial values in their domains, and at
every reachable state, for every event and every choice of enabled edges, the successor exists
(every update evaluates and stays in its domain). (Guard and marking errors read as false; the
unfolder reports them too.) -/
def WF : Prop :=
  (∀ i, M.lo i ≤ M.init i ∧ M.init i ≤ M.hi i) ∧
    ∀ s ∈ Reach M, ∀ e, ∀ c ∈ choices M s e, (succ M s c).isSome

end step

/-! ## (L1) The n-ary merge is [SÅF]'s binary merge, iterated -/

section merge

/-- A Ξ write changes nothing in a left fold of `merge2`:
$fold(acc, ws) = fold(acc, \text{explicit writes of } ws)$. -/
theorem foldl_merge2_filterMap (old : ℤ) (acc : Option ℤ) (ws : List (Option ℤ)) :
    ws.foldl (merge2 old) acc = ((ws.filterMap id).map some).foldl (merge2 old) acc := by
  induction ws generalizing acc with
  | nil => rfl
  | cons w ws ih =>
    cases w with
    | none =>
      cases acc <;> simp [merge2, ih]
    | some c => simp [ih]

/-- After a conflict the value stays $old$: $fold(old, cs) = old$. -/
theorem foldl_merge2_old (old : ℤ) (cs : List ℤ) :
    (cs.map some).foldl (merge2 old) (some old) = some old := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, List.foldl_cons, merge2]
    split_ifs <;> simp_all

/-- From an explicit value $c$: $fold(c, cs) = c$ if every $c' \in cs$ equals $c$, else $old$. -/
theorem foldl_merge2_some (old c : ℤ) (cs : List ℤ) :
    (cs.map some).foldl (merge2 old) (some c) =
      if cs.all (· == c) then some c else some old := by
  induction cs with
  | nil => rfl
  | cons x cs ih =>
    rw [List.map_cons, List.foldl_cons, List.all_cons]
    change (cs.map some).foldl (merge2 old) (if c = x then some c else some old) = _
    by_cases h : c = x
    · subst h
      rw [ite_eq_left rfl, ih, beq_self_eq_true, Bool.true_and]
    · rw [ite_eq_right h, foldl_merge2_old]
      have hx : (x == c) = false := beq_false_of_ne (Ne.symm h)
      rw [hx, Bool.false_and]
      rfl

/-- **(L1)** Merging the writes $w_1, \dots, w_m$ two at a time with [SÅF] Def. 4, left to
right, gives `mergeN`:
$$(\dots((Ξ \oplus w_1) \oplus w_2) \dots \oplus w_m), \text{ read as } old \text{ if Ξ}
  \;=\; \mathrm{merge}(old, [w_1, \dots, w_m]).$$

**Proof:** drop the Ξ writes (`foldl_merge2_filterMap`); with no explicit write both sides are
$old$; otherwise the fold starts at the first explicit write $c$ and `foldl_merge2_some` gives
$c$ if all others equal $c$, else $old$, which is `mergeN`. -/
theorem merge_fold (old : ℤ) (ws : List (Option ℤ)) :
    (ws.foldl (merge2 old) none).getD old = mergeN old ws := by
  rw [foldl_merge2_filterMap, mergeN]
  cases ws.filterMap id with
  | nil => rfl
  | cons c cs =>
    rw [List.map_cons, List.foldl_cons]
    change ((cs.map some).foldl (merge2 old) (some c)).getD old = _
    rw [foldl_merge2_some]
    change _ = (if cs.all (· == c) = true then c else old)
    by_cases h : cs.all (· == c) = true
    · rw [ite_eq_left h, ite_eq_left h]; rfl
    · rw [ite_eq_right h, ite_eq_right h]; rfl

/-- "Every other write equals the first" is "all writes are equal":
$(\forall x \in cs,\ x = c) \iff \forall x, y \in c :: cs,\ x = y$. -/
theorem all_eq_head_iff (c : ℤ) (cs : List ℤ) :
    cs.all (· == c) = true ↔ ∀ x ∈ c :: cs, ∀ y ∈ c :: cs, x = y := by
  simp only [List.all_eq_true, beq_iff_eq]
  constructor
  · intro h x hx y hy
    have hx' : x = c := by
      rcases List.mem_cons.1 hx with rfl | hx
      · rfl
      · exact h x hx
    have hy' : y = c := by
      rcases List.mem_cons.1 hy with rfl | hy
      · rfl
      · exact h y hy
    rw [hx', hy']
  · intro h x hx
    exact h x (List.mem_cons.2 (Or.inr hx)) c (List.mem_cons.2 (Or.inl rfl))

/-- `mergeN` through the explicit writes: $old$ if there are none; the first one if all are
equal; else $old$. -/
theorem mergeN_eq (old : ℤ) (ws : List (Option ℤ)) :
    mergeN old ws =
      if h : ws.filterMap id = [] then old
      else if ∀ x ∈ ws.filterMap id, ∀ y ∈ ws.filterMap id, x = y
        then (ws.filterMap id).head h else old := by
  unfold mergeN
  cases ws.filterMap id with
  | nil => rfl
  | cons c cs =>
    rw [dite_eq_right (List.cons_ne_nil c cs), List.head_cons]
    change (if cs.all (· == c) then c else old) = _
    by_cases h : cs.all (· == c) = true
    · rw [ite_eq_left h, ite_eq_left ((all_eq_head_iff c cs).1 h)]
    · rw [ite_eq_right h, ite_eq_right (mt (all_eq_head_iff c cs).2 h)]

/-- **(L1), any order.** The merge does not depend on the order of the writes: a permutation
$ws'$ of $ws$ gives the same value. So the system's merge equals $E_1 \| \dots \| E_k$ of
[SÅF] composed in any order.

**Proof:** by `mergeN_eq`, the value depends only on which explicit writes occur (the same for
a permutation), except for the first one; when all are equal, the two first ones are both
members and so equal. -/
theorem mergeN_perm (old : ℤ) {ws ws' : List (Option ℤ)} (h : ws.Perm ws') :
    mergeN old ws = mergeN old ws' := by
  have hp : (ws.filterMap id).Perm (ws'.filterMap id) := h.filterMap id
  have hmem : ∀ x, x ∈ ws.filterMap id ↔ x ∈ ws'.filterMap id := fun x => hp.mem_iff
  rw [mergeN_eq, mergeN_eq]
  by_cases h0 : ws.filterMap id = []
  · have h0' : ws'.filterMap id = [] := (List.Perm.nil_eq (h0 ▸ hp)).symm
    rw [dite_eq_left h0, dite_eq_left h0']
  · have h0' : ws'.filterMap id ≠ [] := fun h' => h0 (List.Perm.eq_nil (h' ▸ hp))
    rw [dite_eq_right h0, dite_eq_right h0']
    by_cases hall : ∀ x ∈ ws.filterMap id, ∀ y ∈ ws.filterMap id, x = y
    · have hall' : ∀ x ∈ ws'.filterMap id, ∀ y ∈ ws'.filterMap id, x = y := by
        intro x hx y hy; exact hall x ((hmem x).2 hx) y ((hmem y).2 hy)
      rw [ite_eq_left hall, ite_eq_left hall']
      exact hall _ (List.head_mem h0) _ ((hmem _).2 (List.head_mem h0'))
    · have hall' : ¬ ∀ x ∈ ws'.filterMap id, ∀ y ∈ ws'.filterMap id, x = y := by
        intro h'; exact hall fun x hx y hy => h' x ((hmem x).1 hx) y ((hmem y).1 hy)
      rw [ite_eq_right hall, ite_eq_right hall']

end merge

/-! ## The unfolder's result: `IsFlat`

`H` is the automaton the library returns, with labels `φ i` = the global state of its state `i`.
`IsFlat` lists the facts the verified unfolder will establish (spec §9); from them, `H` has the
languages of the system's meaning. -/

section flat

variable {α : Type} [DecidableEq α] {M : EfsmSystem α}

/-- $H$ is the flat automaton of $M$ with state labels $\varphi$:
- step, sound: $y \in f_H(i, e) \implies \varphi(y) \in f_M(\varphi(i), e)$;
- step, complete: $q \in f_M(\varphi(i), e) \implies \exists y \in f_H(i, e),\ \varphi(y) = q$;
- initial, sound and complete: $\varphi(X_{0H}) = X_{0M}$;
- marked: $m_H(i) = m_M(\varphi(i))$;
- events: $E_H = E_M$, and the same for $E_{uc}$, $E_{uo}$. -/
structure IsFlat (M : EfsmSystem α) (H : Automaton α) (φ : Fin H.n → State M.k M.nv) : Prop where
  step_sound : ∀ i e y, y ∈ H.f i e → φ y ∈ (sem M).f (φ i) e
  step_complete : ∀ i e q, q ∈ (sem M).f (φ i) e → ∃ y ∈ H.f i e, φ y = q
  init_sound : ∀ i ∈ H.X0, φ i ∈ (sem M).X0
  init_complete : ∀ q ∈ (sem M).X0, ∃ i ∈ H.X0, φ i = q
  marked : ∀ i, H.marked i = (sem M).marked (φ i)
  E : H.E = M.E
  Euc : H.Euc = M.Euc
  Euo : H.Euo = M.Euo

namespace IsFlat

variable {H : Automaton α} {φ : Fin H.n → State M.k M.nv}

/-- $\varphi(f_H(i, e)) = f_M(\varphi(i), e)$. **Proof:** `step_sound`, `step_complete`. -/
theorem image_f (h : IsFlat M H φ) (i : Fin H.n) (e : α) :
    (H.f i e).image φ = (sem M).f (φ i) e := by
  ext q
  rw [Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact h.step_sound i e y hy
  · exact h.step_complete i e q

/-- $\varphi(X_{0H}) = X_{0M}$. **Proof:** `init_sound`, `init_complete`. -/
theorem image_X0 (h : IsFlat M H φ) : H.X0.image φ = (sem M).X0 := by
  ext q
  rw [Finset.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact h.init_sound i hi
  · exact h.init_complete q

/-- $L(H) = L(M)$ (`gen_eq_of_labels`). -/
theorem L (h : IsFlat M H φ) : H.L = (sem M).L :=
  gen_eq_of_labels φ h.image_X0 h.image_f

/-- $L_m(H) = L_m(M)$ (`mkd_eq_of_labels`). -/
theorem Lm (h : IsFlat M H φ) : H.Lm = (sem M).Lm :=
  mkd_eq_of_labels φ h.image_X0 h.image_f h.marked

end IsFlat

end flat

/-! ## Spec §4: the worked examples, checked

Events are natural numbers here (`0` = `e` or `inc`). Each `example` is closed by `decide`: Lean
computes both sides. -/

namespace Examples

/-- An edge from location 0 to location 0 on event 0, no guard, updates `u`. -/
def loop {k nv : ℕ} (u : Fin nv → Option (Expr k nv)) (g : List (Expr k nv) := []) :
    Edge ℕ k nv := ⟨0, 0, g, u, 0⟩

/-- One-location EFSM with alphabet {0}, always marked. -/
def one {k nv : ℕ} (edges : List (Edge ℕ k nv)) : Efsm ℕ k nv :=
  ⟨1, {0}, {0}, .lit 1, edges⟩

/-- **Example 1, swap.** $x, y \in [0,1]$, $x = 0, y = 1$; one edge `x := y, y := x`. -/
def swap : EfsmSystem ℕ where
  k := 1
  nv := 2
  aut _ := one [loop ![some (.var 1), some (.var 0)]]
  lo _ := 0
  hi _ := 1
  init := ![0, 1]
  E := {0}
  Euc := ∅
  Euo := ∅

/-- From $(x, y) = (0, 1)$, `e` leads to $(1, 0)$ only: the updates are simultaneous. -/
example : (sem swap).f (fun _ => 0, ![0, 1]) 0 = {(fun _ => 0, ![1, 0])} := by decide

/-- **Example 1, split over two EFSMs**: `A: x := y`, `B: y := x`. The same swap. -/
def swap2 : EfsmSystem ℕ where
  k := 2
  nv := 2
  aut := ![one [loop ![some (.var 1), none]], one [loop ![none, some (.var 0)]]]
  lo _ := 0
  hi _ := 1
  init := ![0, 1]
  E := {0}
  Euc := ∅
  Euo := ∅

example : (sem swap2).f (fun _ => 0, ![0, 1]) 0 = {(fun _ => 0, ![1, 0])} := by decide

/-- **Example 2, out of range.** $x \in [0, 2]$, `inc: x := x + 1`, no guard. -/
def counter (g : List (Expr 1 1)) : EfsmSystem ℕ where
  k := 1
  nv := 1
  aut _ := one [loop ![some (.bin .add (.var 0) (.lit 1))] g]
  lo _ := 0
  hi _ := 2
  init _ := 0
  E := {0}
  Euc := ∅
  Euo := ∅

/-- At $x = 2$ the only choice has no successor ($3 \notin [0, 2]$): a model error. -/
example : (choices (counter []) (fun _ => 0, fun _ => 2) 0).card = 1 ∧
    (sem (counter [])).f (fun _ => 0, fun _ => 2) 0 = ∅ := by decide

/-- With the guard $x < 2$, nothing is enabled at $x = 2$ (no choice, so no error), and
$x = 1$ steps to $x = 2$. -/
example : choices (counter [.bin .lt (.var 0) (.lit 2)]) (fun _ => 0, fun _ => 2) 0 = ∅ ∧
    (sem (counter [.bin .lt (.var 0) (.lit 2)])).f (fun _ => 0, fun _ => 1) 0 =
      {(fun _ => 0, fun _ => 2)} := by decide

/-- **Example 3, conflicting writes.** $x \in [0, 2]$, `A: x := 1`, `B: x := 2`. -/
def conflict : EfsmSystem ℕ where
  k := 2
  nv := 1
  aut := ![one [loop ![some (.lit 1)]], one [loop ![some (.lit 2)]]]
  lo _ := 0
  hi _ := 2
  init _ := 0
  E := {0}
  Euc := ∅
  Euo := ∅

/-- $x$ is not updated: $x = 0$ steps to $x = 0$. -/
example : (sem conflict).f (fun _ => 0, fun _ => 0) 0 = {(fun _ => 0, fun _ => 0)} := by
  decide

/-- **Example 4, Ξ is not `x := x`.** $x \in [0, 1]$; `B: x := 1`; `A` writes nothing (Ξ) or
writes `x := x`. -/
def xi (a : Option (Expr 2 1)) : EfsmSystem ℕ where
  k := 2
  nv := 1
  aut := ![one [loop ![a]], one [loop ![some (.lit 1)]]]
  lo _ := 0
  hi _ := 1
  init _ := 0
  E := {0}
  Euc := ∅
  Euo := ∅

/-- Ξ: $x = 0$ steps to $x = 1$. -/
example : (sem (xi none)).f (fun _ => 0, fun _ => 0) 0 = {(fun _ => 0, fun _ => 1)} := by
  decide

/-- `x := x`: a conflict ($0 \neq 1$), so $x = 0$ stays. -/
example : (sem (xi (some (.var 0)))).f (fun _ => 0, fun _ => 0) 0 =
    {(fun _ => 0, fun _ => 0)} := by decide

/-- **Example 5, marking** $x + y \ge 1$: marked at $(0,1), (1,0), (1,1)$, not at $(0,0)$. -/
def mark : EfsmSystem ℕ where
  k := 1
  nv := 2
  aut _ := ⟨1, {0}, {0}, .bin .ge (.bin .add (.var 0) (.var 1)) (.lit 1), []⟩
  lo _ := 0
  hi _ := 1
  init _ := 0
  E := {0}
  Euc := ∅
  Euo := ∅

/-- An event in no alphabet never occurs (event 1 here; the alphabet is {0}). -/
example : (sem mark).f (fun _ => 0, ![0, 0]) 1 = ∅ := by decide

example : (sem mark).marked (fun _ => 0, ![0, 0]) = false ∧
    (sem mark).marked (fun _ => 0, ![0, 1]) = true ∧
    (sem mark).marked (fun _ => 0, ![1, 0]) = true ∧
    (sem mark).marked (fun _ => 0, ![1, 1]) = true := by decide

/-- `div` / `mod` as CIF (spec Q6): the values of ESCET's `CifMathTest.testDiv` / `testMod`
($\pm 7$ by $\pm 4$), and division by zero is an error. -/
example : BinOp.apply .div 7 4 = some 1 ∧ BinOp.apply .div 7 (-4) = some (-1) ∧
    BinOp.apply .div (-7) 4 = some (-1) ∧ BinOp.apply .div (-7) (-4) = some 1 := by decide

example : BinOp.apply .mod 7 4 = some 3 ∧ BinOp.apply .mod 7 (-4) = some 3 ∧
    BinOp.apply .mod (-7) 4 = some (-3) ∧ BinOp.apply .mod (-7) (-4) = some (-3) := by decide

example : BinOp.apply .div 1 0 = none ∧ BinOp.apply .mod 1 0 = none := by decide

/-- 32-bit overflow is an error, as in CIF (ESCET `CifMathTest`: `testAddOverflow`,
`testMultiplyOverflow`, `testDivOverflow`, `testNegateOverflow`), evaluated in an empty system
state (no locations, no variables); in-range results are kept. -/
def s0 : State 0 0 := (fun i => i.elim0, fun i => i.elim0)

example : (Expr.bin .add (.lit intMax) (.lit 1) : Expr 0 0).eval s0 = none ∧
    (Expr.bin .mul (.lit 65536) (.lit 32768) : Expr 0 0).eval s0 = none ∧
    (Expr.bin .div (.lit intMin) (.lit (-1)) : Expr 0 0).eval s0 = none ∧
    (Expr.un .neg (.lit intMin) : Expr 0 0).eval s0 = none ∧
    (Expr.lit (intMax + 1) : Expr 0 0).eval s0 = none := by decide

example : (Expr.bin .sub (.lit intMax) (.lit 1) : Expr 0 0).eval s0 = some (intMax - 1) ∧
    (Expr.bin .mul (.lit 65536) (.lit 16384) : Expr 0 0).eval s0 = some (2 ^ 30) ∧
    (Expr.bin .mod (.lit intMin) (.lit (-1)) : Expr 0 0).eval s0 = some 0 := by decide

/-- ESCET's `testMod2`: $a \bmod b = a - b \cdot (a \operatorname{div} b)$, for every $b \ne 0$. -/
theorem mod_eq_sub_mul_div (a b : ℤ) (hb : b ≠ 0) :
    BinOp.apply .mod a b = (BinOp.apply .div a b).map (fun q => a - b * q) := by
  simp only [BinOp.apply, hb, ite_false, Option.map_some]
  rw [Int.tmod_def]

end Examples

end DESopsProof
