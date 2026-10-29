import DESopsProof.Automaton
import Mathlib.Data.Finset.Prod

/-!
# Parallel composition and product

The definitions and theorems of `spec/parallel.md`, §2 (draft of 2026-10-29).

- (L1, L2, L2'): `G1 ‖ G2` over pairs of states (`par`), its languages and determinism.
- (L3, L5): the bridge from local facts about a labelled automaton `H` to its languages and its
  determinism (`gen_eq_of_labels`, `mkd_eq_of_labels`, `det_of_labels`).
- Modes: both operations as one construction `comp mode` (`syncF`); `par = comp parMode`
  (`par_eq_comp`), and the product `prod = comp prodMode` with its languages and determinism.
- (L4): `IsComposition`, the facts the verified checker establishes about the Python output, and
  the results `IsComposition.par_L`, `par_Lm`, `prod_L`, `prod_Lm`.

Notation as in `Automaton.lean`. In addition:

| Math | Lean |
|---|---|
| transition system $(f, X_0, X_m)$ over states $\sigma$ | `T : TS σ α` |
| $P_E(s)$, $s$ with the events outside $E$ erased | `proj E s` |
| $\varphi(S) = \{\varphi(i) \mid i \in S\}$ | `S.image φ` |
| $S_1 \times S_2$ | `S1 ×ˢ S2` |
| $s \in E^*$ | `∀ e ∈ s, e ∈ E` |
-/

namespace DESopsProof

variable {α : Type} {σ τ ι : Type} [DecidableEq σ] [DecidableEq τ] [DecidableEq ι]

/-! ## Transition systems -/

/-- A transition system $(f, X_0, X_m)$ over the states `σ`: an automaton without the event sets
and without well-formedness. The product `G1 ‖ G2` is one, over pairs of states. -/
structure TS (σ α : Type) where
  f : σ → α → Finset σ
  X0 : Finset σ
  marked : σ → Bool

namespace TS

variable (T : TS σ α)

/-- $L(T)$. -/
def L : Language α := gen T.f T.X0
/-- $L_m(T)$. -/
def Lm : Language α := mkd T.f T.X0 T.marked
/-- $|X_0| \le 1$ and $|f(x, e)| \le 1$ for all $x, e$. -/
def IsDeterministic : Prop := T.X0.card ≤ 1 ∧ ∀ x e, (T.f x e).card ≤ 1

end TS

/-- If every transition uses an event of $E$, every word that leads somewhere is in $E^*$:
$$\bigl(\forall x, e:\ f(x, e) \neq \emptyset \implies e \in E\bigr) \implies
  \bigl(f^*(S, s) \neq \emptyset \implies s \in E^*\bigr).$$

**Proof:** induction on $s$ for every $S$. If $f^*(S, e \cdot s) \neq \emptyset$, then
$\delta_f(S, e) \neq \emptyset$ (else the run is empty from there on), so some $f(x, e) \neq \emptyset$
and $e \in E$; the rest of $s$ follows from the induction hypothesis. -/
theorem mem_of_run_nonempty (f : σ → α → Finset σ) (E : Finset α)
    (hf : ∀ x e, (f x e).Nonempty → e ∈ E) :
    ∀ (S : Finset σ) (s : List α), (run f S s).Nonempty → ∀ e ∈ s, e ∈ E := by
  intro S s
  induction s generalizing S with
  | nil => intro _ e he; simp at he
  | cons a s ih =>
    intro h e he
    rw [run_cons] at h
    rcases List.mem_cons.1 he with rfl | he'
    · have hstep : (step f S e).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h0
        rw [h0, run_empty] at h
        exact Finset.not_nonempty_empty h
      obtain ⟨y, hy⟩ := hstep
      obtain ⟨x, -, hyx⟩ := (mem_step f).1 hy
      exact hf x e ⟨y, hyx⟩
    · exact ih _ h e he'

/-! ## §4 (L3): from local facts to languages

`H` has transitions `fH`, initial states `X0H` and marking `mH` over states `ι` (`Fin k` for the
Python output). `φ : ι → σ` labels each state of `H` with a state of `T`. -/

section bridge

variable (φ : ι → σ) {fH : ι → α → Finset ι} {f : σ → α → Finset σ}

/-- One step commutes with the labels: if $\varphi(f_H(i, e)) = f(\varphi(i), e)$ for all $i, e$,
then $\varphi(\delta_{f_H}(S, e)) = \delta_f(\varphi(S), e)$.

**Proof:** both sides are $\bigcup_{i \in S} f(\varphi(i), e)$: the image of a union is the union
of the images (`Finset.image_biUnion`), and a union over $\varphi(S)$ is a union over $S$
(`Finset.biUnion_image`). -/
theorem image_step (hstep : ∀ i e, (fH i e).image φ = f (φ i) e) (S : Finset ι) (e : α) :
    (step fH S e).image φ = step f (S.image φ) e := by
  simp only [step, Finset.image_biUnion, hstep, Finset.biUnion_image]

/-- Runs commute with the labels: $\varphi(f_H^*(S, s)) = f^*(\varphi(S), s)$.

**Proof:** induction on $s$ for every $S$, using `image_step` at each event. -/
theorem image_run (hstep : ∀ i e, (fH i e).image φ = f (φ i) e) (S : Finset ι) (s : List α) :
    (run fH S s).image φ = run f (S.image φ) s := by
  induction s generalizing S with
  | nil => rfl
  | cons e s ih => rw [run_cons, run_cons, ih, image_step φ hstep]

/-- **(L3), generated language.** *start* $\varphi(X_{0H}) = X_0$ and *step* give $L(H) = L(T)$.

**Proof:** $f_H^*(X_{0H}, s) \neq \emptyset \iff \varphi(f_H^*(X_{0H}, s)) \neq \emptyset
\iff f^*(\varphi(X_{0H}), s) \neq \emptyset \iff f^*(X_0, s) \neq \emptyset$. -/
theorem gen_eq_of_labels {X0H : Finset ι} {X0 : Finset σ} (h0 : X0H.image φ = X0)
    (hstep : ∀ i e, (fH i e).image φ = f (φ i) e) : gen fH X0H = gen f X0 := by
  ext s
  rw [mem_gen, mem_gen, ← Finset.image_nonempty (f := φ), image_run φ hstep, h0]

/-- **(L3), marked language.** *start*, *step* and *marking* $m_H(i) = m(\varphi(i))$ give
$L_m(H) = L_m(T)$.

**Proof:** a marked $y \in f_H^*(X_{0H}, s)$ gives the marked $\varphi(y)$ in
$\varphi(f_H^*(X_{0H}, s)) = f^*(X_0, s)$; conversely a marked $z$ there is some $\varphi(y)$
with $y \in f_H^*(X_{0H}, s)$, and $m_H(y) = m(z)$. -/
theorem mkd_eq_of_labels {X0H : Finset ι} {X0 : Finset σ} {mH : ι → Bool} {m : σ → Bool}
    (h0 : X0H.image φ = X0) (hstep : ∀ i e, (fH i e).image φ = f (φ i) e)
    (hm : ∀ i, mH i = m (φ i)) : mkd fH X0H mH = mkd f X0 m := by
  ext s
  rw [mem_mkd, mem_mkd, ← h0, ← image_run φ hstep]
  constructor
  · rintro ⟨y, hy, hmy⟩
    exact ⟨φ y, Finset.mem_image_of_mem φ hy, (hm y) ▸ hmy⟩
  · rintro ⟨z, hz, hmz⟩
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
    exact ⟨y, hy, (hm y).symm ▸ hmz⟩

omit [DecidableEq ι] in
/-- **(L5), determinism.** If moreover $\varphi$ is injective and $T$ is deterministic, so is $H$:
$|X_{0H}| = |\varphi(X_{0H})| = |X_0| \le 1$ and $|f_H(i, e)| = |\varphi(f_H(i, e))| =
|f(\varphi(i), e)| \le 1$ (an injective map keeps sizes, `Finset.card_image_of_injective`). -/
theorem det_of_labels {X0H : Finset ι} {T : TS σ α} (hφ : Function.Injective φ)
    (h0 : X0H.image φ = T.X0) (hstep : ∀ i e, (fH i e).image φ = T.f (φ i) e)
    (hT : T.IsDeterministic) : X0H.card ≤ 1 ∧ ∀ i e, (fH i e).card ≤ 1 := by
  constructor
  · rw [← Finset.card_image_of_injective X0H hφ, h0]
    exact hT.1
  · intro i e
    rw [← Finset.card_image_of_injective _ hφ, hstep]
    exact hT.2 _ e

end bridge

/-! ## §3 (L1): the product -/

section product

variable [DecidableEq α]

/-- $P_E(s)$: $s$ with the events outside $E$ erased. -/
def proj (E : Finset α) (s : List α) : List α := s.filter (fun e => decide (e ∈ E))

@[simp] theorem proj_nil (E : Finset α) : proj E [] = [] := rfl

theorem proj_cons (E : Finset α) (e : α) (s : List α) :
    proj E (e :: s) = if e ∈ E then e :: proj E s else proj E s := by
  unfold proj
  by_cases h : e ∈ E <;> simp [h]

/-- The product transition function (spec §2):
$$f_\parallel((x_1, x_2), e) = \begin{cases}
  f_1(x_1, e) \times f_2(x_2, e) & e \in E_1 \cap E_2 \\
  f_1(x_1, e) \times \{x_2\} & e \in E_1 \setminus E_2 \\
  \{x_1\} \times f_2(x_2, e) & e \in E_2 \setminus E_1 \\
  \emptyset & \text{otherwise.}
\end{cases}$$ -/
def parF (f1 : σ → α → Finset σ) (f2 : τ → α → Finset τ) (E1 E2 : Finset α) :
    σ × τ → α → Finset (σ × τ) :=
  fun p e =>
    if e ∈ E1 then (if e ∈ E2 then f1 p.1 e ×ˢ f2 p.2 e else f1 p.1 e ×ˢ {p.2})
    else (if e ∈ E2 then {p.1} ×ˢ f2 p.2 e else ∅)

/-- **(L1)** $G_1 \parallel G_2$ as a transition system over pairs of states:
$X_0 = X_{01} \times X_{02}$, and $(x_1, x_2)$ is marked iff $x_1$ and $x_2$ are. -/
def par (G1 G2 : Automaton α) : TS (Fin G1.n × Fin G2.n) α where
  f := parF G1.f G2.f G1.E G2.E
  X0 := G1.X0 ×ˢ G2.X0
  marked := fun p => G1.marked p.1 && G2.marked p.2

variable {f1 : σ → α → Finset σ} {f2 : τ → α → Finset τ} {E1 E2 : Finset α}

omit [DecidableEq σ] [DecidableEq τ] in
/-- $f_\parallel(p, e) \neq \emptyset \implies e \in E_1 \cup E_2$ (the product satisfies W1). -/
theorem parF_nonempty {p : σ × τ} {e : α} (h : (parF f1 f2 E1 E2 p e).Nonempty) :
    e ∈ E1 ∪ E2 := by
  unfold parF at h
  by_cases h1 : e ∈ E1
  · exact Finset.mem_union_left _ h1
  · by_cases h2 : e ∈ E2
    · exact Finset.mem_union_right _ h2
    · simp [h1, h2] at h

/-- One step from a product of sets is a product of sets ("rectangle"):
$\delta_\parallel(S_1 \times S_2, e)$ is $\delta_1(S_1, e) \times \delta_2(S_2, e)$,
$\delta_1(S_1, e) \times S_2$ or $S_1 \times \delta_2(S_2, e)$ for a shared, $G_1$-only or
$G_2$-only event. Stated with the next sets as $\delta_i$ or $S_i$ depending on membership.

**Proof:** membership on both sides, case by case (`Finset.mem_product`, `mem_step`). -/
theorem step_parF (S1 : Finset σ) (S2 : Finset τ) {e : α} (he : e ∈ E1 ∪ E2) :
    step (parF f1 f2 E1 E2) (S1 ×ˢ S2) e =
      (if e ∈ E1 then step f1 S1 e else S1) ×ˢ (if e ∈ E2 then step f2 S2 e else S2) := by
  ext ⟨y1, y2⟩
  by_cases h1 : e ∈ E1 <;> by_cases h2 : e ∈ E2
  · simp only [mem_step, parF, h1, h2, ↓reduceIte, Finset.mem_product, Prod.exists]
    constructor
    · rintro ⟨x1, x2, ⟨hx1, hx2⟩, hy1, hy2⟩
      exact ⟨⟨x1, hx1, hy1⟩, ⟨x2, hx2, hy2⟩⟩
    · rintro ⟨⟨x1, hx1, hy1⟩, ⟨x2, hx2, hy2⟩⟩
      exact ⟨x1, x2, ⟨hx1, hx2⟩, hy1, hy2⟩
  · simp only [mem_step, parF, h1, h2, ↓reduceIte, Finset.mem_product,
      Finset.mem_singleton, Prod.exists]
    constructor
    · rintro ⟨x1, x2, ⟨hx1, hx2⟩, hy1, rfl⟩
      exact ⟨⟨x1, hx1, hy1⟩, hx2⟩
    · rintro ⟨⟨x1, hx1, hy1⟩, hy2⟩
      exact ⟨x1, y2, ⟨hx1, hy2⟩, hy1, rfl⟩
  · simp only [mem_step, parF, h1, h2, ↓reduceIte, Finset.mem_product,
      Finset.mem_singleton, Prod.exists]
    constructor
    · rintro ⟨x1, x2, ⟨hx1, hx2⟩, rfl, hy2⟩
      exact ⟨hx1, ⟨x2, hx2, hy2⟩⟩
    · rintro ⟨hy1, ⟨x2, hx2, hy2⟩⟩
      exact ⟨y1, x2, ⟨hy1, hx2⟩, rfl, hy2⟩
  · exact absurd he (by simp [h1, h2])

/-- Runs from a product of sets stay products of sets, for words over $E_1 \cup E_2$:
$$f_\parallel^*(S_1 \times S_2, s) = f_1^*(S_1, P_1(s)) \times f_2^*(S_2, P_2(s)).$$

**Proof:** induction on $s$ for every $S_1, S_2$: `step_parF`, and $P_i(e \cdot s)$ is
$e \cdot P_i(s)$ if $e \in E_i$ and $P_i(s)$ otherwise. -/
theorem run_parF (S1 : Finset σ) (S2 : Finset τ) (s : List α) (hs : ∀ e ∈ s, e ∈ E1 ∪ E2) :
    run (parF f1 f2 E1 E2) (S1 ×ˢ S2) s = run f1 S1 (proj E1 s) ×ˢ run f2 S2 (proj E2 s) := by
  induction s generalizing S1 S2 with
  | nil => rfl
  | cons e s ih =>
    have he : e ∈ E1 ∪ E2 := hs e List.mem_cons_self
    have hs' : ∀ a ∈ s, a ∈ E1 ∪ E2 := fun a ha => hs a (List.mem_cons_of_mem e ha)
    rw [run_cons, step_parF S1 S2 he, ih _ _ hs', proj_cons, proj_cons]
    by_cases h1 : e ∈ E1 <;> by_cases h2 : e ∈ E2 <;> simp [h1, h2]

/-- **(L2), generated language.**
$$s \in L(G_1 \parallel G_2) \iff s \in (E_1 \cup E_2)^* \wedge P_1(s) \in L(G_1)
  \wedge P_2(s) \in L(G_2).$$

**Proof:** a word that leads somewhere is in $(E_1 \cup E_2)^*$ (`mem_of_run_nonempty`,
`parF_nonempty`); for such words, `run_parF`, and a product is nonempty iff both factors are. -/
theorem mem_par_L (G1 G2 : Automaton α) (s : List α) :
    s ∈ (par G1 G2).L ↔
      (∀ e ∈ s, e ∈ G1.E ∪ G2.E) ∧ proj G1.E s ∈ G1.L ∧ proj G2.E s ∈ G2.L := by
  constructor
  · intro h
    have hs := mem_of_run_nonempty _ _ (fun _ _ => parF_nonempty) _ s h
    refine ⟨hs, ?_⟩
    have h' := h
    change (run (parF G1.f G2.f G1.E G2.E) (G1.X0 ×ˢ G2.X0) s).Nonempty at h'
    rw [run_parF _ _ s hs, Finset.nonempty_product] at h'
    exact h'
  · rintro ⟨hs, h1, h2⟩
    change (run (parF G1.f G2.f G1.E G2.E) (G1.X0 ×ˢ G2.X0) s).Nonempty
    rw [run_parF _ _ s hs, Finset.nonempty_product]
    exact ⟨h1, h2⟩

/-- **(L2), marked language.**
$$s \in L_m(G_1 \parallel G_2) \iff s \in (E_1 \cup E_2)^* \wedge P_1(s) \in L_m(G_1)
  \wedge P_2(s) \in L_m(G_2).$$

**Proof:** as for $L$; a pair is marked iff both components are. -/
theorem mem_par_Lm (G1 G2 : Automaton α) (s : List α) :
    s ∈ (par G1 G2).Lm ↔
      (∀ e ∈ s, e ∈ G1.E ∪ G2.E) ∧ proj G1.E s ∈ G1.Lm ∧ proj G2.E s ∈ G2.Lm := by
  have key : ∀ hs : ∀ e ∈ s, e ∈ G1.E ∪ G2.E,
      s ∈ (par G1 G2).Lm ↔ proj G1.E s ∈ G1.Lm ∧ proj G2.E s ∈ G2.Lm := by
    intro hs
    change (∃ y ∈ run (parF G1.f G2.f G1.E G2.E) (G1.X0 ×ˢ G2.X0) s,
      (G1.marked y.1 && G2.marked y.2) = true) ↔ _
    rw [run_parF _ _ s hs]
    simp only [Automaton.Lm, mem_mkd, Finset.mem_product, Bool.and_eq_true, Prod.exists]
    constructor
    · rintro ⟨y1, y2, ⟨hy1, hy2⟩, hm1, hm2⟩
      exact ⟨⟨y1, hy1, hm1⟩, ⟨y2, hy2, hm2⟩⟩
    · rintro ⟨⟨y1, hy1, hm1⟩, ⟨y2, hy2, hm2⟩⟩
      exact ⟨y1, y2, ⟨hy1, hy2⟩, hm1, hm2⟩
  constructor
  · intro h
    have hL : s ∈ (par G1 G2).L := by
      obtain ⟨y, hy, -⟩ := mem_mkd.1 h
      exact ⟨y, hy⟩
    have hs := mem_of_run_nonempty _ _ (fun _ _ => parF_nonempty) _ s hL
    exact ⟨hs, (key hs).1 h⟩
  · rintro ⟨hs, h⟩
    exact (key hs).2 h

/-- **(L2')** $G_1$, $G_2$ deterministic $\implies$ $G_1 \parallel G_2$ deterministic.

**Proof:** $|X_{01} \times X_{02}| = |X_{01}| \cdot |X_{02}| \le 1$, and in each case of
$f_\parallel$ the size is a product of sizes $\le 1$ (`Finset.card_product`). -/
theorem par_det {G1 G2 : Automaton α} (h1 : G1.IsDeterministic) (h2 : G2.IsDeterministic) :
    (par G1 G2).IsDeterministic := by
  constructor
  · change (G1.X0 ×ˢ G2.X0).card ≤ 1
    rw [Finset.card_product]
    simpa using Nat.mul_le_mul h1.1 h2.1
  · intro p e
    change (parF G1.f G2.f G1.E G2.E p e).card ≤ 1
    unfold parF
    split_ifs
    · rw [Finset.card_product]; simpa using Nat.mul_le_mul (h1.2 p.1 e) (h2.2 p.2 e)
    · rw [Finset.card_product, Finset.card_singleton]; simpa using h1.2 p.1 e
    · rw [Finset.card_product, Finset.card_singleton]; simpa using h2.2 p.2 e
    · simp

end product

/-! ## Modes: parallel composition and product as one construction (spec §1)

Both operations run on pairs of states and differ only in what each event does. A *mode* per
event says which side moves; `syncF` is the transition function for a given mode table. The
parallel composition is `syncF (parMode E1 E2)` (`parF_eq_syncF`), the product
`syncF (prodMode E1 E2)`. The Python checker checks its output against such a mode table. -/

/-- What an event does in a composition of two automata (spec §1): both sides move (`both`),
only $G_1$ (`left`), only $G_2$ (`right`), or nothing (`none`). -/
inductive Mode
  | both
  | left
  | right
  | none
  deriving DecidableEq

section modes

/-- The transition function of a composition with the mode table `mode`:
$$f_{mode}((x_1, x_2), e) = \begin{cases}
  f_1(x_1, e) \times f_2(x_2, e) & mode(e) = both \\
  f_1(x_1, e) \times \{x_2\} & mode(e) = left \\
  \{x_1\} \times f_2(x_2, e) & mode(e) = right \\
  \emptyset & mode(e) = none.
\end{cases}$$ -/
def syncF (mode : α → Mode) (f1 : σ → α → Finset σ) (f2 : τ → α → Finset τ) :
    σ × τ → α → Finset (σ × τ) :=
  fun p e =>
    match mode e with
    | .both => f1 p.1 e ×ˢ f2 p.2 e
    | .left => f1 p.1 e ×ˢ {p.2}
    | .right => {p.1} ×ˢ f2 p.2 e
    | .none => ∅

/-- The composition of $G_1$ and $G_2$ with the mode table `mode`, as a transition system over
pairs of states: $X_0 = X_{01} \times X_{02}$, and $(x_1, x_2)$ is marked iff $x_1$ and $x_2$
are. -/
def comp (mode : α → Mode) (G1 G2 : Automaton α) : TS (Fin G1.n × Fin G2.n) α where
  f := syncF mode G1.f G2.f
  X0 := G1.X0 ×ˢ G2.X0
  marked := fun p => G1.marked p.1 && G2.marked p.2

variable {f1 : σ → α → Finset σ} {f2 : τ → α → Finset τ} {mode : α → Mode}
  {p q : σ × τ} {e : α}

omit [DecidableEq σ] [DecidableEq τ] in
/-- A `both` event: $q \in f_{mode}(p, e) \iff q_1 \in f_1(p_1, e) \wedge q_2 \in f_2(p_2, e)$. -/
theorem mem_syncF_both (h : mode e = .both) :
    q ∈ syncF mode f1 f2 p e ↔ q.1 ∈ f1 p.1 e ∧ q.2 ∈ f2 p.2 e := by
  simp [syncF, h, Finset.mem_product]

omit [DecidableEq σ] [DecidableEq τ] in
/-- A `left` event: $q \in f_{mode}(p, e) \iff q_1 \in f_1(p_1, e) \wedge q_2 = p_2$. -/
theorem mem_syncF_left (h : mode e = .left) :
    q ∈ syncF mode f1 f2 p e ↔ q.1 ∈ f1 p.1 e ∧ q.2 = p.2 := by
  simp only [syncF, h]
  rw [Finset.mem_product, Finset.mem_singleton]

omit [DecidableEq σ] [DecidableEq τ] in
/-- A `right` event: $q \in f_{mode}(p, e) \iff q_1 = p_1 \wedge q_2 \in f_2(p_2, e)$. -/
theorem mem_syncF_right (h : mode e = .right) :
    q ∈ syncF mode f1 f2 p e ↔ q.1 = p.1 ∧ q.2 ∈ f2 p.2 e := by
  simp only [syncF, h]
  rw [Finset.mem_product, Finset.mem_singleton]

omit [DecidableEq σ] [DecidableEq τ] in
/-- A `none` event: $f_{mode}(p, e) = \emptyset$. -/
theorem syncF_none (h : mode e = .none) : syncF mode f1 f2 p e = ∅ := by
  simp [syncF, h]

/-- One step on a `both` event from a product of sets is the product of the steps:
$\delta(S_1 \times S_2, e) = \delta_1(S_1, e) \times \delta_2(S_2, e)$.

**Proof:** membership on both sides (`mem_step`, `mem_syncF_both`). -/
theorem step_syncF_both (h : mode e = .both) (S1 : Finset σ) (S2 : Finset τ) :
    step (syncF mode f1 f2) (S1 ×ˢ S2) e = step f1 S1 e ×ˢ step f2 S2 e := by
  ext ⟨y1, y2⟩
  simp only [mem_step, mem_syncF_both h, Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨x1, x2, ⟨hx1, hx2⟩, hy1, hy2⟩
    exact ⟨⟨x1, hx1, hy1⟩, ⟨x2, hx2, hy2⟩⟩
  · rintro ⟨⟨x1, hx1, hy1⟩, ⟨x2, hx2, hy2⟩⟩
    exact ⟨x1, x2, ⟨hx1, hx2⟩, hy1, hy2⟩

variable [DecidableEq α]

/-- The modes of the parallel composition: shared events `both`, private events `left` or
`right`, others `none`. -/
def parMode (E1 E2 : Finset α) (e : α) : Mode :=
  if e ∈ E1 then (if e ∈ E2 then .both else .left) else (if e ∈ E2 then .right else .none)

/-- The modes of the product: shared events `both`, all others `none` (spec §1: the private
events stay in the alphabet, question 2, but are never enabled). -/
def prodMode (E1 E2 : Finset α) (e : α) : Mode :=
  if e ∈ E1 ∧ e ∈ E2 then .both else .none

omit [DecidableEq σ] [DecidableEq τ] in
/-- The parallel transition function is the composition with the parallel modes:
`parF f1 f2 E1 E2 = syncF (parMode E1 E2) f1 f2`.

**Proof:** the four cases of $e \in E_1$, $e \in E_2$ give the same set on both sides. -/
theorem parF_eq_syncF (E1 E2 : Finset α) : parF f1 f2 E1 E2 = syncF (parMode E1 E2) f1 f2 := by
  funext p e
  by_cases h1 : e ∈ E1 <;> by_cases h2 : e ∈ E2 <;> simp [parF, syncF, parMode, h1, h2]

/-- $G_1 \parallel G_2$ is the composition with the parallel modes. -/
theorem par_eq_comp (G1 G2 : Automaton α) : par G1 G2 = comp (parMode G1.E G2.E) G1 G2 := by
  unfold par comp
  rw [parF_eq_syncF]

/-- **(L1)** The product $G_1 \times G_2$: the composition with the product modes. -/
def prod (G1 G2 : Automaton α) : TS (Fin G1.n × Fin G2.n) α :=
  comp (prodMode G1.E G2.E) G1 G2

variable {E1 E2 : Finset α}

omit [DecidableEq σ] [DecidableEq τ] in
/-- $f_\times(p, e) \neq \emptyset \implies e \in E_1 \wedge e \in E_2$: the product moves only
on shared events.

**Proof:** otherwise the mode of $e$ is `none` and the set is empty. -/
theorem prodF_nonempty (h : (syncF (prodMode E1 E2) f1 f2 p e).Nonempty) : e ∈ E1 ∧ e ∈ E2 := by
  by_contra hn
  have hm : prodMode E1 E2 e = .none := by simp only [prodMode, hn, ↓reduceIte]
  rw [syncF_none hm] at h
  exact Finset.not_nonempty_empty h

/-- Runs of the product from a product of sets, for words over $E_1 \cap E_2$:
$$f_\times^*(S_1 \times S_2, s) = f_1^*(S_1, s) \times f_2^*(S_2, s).$$

**Proof:** induction on $s$ for every $S_1, S_2$; every event of $s$ is `both`
(`step_syncF_both`). -/
theorem run_prodF (S1 : Finset σ) (S2 : Finset τ) (s : List α)
    (hs : ∀ e ∈ s, e ∈ E1 ∧ e ∈ E2) :
    run (syncF (prodMode E1 E2) f1 f2) (S1 ×ˢ S2) s = run f1 S1 s ×ˢ run f2 S2 s := by
  induction s generalizing S1 S2 with
  | nil => rfl
  | cons e s ih =>
    have hm : prodMode E1 E2 e = .both := by
      simp only [prodMode, hs e List.mem_cons_self, and_self, ↓reduceIte]
    simp only [run_cons]
    rw [step_syncF_both hm]
    exact ih _ _ (fun a ha => hs a (List.mem_cons_of_mem e ha))

/-- **(L2), product, generated language.**
$$s \in L(G_1 \times G_2) \iff s \in L(G_1) \wedge s \in L(G_2).$$

**Proof:** a word that leads somewhere in the product is in $(E_1 \cap E_2)^*$
(`prodF_nonempty`); a word of $L(G_1) \cap L(G_2)$ is too ($L(G_i) \subseteq E_i^*$). For such
words, `run_prodF`, and a product is nonempty iff both factors are. -/
theorem mem_prod_L (G1 G2 : Automaton α) (s : List α) :
    s ∈ (prod G1 G2).L ↔ s ∈ G1.L ∧ s ∈ G2.L := by
  constructor
  · intro h
    have hs := mem_of_run_nonempty _ (G1.E ∩ G2.E)
      (fun _ _ hne => Finset.mem_inter.2 (prodF_nonempty hne)) _ s h
    change (run (syncF (prodMode G1.E G2.E) G1.f G2.f) (G1.X0 ×ˢ G2.X0) s).Nonempty at h
    rw [run_prodF _ _ s (fun e he => Finset.mem_inter.1 (hs e he)),
      Finset.nonempty_product] at h
    exact h
  · rintro ⟨h1, h2⟩
    change (run (syncF (prodMode G1.E G2.E) G1.f G2.f) (G1.X0 ×ˢ G2.X0) s).Nonempty
    rw [run_prodF _ _ s (fun e he => ⟨G1.mem_E_of_mem_L h1 e he, G2.mem_E_of_mem_L h2 e he⟩),
      Finset.nonempty_product]
    exact ⟨h1, h2⟩

/-- **(L2), product, marked language.**
$$s \in L_m(G_1 \times G_2) \iff s \in L_m(G_1) \wedge s \in L_m(G_2).$$

**Proof:** as for $L$; a pair is marked iff both components are, and
$L_m(G_i) \subseteq L(G_i) \subseteq E_i^*$. -/
theorem mem_prod_Lm (G1 G2 : Automaton α) (s : List α) :
    s ∈ (prod G1 G2).Lm ↔ s ∈ G1.Lm ∧ s ∈ G2.Lm := by
  have key : (∀ e ∈ s, e ∈ G1.E ∧ e ∈ G2.E) →
      (s ∈ (prod G1 G2).Lm ↔ s ∈ G1.Lm ∧ s ∈ G2.Lm) := by
    intro hs
    change (∃ y ∈ run (syncF (prodMode G1.E G2.E) G1.f G2.f) (G1.X0 ×ˢ G2.X0) s,
      (G1.marked y.1 && G2.marked y.2) = true) ↔ _
    rw [run_prodF _ _ s hs]
    simp only [Automaton.Lm, mem_mkd, Finset.mem_product, Bool.and_eq_true, Prod.exists]
    constructor
    · rintro ⟨y1, y2, ⟨hy1, hy2⟩, hm1, hm2⟩
      exact ⟨⟨y1, hy1, hm1⟩, ⟨y2, hy2, hm2⟩⟩
    · rintro ⟨⟨y1, hy1, hm1⟩, ⟨y2, hy2, hm2⟩⟩
      exact ⟨y1, y2, ⟨hy1, hy2⟩, hm1, hm2⟩
  constructor
  · intro h
    have hL : s ∈ (prod G1 G2).L := by
      obtain ⟨y, hy, -⟩ := mem_mkd.1 h
      exact ⟨y, hy⟩
    obtain ⟨h1, h2⟩ := (mem_prod_L G1 G2 s).1 hL
    exact (key (fun e he => ⟨G1.mem_E_of_mem_L h1 e he, G2.mem_E_of_mem_L h2 e he⟩)).1 h
  · rintro ⟨h1, h2⟩
    have hL1 : s ∈ G1.L := G1.Lm_le_L h1
    have hL2 : s ∈ G2.L := G2.Lm_le_L h2
    exact (key (fun e he => ⟨G1.mem_E_of_mem_L hL1 e he, G2.mem_E_of_mem_L hL2 e he⟩)).2 ⟨h1, h2⟩

/-- **(L2')** $G_1$, $G_2$ deterministic $\implies$ $G_1 \times G_2$ deterministic.

**Proof:** as `par_det`: $|X_{01} \times X_{02}| \le 1$; a `both` step has size
$|f_1(x_1, e)| \cdot |f_2(x_2, e)| \le 1$, a `none` step size 0. -/
theorem prod_det {G1 G2 : Automaton α} (h1 : G1.IsDeterministic) (h2 : G2.IsDeterministic) :
    (prod G1 G2).IsDeterministic := by
  constructor
  · change (G1.X0 ×ˢ G2.X0).card ≤ 1
    rw [Finset.card_product]
    simpa using Nat.mul_le_mul h1.1 h2.1
  · intro p e
    change (syncF (prodMode G1.E G2.E) G1.f G2.f p e).card ≤ 1
    by_cases h : e ∈ G1.E ∧ e ∈ G2.E
    · have hm : prodMode G1.E G2.E e = .both := by simp only [prodMode, h, and_self, ↓reduceIte]
      simp only [syncF, hm, Finset.card_product]
      simpa using Nat.mul_le_mul (h1.2 p.1 e) (h2.2 p.2 e)
    · have hm : prodMode G1.E G2.E e = .none := by simp only [prodMode, h, ↓reduceIte]
      rw [syncF_none hm]
      simp

end modes

/-! ## (L4) The Python output: `IsComposition`

`H` is the automaton the library returns (an `Automaton`: the validity pass gives W1–W3), with
labels `φ i = (p1[i], p2[i])`. `IsComposition` lists, as one structure, the facts the verified
checker establishes (spec §4; the hand check matches each field to a checker fact). From them:
the languages of `H` are those of the composition (`IsComposition.L`, `.Lm`), and so, for the
two mode tables, those of $G_1 \parallel G_2$ and $G_1 \times G_2$. -/

section composition

variable [DecidableEq α]

/-- **(L4)** $H$ is the composition of $G_1$ and $G_2$ with the mode table `mode`, with state
labels $\varphi : X_H \to X_1 \times X_2$:
- step, sound: $y \in f_H(i, e) \implies \varphi(y) \in f_{mode}(\varphi(i), e)$;
- step, complete: $q \in f_{mode}(\varphi(i), e) \implies \exists y \in f_H(i, e),\ \varphi(y) = q$;
- initial, sound: $i \in X_{0H} \implies \varphi(i) \in X_{01} \times X_{02}$;
- initial, complete: $(x_1, x_2) \in X_{01} \times X_{02} \implies$
  $\exists i \in X_{0H},\ \varphi(i) = (x_1, x_2)$;
- marked: $m_H(i) = m_1(\varphi(i)_1) \wedge m_2(\varphi(i)_2)$;
- events: $E_H = E_1 \cup E_2$, and the same for $E_{uc}$, $E_{uo}$.

Neither distinct labels nor reachability of every state is required (spec §4, questions 4, 6).

**Lean:** a structure of proofs (a `Prop`), as `IsDeletion`. -/
structure IsComposition (mode : α → Mode) (G1 G2 H : Automaton α)
    (φ : Fin H.n → Fin G1.n × Fin G2.n) : Prop where
  step_sound : ∀ i e y, y ∈ H.f i e → φ y ∈ syncF mode G1.f G2.f (φ i) e
  step_complete : ∀ i e q, q ∈ syncF mode G1.f G2.f (φ i) e → ∃ y ∈ H.f i e, φ y = q
  init_sound : ∀ i ∈ H.X0, (φ i).1 ∈ G1.X0 ∧ (φ i).2 ∈ G2.X0
  init_complete : ∀ x1 ∈ G1.X0, ∀ x2 ∈ G2.X0, ∃ i ∈ H.X0, φ i = (x1, x2)
  marked : ∀ i, H.marked i = (G1.marked (φ i).1 && G2.marked (φ i).2)
  E : H.E = G1.E ∪ G2.E
  Euc : H.Euc = G1.Euc ∪ G2.Euc
  Euo : H.Euo = G1.Euo ∪ G2.Euo

namespace IsComposition

variable {mode : α → Mode} {G1 G2 H : Automaton α} {φ : Fin H.n → Fin G1.n × Fin G2.n}

/-- *step* of (L3): $\varphi(f_H(i, e)) = f_{mode}(\varphi(i), e)$.

**Proof:** $\subseteq$ is `step_sound`, $\supseteq$ is `step_complete`. -/
theorem image_f (h : IsComposition mode G1 G2 H φ) (i : Fin H.n) (e : α) :
    (H.f i e).image φ = (comp mode G1 G2).f (φ i) e := by
  ext q
  rw [Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact h.step_sound i e y hy
  · intro hq
    exact h.step_complete i e q hq

/-- *start* of (L3): $\varphi(X_{0H}) = X_{01} \times X_{02}$.

**Proof:** $\subseteq$ is `init_sound`, $\supseteq$ is `init_complete`. -/
theorem image_X0 (h : IsComposition mode G1 G2 H φ) :
    H.X0.image φ = (comp mode G1 G2).X0 := by
  ext ⟨x1, x2⟩
  change _ ↔ (x1, x2) ∈ G1.X0 ×ˢ G2.X0
  rw [Finset.mem_image, Finset.mem_product]
  constructor
  · rintro ⟨i, hi, hφ⟩
    have h0 := h.init_sound i hi
    rw [hφ] at h0
    exact h0
  · rintro ⟨h1, h2⟩
    exact h.init_complete x1 h1 x2 h2

/-- $L(H) = L(\text{composition})$, by (L3) (`gen_eq_of_labels`). -/
theorem L (h : IsComposition mode G1 G2 H φ) : H.L = (comp mode G1 G2).L :=
  gen_eq_of_labels φ h.image_X0 h.image_f

/-- $L_m(H) = L_m(\text{composition})$, by (L3) (`mkd_eq_of_labels`). -/
theorem Lm (h : IsComposition mode G1 G2 H φ) : H.Lm = (comp mode G1 G2).Lm :=
  mkd_eq_of_labels φ h.image_X0 h.image_f h.marked

/-- **(L5)** Distinct labels and a deterministic composition give a deterministic $H$
(`det_of_labels`). Not used by the library for now (spec question 4, option (b)). -/
theorem det (h : IsComposition mode G1 G2 H φ) (hφ : Function.Injective φ)
    (hT : (comp mode G1 G2).IsDeterministic) : H.IsDeterministic :=
  det_of_labels φ hφ h.image_X0 h.image_f hT

/-- **Result, parallel composition.** If the checker accepts the output $H$ for the parallel
modes:
$$s \in L(H) \iff s \in (E_1 \cup E_2)^* \wedge P_1(s) \in L(G_1) \wedge P_2(s) \in L(G_2),$$
and the same for $L_m$ (`par_Lm`). -/
theorem par_L (h : IsComposition (parMode G1.E G2.E) G1 G2 H φ) (s : List α) :
    s ∈ H.L ↔ (∀ e ∈ s, e ∈ G1.E ∪ G2.E) ∧ proj G1.E s ∈ G1.L ∧ proj G2.E s ∈ G2.L := by
  rw [h.L, ← par_eq_comp, mem_par_L]

theorem par_Lm (h : IsComposition (parMode G1.E G2.E) G1 G2 H φ) (s : List α) :
    s ∈ H.Lm ↔ (∀ e ∈ s, e ∈ G1.E ∪ G2.E) ∧ proj G1.E s ∈ G1.Lm ∧ proj G2.E s ∈ G2.Lm := by
  rw [h.Lm, ← par_eq_comp, mem_par_Lm]

/-- **Result, product.** If the checker accepts the output $H$ for the product modes:
$L(H) = L(G_1) \cap L(G_2)$ and $L_m(H) = L_m(G_1) \cap L_m(G_2)$. -/
theorem prod_L (h : IsComposition (prodMode G1.E G2.E) G1 G2 H φ) (s : List α) :
    s ∈ H.L ↔ s ∈ G1.L ∧ s ∈ G2.L := by
  rw [h.L]
  exact mem_prod_L G1 G2 s

theorem prod_Lm (h : IsComposition (prodMode G1.E G2.E) G1 G2 H φ) (s : List α) :
    s ∈ H.Lm ↔ s ∈ G1.Lm ∧ s ∈ G2.Lm := by
  rw [h.Lm]
  exact mem_prod_Lm G1 G2 s

/-- DFA in ⇒ DFA out, parallel, given distinct labels (deferred, spec question 4 (a)). -/
theorem par_det (h : IsComposition (parMode G1.E G2.E) G1 G2 H φ) (hφ : Function.Injective φ)
    (h1 : G1.IsDeterministic) (h2 : G2.IsDeterministic) : H.IsDeterministic :=
  h.det hφ (par_eq_comp G1 G2 ▸ DESopsProof.par_det h1 h2)

/-- DFA in ⇒ DFA out, product, given distinct labels (deferred, spec question 4 (a)). -/
theorem prod_det (h : IsComposition (prodMode G1.E G2.E) G1 G2 H φ) (hφ : Function.Injective φ)
    (h1 : G1.IsDeterministic) (h2 : G2.IsDeterministic) : H.IsDeterministic :=
  h.det hφ (DESopsProof.prod_det h1 h2)

end IsComposition

end composition

end DESopsProof
