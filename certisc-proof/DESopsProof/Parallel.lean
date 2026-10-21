import DESopsProof.Automaton
import Mathlib.Data.Finset.Prod

/-!
# Parallel composition

The definitions and theorems of `spec/parallel.md`, §3 and §4.

- §3 (L1, L2, L2'): the product `G1 ‖ G2` over pairs of states, its languages, determinism.
- §4 (L3, L4, L5): the bridge from the local facts that Nagini proves about the Python output `H`
  to the languages and the determinism of `H`.

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

/-! ## §4 (L4) and the result for the Python output

`H` has `k` states, transitions `fH`, initial states `X0H`, marking `mH`, and labels
`φ i = (p1[i], p2[i])`. The hypotheses are what Nagini proves (spec §5, §6):

| hypothesis | Nagini |
|---|---|
| `h0 : X0H.image φ = (par G1 G2).X0` | N3 |
| `hstep : ∀ i e, (fH i e).image φ = (par G1 G2).f (φ i) e` | N2a, N2b |
| `hm : ∀ i, mH i = (par G1 G2).marked (φ i)` | N4 |
| `hφ : Function.Injective φ` | N5 |
-/

section output

variable [DecidableEq α] (G1 G2 : Automaton α) {k : ℕ}
  (φ : Fin k → Fin G1.n × Fin G2.n) {fH : Fin k → α → Finset (Fin k)} {X0H : Finset (Fin k)}

/-- **(L4)** The output is a well-formed automaton with alphabet $E_1 \cup E_2$ and
$E_{uc} = E_{uc,1} \cup E_{uc,2}$, $E_{uo} = E_{uo,1} \cup E_{uo,2}$.

**Proof:** W1: $f_H(i, e) \neq \emptyset$ gives $f_\parallel(\varphi(i), e) \neq \emptyset$ (by
*step*), so $e \in E_1 \cup E_2$. W2: unions of subsets. W3: an initial state is a state; and if
$k > 0$, the pair $\varphi(0)$ shows $n_1, n_2 > 0$, so $X_{01}, X_{02} \neq \emptyset$ (W3 of the
inputs), so $X_{01} \times X_{02} = \varphi(X_{0H}) \neq \emptyset$, so $X_{0H} \neq \emptyset$. -/
def output (h0 : X0H.image φ = (par G1 G2).X0)
    (hstep : ∀ i e, (fH i e).image φ = (par G1 G2).f (φ i) e) (mH : Fin k → Bool) :
    Automaton α where
  n := k
  E := G1.E ∪ G2.E
  Euc := G1.Euc ∪ G2.Euc
  Euo := G1.Euo ∪ G2.Euo
  f := fH
  X0 := X0H
  marked := mH
  wf_E := by
    intro i e h
    have h' : ((par G1 G2).f (φ i) e).Nonempty := by
      rw [← hstep]; exact h.image φ
    exact parF_nonempty h'
  wf_Euc := Finset.union_subset_union G1.wf_Euc G2.wf_Euc
  wf_Euo := Finset.union_subset_union G1.wf_Euo G2.wf_Euo
  wf_X0 := by
    constructor
    · rintro ⟨i, -⟩
      exact Nat.pos_of_ne_zero (fun hk => by subst hk; exact i.elim0)
    · intro hk
      have p := φ ⟨0, hk⟩
      have hn1 : 0 < G1.n := Nat.pos_of_ne_zero (fun h => by
        have := p.1.isLt; omega)
      have hn2 : 0 < G2.n := Nat.pos_of_ne_zero (fun h => by
        have := p.2.isLt; omega)
      have hX0 : (X0H.image φ).Nonempty := by
        rw [h0]
        exact Finset.Nonempty.product (G1.wf_X0.2 hn1) (G2.wf_X0.2 hn2)
      exact Finset.image_nonempty.1 hX0

/-- **Result for the Python output.** Under the hypotheses that Nagini proves, the output
automaton has the languages of $G_1 \parallel G_2$:
$$s \in L(H) \iff s \in (E_1 \cup E_2)^* \wedge P_1(s) \in L(G_1) \wedge P_2(s) \in L(G_2),$$
and the same for $L_m$. -/
theorem output_L (h0 : X0H.image φ = (par G1 G2).X0)
    (hstep : ∀ i e, (fH i e).image φ = (par G1 G2).f (φ i) e) (mH : Fin k → Bool)
    (s : List α) :
    s ∈ (output G1 G2 φ h0 hstep mH).L ↔
      (∀ e ∈ s, e ∈ G1.E ∪ G2.E) ∧ proj G1.E s ∈ G1.L ∧ proj G2.E s ∈ G2.L := by
  have : (output G1 G2 φ h0 hstep mH).L = (par G1 G2).L := gen_eq_of_labels φ h0 hstep
  rw [this, mem_par_L]

theorem output_Lm (h0 : X0H.image φ = (par G1 G2).X0)
    (hstep : ∀ i e, (fH i e).image φ = (par G1 G2).f (φ i) e) (mH : Fin k → Bool)
    (hm : ∀ i, mH i = (par G1 G2).marked (φ i)) (s : List α) :
    s ∈ (output G1 G2 φ h0 hstep mH).Lm ↔
      (∀ e ∈ s, e ∈ G1.E ∪ G2.E) ∧ proj G1.E s ∈ G1.Lm ∧ proj G2.E s ∈ G2.Lm := by
  have : (output G1 G2 φ h0 hstep mH).Lm = (par G1 G2).Lm := mkd_eq_of_labels φ h0 hstep hm
  rw [this, mem_par_Lm]

/-- **DFA in ⇒ DFA out.** If $G_1$, $G_2$ are deterministic and the labels are distinct (N5),
the output is deterministic. **Proof:** (L2') and (L5). -/
theorem output_det (h0 : X0H.image φ = (par G1 G2).X0)
    (hstep : ∀ i e, (fH i e).image φ = (par G1 G2).f (φ i) e) (mH : Fin k → Bool)
    (hφ : Function.Injective φ) (h1 : G1.IsDeterministic) (h2 : G2.IsDeterministic) :
    (output G1 G2 φ h0 hstep mH).IsDeterministic :=
  det_of_labels φ hφ h0 hstep (par_det h1 h2)

end output

end DESopsProof
