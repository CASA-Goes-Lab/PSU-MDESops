import DESopsProof.Automaton
import DESopsProof.Parallel

/-!
# Supervisory control, part 1: prefix-closed (spec/supervisor.md)

Languages first (§1 of the spec): prefix closure, controllability, and the supremal controllable
sublanguage $K^{\uparrow C}$. Then the state-level algorithm (§2) on a deterministic transition
structure $P$ in which the specification is a set of states $I$ ("inside"):
$$Bad = CoAc_{E_{uc}}(X \setminus I), \qquad S = P \text{ restricted to } X \setminus Bad,$$
and the main theorem `supcon_strict_sub`: $L(S) = K^{\uparrow C}$ with $K = L(P|_I)$.
Last, `supervisor_L` states it for the automata that the library builds (two deletions,
`IsDeletion`).

## Notation: math ↔ Lean (in addition to `Automaton.lean`)

| Math | Lean |
|---|---|
| $K$ prefix-closed | `PrefixClosed K` |
| $K$ controllable w.r.t. $L$, $E_{uc}$ | `Controllable K L Euc` |
| $K^{\uparrow C}$ | `supC K L Euc` |
| $f$ restricted to the states $g$: $f\vert_g(x, e) = f(x, e) \cap g$ | `restrict f g` |
| $f$ on uncontrollable events only | `ucOnly f Euc` |
| $L(P\vert_g)$: the words whose run stays in $g$ | `gen (restrict f g) (X0.filter g)` |
-/

namespace DESopsProof

variable {α : Type} {σ : Type} [DecidableEq σ]

/-! ## Languages -/

/-- $K$ is prefix-closed: $s \cdot t \in K \implies s \in K$. -/
def PrefixClosed (K : Language α) : Prop := ∀ s t, s ++ t ∈ K → s ∈ K

/-- $K$ is controllable with respect to $L$ and $E_{uc}$ (for prefix-closed $K$):
$$K \cdot E_{uc} \cap L \subseteq K,$$
i.e. $\forall s \in K,\ \forall e \in E_{uc}:\ s e \in L \implies s e \in K$. -/
def Controllable (K L : Language α) (Euc : Set α) : Prop :=
  ∀ s ∈ K, ∀ e ∈ Euc, s ++ [e] ∈ L → s ++ [e] ∈ K

/-- The supremal (prefix-closed) controllable sublanguage of $K$:
$$K^{\uparrow C} = \bigcup \{\, M \subseteq K \mid M \text{ prefix-closed and controllable} \,\}.$$

**Lean:** `supC K L Euc`, the words that belong to some such $M$. -/
def supC (K L : Language α) (Euc : Set α) : Language α :=
  {s | ∃ M : Language α, M ≤ K ∧ PrefixClosed M ∧ Controllable M L Euc ∧ s ∈ M}

section supC

variable {K L M : Language α} {Euc : Set α}

/-- $K^{\uparrow C} \subseteq K$. -/
theorem supC_le : supC K L Euc ≤ K := by
  rintro s ⟨M, hMK, -, -, hs⟩
  exact hMK hs

/-- Every prefix-closed controllable $M \subseteq K$ is inside $K^{\uparrow C}$ (it is the
largest). -/
theorem le_supC (hMK : M ≤ K) (hM : PrefixClosed M) (hc : Controllable M L Euc) :
    M ≤ supC K L Euc :=
  fun _ hs => ⟨M, hMK, hM, hc, hs⟩

/-- $K^{\uparrow C}$ is prefix-closed: a prefix of a word of some $M$ is in that $M$. -/
theorem supC_prefixClosed : PrefixClosed (supC K L Euc) := by
  rintro s t ⟨M, hMK, hM, hc, hs⟩
  exact ⟨M, hMK, hM, hc, hM s t hs⟩

/-- $K^{\uparrow C}$ is controllable: an uncontrollable continuation of a word of $M$ stays in
$M$. -/
theorem supC_controllable : Controllable (supC K L Euc) L Euc := by
  rintro s ⟨M, hMK, hM, hc, hs⟩ e he hL
  exact ⟨M, hMK, hM, hc, hc s hs e he hL⟩

/-- Iterated controllability: if $t \in M$, $u \in E_{uc}^*$ and $t u \in L$ (with $L$
prefix-closed), then $t u \in M$.

**Proof:** induction on $u$ for every $t$. For $u = e \cdot u'$: $t e \in L$ (a prefix of
$t e u'$), so $t e \in M$ by controllability; then the induction hypothesis from $t e$. -/
theorem controllable_iter (hc : Controllable M L Euc) (hL : PrefixClosed L) :
    ∀ (u t : List α), t ∈ M → (∀ e ∈ u, e ∈ Euc) → t ++ u ∈ L → t ++ u ∈ M := by
  intro u
  induction u with
  | nil => intro t ht _ _; simpa using ht
  | cons e u ih =>
    intro t ht hu htu
    have h1 : t ++ [e] ∈ L := hL _ u (by simpa [List.append_assoc] using htu)
    have h2 : t ++ [e] ∈ M := hc t ht e (hu e List.mem_cons_self) h1
    have h3 := ih (t ++ [e]) h2 (fun e' he' => hu e' (List.mem_cons_of_mem _ he'))
      (by simpa [List.append_assoc] using htu)
    simpa [List.append_assoc] using h3

end supC

/-- A generated language is prefix-closed (Lemma 1 of `Automaton.lean`, for any $f$). -/
theorem gen_prefixClosed (f : σ → α → Finset σ) (X0 : Finset σ) : PrefixClosed (gen f X0) :=
  fun _ _ h => run_nonempty_of_append f h

/-! ## Restricting a transition function -/

/-- $f|_g(x, e) = \{\, y \in f(x, e) \mid g(y) \,\}$: only moves into states satisfying $g$. -/
def restrict (f : σ → α → Finset σ) (g : σ → Prop) [DecidablePred g] : σ → α → Finset σ :=
  fun x e => (f x e).filter g

/-- $f$ on the uncontrollable events only: $f_{uc}(x, e) = f(x, e)$ if $e \in E_{uc}$, else
$\emptyset$. -/
def ucOnly [DecidableEq α] (f : σ → α → Finset σ) (Euc : Finset α) : σ → α → Finset σ :=
  fun x e => if e ∈ Euc then f x e else ∅

/-- Runs grow with the transition function and the start set: if $f(x, e) \subseteq f'(x, e)$
for all $x, e$ and $S \subseteq S'$, then $f^*(S, s) \subseteq f'^*(S', s)$.

**Proof:** induction on $s$ for every $S, S'$; one step maps $\delta_f(S, e)$ into
$\delta_{f'}(S', e)$. -/
theorem run_mono_f {f f' : σ → α → Finset σ} (hf : ∀ x e, f x e ⊆ f' x e) :
    ∀ (s : List α) {S S' : Finset σ}, S ⊆ S' → run f S s ⊆ run f' S' s := by
  intro s
  induction s with
  | nil => intro S S' h; exact h
  | cons e s ih =>
    intro S S' h
    apply ih
    intro y hy
    obtain ⟨x, hx, hyx⟩ := (mem_step f).1 hy
    exact (mem_step f').2 ⟨x, h hx, hf x e hyx⟩

section restrict

variable (f : σ → α → Finset σ) (g : σ → Prop) [DecidablePred g]

/-- $f|_g^*(S, s) \subseteq f^*(S, s)$: the restriction only removes moves. -/
theorem run_restrict_sub (s : List α) (S : Finset σ) : run (restrict f g) S s ⊆ run f S s :=
  run_mono_f (fun _ _ => Finset.filter_subset _ _) s (subset_refl S)

/-- A run of $f|_g$ from states satisfying $g$ only visits states satisfying $g$.

**Proof:** induction on $s$; every target of $f|_g$ satisfies $g$ (`Finset.mem_filter`). -/
theorem run_restrict_good :
    ∀ (s : List α) (S : Finset σ), (∀ x ∈ S, g x) → ∀ y ∈ run (restrict f g) S s, g y := by
  intro s
  induction s with
  | nil => intro S hS y hy; exact hS y hy
  | cons e s ih =>
    intro S _ y hy
    refine ih _ ?_ y hy
    intro z hz
    obtain ⟨x, -, hzx⟩ := (mem_step _).1 hz
    exact (Finset.mem_filter.1 hzx).2

/-- If $g \Rightarrow g'$, then $L(P|_g) \subseteq L(P|_{g'})$. -/
theorem gen_restrict_mono (g' : σ → Prop) [DecidablePred g'] (h : ∀ x, g x → g' x)
    (X0 : Finset σ) : gen (restrict f g) (X0.filter g) ≤ gen (restrict f g') (X0.filter g') := by
  have hf : ∀ x e, restrict f g x e ⊆ restrict f g' x e := by
    intro x e y hy
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hy
    exact Finset.mem_filter.2 ⟨h1, h y h2⟩
  have hS : X0.filter g ⊆ X0.filter g' := by
    intro y hy
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hy
    exact Finset.mem_filter.2 ⟨h1, h y h2⟩
  intro s ⟨y, hy⟩
  exact ⟨y, run_mono_f hf s hS hy⟩

/-- Deterministic case: if $s \in L(P|_g)$, the state that $s$ reaches in $P$ satisfies $g$.

**Proof:** $f|_g^*(X_0 \cap g, s)$ has some state $x$, also in $f^*(X_0, s)$, and $x$ satisfies
$g$ (`run_restrict_good`). $f^*(X_0, s)$ has at most one state, so $y = x$. -/
theorem good_of_mem_gen_restrict {X0 : Finset σ} (hdet : ∀ s, (run f X0 s).card ≤ 1)
    {s : List α} (hs : s ∈ gen (restrict f g) (X0.filter g)) {y : σ} (hy : y ∈ run f X0 s) :
    g y := by
  obtain ⟨x, hx⟩ := hs
  have hx' : x ∈ run f X0 s :=
    run_mono_f (fun _ _ => Finset.filter_subset _ _) s (Finset.filter_subset _ _) hx
  have hgx : g x := run_restrict_good f g s _ (fun z hz => (Finset.mem_filter.1 hz).2) x hx
  rwa [Finset.card_le_one.1 (hdet s) y hy x hx']

end restrict

/-- A run of $f_{uc}$ that reaches a state uses only uncontrollable events, and is a run of $f$:
$z \in f_{uc}^*(S, u) \implies u \in E_{uc}^* \wedge z \in f^*(S, u)$.

**Proof:** induction on $u$. A step on $e \notin E_{uc}$ is empty, and so is every run after it. -/
theorem ucOnly_run [DecidableEq α] (f : σ → α → Finset σ) (Euc : Finset α) :
    ∀ (u : List α) (S : Finset σ) (z : σ), z ∈ run (ucOnly f Euc) S u →
      (∀ e ∈ u, e ∈ Euc) ∧ z ∈ run f S u := by
  have hsub : ∀ x e, ucOnly f Euc x e ⊆ f x e := by
    intro x e
    unfold ucOnly
    split_ifs
    · exact subset_refl _
    · exact Finset.empty_subset _
  intro u
  induction u with
  | nil => intro S z hz; exact ⟨by simp, hz⟩
  | cons e u ih =>
    intro S z hz
    refine ⟨?_, run_mono_f hsub _ (subset_refl S) hz⟩
    have he : e ∈ Euc := by
      by_contra he
      have h0 : step (ucOnly f Euc) S e = ∅ := by
        ext y
        simp [step, ucOnly, he]
      rw [run_cons, h0, run_empty] at hz
      exact Finset.notMem_empty z hz
    rw [run_cons] at hz
    have hu := (ih _ z hz).1
    intro e' he'
    rcases List.mem_cons.1 he' with rfl | he'
    · exact he
    · exact hu e' he'

/-! ## The main theorem -/

section main

variable [Fintype σ] [DecidableEq α] (f : σ → α → Finset σ) (X0 : Finset σ)
  (I : σ → Prop) [DecidablePred I] (Euc : Finset α)

/-- The bad states: those from which an uncontrollable word leads out of $I$,
$$Bad = CoAc_{E_{uc}}(X \setminus I) = \{\, x \mid \exists u \in E_{uc}^*,\ f^*(\{x\}, u)
  \not\subseteq I \,\}.$$
This is what the library computes: `coreachable` over the uncontrollable transitions, from the
states outside $I$ (spec §2). -/
def bad : Set σ := coreach (ucOnly f Euc) (Finset.univ.filter (fun x => ¬ I x))

/-- **Main theorem (prefix-closed supervisory control on a strict subautomaton).**

Let $P = (f, X_0)$ be deterministic, $I$ a set of states, $K = L(P|_I)$ (the words whose run
stays in $I$), and $G$ any decidable predicate with $G(x) \iff x \notin Bad$. Then
$$L(P|_G) = K^{\uparrow C} \quad (\text{w.r.t. } L(P),\ E_{uc}).$$

**Proof.** Write $K_G = L(P|_G)$. Every good state is in $I$ (a state outside $I$ is bad by the
empty word), so $K_G \subseteq K$; it is prefix-closed (a generated language).
- *Controllable:* let $s \in K_G$ reach $x$ (good), $e \in E_{uc}$, $s e \in L(P)$ reach $y$,
  so $y \in f(x, e)$ by determinism. If $y$ were bad, $x$ would be bad too (one uncontrollable
  step back, `mem_coreach_of_step`). So $y$ is good and $s e \in K_G$.
- *Largest:* let $M \subseteq K$ be prefix-closed and controllable. A state $y$ reached by a word
  $t \in M$ is not bad: else an uncontrollable $u$ leads from $y$ to some $z \notin I$; by
  iterated controllability $t u \in M \subseteq K$, so its state $z$ is in $I$, a contradiction.
  Then $M \subseteq K_G$ by induction on the word (from the right): each next state is in $I$
  (as $M \subseteq K$) and not bad (as just shown), so the run of $P|_G$ continues. -/
theorem supcon_strict_sub (hX0 : X0.card ≤ 1) (hf : ∀ x e, (f x e).card ≤ 1)
    (G : σ → Prop) [DecidablePred G] (hG : ∀ x, G x ↔ x ∉ bad f I Euc) :
    gen (restrict f G) (X0.filter G) =
      supC (gen (restrict f I) (X0.filter I)) (gen f X0) (Euc : Set α) := by
  -- Determinism: one state per word.
  have hdet : ∀ s, (run f X0 s).card ≤ 1 := fun s =>
    Automaton.card_run_le_one f hf X0 s hX0
  have heq : ∀ s, ∀ x ∈ run f X0 s, ∀ x' ∈ run f X0 s, x = x' := fun s x hx x' hx' =>
    Finset.card_le_one.1 (hdet s) x hx x' hx'
  -- Outside I is bad (empty word), so good states are in I.
  have hout : ∀ x, ¬ I x → x ∈ bad f I Euc := fun x hx =>
    mem_coreach_of_mem (Finset.mem_filter.2 ⟨Finset.mem_univ x, hx⟩)
  have hGI : ∀ x, G x → I x := fun x hx => by
    by_contra h
    exact (hG x).1 hx (hout x h)
  -- The run of P|_G is the run of P (one state x, which is good).
  have hrunG : ∀ s, ∀ x ∈ run (restrict f G) (X0.filter G) s, x ∈ run f X0 s ∧ G x :=
    fun s x hx =>
      ⟨run_mono_f (fun _ _ => Finset.filter_subset _ _) s (Finset.filter_subset _ _) hx,
        run_restrict_good f G s _ (fun z hz => (Finset.mem_filter.1 hz).2) x hx⟩
  -- The next state: y reached by s e in P is in f(x, e) for the state x of s.
  have hnext : ∀ s e y x, y ∈ run f X0 (s ++ [e]) → x ∈ run f X0 s → y ∈ f x e := by
    intro s e y x hy hx
    rw [run_append, run_cons, run_nil] at hy
    obtain ⟨x', hx', hyx⟩ := (mem_step f).1 hy
    rwa [heq s x hx x' hx']
  -- Extending a run of P|_G by a move into a good state.
  have hextend : ∀ s e x y, x ∈ run (restrict f G) (X0.filter G) s → y ∈ f x e → G y →
      s ++ [e] ∈ gen (restrict f G) (X0.filter G) := by
    intro s e x y hx hy hGy
    refine ⟨y, ?_⟩
    rw [run_append, run_cons, run_nil]
    exact (mem_step _).2 ⟨x, hx, Finset.mem_filter.2 ⟨hy, hGy⟩⟩
  apply le_antisymm
  · -- K_G is prefix-closed, inside K, and controllable.
    apply le_supC (gen_restrict_mono f G I hGI X0) (gen_prefixClosed _ _)
    rintro s ⟨x, hx⟩ e he ⟨y, hy⟩
    obtain ⟨hxP, hGx⟩ := hrunG s x hx
    have hyx := hnext s e y x hy hxP
    refine hextend s e x y hx hyx ((hG y).2 ?_)
    intro hyb
    apply (hG x).1 hGx
    refine mem_coreach_of_step (e := e) hyb ?_
    have he' : e ∈ Euc := Finset.mem_coe.1 he
    simpa [ucOnly, he'] using hyx
  · rintro s ⟨M, hMK, hM, hc, hs⟩
    -- States reached by words of M are not bad.
    have hnobad : ∀ t ∈ M, ∀ y ∈ run f X0 t, y ∉ bad f I Euc := by
      intro t ht y hy hyb
      obtain ⟨u, z, hz, hzO⟩ := hyb
      obtain ⟨hu, hz'⟩ := ucOnly_run f Euc u {y} z hz
      have hzt : z ∈ run f X0 (t ++ u) := by
        rw [run_append]
        exact run_mono_f (fun _ _ => subset_refl _) u (Finset.singleton_subset_iff.2 hy) hz'
      have htu : t ++ u ∈ M :=
        controllable_iter hc (gen_prefixClosed f X0) u t ht
          (fun e he => Finset.mem_coe.2 (hu e he)) ⟨z, hzt⟩
      exact (Finset.mem_filter.1 hzO).2 (good_of_mem_gen_restrict f I hdet (hMK htu) hzt)
    -- Induction on s from the right: the run of P|_G goes on.
    induction s using List.reverseRecOn with
    | nil =>
      obtain ⟨x, hx⟩ := hMK hs
      have hx0 : x ∈ X0 := (Finset.mem_filter.1 hx).1
      exact ⟨x, Finset.mem_filter.2 ⟨hx0, (hG x).2 (hnobad [] hs x hx0)⟩⟩
    | append_singleton s e ih =>
      obtain ⟨x, hx⟩ := ih (hM s [e] hs)
      obtain ⟨w, hw⟩ := hMK hs
      have hwP : w ∈ run f X0 (s ++ [e]) :=
        run_mono_f (fun _ _ => Finset.filter_subset _ _) _ (Finset.filter_subset _ _) hw
      have hwx := hnext s e w x hwP (hrunG s x hx).1
      exact hextend s e x w hx hwx ((hG w).2 (hnobad _ hs w hwP))

/-- The empty case: if every initial state is bad, $K^{\uparrow C} = \emptyset$ (the library
then returns the empty automaton).

**Proof:** `supcon_strict_sub` with $G = (\cdot \notin Bad)$; no initial state passes the filter,
so every run of $P|_G$ is empty. -/
theorem supC_empty (hX0 : X0.card ≤ 1) (hf : ∀ x e, (f x e).card ≤ 1)
    (h0 : ∀ x ∈ X0, x ∈ bad f I Euc) (s : List α) :
    s ∉ supC (gen (restrict f I) (X0.filter I)) (gen f X0) (Euc : Set α) := by
  classical
  rw [← supcon_strict_sub f X0 I Euc hX0 hf (fun x => x ∉ bad f I Euc) (fun _ => Iff.rfl)]
  rintro ⟨y, hy⟩
  have hempty : X0.filter (fun x => x ∉ bad f I Euc) = ∅ :=
    Finset.filter_eq_empty_iff.2 (fun x hx => not_not.2 (h0 x hx))
  rw [hempty, run_empty] at hy
  exact Finset.notMem_empty y hy

end main

/-! ## The escape form (what the library runs)

The library does not complete $H$. It works on $P_0 = G \parallel H$ (with $E_H \subseteq E_G$),
whose language is $K$ itself, and detects where the plant could leave $K$: at a state $x$ of
$P_0$, an event $e$ *escapes* if the plant can do it ($en(x, e)$: $e$ is enabled in $G$ at the
plant state of $x$) but $P_0$ cannot ($f(x, e) = \emptyset$). The bad states are those from which
an uncontrollable word leads to an uncontrollable escape:
$$Bad_0 = \{\, x \mid \exists e \in E_{uc},\ en(x, e) \wedge f(x, e) = \emptyset \,\}, \qquad
  Bad = CoAc_{E_{uc}}(Bad_0).$$
The plant language $L_p$ enters only through `hen`: after a word $s$ of $K$ that reaches $x$,
$s e \in L_p \iff en(x, e)$. -/

section escape

variable [Fintype σ] [DecidableEq α] (f : σ → α → Finset σ) (X0 : Finset σ) (Euc : Finset α)
  (en : σ → α → Prop)

open Classical in
/-- $Bad_0$: the states with an uncontrollable escape. -/
noncomputable def bad0 : Finset σ :=
  Finset.univ.filter (fun x => ∃ e ∈ Euc, en x e ∧ f x e = ∅)

omit [DecidableEq α] in
/-- $x \in Bad_0 \iff \exists e \in E_{uc},\ en(x, e) \wedge f(x, e) = \emptyset$. -/
theorem mem_bad0 {x : σ} : x ∈ bad0 f Euc en ↔ ∃ e ∈ Euc, en x e ∧ f x e = ∅ := by
  classical
  simp [bad0]

/-- $Bad = CoAc_{E_{uc}}(Bad_0)$: what the library computes (`coreachable` over the
uncontrollable transitions of $P_0$, from $Bad_0$). -/
def badE : Set σ := coreach (ucOnly f Euc) (bad0 f Euc en)

/-- **Main theorem, escape form.** Let $P_0 = (f, X_0)$ be deterministic with $K = L(P_0)$, and
$L_p$ a prefix-closed language with $K \subseteq L_p$ such that after any $s \in K$ reaching $x$,
$s e \in L_p \iff en(x, e)$. If $G(x) \iff x \notin Bad$, then
$$L(P_0|_G) = K^{\uparrow C} \quad (\text{w.r.t. } L_p,\ E_{uc}).$$

**Proof.** As `supcon_strict_sub`, with escapes in place of the states outside $I$.
- *Controllable:* $s \in L(P_0|_G)$ reaches a good $x$; for $e \in E_{uc}$ with $s e \in L_p$,
  $en(x, e)$ holds, so $f(x, e) \neq \emptyset$ (else $x \in Bad_0$), and its state $y$ is good
  (else $x$ is bad, one uncontrollable step back).
- *Largest:* for $M \subseteq K$ prefix-closed and controllable, a state $y$ reached by $t \in M$
  is not bad: else an uncontrollable $u$ leads to $z \in Bad_0$ with an escape $e$; then
  $t u \in M$ (iterated controllability) and $t u e \in L_p$, so $t u e \in M \subseteq K$, but
  $f(z, e) = \emptyset$. Then the induction on the word, as before. -/
theorem supcon_escape (hX0 : X0.card ≤ 1) (hf : ∀ x e, (f x e).card ≤ 1)
    (Lp : Language α) (hLp : PrefixClosed Lp) (hK : gen f X0 ≤ Lp)
    (hen : ∀ s x e, x ∈ run f X0 s → (s ++ [e] ∈ Lp ↔ en x e))
    (G : σ → Prop) [DecidablePred G] (hG : ∀ x, G x ↔ x ∉ badE f Euc en) :
    gen (restrict f G) (X0.filter G) = supC (gen f X0) Lp (Euc : Set α) := by
  have hdet : ∀ s, (run f X0 s).card ≤ 1 := fun s =>
    Automaton.card_run_le_one f hf X0 s hX0
  have heq : ∀ s, ∀ x ∈ run f X0 s, ∀ x' ∈ run f X0 s, x = x' := fun s x hx x' hx' =>
    Finset.card_le_one.1 (hdet s) x hx x' hx'
  have hrunG : ∀ s, ∀ x ∈ run (restrict f G) (X0.filter G) s, x ∈ run f X0 s ∧ G x :=
    fun s x hx =>
      ⟨run_mono_f (fun _ _ => Finset.filter_subset _ _) s (Finset.filter_subset _ _) hx,
        run_restrict_good f G s _ (fun z hz => (Finset.mem_filter.1 hz).2) x hx⟩
  have hnext : ∀ s e y x, y ∈ run f X0 (s ++ [e]) → x ∈ run f X0 s → y ∈ f x e := by
    intro s e y x hy hx
    rw [run_append, run_cons, run_nil] at hy
    obtain ⟨x', hx', hyx⟩ := (mem_step f).1 hy
    rwa [heq s x hx x' hx']
  have hextend : ∀ s e x y, x ∈ run (restrict f G) (X0.filter G) s → y ∈ f x e → G y →
      s ++ [e] ∈ gen (restrict f G) (X0.filter G) := by
    intro s e x y hx hy hGy
    refine ⟨y, ?_⟩
    rw [run_append, run_cons, run_nil]
    exact (mem_step _).2 ⟨x, hx, Finset.mem_filter.2 ⟨hy, hGy⟩⟩
  apply le_antisymm
  · have hsub : gen (restrict f G) (X0.filter G) ≤ gen f X0 := by
      rintro s ⟨y, hy⟩
      exact ⟨y, run_mono_f (fun _ _ => Finset.filter_subset _ _) s
        (Finset.filter_subset _ _) hy⟩
    apply le_supC hsub (gen_prefixClosed _ _)
    rintro s ⟨x, hx⟩ e he hL
    obtain ⟨hxP, hGx⟩ := hrunG s x hx
    have he' : e ∈ Euc := Finset.mem_coe.1 he
    have hen' : en x e := (hen s x e hxP).1 hL
    have hne : (f x e).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h0
      exact (hG x).1 hGx (mem_coreach_of_mem ((mem_bad0 f Euc en).2 ⟨e, he', hen', h0⟩))
    obtain ⟨y, hyx⟩ := hne
    refine hextend s e x y hx hyx ((hG y).2 ?_)
    intro hyb
    apply (hG x).1 hGx
    refine mem_coreach_of_step (e := e) hyb ?_
    simpa [ucOnly, he'] using hyx
  · rintro s ⟨M, hMK, hM, hc, hs⟩
    have hnobad : ∀ t ∈ M, ∀ y ∈ run f X0 t, y ∉ badE f Euc en := by
      intro t ht y hy hyb
      obtain ⟨u, z, hz, hz0⟩ := hyb
      obtain ⟨hu, hz'⟩ := ucOnly_run f Euc u {y} z hz
      have hzt : z ∈ run f X0 (t ++ u) := by
        rw [run_append]
        exact run_mono_f (fun _ _ => subset_refl _) u (Finset.singleton_subset_iff.2 hy) hz'
      have htu : t ++ u ∈ M :=
        controllable_iter hc hLp u t ht (fun e he => Finset.mem_coe.2 (hu e he))
          (hK ⟨z, hzt⟩)
      obtain ⟨e, heE, hen', hfe⟩ := (mem_bad0 f Euc en).1 hz0
      have hLe : t ++ u ++ [e] ∈ Lp := (hen (t ++ u) z e hzt).2 hen'
      have hMe : t ++ u ++ [e] ∈ M := hc _ htu e (Finset.mem_coe.2 heE) hLe
      obtain ⟨w, hw⟩ := hMK hMe
      have hwz := hnext (t ++ u) e w z hw hzt
      rw [hfe] at hwz
      exact Finset.notMem_empty w hwz
    induction s using List.reverseRecOn with
    | nil =>
      obtain ⟨x, hx⟩ := hMK hs
      exact ⟨x, Finset.mem_filter.2 ⟨hx, (hG x).2 (hnobad [] hs x hx)⟩⟩
    | append_singleton s e ih =>
      obtain ⟨x, hx⟩ := ih (hM s [e] hs)
      obtain ⟨w, hw⟩ := hMK hs
      have hwx := hnext s e w x hw (hrunG s x hx).1
      exact hextend s e x w hx hwx ((hG w).2 (hnobad _ hs w hw))

end escape

/-! ## The automata the library builds -/

namespace Automaton

/-- The language of a deletion: if $G'$ is $G$ with $D$ deleted, then
$L(G') = L(G|_{X \setminus D})$.

**Proof:** the labels $old$ map $G'$ onto $G|_{X \setminus D}$ step by step (`IsDeletion.f`,
`IsDeletion.range`) and on the initial states (`IsDeletion.X0`), so `gen_eq_of_labels`
applies. -/
theorem IsDeletion.L_eq {G G' : Automaton α} {D : Finset (Fin G.n)} {old : Fin G'.n → Fin G.n}
    (h : IsDeletion G D G' old) :
    G'.L = gen (restrict G.f (· ∉ D)) (G.X0.filter (· ∉ D)) := by
  unfold Automaton.L
  apply gen_eq_of_labels old
  · ext y
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨(h.X0 i).1 hi, (h.range _).2 ⟨i, rfl⟩⟩
    · rintro ⟨hy, hyD⟩
      obtain ⟨i, rfl⟩ := (h.range y).1 hyD
      exact ⟨i, (h.X0 i).2 hy, rfl⟩
  · intro i e
    ext y
    simp only [restrict, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨(h.f i e j).1 hj, (h.range _).2 ⟨j, rfl⟩⟩
    · rintro ⟨hy, hyD⟩
      obtain ⟨j, rfl⟩ := (h.range y).1 hyD
      exact ⟨j, (h.f i e j).2 hy, rfl⟩

/-- Restricting to a set that contains every reachable state changes no run:
$Ac \subseteq R \implies L(G|_R) = L(G)$.

**Proof:** by induction on the word from the right, the two runs are equal: every initial state
and every state reached by one more step is reachable, so the filter keeps it. -/
theorem gen_restrict_reach (f : σ → α → Finset σ) (X0 : Finset σ) (R : σ → Prop)
    [DecidablePred R] (hR : ∀ y ∈ reach f X0, R y) :
    gen (restrict f R) (X0.filter R) = gen f X0 := by
  have key : ∀ s, run (restrict f R) (X0.filter R) s = run f X0 s := by
    intro s
    induction s using List.reverseRecOn with
    | nil =>
      exact Finset.filter_true_of_mem (fun x hx => hR x (mem_reach_of_mem hx))
    | append_singleton s e ih =>
      rw [run_append, run_append, ih]
      simp only [run_cons, run_nil, step, restrict]
      refine Finset.biUnion_congr rfl (fun x hx => ?_)
      refine Finset.filter_true_of_mem (fun y hy => hR y ⟨s ++ [e], ?_⟩)
      rw [run_append, run_cons, run_nil]
      exact (mem_step f).2 ⟨x, hx, hy⟩
  ext s
  rw [mem_gen, mem_gen, key]

/-- Deleting the unreachable states keeps the language: if $G'$ is $G$ with the states outside
$Ac(G)$ deleted (what `accessible` returns), then $L(G') = L(G)$. -/
theorem IsDeletion.L_accessible {G G' : Automaton α} {D : Finset (Fin G.n)}
    {old : Fin G'.n → Fin G.n} (h : IsDeletion G D G' old) (hD : ∀ x, x ∈ D ↔ x ∉ G.Ac) :
    G'.L = G.L := by
  rw [h.L_eq]
  exact gen_restrict_reach G.f G.X0 _ (fun y hy => by rw [hD]; exact not_not.2 hy)

/-- **The supervisor the library returns** (prefix-closed, spec §2). Let $P$ be deterministic
and $I$ its inside states, so $K = L(P|_I)$. If
- $D_1 = Bad$ (verified `coreachable` over `keep_events(P, E_uc)`, from $X \setminus I$),
- $Q$ is $P$ with $D_1$ deleted (verified `delete_states`),
- $S$ is $Q$ with the states outside $Ac(Q)$ deleted (verified `accessible`),

then $L(S) = K^{\uparrow C}$ with respect to $L(P)$ and $E_{uc}(P)$.

**Proof:** $L(S) = L(Q)$ (`L_accessible`) $= L(P|_{X \setminus D_1})$ (`L_eq`), and
`supcon_strict_sub` with $G = (\cdot \notin D_1)$. -/
theorem supervisor_L [DecidableEq α] (P : Automaton α) (hP : P.IsDeterministic)
    (I : Fin P.n → Prop) [DecidablePred I]
    (D1 : Finset (Fin P.n)) (hD1 : ∀ x, x ∈ D1 ↔ x ∈ bad P.f I P.Euc)
    {Q : Automaton α} {old1 : Fin Q.n → Fin P.n} (h1 : IsDeletion P D1 Q old1)
    (D2 : Finset (Fin Q.n)) (hD2 : ∀ x, x ∈ D2 ↔ x ∉ Q.Ac)
    {S : Automaton α} {old2 : Fin S.n → Fin Q.n} (h2 : IsDeletion Q D2 S old2) :
    S.L = supC (gen (restrict P.f I) (P.X0.filter I)) P.L (P.Euc : Set α) := by
  rw [h2.L_accessible hD2, h1.L_eq]
  exact supcon_strict_sub P.f P.X0 I P.Euc hP.1 hP.2 _ (fun x => not_congr (hD1 x))

/-- **The supervisor the library returns, escape form** (`sup.supervisor`, spec §2). Let $P_0$
(in the library: $G \parallel H$) be deterministic, $L_p$ (the plant language $L(G)$) prefix-closed
with $L(P_0) \subseteq L_p$, and $en$ the plant's enabled events as in `supcon_escape`. If
- $D_1 = Bad$ (verified `bad0`, `keep_events(P_0, E_{uc})`, `coreachable`),
- $Q$ is $P_0$ with $D_1$ deleted (verified `delete_states`),
- $S$ is $Q$ with the states outside $Ac(Q)$ deleted (verified `accessible`),

then $L(S) = L(P_0)^{\uparrow C}$ with respect to $L_p$ and $E_{uc}(P_0)$.

**Proof:** as `supervisor_L`, with `supcon_escape`. -/
theorem supervisor_escape_L [DecidableEq α] (P : Automaton α) (hP : P.IsDeterministic)
    (Lp : Language α) (hLp : PrefixClosed Lp) (hK : P.L ≤ Lp) (en : Fin P.n → α → Prop)
    (hen : ∀ s x e, x ∈ run P.f P.X0 s → (s ++ [e] ∈ Lp ↔ en x e))
    (D1 : Finset (Fin P.n)) (hD1 : ∀ x, x ∈ D1 ↔ x ∈ badE P.f P.Euc en)
    {Q : Automaton α} {old1 : Fin Q.n → Fin P.n} (h1 : IsDeletion P D1 Q old1)
    (D2 : Finset (Fin Q.n)) (hD2 : ∀ x, x ∈ D2 ↔ x ∉ Q.Ac)
    {S : Automaton α} {old2 : Fin S.n → Fin Q.n} (h2 : IsDeletion Q D2 S old2) :
    S.L = supC P.L Lp (P.Euc : Set α) := by
  rw [h2.L_accessible hD2, h1.L_eq]
  exact supcon_escape P.f P.X0 P.Euc en hP.1 hP.2 Lp hLp hK hen _ (fun x => not_congr (hD1 x))

end Automaton

end DESopsProof
