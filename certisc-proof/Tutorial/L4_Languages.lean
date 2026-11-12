import Tutorial.L3_Words

/-!
# Lesson 4: the languages $L(G)$ and $L_m(G)$

**Math.** The *language generated* by $G$ is the set of words $G$ can execute from $x_0$; the
*marked language* is the set of those that end in a marked state:
$$L(G) = \{\, s \in E^* \mid \delta^*(x_0, s) \text{ is defined} \,\}, \qquad
  L_m(G) = \{\, s \in E^* \mid \delta^*(x_0, s) \in X_m \,\}.$$

We prove, for the machine $G$ of Lesson 2 and for every automaton:
1. specific words are in, or not in, the languages (§2);
2. $L_m(G) \subseteq L(G)$ (§3);
3. $L(G)$ is prefix-closed: $s\,t \in L(G) \implies s \in L(G)$ (§4);
4. for every $n$, $(\mathrm{start}\ \mathrm{finish})^n \in L_m(G)$, by induction on $n$ (§5).

New Lean in this lesson: sets `{s | P s}` and membership, `Set.mem_ofPred_eq`, `obtain` on an
equation, `Option.some.inj`, the `⊆` of sets.
-/

namespace Tutorial.L4

open Tutorial.L2 Tutorial.L2.State Tutorial.L2.Event Tutorial.L3

variable {X E : Type}

/-! ## 1. The definitions

"$\delta^*(x_0, s)$ is defined" is $\exists y,\ \delta^*(x_0, s) = y$; "$\delta^*(x_0, s) \in X_m$"
is $\exists y \in X_m,\ \delta^*(x_0, s) = y$. Writing them with $\exists$ makes the proofs
below follow the math: to show a word is in, give the state it reaches. -/

/-- $L(G) = \{s \mid \exists y,\ \delta^*(x_0, s) = y\}$. -/
def L (G : Automaton X E) : Set (List E) :=
  {s | ∃ y, δstar G G.x0 s = some y}

/-- $L_m(G) = \{s \mid \exists y \in X_m,\ \delta^*(x_0, s) = y\}$. -/
def Lm (G : Automaton X E) : Set (List E) :=
  {s | ∃ y ∈ G.Xm, δstar G G.x0 s = some y}

/-! For `S = {s | P s}`, membership `w ∈ S` *is* `P w` by definition. The library lemma
`Set.mem_ofPred_eq : (a ∈ {x | p x}) = p a` does this rewriting step explicitly; we use it so the
goal shows the property itself. -/

/-! ## 2. Words in and out of the languages

**Math.** $\mathrm{start}\ \mathrm{finish} \in L_m(G)$.
*Proof:* $\delta^*(\mathrm{Idle}, \mathrm{start}\ \mathrm{finish}) = \mathrm{Idle}$
(Lesson 3), and $\mathrm{Idle} \in X_m$ (Lesson 2). So $y = \mathrm{Idle}$ works. ∎ -/

theorem start_finish_mem_Lm : [start, finish] ∈ Lm G := by
  -- ⊢ [start, finish] ∈ Lm G
  rw [Lm, Set.mem_ofPred_eq]
  -- ⊢ ∃ y, y ∈ G.Xm ∧ δstar G G.x0 [start, finish] = some y
  -- (Lean shows `∃ y ∈ S, P` as `∃ y, y ∈ S ∧ P`: "some y, in S, with P".)
  refine ⟨Idle, ?_, ?_⟩
  -- "take y = Idle"; `refine ⟨Idle, ?_, ?_⟩` leaves one goal for each `?_`:
  -- ⊢ Idle ∈ G.Xm
  · exact Idle_marked
  -- ⊢ δstar G G.x0 [start, finish] = some Idle
  · exact start_finish

/-! **Math.** $\mathrm{finish} \notin L(G)$.
*Proof:* suppose $\mathrm{finish} \in L(G)$: $\delta^*(\mathrm{Idle}, \mathrm{finish}) = y$ for
some $y$. But $\delta(\mathrm{Idle}, \mathrm{finish})$ is undefined, so
$\delta^*(\mathrm{Idle}, \mathrm{finish})$ is undefined: contradiction. ∎ -/

theorem finish_not_mem_L : [finish] ∉ L G := by
  -- ⊢ ¬[finish] ∈ L G
  -- (Lean shows `a ∉ S` as `¬a ∈ S`: "not a ∈ S".)
  intro h
  -- `¬P` is `P → False`: assume s ∈ S, reach False.
  -- h : [finish] ∈ L G
  -- ⊢ False
  rw [L, Set.mem_ofPred_eq] at h
  -- h : ∃ y, δstar G G.x0 [finish] = some y
  -- ⊢ False
  obtain ⟨y, hy⟩ := h
  -- hy : δstar G G.x0 [finish] = some y
  -- ⊢ False
  change δstar G Idle [finish] = some y at hy
  -- G.x0 is Idle by definition, but `rw` only matches what is written, not what it means;
  -- `change` rewrites hy into an equal-by-definition form where Idle appears:
  -- hy : δstar G Idle [finish] = some y
  -- ⊢ False
  rw [δstar_cons_none G δ_Idle_finish] at hy
  -- δ(Idle, finish) is undefined (Lesson 2), so δ*(Idle, finish ...) is too (Lesson 3):
  -- hy : none = some y
  -- ⊢ False
  cases hy
  -- `none` and `some y` are built differently (different constructors of `Option`), so
  -- `none = some y` can never hold. `cases hy` asks "in which ways could hy be true?"; there
  -- are none, so no case is left to prove and the goal is closed.

/-! ## 3. $L_m(G) \subseteq L(G)$, for every automaton

**Math.** Let $s \in L_m(G)$: there is $y \in X_m$ with $\delta^*(x_0, s) = y$. Then
$\delta^*(x_0, s)$ is defined, so $s \in L(G)$. ∎

`S ⊆ T` for sets is, by definition, `∀ s, s ∈ S → s ∈ T`. -/

theorem Lm_subset_L (G : Automaton X E) : Lm G ⊆ L G := by
  -- ⊢ Lm G ⊆ L G
  intro s hs
  -- s : List E
  -- hs : s ∈ Lm G
  -- ⊢ s ∈ L G
  rw [Lm, Set.mem_ofPred_eq] at hs
  -- hs : ∃ y, y ∈ G.Xm ∧ δstar G G.x0 s = some y
  obtain ⟨y, _hy_marked, hy⟩ := hs
  -- y : X
  -- _hy_marked : y ∈ G.Xm      (not needed: the name starts with _ to say so)
  -- hy : δstar G G.x0 s = some y
  -- ⊢ s ∈ L G
  rw [L, Set.mem_ofPred_eq]
  -- ⊢ ∃ y, δstar G G.x0 s = some y
  exact ⟨y, hy⟩

/-! ## 4. $L(G)$ is prefix-closed, for every automaton

**Math.** If $s\,t \in L(G)$ then $s \in L(G)$.
*Proof:* $\delta^*(x_0, s\,t)$ is defined, so $\delta^*(x_0, s)$ is defined (Lesson 3,
`δstar_prefix`). ∎

Here "defined" was written two ways: `∃ y, o = some y` (in `L`) and `o ≠ none` (in Lesson 3). The
library lemma `Option.ne_none_iff_exists'` says they are the same: `o ≠ none ↔ ∃ y, o = some y`. -/

theorem L_prefix_closed (G : Automaton X E) {s t : List E} (h : s ++ t ∈ L G) : s ∈ L G := by
  -- h : s ++ t ∈ L G
  -- ⊢ s ∈ L G
  rw [L, Set.mem_ofPred_eq, ← Option.ne_none_iff_exists'] at h ⊢
  -- `at h ⊢` rewrites both the hypothesis h and the goal (⊢).
  -- h : δstar G G.x0 (s ++ t) ≠ none
  -- ⊢ δstar G G.x0 s ≠ none
  exact δstar_prefix G h

/-! ## 5. Induction: $(\mathrm{start}\ \mathrm{finish})^n \in L_m(G)$ for every $n$

Define $c_0 = \varepsilon$ and $c_{n+1} = \mathrm{start}\ \mathrm{finish}\ c_n$, so
$c_n = (\mathrm{start}\ \mathrm{finish})^n$: $n$ complete work cycles. -/

/-- $c_n$: $n$ work cycles. -/
def cycles : ℕ → List Event
  | 0 => []
  | n + 1 => [start, finish] ++ cycles n

#eval cycles 2      -- [start, finish, start, finish]

/-! **Math (lemma).** For every $n$, $\delta^*(\mathrm{Idle}, c_n) = \mathrm{Idle}$.
*Proof:* by induction on $n$.
- $n = 0$: $\delta^*(\mathrm{Idle}, \varepsilon) = \mathrm{Idle}$.
- Step, IH $\delta^*(\mathrm{Idle}, c_n) = \mathrm{Idle}$:
  $$\delta^*(\mathrm{Idle}, \mathrm{start}\ \mathrm{finish}\ c_n)
    = \delta^*(\delta^*(\mathrm{Idle}, \mathrm{start}\ \mathrm{finish}), c_n)
    = \delta^*(\mathrm{Idle}, c_n) = \mathrm{Idle},$$
  by the main lemma of Lesson 3, then `start_finish`, then the IH. ∎ -/

theorem δstar_cycles (n : ℕ) : δstar G Idle (cycles n) = some Idle := by
  induction n with
  | zero =>
    -- ⊢ δstar G Idle (cycles 0) = some Idle
    rfl
  | succ n ih =>
    -- ih : δstar G Idle (cycles n) = some Idle
    -- ⊢ δstar G Idle (cycles (n + 1)) = some Idle
    rw [cycles]
    -- unfold c_{n+1}:
    -- ⊢ δstar G Idle ([start, finish] ++ cycles n) = some Idle
    rw [δstar_append]
    -- ⊢ ((δstar G Idle [start, finish]).bind fun y => δstar G y (cycles n)) = some Idle
    rw [start_finish]
    -- ⊢ ((some Idle).bind fun y => δstar G y (cycles n)) = some Idle
    rw [Option.bind_some]
    -- ⊢ δstar G Idle (cycles n) = some Idle
    exact ih

/-! **Math (theorem).** For every $n$, $c_n \in L_m(G)$.
*Proof:* $\delta^*(x_0, c_n) = \mathrm{Idle} \in X_m$ by the lemma. ∎ -/

theorem cycles_mem_Lm (n : ℕ) : cycles n ∈ Lm G := by
  rw [Lm, Set.mem_ofPred_eq]
  -- ⊢ ∃ y, y ∈ G.Xm ∧ δstar G G.x0 (cycles n) = some y
  exact ⟨Idle, Idle_marked, δstar_cycles n⟩

/-! So $L_m(G)$ is infinite: it contains $c_0, c_1, c_2, \dots$, all different (they have
different lengths). Proving "infinite" formally is Exercise 4.

## What comes next

This tutorial's automaton is deterministic with a partial $\delta$ (`Option`). The project's
definitions (`DESopsProof/Automaton.lean`) are the general ones the verified code needs:
- **nondeterministic**: $f : X \times E \to 2^X$ (`Fin n → α → Finset (Fin n)`), a set of next
  states instead of at most one, and a set of initial states $X_0$;
- the states are numbered, $X = \{0, \dots, n-1\}$ (`Fin n`), as in the Rust code;
- $\delta^*$ is `run`, $L$ is `gen` (`L G`), $L_m$ is `mkd` (`Lm G`); "defined" becomes "the set
  of states reached is nonempty".

The proofs have the same shape as here: `run_append` is Lesson 3's main lemma, and
`L_of_append` is §4's prefix closure. Read those next.

## Exercises (solutions in `Solutions.lean`)

1. `[start, breakdown, repair] ∈ Lm G`.
2. `[start] ∈ L G` but `[start] ∉ Lm G`.
3. `[] ∈ L G` for every automaton (`G : Automaton X E`).
4. `Set.Infinite (Lm G)`. (Hint: the map `cycles` is injective, because
   `(cycles n).length = 2 * n`; then use `Set.infinite_of_injective_forall_mem`.)
-/

end Tutorial.L4
