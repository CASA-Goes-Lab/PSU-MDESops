import Mathlib.Data.Set.Finite.Basic
import Tutorial.L4_Languages

/-!
# Solutions to the exercises

Try each exercise in its lesson first: copy the statement into a new file (or below the lesson),
write `by sorry`, and replace `sorry` step by step while watching the goal in the Infoview.
`sorry` is Lean's "proof to be done": the file still compiles, with a warning.

Each solution gives the math proof first, then the Lean proof with the goals.
-/

namespace Tutorial.Solutions

open Tutorial.L1 Tutorial.L2 Tutorial.L2.State Tutorial.L2.Event Tutorial.L3 Tutorial.L4

/-! ## Lesson 1 -/

/-- 1. $\mathrm{double}(\mathrm{double}(3)) = \mathrm{double}(6) = 12$. -/
example : double (double 3) = 12 := by
  rfl

/-- 2. $\mathrm{double}(n) = 2n \ge n$. -/
example : ∀ n : ℕ, double n ≥ n := by
  intro n
  -- ⊢ double n ≥ n
  unfold double
  -- ⊢ 2 * n ≥ n
  omega

/-- 3. From $A \land B$, take both parts and put them back in the other order. -/
example (A B : Prop) : A ∧ B → B ∧ A := by
  intro h
  -- h : A ∧ B
  -- ⊢ B ∧ A
  obtain ⟨hA, hB⟩ := h
  -- hA : A
  -- hB : B
  -- ⊢ B ∧ A
  exact ⟨hB, hA⟩
  -- `⟨hB, hA⟩` builds a proof of B ∧ A from its two parts (same as `constructor`, then
  -- `exact hB` and `exact hA`).

/-- 4. $n = 0$: $\mathrm{double}(0) = 0$. (It is the only one, but the exercise only asks for
one.) -/
example : ∃ n : ℕ, double n = n := by
  use 0
  -- ⊢ double 0 = 0
  rfl

/-! ## Lesson 2 -/

/-- 1. By the definition of $\delta$ (third line). -/
example : G.δ Working breakdown = some Down := by
  rfl

/-- 2. $\mathrm{Working} \notin \{\mathrm{Idle}\}$, since $\mathrm{Working} \neq \mathrm{Idle}$.
Named, because Lesson 4's exercise 2 uses it. -/
theorem Working_not_marked : Working ∉ G.Xm := by
  intro h
  -- h : Working ∈ G.Xm
  -- ⊢ False
  change Working ∈ ({Idle} : Set State) at h
  -- h : Working ∈ {Idle}
  rw [Set.mem_singleton_iff] at h
  -- h : Working = Idle
  -- ⊢ False
  cases h
  -- Working and Idle are different constructors: no way for h to hold, goal closed.

/-- 3. As `Down_only_repair`: four cases, each a finite check. -/
example (e : Event) : G.δ Idle e ≠ none ↔ e = start := by
  cases e <;> decide

/-! ## Lesson 3 -/

/-- 1. $\delta^*(\mathrm{Down}, \mathrm{repair}\ \mathrm{start})
= \delta^*(\mathrm{Idle}, \mathrm{start}) = \delta^*(\mathrm{Working}, \varepsilon)
= \mathrm{Working}$. -/
example : δstar G Down [repair, start] = some Working := by
  rfl

example : δstar G Down [repair, start] = some Working := by
  calc δstar G Down [repair, start]
      = δstar G Idle [start] := rfl
    _ = δstar G Working [] := rfl
    _ = some Working := rfl

/-- 2. $\delta^*(\mathrm{Idle}, \mathrm{start}\ \mathrm{breakdown}\ \mathrm{finish})
= \delta^*(\mathrm{Down}, \mathrm{finish})$, undefined. -/
example : δstar G Idle [start, breakdown, finish] = none := by
  rfl

/-- 3. $s\,\varepsilon = s$. -/
example {X E : Type} (G : Automaton X E) (x : X) (s : List E) :
    δstar G x (s ++ []) = δstar G x s := by
  rw [List.append_nil]

/-- 4. By the main lemma: $\delta^*(x, s\,t)$ continues from $\delta^*(x, s) = y$. -/
example {X E : Type} (G : Automaton X E) {x y : X} {s : List E} (t : List E)
    (h : δstar G x s = some y) : δstar G x (s ++ t) = δstar G y t := by
  rw [δstar_append]
  -- ⊢ ((δstar G x s).bind fun y => δstar G y t) = δstar G y t
  rw [h]
  -- ⊢ ((some y).bind fun y => δstar G y t) = δstar G y t
  rw [Option.bind_some]

/-! ## Lesson 4 -/

/-- 1. $\delta^*(\mathrm{Idle}, \mathrm{start}\ \mathrm{breakdown}\ \mathrm{repair})
= \mathrm{Idle} \in X_m$. -/
example : [start, breakdown, repair] ∈ Lm G := by
  rw [Lm, Set.mem_ofPred_eq]
  exact ⟨Idle, Idle_marked, rfl⟩

/-- 2a. $\delta^*(\mathrm{Idle}, \mathrm{start}) = \mathrm{Working}$ is defined. -/
example : [start] ∈ L G := by
  rw [L, Set.mem_ofPred_eq]
  exact ⟨Working, rfl⟩

/-- 2b. If $\delta^*(\mathrm{Idle}, \mathrm{start}) = y \in X_m$, then $y = \mathrm{Working}$
(the value is unique), but $\mathrm{Working} \notin X_m$. -/
example : [start] ∉ Lm G := by
  intro h
  rw [Lm, Set.mem_ofPred_eq] at h
  obtain ⟨y, hy, hs⟩ := h
  -- hy : y ∈ G.Xm
  -- hs : δstar G G.x0 [start] = some y
  -- ⊢ False
  have hw : some Working = some y := hs
  -- `have` states and proves an intermediate fact; `hs` proves it because its left side
  -- computes to `some Working`.
  have hyW : Working = y := Option.some.inj hw
  -- `Option.some.inj`: some a = some b → a = b.
  rw [← hyW] at hy
  -- hy : Working ∈ G.Xm
  exact Working_not_marked hy

/-- 3. $\delta^*(x_0, \varepsilon) = x_0$ is defined. -/
example {X E : Type} (G : Automaton X E) : [] ∈ L G := by
  rw [L, Set.mem_ofPred_eq]
  exact ⟨G.x0, rfl⟩

/-- 4, step 1. $|c_n| = 2n$, by induction: $|c_{n+1}| = 2 + |c_n| = 2 + 2n = 2(n+1)$. -/
theorem length_cycles (n : ℕ) : (cycles n).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    -- ih : (cycles n).length = 2 * n
    -- ⊢ (cycles (n + 1)).length = 2 * (n + 1)
    rw [cycles, List.length_append, ih]
    -- ⊢ [start, finish].length + 2 * n = 2 * (n + 1)
    rw [List.length_cons, List.length_cons, List.length_nil]
    -- ⊢ 0 + 1 + 1 + 2 * n = 2 * (n + 1)
    omega
    -- (`rfl` fails here: `n` is a variable, so the two sides do not compute to the same
    -- thing; it takes arithmetic, which `omega` does.)

/-- 4. $L_m(G)$ is infinite: $n \mapsto c_n$ is injective (equal words have equal lengths
$2a = 2b$, so $a = b$) and every $c_n \in L_m(G)$; an injective image of the infinite set
$\mathbb{N}$ is infinite. -/
example : Set.Infinite (Lm G) := by
  apply Set.infinite_of_injective_forall_mem (f := cycles)
  -- Two goals: injectivity, and membership.
  · -- ⊢ Function.Injective cycles
    intro a b hab
    -- hab : cycles a = cycles b
    -- ⊢ a = b
    have hlen : (cycles a).length = (cycles b).length := by rw [hab]
    rw [length_cycles, length_cycles] at hlen
    -- hlen : 2 * a = 2 * b
    omega
  · -- ⊢ ∀ (x : ℕ), cycles x ∈ Lm G
    exact cycles_mem_Lm

end Tutorial.Solutions
