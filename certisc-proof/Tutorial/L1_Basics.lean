import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.Use

/-!
# Lesson 1: Lean for someone who already writes proofs

You know how to prove things on paper. Lean asks for the same proof, but every step must be
explicit enough for a machine to check. This lesson maps the pieces of a paper proof to Lean,
one at a time. Nothing here is about automata yet; that starts in Lesson 2.

**How to read this file.** Open it in VS Code (with the `lean4` extension) and put the cursor on
a line inside a proof. The *Infoview* panel on the right shows the **goal**: what is left to
prove at that point, written

    hypotheses we may use
    ⊢ the statement still to prove

The comments `-- ⊢ ...` below copy what the Infoview shows, so you can also read the file
without Lean. Two things the Infoview shows that the comments often leave out:
- the variables of the statement itself (e.g. `A B : Prop`), when nothing about them changes;
- a label such as `case h` or `case succ`: the name Lean gives each open goal (useful when
  there are several; you can ignore it).

## The dictionary

| On paper | In Lean |
|---|---|
| "Let $n \in \mathbb{N}$." | `(n : ℕ)`: `n` has *type* `ℕ` |
| a definition $f(n) = 2n$ | `def f (n : ℕ) : ℕ := 2 * n` |
| a statement $P$ | `P : Prop`, a proposition |
| a proof of $P$ | `h : P`, a term whose type is `P` |
| "Theorem. $P$. Proof. ..." | `theorem name : P := by ...` |
| "by definition" / "compute" | `rfl`, `decide`, `simp` |
| "assume $A$" (to prove $A \Rightarrow B$) | `intro hA` |
| "let $x$ be arbitrary" (to prove $\forall x$) | `intro x` |
| "take $x = 3$" (to prove $\exists x$) | `use 3` / `exact ⟨3, proof⟩` |
| "it suffices to prove both parts" ($A \land B$) | `constructor` |
| "by the hypothesis $h$" | `exact h` |
| "rewrite with the equation $h$" | `rw [h]` |
| "by cases on $x$" | `cases x` / `rcases` |
| "by induction on $n$" | `induction n with ...` |

The one real difference from paper: a type is not a set. `n : ℕ` is a *declaration* ("n is a
natural number"), not a proposition `n ∈ ℕ` that could be true or false. Sets exist too
(`Set ℕ`), and we use them for languages in Lesson 4.
-/

namespace Tutorial.L1

/-! ## 1. Definitions and computation

`def` makes a definition. `#eval` computes it (like a calculator); `#check` shows a type.
Hover over `#eval` in VS Code to see the output. -/

/-- $\mathrm{double}(n) = 2n$. -/
def double (n : ℕ) : ℕ := 2 * n

#eval double 21        -- 42
#check double          -- double : ℕ → ℕ   (a function from ℕ to ℕ)
#check double 21 = 42  -- double 21 = 42 : Prop   (a statement; not yet proved)

/-! ## 2. The simplest proofs: "by definition"

**Math.** $\mathrm{double}(21) = 42$. *Proof:* $2 \cdot 21 = 42$. ∎

`rfl` ("reflexivity") proves `a = b` when both sides compute to the same value. -/

theorem double_21 : double 21 = 42 := by
  -- ⊢ double 21 = 42
  rfl
  -- no goals: the proof is complete

/-- `decide` proves a statement that Lean can *decide* by running a check, e.g. a comparison of
numbers or a fact about a finite set of cases. -/
theorem double_21_lt : double 21 < 50 := by
  decide

/-! ## 3. Implication and "for all": `intro`

**Math.** For every $n$, $\mathrm{double}(n) = n + n$.
*Proof:* let $n$ be arbitrary. Then $2n = n + n$. ∎

In Lean, "let $n$ be arbitrary" is `intro n`: it moves `n` from the goal into the context. -/

theorem double_eq_add : ∀ n : ℕ, double n = n + n := by
  -- ⊢ ∀ (n : ℕ), double n = n + n
  intro n
  -- n : ℕ
  -- ⊢ double n = n + n
  unfold double
  -- n : ℕ
  -- ⊢ 2 * n = n + n
  omega
  -- `omega` proves linear arithmetic over ℕ and ℤ: here 2n = n + n.

/-- The usual style puts the "let n be arbitrary" in the statement itself: `(n : ℕ)` before the
colon means "for every n". Same theorem, no `intro` needed. -/
theorem double_eq_add' (n : ℕ) : double n = n + n := by
  -- n : ℕ
  -- ⊢ double n = n + n
  unfold double
  omega

/-! **Math.** If $A$ and $A \Rightarrow B$, then $B$ (modus ponens).
*Proof:* assume $A$ (call it $h_A$) and $A \Rightarrow B$ (call it $h_{AB}$). Applying
$h_{AB}$ to $h_A$ gives $B$. ∎

In Lean a proof of `A → B` *is a function* that turns a proof of `A` into a proof of `B`. So
"applying $h_{AB}$ to $h_A$" is literally function application: `hAB hA`. -/

theorem modus_ponens (A B : Prop) : A → (A → B) → B := by
  -- A B : Prop
  -- ⊢ A → (A → B) → B
  intro hA
  -- A B : Prop
  -- hA : A
  -- ⊢ (A → B) → B
  intro hAB
  -- A B : Prop
  -- hA : A
  -- hAB : A → B
  -- ⊢ B
  exact hAB hA

/-! ## 4. "And" and "there exists"

**Math.** There is an $n$ with $\mathrm{double}(n) = 10$ and $n < 6$.
*Proof:* take $n = 5$. Then $\mathrm{double}(5) = 10$ and $5 < 6$. ∎ -/

theorem exists_double_10 : ∃ n : ℕ, double n = 10 ∧ n < 6 := by
  -- ⊢ ∃ n, double n = 10 ∧ n < 6
  use 5
  -- ⊢ double 5 = 10 ∧ 5 < 6
  constructor
  -- two goals now, one per side of ∧:
  -- ⊢ double 5 = 10
  · rfl
  -- ⊢ 5 < 6
  · decide

/-! Using an "and" or an "exists" hypothesis is the other direction: we take it apart.
`obtain ⟨x, hx⟩ := h` reads "let $x$ be the witness given by $h$, with property $hx$".

**Math.** If some $n$ has $\mathrm{double}(n) = 10$, then some $m$ has $m + m = 10$.
*Proof:* let $n$ be such that $\mathrm{double}(n) = 10$. Take $m = n$: $n + n =
\mathrm{double}(n) = 10$. ∎ -/

theorem exists_add_10 (h : ∃ n : ℕ, double n = 10) : ∃ m : ℕ, m + m = 10 := by
  -- h : ∃ n, double n = 10
  -- ⊢ ∃ m, m + m = 10
  obtain ⟨n, hn⟩ := h
  -- n : ℕ
  -- hn : double n = 10
  -- ⊢ ∃ m, m + m = 10
  use n
  -- ⊢ n + n = 10
  rw [← double_eq_add n]
  -- `rw [← e]` rewrites with the equation e from right to left: `n + n` becomes `double n`.
  -- ⊢ double n = 10
  exact hn

/-! ## 5. Cases

**Math.** For every boolean $b$, $\neg\neg b = b$.
*Proof:* by cases. If $b$ is false, $\neg\neg\mathrm{false} = \neg\mathrm{true} =
\mathrm{false}$. If $b$ is true, likewise. ∎ -/

theorem not_not_bool (b : Bool) : (!(!b)) = b := by
  -- b : Bool
  -- ⊢ (!!b) = b
  cases b with
  | false =>
    -- case false
    -- ⊢ (!!false) = false
    rfl
  | true =>
    -- case true
    -- ⊢ (!!true) = true
    rfl

/-! **A trap worth knowing.** Without the outer parentheses, `!(!b) = b` means `!((!b) = b)`
("it is false that ¬b = b"), because `!` binds more loosely than `=` here. That statement is
also true, so Lean would accept the proof, and we would have proved something other than what
we meant. Lean checks the proof, not that the statement is the one you had in mind: read your
statements carefully, and check them in the Infoview (hover over them). -/

/-! ## 6. Induction

**Math.** For every $n$, $0 + n = n$.
*Proof:* by induction on $n$.
- Base case $n = 0$: $0 + 0 = 0$.
- Step: assume $0 + k = k$ (the induction hypothesis, IH). Then
  $0 + (k + 1) = (0 + k) + 1 = k + 1$, by associativity and the IH. ∎

(This is not obvious to Lean: `+` on ℕ is defined by recursion on the *second* argument, so
`n + 0 = n` holds by definition but `0 + n = n` needs induction.) -/

theorem zero_add' (n : ℕ) : 0 + n = n := by
  induction n with
  | zero =>
    -- ⊢ 0 + 0 = 0
    rfl
  | succ k ih =>
    -- case succ
    -- k : ℕ
    -- ih : 0 + k = k            (the induction hypothesis)
    -- ⊢ 0 + (k + 1) = k + 1
    rw [← Nat.add_assoc]
    -- ⊢ 0 + k + 1 = k + 1
    rw [ih]
    -- `rw` closes the goal by itself once both sides are identical (k + 1 = k + 1).

/-! ## 7. Automation, and when to use it

`simp` rewrites with a large set of known equations; `omega` does linear arithmetic; `decide`
checks finite facts. They replace routine steps, the ones a paper proof writes as "clearly".
In this tutorial we mostly write the steps out, so each step matches a line of math, and say
when a tactic is doing the routine part. -/

/-- `simp` finds `Nat.zero_add` (the library's version of the theorem above) by itself. -/
example (n : ℕ) : 0 + n = n := by simp

/-! ## Exercises (solutions in `Solutions.lean`)

1. `double (double 3) = 12`.
2. `∀ n : ℕ, double n ≥ n`.
3. For propositions `A B`: `A ∧ B → B ∧ A`.
4. `∃ n : ℕ, double n = n` (which `n`?).
-/

end Tutorial.L1
