import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.Use

/-!
# Lesson 1: Lean for someone who already writes proofs

You know how to prove things on paper.
Lean asks for the same proof, but every step must be
explicit enough for a machine to check.
This lesson maps the pieces of a paper proof to Lean,
one at a time. Nothing here is about automata yet; that starts in Lesson 2.

**How to read this file.** Open it in VS Code (with the `lean4` extension) and put the cursor on
a line inside a proof.
The *Infoview* panel on the right shows the **goal**: what is left to
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
| "For example, $P$. Proof. ..." | `example : P := by ...` (a theorem with no name) |
| "by definition" / "compute" | `rfl`, `decide`, `simp` |
| "assume $A$" (to prove $A \Rightarrow B$) | `intro hA` |
| "let $x$ be arbitrary" (to prove $\forall x$) | `intro x` |
| "take $x = 3$" (to prove $\exists x$) | `use 3` / `exact ⟨3, proof⟩` |
| "it suffices to prove both parts" ($A \land B$) | `constructor` |
| "by the hypothesis $h$" | `exact h` |
| "by $h : A \Rightarrow B$, it suffices to prove $A$" (goal $B$) | `apply h` |
| "rewrite with the equation $h$" | `rw [h]` |
| "by cases on $x$" | `cases x` / `rcases` |
| "by induction on $n$" | `induction n with ...` |

The one real difference from paper: a type is not a set.
`n : ℕ` is a *declaration* ("n is a natural number"), not a proposition `n ∈ ℕ` that could be true or false.
Sets exist too (`Set ℕ`), and we use them for languages in Lesson 4.
-/

namespace Tutorial.L1

/-! ## 1. Definitions and computation

`def` makes a definition.
`#eval` computes it (like a calculator);
`#check` shows a type.
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
  unfold double
  -- `unfold double` replaces `double 21` by its definition, `2 * 21`.
  -- ⊢ 2 * 21 = 42
  have h : 2 * 21 = 42 := by decide
  -- `have` proves a side fact and names it `h`; `decide` checks it by computing.
  -- h : 2 * 21 = 42
  -- ⊢ 2 * 21 = 42
  rewrite [h]
  -- `rewrite [h]` replaces the left side of h (`2 * 21`) by its right side (`42`) in the goal.
  -- h : 2 * 21 = 42
  -- ⊢ 42 = 42
  rfl
  -- `rfl`: both sides are literally the same.
  -- no goals: the proof is complete

/-- The same proof in one step: `rfl` unfolds `double` and computes by itself. -/
theorem double_21_short : double 21 = 42 := by
  rfl

/-- `decide` proves a statement that Lean can *decide* by running a check, e.g. a comparison of
numbers or a fact about a finite set of cases. -/
theorem double_21_lt : double 21 < 50 := by
  decide

/-! **Rewriting with an equation: `rw`.** On paper, "since $a = b$, replace $a$ by $b$". In Lean,
for a proof `h : a = b`:

| Lean | What it does |
|---|---|
| `rw [h]` | replaces every `a` in the goal by `b` (left side → right side) |
| `rw [← h]` | the other way: replaces every `b` by `a` (type `←` as `\l`) |
| `rw [h] at h2` | rewrites inside the hypothesis `h2` instead of the goal |
| `rw [h1, h2]` | `rw [h1]`, then `rw [h2]` |

Things to know:
- `rw` uses `h` as a replacement rule; it does not change the goal's own `=`. In
  `⊢ 2 * 21 = 42` above, `rewrite [h]` replaced the piece `2 * 21`, and the goal became `42 = 42`.
- `rw` is `rewrite` followed by an automatic `rfl`: if both sides become identical, `rw` closes
  the goal by itself, and a `rfl` written after it fails with "no goals". `double_21` used
  `rewrite` so that the `42 = 42` step stays visible.
- `rw` matches what is *written*, not what it means. If `a` does not appear literally in the goal,
  it fails with "did not find the pattern". Beware of hidden parentheses: `+` groups to the left,
  so `0 + k + 1` is `(0 + k) + 1` (it contains `0 + k`), while `0 + (k + 1)` does not contain
  `0 + k` (§6 shows how to get from one to the other). -/

/-- Left to right: replace `a` by `b`. -/
example (a b : ℕ) (h : a = b) : a + 1 = b + 1 := by
  -- h : a = b
  -- ⊢ a + 1 = b + 1
  rewrite [h]
  -- every `a` became `b`:
  -- ⊢ b + 1 = b + 1
  rfl
  -- (`rw [h]` alone would have done both lines: rewrite, then `rfl`.)

/-- Right to left, `←`: replace `b` by `a`. -/
example (a b : ℕ) (h1 : a = b) (h2 : a + 1 = 5) : b + 1 = 5 := by
  -- h1 : a = b
  -- h2 : a + 1 = 5
  -- ⊢ b + 1 = 5
  rw [← h1]
  -- every `b` in the goal became `a`:
  -- ⊢ a + 1 = 5
  exact h2

/-- The same, rewriting the hypothesis instead of the goal, `at h2`. -/
example (a b : ℕ) (h1 : a = b) (h2 : a + 1 = 5) : b + 1 = 5 := by
  rw [h1] at h2
  -- every `a` in h2 became `b`:
  -- h2 : b + 1 = 5
  -- ⊢ b + 1 = 5
  exact h2

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
  set_option trace.omega true in
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
"applying $h_{AB}$ to $h_A$" is literally function application: `hAB hA`.

**Reading the statement.** Arrows group to the right: `A → (A → B) → B` is
`A → ((A → B) → B)`, "assume $A$; then assume $A \Rightarrow B$; then $B$". Each `intro` takes
the part of the goal before the first `→` and adds it as a hypothesis.

**The names are ours.** `hA` and `hAB` are labels we choose, as "call it $h_A$" on paper; Lean
does not read them. What a hypothesis stands for comes from the goal, and the Infoview shows it
after the `:` (more on this after the proof). -/

theorem modus_ponens (A B : Prop) : A → (A → B) → B := by
  -- A B : Prop
  -- ⊢ A → (A → B) → B
  intro hA
  -- Before the first `→` is `A`: it becomes a hypothesis, which we name hA.
  -- A B : Prop
  -- hA : A
  -- ⊢ (A → B) → B
  intro hAB
  -- Before the first `→` is now the whole `(A → B)`: it becomes a hypothesis named hAB.
  -- A B : Prop
  -- hA : A
  -- hAB : A → B
  -- ⊢ B
  exact hAB hA
  -- hAB is a function from proofs of A to proofs of B; given hA, it returns a proof of B.

/-! **Opening up `exact hAB hA`.** `exact` hides nothing: `hAB hA` *is* the proof, and `exact`
only checks that its type is the goal `B`. To see the step more slowly, split it in two with
`apply`. On paper: "to prove $B$, by $A \Rightarrow B$ it suffices to prove $A$; and $A$ holds
by $h_A$."

`example` is a `theorem` with no name: Lean checks it, but later proofs cannot use it. We use it
here because `modus_ponens` already exists; this is the same proof, written another way. -/

example (A B : Prop) : A → (A → B) → B := by
  intro hA
  intro hAB
  -- hA : A
  -- hAB : A → B
  -- ⊢ B
  apply hAB
  -- `apply hAB`: hAB gives B once it has a proof of A, so the goal B becomes the goal A
  -- ("it suffices to prove A").
  -- hA : A
  -- hAB : A → B
  -- ⊢ A
  exact hA
  -- `exact hA`: hA is a proof of A; goal closed.

/-! To see the whole proof Lean built, as one term, use `#print`. Hover over it in VS Code: -/

#print modus_ponens
-- theorem Tutorial.L1.modus_ponens : ∀ (A B : Prop), A → (A → B) → B :=
-- fun A B hA hAB ↦ hAB hA

/-! `fun x ↦ t` is the function $x \mapsto t$ (also written `fun x => t`).
Read it as the paper proof: "given $A$, $B$, a proof `hA` of $A$ and a proof `hAB` of
$A \Rightarrow B$, the proof of $B$ is `hAB hA`". Each `intro` became one `fun` argument, and
`exact` gave the body. That is all the tactics did: build this term step by step.

**Why `hAB` is `A → B`.** Not because of its name: because `(A → B)` was the next
assumption in the goal when we wrote `intro hAB`. To see that the name plays no part, swap the
names. The proof still works; only the names now mislead: -/

example (A B : Prop) : A → (A → B) → B := by
  intro hAB
  -- hAB : A          (the name says A → B, the type says A: the type is what counts)
  -- ⊢ (A → B) → B
  intro hA
  -- hAB : A
  -- hA : A → B
  -- ⊢ B
  exact hA hAB

/-! To see what a hypothesis is, read its type in the Infoview (after the `:`), not its name.
Common habits, not rules: `h` for "hypothesis", followed by a hint of what it is about (`hA : A`,
`hAB : A → B`, `hlen` for a fact about lengths); lowercase letters for the variables involved
(`hab : f a = f b`); `ih` for an induction hypothesis (Lean's default name); a leading `_` for a
hypothesis that is named but not used. -/

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
  · unfold double
    rfl
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

example : double (double 3) = 12 := by
  unfold double
  rw[← Nat.mul_assoc]


end Tutorial.L1
