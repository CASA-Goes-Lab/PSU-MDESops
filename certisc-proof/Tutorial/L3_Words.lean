import Tutorial.L2_Automaton

/-!
# Lesson 3: words and the extended transition function $\delta^*$

**Math.** A *word* (or string) over $E$ is a finite sequence of events,
$s = e_1 e_2 \cdots e_k$; $\varepsilon$ is the empty word, and $E^*$ the set of all words. The
extended transition function $\delta^* : X \times E^* \rightharpoonup X$ follows a word, one
event at a time:
$$\delta^*(x, \varepsilon) = x, \qquad
  \delta^*(x, e\,s) = \begin{cases} \delta^*(y, s) & \text{if } \delta(x, e) = y \\
                                    \text{undefined} & \text{if } \delta(x, e) \text{ undefined.}
                      \end{cases}$$

(Textbooks often define it from the other end, $\delta^*(x, s\,e) = \delta(\delta^*(x, s), e)$.
Both give the same function; reading from the front matches how Lean builds lists. The project's
`DESopsProof/Automaton.lean` makes the same choice and proves the other form as a lemma.)

New Lean in this lesson: `List` (words), recursive definitions, `induction ... generalizing`,
`cases h : ...` (cases on a value, remembering which case we are in), `simp only`.

| Math | Lean |
|---|---|
| word $s \in E^*$ | `s : List E` |
| $\varepsilon$ | `[]` |
| $e\,s$ (event $e$, then the word $s$) | `e :: s` |
| $e_1 e_2 e_3$ | `[e₁, e₂, e₃]` (short for `e₁ :: e₂ :: e₃ :: []`) |
| $s\,t$ (concatenation) | `s ++ t` |
-/

namespace Tutorial.L3

open Tutorial.L2 Tutorial.L2.State Tutorial.L2.Event

variable {X E : Type}

/-! ## 1. The definition

A recursive definition, by cases on the word: the two lines are the two equations above. In the
second line, `match G.δ x e with` is the case split "is $\delta(x, e)$ defined?". Lean accepts
the recursion because the word gets shorter (`s` is shorter than `e :: s`). -/

/-- $\delta^*(x, s)$, for any automaton `G`. -/
def δstar (G : Automaton X E) : X → List E → Option X
  | x, [] => some x
  | x, e :: s =>
    match G.δ x e with
    | none => none
    | some y => δstar G y s

/-! ## 2. Computing with it -/

#eval δstar G Idle [start, finish]              -- some Idle
#eval δstar G Idle [start, breakdown, repair]   -- some Idle
#eval δstar G Idle [start, breakdown, finish]   -- none (finish is impossible in Down)

/-! **Math.** $\delta^*(\mathrm{Idle}, \mathrm{start}\ \mathrm{finish}) = \mathrm{Idle}$.
*Proof (step by step, by the definition):*
$$\delta^*(\mathrm{Idle}, \mathrm{start}\ \mathrm{finish})
  = \delta^*(\mathrm{Working}, \mathrm{finish})
  = \delta^*(\mathrm{Idle}, \varepsilon) = \mathrm{Idle}. \;∎$$

In Lean, `rfl` does all three steps at once: it computes both sides. -/

theorem start_finish : δstar G Idle [start, finish] = some Idle := by
  rfl

/-- The same proof, with each step of the calculation written out. `calc` is Lean's version of a
chain of equalities on paper; each step is justified by `rfl` (by definition). -/
example : δstar G Idle [start, finish] = some Idle := by
  calc δstar G Idle [start, finish]
      = δstar G Working [finish] := rfl
    _ = δstar G Idle [] := rfl
    _ = some Idle := rfl

/-! ## 3. The two defining equations, as theorems

It helps to have the definition as named equations we can rewrite with. Both hold by
definition (`rfl`). -/

/-- $\delta^*(x, \varepsilon) = x$. -/
theorem δstar_nil (G : Automaton X E) (x : X) : δstar G x [] = some x := rfl

/-- If $\delta(x, e) = y$, then $\delta^*(x, e\,s) = \delta^*(y, s)$. -/
theorem δstar_cons_some (G : Automaton X E) {x y : X} {e : E} (h : G.δ x e = some y)
    (s : List E) : δstar G x (e :: s) = δstar G y s := by
  -- h : G.δ x e = some y
  -- ⊢ δstar G x (e :: s) = δstar G y s
  simp only [δstar, h]
  -- `simp only [δstar, h]` unfolds `δstar` once and rewrites `G.δ x e` to `some y` with `h`;
  -- the `match` then picks its `some y` line, and both sides are equal.

/-- If $\delta(x, e)$ is undefined, so is $\delta^*(x, e\,s)$. -/
theorem δstar_cons_none (G : Automaton X E) {x : X} {e : E} (h : G.δ x e = none)
    (s : List E) : δstar G x (e :: s) = none := by
  simp only [δstar, h]

/-! ## 4. The main lemma: reading $s\,t$ is reading $s$, then $t$

**Math.** For all $x$, $s$, $t$:
$$\delta^*(x, s\,t) = \begin{cases} \delta^*(y, t) & \text{if } \delta^*(x, s) = y \\
                                   \text{undefined} & \text{if } \delta^*(x, s) \text{ undefined.}
                     \end{cases}$$

*Proof:* by induction on $s$, **for every $x$** (the step changes the state, so the
induction hypothesis must hold for all states, not only for the $x$ we started with).
- Base, $s = \varepsilon$: $\delta^*(x, \varepsilon\,t) = \delta^*(x, t)$, and
  $\delta^*(x, \varepsilon) = x$, so the right side is $\delta^*(x, t)$ too.
- Step, $s = e\,s'$. IH: for every $x'$, the claim holds for $s'$. Then
  $(e\,s')\,t = e\,(s'\,t)$. Cases on $\delta(x, e)$:
  - undefined: $\delta^*(x, e\,(s'\,t))$ and $\delta^*(x, e\,s')$ are both undefined, so both
    sides are undefined.
  - $= y$: $\delta^*(x, e\,(s'\,t)) = \delta^*(y, s'\,t)$ and
    $\delta^*(x, e\,s') = \delta^*(y, s')$, so the claim is the IH at $x' = y$. ∎

**Lean.** "if $\delta^*(x, s) = y$ then ..., if undefined then undefined" is `Option.bind`:
`o.bind f` is `f y` when `o = some y`, and `none` when `o = none`. So the statement is
`δstar G x (s ++ t) = (δstar G x s).bind (fun y => δstar G y t)`, where `fun y => ...` is the
function $y \mapsto \delta^*(y, t)$. -/

theorem δstar_append (G : Automaton X E) (s t : List E) (x : X) :
    δstar G x (s ++ t) = (δstar G x s).bind (fun y => δstar G y t) := by
  induction s generalizing x with
  | nil =>
    -- Base case.
    -- x : X
    -- ⊢ δstar G x ([] ++ t) = (δstar G x []).bind fun y => δstar G y t
    rw [List.nil_append, δstar_nil, Option.bind_some]
    -- `List.nil_append`: [] ++ t = t.   `δstar_nil`: δ*(x, ε) = x.
    -- `Option.bind_some`: (some x).bind f = f x.  After these, both sides are δ*(x, t).
  | cons e s' ih =>
    -- Step. The IH holds for every state x (that is what `generalizing x` gave us):
    -- ih : ∀ (x : X), δstar G x (s' ++ t) = (δstar G x s').bind fun y => δstar G y t
    -- x : X
    -- ⊢ δstar G x (e :: s' ++ t) = (δstar G x (e :: s')).bind fun y => δstar G y t
    rw [List.cons_append]
    -- (e s') t = e (s' t):
    -- ⊢ δstar G x (e :: (s' ++ t)) = (δstar G x (e :: s')).bind fun y => δstar G y t
    cases h : G.δ x e with
    -- Cases on δ(x, e); `h` records which case we are in.
    | none =>
      -- h : G.δ x e = none
      rw [δstar_cons_none G h, δstar_cons_none G h, Option.bind_none]
      -- Both sides became `none`.
    | some y =>
      -- h : G.δ x e = some y
      rw [δstar_cons_some G h, δstar_cons_some G h]
      -- ⊢ δstar G y (s' ++ t) = (δstar G y s').bind fun y => δstar G y t
      exact ih y
      -- This is the IH at the state y.

/-! ## 5. A consequence: a defined word has defined prefixes

**Math.** If $\delta^*(x, s\,t)$ is defined, so is $\delta^*(x, s)$.
*Proof:* by contradiction. If $\delta^*(x, s)$ were undefined, then by the main lemma
$\delta^*(x, s\,t)$ would be undefined too. ∎

In Lean, "is defined" is `≠ none`. A proof of `a ≠ b` is a proof of `a = b → False`: assume the
equation (`intro`), and reach a contradiction. -/

theorem δstar_prefix (G : Automaton X E) {x : X} {s t : List E}
    (h : δstar G x (s ++ t) ≠ none) : δstar G x s ≠ none := by
  -- h : δstar G x (s ++ t) ≠ none
  -- ⊢ δstar G x s ≠ none
  intro hs
  -- Assume δ*(x, s) is undefined:
  -- hs : δstar G x s = none
  -- ⊢ False
  rw [δstar_append, hs, Option.bind_none] at h
  -- `rw ... at h` rewrites the hypothesis h instead of the goal. Now:
  -- h : none ≠ none
  -- ⊢ False
  exact h rfl
  -- h says "none = none is false"; `rfl` proves none = none: contradiction.

/-! ## Exercises (solutions in `Solutions.lean`)

1. `δstar G Down [repair, start] = some Working`, with `rfl`, then again with a `calc` chain.
2. `δstar G Idle [start, breakdown, finish] = none`.
3. For every word `s`: `δstar G x (s ++ []) = δstar G x s`. (Hint: `List.append_nil`.)
4. If `δstar G x s = some y` then `δstar G x (s ++ t) = δstar G y t`. (Hint: `δstar_append`,
   then rewrite with the hypothesis, then `Option.bind_some`.)
-/

end Tutorial.L3
