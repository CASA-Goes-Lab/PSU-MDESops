import Mathlib.Data.Set.Insert
import Tutorial.L1_Basics

/-!
# Lesson 2: a first automaton

**Math.** A deterministic automaton is a tuple
$$G = (X, E, \delta, x_0, X_m)$$
- $X$: the states;
- $E$: the events (the alphabet; textbooks write $\Sigma$, but `Σ` means something else in
  Lean);
- $\delta : X \times E \rightharpoonup X$: the transition function, a **partial** function
  ($\delta(x, e)$ may be undefined: event $e$ cannot happen in state $x$);
- $x_0 \in X$: the initial state;
- $X_m \subseteq X$: the marked states (a task is complete).

Our running example is the machine of the textbook (Cassandras & Lafortune), also in
`Examples/v2/testing/certisc/models/M1.json`:

            start             breakdown
    Idle ---------> Working -----------> Down
     ^  <---------           <---------   |
     |     finish      (no edge back)     |
     +------------------------------------+
                        repair

$X = \{\mathrm{Idle}, \mathrm{Working}, \mathrm{Down}\}$,
$E = \{\mathrm{start}, \mathrm{finish}, \mathrm{breakdown}, \mathrm{repair}\}$,
$x_0 = \mathrm{Idle}$, $X_m = \{\mathrm{Idle}\}$, and
$\delta(\mathrm{Idle}, \mathrm{start}) = \mathrm{Working}$,
$\delta(\mathrm{Working}, \mathrm{finish}) = \mathrm{Idle}$,
$\delta(\mathrm{Working}, \mathrm{breakdown}) = \mathrm{Down}$,
$\delta(\mathrm{Down}, \mathrm{repair}) = \mathrm{Idle}$, undefined otherwise.

New Lean in this lesson: `inductive` (a finite set of named values), `Option` (partial
functions), `structure` (a tuple with named fields), `match` (definition by cases), `<;>`.
-/

namespace Tutorial.L2

/-! ## 1. States and events: `inductive`

A finite set whose elements we name is an `inductive` type: the values listed are all the values
of the type, and they are all different. (On paper we would just write the set.) The
`deriving` line asks Lean to build, for us, an equality test (`DecidableEq`), so `decide` can
compare states, and a way to print values (`Repr`), so `#eval` can show them. -/

inductive State where
  | Idle
  | Working
  | Down
  deriving DecidableEq, Repr

inductive Event where
  | start
  | finish
  | breakdown
  | repair
  deriving DecidableEq, Repr

-- `open` lets us write `Idle` instead of `State.Idle`, and `start` instead of `Event.start`.
open State Event

/-! "All different" and "nothing else" are theorems Lean gives for free; `decide` checks them by
looking at the finitely many cases. -/

example : Idle ≠ Working := by decide

/-- Every state is one of the three: proof by cases on `x`. -/
example (x : State) : x = Idle ∨ x = Working ∨ x = Down := by
  cases x with
  | Idle => left; rfl
  | Working => right; left; rfl
  | Down => right; right; rfl

/-! ## 2. Partial functions: `Option`

Lean functions are total: they give a value for every input. A partial function
$X \rightharpoonup Y$ becomes a total function $X \to$ `Option Y`, where `Option Y` has the
values `some y` (defined, with value $y$) and `none` (undefined). So:

| Math | Lean |
|---|---|
| $\delta(x, e) = y$ | `δ x e = some y` |
| $\delta(x, e)$ undefined | `δ x e = none` |
| $\delta(x, e)$ defined, written $\delta(x, e)!$ | `δ x e ≠ none` |

Lean writes function application without parentheses, curried: $\delta(x, e)$ is `δ x e`. -/

/-! ## 3. The tuple $G$: `structure`

A `structure` is a tuple with named fields. The automaton definition, for any types of states
`X` and events `E`: -/

structure Automaton (X E : Type) where
  /-- $\delta : X \times E \rightharpoonup X$. -/
  δ : X → E → Option X
  /-- $x_0$. -/
  x0 : X
  /-- $X_m \subseteq X$, as a set of states. -/
  Xm : Set X

/-! The sets $X$ and $E$ are the types `X` and `E`, so they are *parameters* of the structure,
not fields. A field is read with a dot: for `G : Automaton X E`, `G.δ`, `G.x0` and `G.Xm` are
$\delta$, $x_0$ and $X_m$.

## 4. The machine

The transition function, by cases on the pair (state, event). `match` tries the lines from top
to bottom; the last line `_, _` ("anything else") makes $\delta$ undefined everywhere else. -/

def δ : State → Event → Option State
  | Idle, start => some Working
  | Working, finish => some Idle
  | Working, breakdown => some Down
  | Down, repair => some Idle
  | _, _ => none

/-- The machine $G = (X, E, \delta, \mathrm{Idle}, \{\mathrm{Idle}\})$. -/
def G : Automaton State Event where
  δ := δ
  x0 := Idle
  Xm := {Idle}

#eval G.δ Idle start          -- some (Tutorial.L2.State.Working)
#eval G.δ Idle finish         -- none

/-! ## 5. First facts about $G$

**Math.** $\delta(\mathrm{Idle}, \mathrm{finish})$ is undefined.
*Proof:* by the definition of $\delta$ (no line matches, so the last one does). ∎ -/

theorem δ_Idle_finish : G.δ Idle finish = none := by
  -- ⊢ G.δ Idle finish = none
  rfl

/-- **Math.** $\mathrm{Idle} \in X_m$. *Proof:* $X_m = \{\mathrm{Idle}\}$. ∎

`Set.mem_singleton_iff` is the library fact $a \in \{b\} \iff a = b$. -/
theorem Idle_marked : Idle ∈ G.Xm := by
  -- ⊢ Idle ∈ G.Xm
  change Idle ∈ ({Idle} : Set State)
  -- `change` replaces the goal by one equal to it by definition: here we unfold `G.Xm`.
  -- ⊢ Idle ∈ {Idle}
  rw [Set.mem_singleton_iff]

/-! **Math.** In state Down, only repair is possible:
$$\forall e \in E,\quad \delta(\mathrm{Down}, e) \text{ defined} \iff e = \mathrm{repair}.$$
*Proof:* let $e \in E$; by cases on $e$ (four of them).
- $e = \mathrm{start}$: $\delta(\mathrm{Down}, \mathrm{start})$ is undefined and
  $\mathrm{start} \neq \mathrm{repair}$: both sides false.
- $e = \mathrm{finish}$, $e = \mathrm{breakdown}$: the same.
- $e = \mathrm{repair}$: $\delta(\mathrm{Down}, \mathrm{repair}) = \mathrm{Idle}$ is defined,
  and $\mathrm{repair} = \mathrm{repair}$: both sides true. ∎

Each case is a finite check, so `decide` does it. -/

theorem Down_only_repair (e : Event) : G.δ Down e ≠ none ↔ e = repair := by
  -- e : Event
  -- ⊢ G.δ Down e ≠ none ↔ e = repair
  cases e with
  | start =>
    -- ⊢ G.δ Down start ≠ none ↔ start = repair
    decide
  | finish => decide
  | breakdown => decide
  | repair =>
    -- ⊢ G.δ Down repair ≠ none ↔ repair = repair
    decide

/-- The same proof, shorter: `t1 <;> t2` runs `t1`, then `t2` on *every* goal `t1` produced.
Here: split into the four cases, then `decide` each. -/
example (e : Event) : G.δ Down e ≠ none ↔ e = repair := by
  cases e <;> decide

/-! **Math.** Every state has some event defined ($G$ never gets stuck):
$$\forall x \in X,\ \exists e \in E,\ \delta(x, e) \text{ defined}.$$
*Proof:* by cases on $x$, giving the event each time: start for Idle, finish for Working,
repair for Down. ∎ -/

theorem not_stuck (x : State) : ∃ e, G.δ x e ≠ none := by
  cases x with
  | Idle =>
    -- ⊢ ∃ e, G.δ Idle e ≠ none
    use start
    -- ⊢ G.δ Idle start ≠ none
    decide
  | Working =>
    use finish
    decide
  | Down =>
    use repair
    decide

/-! ## Exercises (solutions in `Solutions.lean`)

1. `G.δ Working breakdown = some Down`.
2. `Working ∉ G.Xm`. (Hint: `x ∉ S` means `x ∈ S → False`; start with `intro h`, then turn `h`
   into `Working = Idle` and finish with `cases` on that equation, or `simp` at it.)
3. In state Idle, only start is possible (like `Down_only_repair`).
-/

end Tutorial.L2
