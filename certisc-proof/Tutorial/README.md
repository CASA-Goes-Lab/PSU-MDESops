# Lean tutorial: an automaton and its languages

For readers who know how to write a proof on paper but have not used Lean. Four short lessons
build one example: the textbook machine (Idle, Working, Down), its transition function, the
words it can execute, and its languages $L(G)$ and $L_m(G)$. Each theorem comes twice: first as
math (statement and paper proof), then in Lean, one step per line, with the goal Lean shows after
each step copied into a comment.

| Lesson | File | Math | Lean you learn |
|---|---|---|---|
| 1 | `L1_Basics.lean` | small facts about numbers and logic | `def`, `theorem`, the goal `⊢`, `rfl`, `decide`, `intro`, `use`, `constructor`, `obtain`, `rw`, `cases`, `induction`, `omega`, `simp` |
| 2 | `L2_Automaton.lean` | $G = (X, E, \delta, x_0, X_m)$; facts about $\delta$ | `inductive`, `Option` (partial functions), `structure`, `match`, `change`, `<;>` |
| 3 | `L3_Words.lean` | $\delta^*$; $\delta^*(x, s\,t)$ = read $s$, then $t$; defined words have defined prefixes | `List`, recursive definitions, `calc`, `induction ... generalizing`, `cases h : ...`, `rw ... at h` |
| 4 | `L4_Languages.lean` | $L(G)$, $L_m(G)$; $L_m \subseteq L$; $L$ prefix-closed; $(\mathrm{start\ finish})^n \in L_m$ | sets `{s \| P s}`, `refine`, `∉`, impossible equations |
| | `Solutions.lean` | the exercises at the end of each lesson | `have`, `Option.some.inj`, `Set.Infinite` |

## How to use it

1. Install Lean as in [`../README.md`](../README.md) (elan, then `lake exe cache get` here, in
   `certisc-proof/`).
2. In VS Code, install the `lean4` extension and open the folder `certisc-proof/` (not a parent
   folder: the extension looks for `lakefile.toml` at the top).
3. Open `Tutorial/L1_Basics.lean`. Click on a line inside a proof: the **Infoview** panel (open it
   with the `∀` menu → "Toggle Infoview" if it is not shown) displays the goal at that point. Move
   the cursor down line by line and watch the goal change; that is the whole proof, step by step.
4. Hover over any name (`rw`, `Set.mem_singleton_iff`, `δstar`) to see what it is.
5. For each exercise: copy its statement under the lesson, write `:= by sorry`, then replace
   `sorry` one step at a time. `sorry` means "to be proved"; Lean accepts the file with a warning.
   Compare with `Solutions.lean` afterwards.

Typing symbols: `\to` gives `→`, `\forall` `∀`, `\exists` `∃`, `\and` `∧`, `\or` `∨`, `\ne` `≠`,
`\in` `∈`, `\notin` `∉`, `\sub` `⊆`, `\d` `δ`, `\|-` `⊢`, `\N` `ℕ`, `\<` `⟨`, `\>` `⟩`. Hover over a
symbol to see how to type it.

`lake build` (from `certisc-proof/`) checks the tutorial together with the project, so the
lessons stay correct when Lean or Mathlib is updated.

## When a tactic fails

The error appears under the line, in red, and the Infoview shows the goal it failed on. The
usual reasons, with the lessons where they come up:
- `rw` "did not find the pattern": `rw` matches the text of the goal, not its meaning. Unfold a
  definition first (`rw [L]`, `unfold double`) or restate the goal with `change` (Lesson 4, §2).
- `rfl` "not definitionally equal": the two sides do not compute to the same value, usually
  because of a variable; use arithmetic (`omega`) or the lemmas (Solutions, `length_cycles`).
- A proof that "works" for the wrong statement: Lean checks the proof, not your intent. Read the
  statement in the Infoview (Lesson 1, §5, the `!(!b) = b` trap).

## From the tutorial to the project

The tutorial's automaton is deterministic, with a partial $\delta$ (`Option`). The project's
definitions, in [`../DESopsProof/Automaton.lean`](../DESopsProof/Automaton.lean), are the general
ones the verified Rust code needs: nondeterministic ($f : X \times E \to 2^X$, a set of initial
states), states numbered $0, \dots, n-1$ (`Fin n`), $\delta^*$ called `run`, $L$ and $L_m$
called `gen` / `mkd` (`G.L`, `G.Lm`). The proofs have the same shape: `run_append` there is
Lesson 3's `δstar_append`, and `L_of_append` is Lesson 4's `L_prefix_closed`. That file follows
the same style (math first, then a **Lean:** line), so it is the natural next read.
