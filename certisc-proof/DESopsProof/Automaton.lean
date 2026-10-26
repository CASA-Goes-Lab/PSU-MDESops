import Mathlib.Computability.Language
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union

/-!
# Automata

The definitions of `spec/automaton.md` (§3, §4) and its sanity lemmas.

Each definition and lemma below has its statement in math first, then a **Lean:** line that maps
the math to the Lean names. Proofs get a short **Proof:** sketch in math.

## Notation: math ↔ Lean

| Math | Lean |
|---|---|
| event set $\Sigma$ | type `α` |
| states $X = \{0, \dots, n-1\}$ | type `Fin n` (the general lemmas: any type `σ` with decidable `=`) |
| $S \subseteq X$ (finite) | `S : Finset (Fin n)` |
| $f : X \times \Sigma \to 2^X$ | `f : Fin n → α → Finset (Fin n)`, curried: $f(x, e)$ is `f x e` |
| word $s \in \Sigma^*$ | `s : List α` |
| empty word $\varepsilon$ | `[]` |
| $e \cdot s$ (event $e$, then word $s$) | `e :: s` |
| concatenation $s \cdot t$ | `s ++ t` |
| $s$ is a prefix of $u$ | `s <+: u` (i.e. $\exists t,\ u = s \cdot t$) |
| language $L \subseteq \Sigma^*$ | `L : Language α` (a `Set (List α)`) |
| $L_1 \subseteq L_2$ | `L₁ ≤ L₂` |
| $S \neq \emptyset$ | `S.Nonempty` (i.e. $\exists y,\ y \in S$) |
| $\lvert S \rvert$ | `S.card` |
| $\bigcup_{x \in S} g(x)$ | `S.biUnion g` |
| $X_m \subseteq X$ | `marked : Fin n → Bool`, with $x \in X_m \iff$ `marked x = true` |

## Design note

The successor function `run` and the languages `gen` / `mkd` are defined for any transition
function $f$, not only for an `Automaton`. That lets lemma 6 (unreachable states don't matter)
compare two transition functions $f, f'$ on the same states.
-/

namespace DESopsProof

/- Throughout: `α` is the event type $\Sigma$ and `σ` the state type (`Fin n` for an `Automaton`). -/
variable {α : Type} {σ : Type} [DecidableEq σ]

/-! ## Successor sets -/

/-- One step:
$$\delta_f(S, e) = \bigcup_{x \in S} f(x, e),$$
the states reached from $S$ by the event $e$.

**Lean:** `step f S e = S.biUnion (fun x => f x e)`. -/
def step (f : σ → α → Finset (σ)) (S : Finset (σ)) (e : α) : Finset (σ) :=
  S.biUnion (fun x => f x e)

/-- The extended transition function $f^* : 2^X \times \Sigma^* \to 2^X$, the states reached
from $S$ by the word $s$:
$$f^*(S, \varepsilon) = S, \qquad f^*(S, e \cdot s) = f^*(\delta_f(S, e),\ s).$$

The spec defines it from the right, $f^*(S, s \cdot e) = \delta_f(f^*(S, s), e)$; the two agree
by `run_append` below. Recursion on the head is what Lean's `List` gives directly.

**Lean:** `run f S s` is $f^*(S, s)$; the two equations are `run_nil` and `run_cons`. -/
def run (f : σ → α → Finset (σ)) : Finset (σ) → List α → Finset (σ)
  | S, [] => S
  | S, e :: s => run f (step f S e) s

section run

variable (f : σ → α → Finset (σ))

/-- $f^*(S, \varepsilon) = S$. Holds by definition (`rfl`). -/
@[simp] theorem run_nil (S : Finset (σ)) : run f S [] = S := rfl

/-- $f^*(S, e \cdot s) = f^*(\delta_f(S, e), s)$. Holds by definition (`rfl`). -/
@[simp] theorem run_cons (S : Finset (σ)) (e : α) (s : List α) :
    run f S (e :: s) = run f (step f S e) s := rfl

/-- $y \in \delta_f(S, e) \iff \exists x \in S,\ y \in f(x, e)$.

**Proof:** unfold the union (`simp [step]`). -/
theorem mem_step {S : Finset (σ)} {e : α} {y : σ} :
    y ∈ step f S e ↔ ∃ x ∈ S, y ∈ f x e := by
  simp [step]

/-- $\delta_f(\emptyset, e) = \emptyset$: a union over no states is empty. -/
@[simp] theorem step_empty (e : α) : step f (∅ : Finset (σ)) e = ∅ := by
  simp [step]

/-- $f^*(\emptyset, s) = \emptyset$ for every word $s$.

**Proof:** induction on $s$. Base: $f^*(\emptyset, \varepsilon) = \emptyset$.
Step: $f^*(\emptyset, e \cdot s) = f^*(\delta_f(\emptyset, e), s) = f^*(\emptyset, s) = \emptyset$
by `step_empty` and the induction hypothesis. -/
@[simp] theorem run_empty (s : List α) : run f (∅ : Finset (σ)) s = ∅ := by
  induction s with
  | nil => rfl
  | cons e s ih => simp [ih]

/-- $f^*(S, s \cdot t) = f^*(f^*(S, s),\ t)$: reading $s \cdot t$ is reading $s$, then $t$.

**Proof:** induction on $s$, for every $S$ (`generalizing S`), since the step case changes $S$
to $\delta_f(S, e)$. -/
theorem run_append (S : Finset (σ)) (s t : List α) :
    run f S (s ++ t) = run f (run f S s) t := by
  induction s generalizing S with
  | nil => rfl
  | cons e s ih => simp [ih]

/-- If a word leads somewhere, so does each of its prefixes:
$$f^*(S, s \cdot t) \neq \emptyset \implies f^*(S, s) \neq \emptyset.$$

**Proof:** by contradiction. If $f^*(S, s) = \emptyset$, then
$f^*(S, s \cdot t) = f^*(\emptyset, t) = \emptyset$ (`run_append`, `run_empty`). -/
theorem run_nonempty_of_append {S : Finset (σ)} {s t : List α}
    (h : (run f S (s ++ t)).Nonempty) : (run f S s).Nonempty := by
  rw [run_append] at h
  rw [Finset.nonempty_iff_ne_empty]
  intro hs
  rw [hs, run_empty] at h
  exact Finset.not_nonempty_empty h

end run

/-! ## Active events -/

/-- The events enabled at some state of $S$:
$$\Sigma_f(S) = \{\, e \mid \delta_f(S, e) \neq \emptyset \,\}.$$

**Lean:** `active f S`, a `Set α` (a property of each event). -/
def active (f : σ → α → Finset σ) (S : Finset σ) : Set α :=
  {e | (step f S e).Nonempty}

/-- $e \in \Sigma_f(S) \iff \exists x \in S,\ f(x, e) \neq \emptyset$.

**Proof:** $\delta_f(S, e) \neq \emptyset$ means some $y \in f(x, e)$ with $x \in S$
(`mem_step`), in both directions. -/
theorem mem_active {f : σ → α → Finset σ} {S : Finset σ} {e : α} :
    e ∈ active f S ↔ ∃ x ∈ S, (f x e).Nonempty := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx, hyx⟩ := (mem_step f).1 hy
    exact ⟨x, hx, y, hyx⟩
  · rintro ⟨x, hx, y, hy⟩
    exact ⟨y, (mem_step f).2 ⟨x, hx, hy⟩⟩

/-! ## Languages of a transition structure

For any $f$ and set of initial states $X_0$ (not necessarily a well-formed automaton). -/

/-- Generated language: the words that lead from $X_0$ to some state,
$$L(f, X_0) = \{\, s \in \Sigma^* \mid f^*(X_0, s) \neq \emptyset \,\}.$$

**Lean:** `gen f X0`. -/
def gen (f : σ → α → Finset (σ)) (X0 : Finset (σ)) : Language α :=
  {s | (run f X0 s).Nonempty}

/-- Marked language: the words that lead from $X_0$ to some marked state,
$$L_m(f, X_0, X_m) = \{\, s \in \Sigma^* \mid f^*(X_0, s) \cap X_m \neq \emptyset \,\}.$$

**Lean:** `mkd f X0 m`, with $X_m = \{x \mid$ `m x = true` $\}$; the intersection is written as
$\exists y \in f^*(X_0, s),\ y \in X_m$. -/
def mkd (f : σ → α → Finset (σ)) (X0 : Finset (σ)) (m : σ → Bool) :
    Language α :=
  {s | ∃ y ∈ run f X0 s, m y = true}

/-- Reachable states:
$$Ac(f, X_0) = \bigcup_{s \in \Sigma^*} f^*(X_0, s)
  = \{\, y \mid \exists s,\ y \in f^*(X_0, s) \,\}.$$

**Lean:** `reach f X0`. It is a `Set`, not a `Finset`, because it is defined by a quantifier over
all words. -/
def reach (f : σ → α → Finset (σ)) (X0 : Finset (σ)) : Set (σ) :=
  {y | ∃ s, y ∈ run f X0 s}

/-- $s \in L(f, X_0) \iff f^*(X_0, s) \neq \emptyset$. True by definition (`Iff.rfl`). -/
theorem mem_gen {f : σ → α → Finset (σ)} {X0 : Finset (σ)} {s : List α} :
    s ∈ gen f X0 ↔ (run f X0 s).Nonempty := Iff.rfl

/-- $s \in L_m(f, X_0, X_m) \iff \exists y \in f^*(X_0, s),\ y \in X_m$.
True by definition (`Iff.rfl`). -/
theorem mem_mkd {f : σ → α → Finset (σ)} {X0 : Finset (σ)} {m : σ → Bool}
    {s : List α} : s ∈ mkd f X0 m ↔ ∃ y ∈ run f X0 s, m y = true := Iff.rfl

/-! ## Automaton -/

/-- An automaton
$$G = (n, E, E_{uc}, E_{uo}, f, X_0, X_m)$$
with the well-formedness conditions (W1)–(W3).

| Math | Lean field |
|---|---|
| $n$, states $X = \{0, \dots, n-1\}$ | `n` |
| alphabet $E \subseteq \Sigma$ | `E` |
| uncontrollable $E_{uc}$, unobservable $E_{uo}$ | `Euc`, `Euo` |
| $f : X \times \Sigma \to 2^X$ | `f` |
| $X_0 \subseteq X$ | `X0` |
| $X_m \subseteq X$ | `marked` |
| (W1) $f(x, e) \neq \emptyset \implies e \in E$ | `wf_E` |
| (W2) $E_{uc} \subseteq E$, $E_{uo} \subseteq E$ | `wf_Euc`, `wf_Euo` |
| (W3) $X_0 \neq \emptyset \iff n > 0$ | `wf_X0` |

The `wf_*` fields are proofs: an `Automaton` value cannot be built without proving (W1)–(W3). -/
structure Automaton (α : Type) where
  n : ℕ
  E : Finset α
  Euc : Finset α
  Euo : Finset α
  f : Fin n → α → Finset (Fin n)
  X0 : Finset (Fin n)
  marked : Fin n → Bool
  /-- (W1) Transitions use only alphabet events:
  $\forall x, e:\ f(x, e) \neq \emptyset \implies e \in E$. -/
  wf_E : ∀ x e, (f x e).Nonempty → e ∈ E
  /-- (W2) $E_{uc} \subseteq E$. -/
  wf_Euc : Euc ⊆ E
  /-- (W2) $E_{uo} \subseteq E$. -/
  wf_Euo : Euo ⊆ E
  /-- (W3) There is an initial state iff there are states: $X_0 \neq \emptyset \iff n > 0$. -/
  wf_X0 : X0.Nonempty ↔ 0 < n

namespace Automaton

variable (G : Automaton α)

/-- $L(G) = L(f, X_0)$, the generated language of $G$. -/
def L : Language α := gen G.f G.X0
/-- $L_m(G) = L_m(f, X_0, X_m)$, the marked language of $G$. -/
def Lm : Language α := mkd G.f G.X0 G.marked
/-- $Ac(G) = Ac(f, X_0)$, the reachable states of $G$. -/
def Ac : Set (Fin G.n) := reach G.f G.X0

/-- $G$ is deterministic:
$$\lvert X_0 \rvert \le 1 \quad\text{and}\quad \forall x, e:\ \lvert f(x, e) \rvert \le 1.$$

**Lean:** a conjunction `A ∧ B`; `hG.1` is the first part and `hG.2` the second. -/
def IsDeterministic : Prop :=
  G.X0.card ≤ 1 ∧ ∀ x e, (G.f x e).card ≤ 1

/-! ### Lemma 1: $L(G)$ is prefix-closed -/

/-- $s \cdot t \in L(G) \implies s \in L(G)$.

**Proof:** this is `run_nonempty_of_append` with $S = X_0$. -/
theorem L_of_append {s t : List α} (h : s ++ t ∈ G.L) : s ∈ G.L :=
  run_nonempty_of_append G.f h

/-- $s \text{ prefix of } u,\ u \in L(G) \implies s \in L(G)$.

**Proof:** write $u = s \cdot t$ (destructuring `hsu`) and apply `L_of_append`. -/
theorem L_of_isPrefix {s u : List α} (hsu : s <+: u) (hu : u ∈ G.L) : s ∈ G.L := by
  obtain ⟨t, rfl⟩ := hsu
  exact G.L_of_append hu

/-! ### Lemma 2: $L_m(G) \subseteq L(G)$ -/

/-- $L_m(G) \subseteq L(G)$ (written `≤` on `Language`).

**Proof:** if $y \in f^*(X_0, s) \cap X_m$, then $y \in f^*(X_0, s)$,
so $f^*(X_0, s) \neq \emptyset$. -/
theorem Lm_le_L : G.Lm ≤ G.L := by
  intro s hs
  obtain ⟨y, hy, -⟩ := mem_mkd.1 hs
  exact ⟨y, hy⟩

/-! ### Lemma 3: $L(G) = \emptyset \iff n = 0$, and $\varepsilon \in L(G) \iff n > 0$ (by W3) -/

/-- $\varepsilon \in L(G) \iff n > 0$.

**Proof:** $\varepsilon \in L(G) \iff f^*(X_0, \varepsilon) = X_0 \neq \emptyset$, which is (W3). -/
theorem nil_mem_L : [] ∈ G.L ↔ 0 < G.n := G.wf_X0

/-- $L(G) = \emptyset \iff n = 0$, stated as $(\forall s,\ s \notin L(G)) \iff n = 0$.

**Proof.** ($\Rightarrow$) If $n \neq 0$ then $\varepsilon \in L(G)$ by `nil_mem_L`, a contradiction.
($\Leftarrow$) If $s \in L(G)$ there is a state $y \in f^*(X_0, s)$, so $y < n = 0$: impossible
(`omega` closes the arithmetic). -/
theorem L_empty_iff : (∀ s, s ∉ G.L) ↔ G.n = 0 := by
  constructor
  · intro h
    by_contra hn
    exact h [] (G.nil_mem_L.2 (Nat.pos_of_ne_zero hn))
  · intro hn s hs
    obtain ⟨y, -⟩ := mem_gen.1 hs
    have := y.isLt
    omega

/-! ### Lemma 4: $L(G) \subseteq E^*$ (by W1) -/

/-- For any start set $S$: if $f^*(S, s) \neq \emptyset$ then every event of $s$ is in $E$.

**Proof:** induction on $s$, for every $S$. Let $s = a \cdot s'$ and $e$ an event of $s$.
- If $e = a$: $\delta_f(S, e) \neq \emptyset$ (otherwise $f^*(S, s) = f^*(\emptyset, s') = \emptyset$),
  so some $y \in f(x, e)$ with $x \in S$; then $e \in E$ by (W1).
- If $e$ is in $s'$: the induction hypothesis with start set $\delta_f(S, a)$. -/
theorem mem_E_of_run_nonempty :
    ∀ (S : Finset (Fin G.n)) (s : List α), (run G.f S s).Nonempty → ∀ e ∈ s, e ∈ G.E := by
  intro S s
  induction s generalizing S with
  | nil => intro _ e he; simp at he
  | cons a s ih =>
    intro h e he
    rw [run_cons] at h
    rcases List.mem_cons.1 he with rfl | he'
    · have hstep : (step G.f S e).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h0
        rw [h0, run_empty] at h
        exact Finset.not_nonempty_empty h
      obtain ⟨y, hy⟩ := hstep
      obtain ⟨x, -, hyx⟩ := (mem_step G.f).1 hy
      exact G.wf_E x e ⟨y, hyx⟩
    · exact ih _ h e he'

/-- $s \in L(G) \implies \forall e \in s,\ e \in E$, i.e. $L(G) \subseteq E^*$.

**Proof:** `mem_E_of_run_nonempty` with $S = X_0$. -/
theorem mem_E_of_mem_L {s : List α} (hs : s ∈ G.L) : ∀ e ∈ s, e ∈ G.E :=
  G.mem_E_of_run_nonempty _ _ hs

/-- The active events of any set of states are events of $G$: $\Sigma_f(S) \subseteq E$.

**Proof:** an active event has some $f(x, e) \neq \emptyset$ (`mem_active`), so $e \in E$ by (W1). -/
theorem active_subset_E (S : Finset (Fin G.n)) : active G.f S ⊆ (G.E : Set α) := by
  intro e he
  obtain ⟨x, -, hne⟩ := mem_active.1 he
  exact Finset.mem_coe.2 (G.wf_E x e hne)

/-! ### Lemma 5: a deterministic automaton is in at most one state -/

/-- $\lvert S \rvert \le 1$ and $\forall x,\ \lvert f(x, e) \rvert \le 1 \implies
\lvert \delta_f(S, e) \rvert \le 1$.

**Proof:** take $a, b \in \delta_f(S, e)$, say $a \in f(x, e)$ and $b \in f(x', e)$ with
$x, x' \in S$. Since $\lvert S \rvert \le 1$, $x = x'$; since $\lvert f(x, e) \rvert \le 1$, $a = b$.
(`Finset.card_le_one`: $\lvert S \rvert \le 1 \iff$ any two elements of $S$ are equal.) -/
theorem card_step_le_one (f : σ → α → Finset (σ)) {S : Finset (σ)} {e : α}
    (hS : S.card ≤ 1) (hf : ∀ x, (f x e).card ≤ 1) : (step f S e).card ≤ 1 := by
  rw [Finset.card_le_one] at hS ⊢
  intro a ha b hb
  obtain ⟨x, hx, hax⟩ := (mem_step f).1 ha
  obtain ⟨x', hx', hbx'⟩ := (mem_step f).1 hb
  obtain rfl := hS x hx x' hx'
  exact Finset.card_le_one.1 (hf x) a hax b hbx'

/-- If $\lvert f(x, e) \rvert \le 1$ for all $x, e$, then for all $S$, $s$:
$\lvert S \rvert \le 1 \implies \lvert f^*(S, s) \rvert \le 1$.

**Proof:** induction on $s$, for every $S$, applying `card_step_le_one` at each step. -/
theorem card_run_le_one (f : σ → α → Finset (σ)) (hf : ∀ x e, (f x e).card ≤ 1) :
    ∀ (S : Finset (σ)) (s : List α), S.card ≤ 1 → (run f S s).card ≤ 1 := by
  intro S s
  induction s generalizing S with
  | nil => exact id
  | cons e s ih => exact fun hS => ih _ (card_step_le_one f hS (fun x => hf x e))

/-- $G$ deterministic $\implies \forall s,\ \lvert f^*(X_0, s) \rvert \le 1$.

**Proof:** `card_run_le_one` with $S = X_0$; `hG.1` is $\lvert X_0 \rvert \le 1$ and `hG.2` is
$\lvert f(x, e) \rvert \le 1$. -/
theorem IsDeterministic.card_run_le_one {G : Automaton α} (hG : G.IsDeterministic)
    (s : List α) : (run G.f G.X0 s).card ≤ 1 :=
  DESopsProof.Automaton.card_run_le_one G.f hG.2 _ s hG.1

/-! ### Lemma 6: only reachable states matter

Changing the transitions or the marking of unreachable states leaves $L$ and $L_m$ unchanged.
Stated for any $f'$ and $m'$ that agree with $G$ on $Ac(G)$, so no renumbering is involved.
A version that removes and renumbers states is deferred to the operation that does it (trim).
-/

/-- If $f'(x, e) = f(x, e)$ for every $x \in Ac(f, X_0)$ and every $e$, then
$f'^*(X_0, s) = f^*(X_0, s)$ for every $s$.

**Proof:** induction on $s$ from the right ($s \cdot e$, `List.reverseRecOn`), so that the start
set stays $X_0$. Step:
$$f'^*(X_0, s \cdot e) = \bigcup_{x \in f'^*(X_0, s)} f'(x, e)
  \overset{\text{IH}}{=} \bigcup_{x \in f^*(X_0, s)} f'(x, e)
  = \bigcup_{x \in f^*(X_0, s)} f(x, e) = f^*(X_0, s \cdot e),$$
where the third equality holds because every $x \in f^*(X_0, s)$ is reachable (by the word $s$).
`Finset.biUnion_congr` is "equal index sets and equal terms give equal unions". -/
theorem run_congr_reach {f f' : σ → α → Finset (σ)} {X0 : Finset (σ)}
    (hf : ∀ x ∈ reach f X0, ∀ e, f' x e = f x e) (s : List α) :
    run f' X0 s = run f X0 s := by
  induction s using List.reverseRecOn with
  | nil => rfl
  | append_singleton s e ih =>
    rw [run_append, run_append, ih]
    simp only [run_cons, run_nil, step]
    exact Finset.biUnion_congr rfl (fun x hx => hf x ⟨s, hx⟩ e)

/-- If $f'$ agrees with $f$ on $Ac(G)$, then $L(f', X_0) = L(G)$.

**Proof:** rewrite $f'^*$ to $f^*$ inside the definition of $L$ (`run_congr_reach`). -/
theorem L_congr_Ac (f' : Fin G.n → α → Finset (Fin G.n))
    (hf : ∀ x ∈ G.Ac, ∀ e, f' x e = G.f x e) : gen f' G.X0 = G.L := by
  unfold L gen
  simp_rw [run_congr_reach hf]
  rfl

/-- If $f'$ agrees with $f$ on $Ac(G)$ and $X_m'$ agrees with $X_m$ on $Ac(G)$, then
$L_m(f', X_0, X_m') = L_m(G)$.

**Proof:** rewrite $f'^*$ to $f^*$ (`run_congr_reach`). Then for each $s$, a witness
$y \in f^*(X_0, s)$ is reachable, so $y \in X_m' \iff y \in X_m$; this gives both directions. -/
theorem Lm_congr_Ac (f' : Fin G.n → α → Finset (Fin G.n)) (m' : Fin G.n → Bool)
    (hf : ∀ x ∈ G.Ac, ∀ e, f' x e = G.f x e) (hm : ∀ x ∈ G.Ac, m' x = G.marked x) :
    mkd f' G.X0 m' = G.Lm := by
  unfold Lm mkd
  simp_rw [run_congr_reach hf]
  ext s
  constructor
  · rintro ⟨y, hy, hmy⟩
    exact ⟨y, hy, (hm y ⟨s, hy⟩) ▸ hmy⟩
  · rintro ⟨y, hy, hmy⟩
    exact ⟨y, hy, (hm y ⟨s, hy⟩).symm ▸ hmy⟩

end Automaton

end DESopsProof
