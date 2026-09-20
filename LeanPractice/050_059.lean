/-!
PRACTICE 050 — Chain two equivalences
-/
theorem practice050 (P Q R : Prop) : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro hpq
  intro hqr
  constructor
  · intro hp
    exact hqr.mp (hpq.mp hp)
  · intro hr
    exact hpq.mpr (hqr.mpr hr)

/-!
PRACTICE 051 — AND is commutative in both directions
-/
theorem practice051 (P Q : Prop) : (P ∧ Q) ↔ (Q ∧ P) := by
  constructor
  · intro mp
    exact mp.symm
  · intro mpr
    exact mpr.symm


/-!
PRACTICE 052 — OR is commutative in both directions
-/
theorem practice052 (P Q : Prop) : (P ∨ Q) ↔ (Q ∨ P) := by
  constructor
  · intro mp
    exact mp.symm
  · intro mpr
    exact mpr.symm

/-!
PRACTICE 053 — Separate inputs or one paired input
-/
theorem practice053 (P Q R : Prop) : (P → Q → R) ↔ (P ∧ Q → R) := by
  constructor
  · intro mp
    intro h
    exact mp h.left h.right
  · intro mpr
    intro hp
    intro hq
    exact mpr ⟨hp, hq⟩

/-!
PRACTICE 054 — An AND with True
-/
theorem practice054 (P : Prop) : (P ∧ True) ↔ P := by
  constructor
  · intro mp
    exact mp.left
  · intro mpr
    exact ⟨mpr, True.intro⟩

/-!
PRACTICE 055 — An OR with False
-/
theorem practice055 (P : Prop) : (P ∨ False) ↔ P := by
  constructor
  · intro mp
    cases mp with
    | inl hp =>
      exact hp
    | inr hf =>
      exact hf.elim
  · intro mpr
    left
    exact mpr

/-!
PRACTICE 056 — One rule with two outputs or two separate rules
-/
theorem practice056 (P Q R : Prop) : (P → Q ∧ R) ↔ ((P → Q) ∧ (P → R)) := by
  constructor
  · intro mp
    constructor
    · intro hp
      exact (mp hp).left
    · intro hp
      exact (mp hp).right
  · intro mpr
    intro hp
    exact ⟨mpr.left hp, mpr.right hp⟩

/-!
PRACTICE 057 — A De Morgan equivalence
-/
theorem practice057 (P Q : Prop) : ¬(P ∨ Q) ↔ (¬P ∧ ¬Q) := by
  constructor
  · intro mp
    constructor
    · intro hl
      apply mp
      left
      exact hl
    · intro hr
      apply mp
      right
      exact hr
  · intro mpr
    intro c
    cases c with
    | inl hl =>
      exact mpr.left hl
    | inr hr =>
      exact mpr.right hr

/-!
PRACTICE 058 — Split on whether a proposition holds
-/
theorem practice058 (P : Prop) : P ∨ ¬P := by
  by_cases h: P
  · left
    exact h
  · right
    exact h

/-!
PRACTICE 059 — Remove double negation classically
-/
theorem practice059 (P : Prop) : ¬¬P → P := by
  intro hnnp
  by_cases h: P
  · exact h
  · exact (hnnp h).elim
