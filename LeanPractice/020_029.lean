/-!
PRACTICE 020 — Rules can also come in a pair
-/
theorem practice020 (P Q R : Prop) : (P → Q) ∧ (Q → R) → P → R := by
  intro hpqqr
  intro hp
  exact hpqqr.right (hpqqr.left hp)

/-!
PRACTICE 021 — Work backward through three rules
-/
theorem practice021 (P Q R S : Prop) : (P → Q) → (Q → R) → (R → S) → P → S := by
  intro hpq
  intro hqr
  intro hrs
  intro hp
  exact hrs (hqr (hpq hp))

/-!
PRACTICE 022 — Use an input both directly and indirectly
-/
theorem practice022 (P Q R : Prop) : (P → Q → R) → (P → Q) → P → R := by
  intro hpqr
  intro hpq
  intro hp
  exact hpqr hp (hpq hp)

/-!
PRACTICE 023 — Rearrange four pieces of evidence
-/
theorem practice023 (P Q R S : Prop) : (P ∧ Q) ∧ (R ∧ S) → (P ∧ R) ∧ (Q ∧ S) := by
  intro hpqrs
  exact ⟨⟨hpqrs.left.left, hpqrs.right.left⟩, ⟨hpqrs.left.right, hpqrs.right.right⟩⟩

/-!
PRACTICE 024 — Prove an OR from its left side
-/
theorem practice024 (P Q : Prop) : P → P ∨ Q := by
  intro hp
  left
  exact hp

/-!
PRACTICE 025 — Prove an OR from its right side
-/
theorem practice025 (P Q : Prop) : Q → P ∨ Q := by
  intro hq
  right
  exact hq

/-!
PRACTICE 026 — Swap an OR
-/
theorem practice026 (P Q : Prop) : P ∨ Q → Q ∨ P := by
  intro h
  cases h with
  | inl hA =>
    right
    exact hA
  | inr hB =>
    left
    exact hB

/-!
PRACTICE 027 — Reach the same conclusion from either case
-/
theorem practice027 (P Q R : Prop) : (P → R) → (Q → R) → P ∨ Q → R := by
  intro hpr
  intro hqr
  intro hpq

  cases hpq with
  | inl hP =>
    exact hpr hP
  | inr hQ =>
    exact hqr hQ

/-!
PRACTICE 028 — Collapse a repeated alternative
-/
theorem practice028 (P : Prop) : P ∨ P → P := by
  intro hpp
  cases hpp with
  | inl hP =>
    exact hP
  | inr hP =>
    exact hP

/-!
PRACTICE 029 — Use stronger evidence to prove an alternative
-/
theorem practice029 (P Q : Prop) : P ∧ Q → P ∨ Q := by
  intro hpq
  left
  exact hpq.left
