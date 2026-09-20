/-!
PRACTICE 010 — Keep your evidence and derive something new
-/
theorem practice010 (P Q : Prop) : (P → Q) → P → P ∧ Q := by
  intro hPQ
  intro hP
  constructor
  · exact hP
  · exact hPQ hP

/-!
PRACTICE 011 — Transform both sides
-/
theorem practice011 (P Q R S : Prop) : (P → R) → (Q → S) → (P ∧ Q) → R ∧ S := by
  intro hPR
  intro hQS
  intro hPQ
  constructor
  · exact hPR hPQ.left
  · exact hQS hPQ.right

/-!
PRACTICE 012 — Look inside a nested AND
-/
theorem practice012 (P Q R : Prop) : P ∧ (Q ∧ R) → Q := by
  intro hPQR
  exact (hPQR.right).left

/-!
PRACTICE 013 — Move the parentheses to the right
-/
theorem practice013 (P Q R : Prop) : (P ∧ Q) ∧ R → P ∧ (Q ∧ R) := by
  intro h
  exact ⟨h.left.left, ⟨h.left.right, h.right⟩⟩

/-!
PRACTICE 014 — Move the parentheses to the left
-/
theorem practice014 (P Q R : Prop) : P ∧ (Q ∧ R) → (P ∧ Q) ∧ R := by
  intro h
  exact ⟨⟨h.left, h.right.left⟩, h.right.right⟩

/-!
PRACTICE 015 — Use one proof twice in a pair
-/
theorem practice015 (P : Prop) : P → P ∧ P := by
  intro h
  exact ⟨h, h⟩

/-!
PRACTICE 016 — Derive two consequences
-/
theorem practice016 (P Q R : Prop) : (P → Q) → (P → R) → P → Q ∧ R := by
  intro hpq
  intro hpr
  intro hp

  exact ⟨hpq hp, hpr hp⟩

/-!
PRACTICE 017 — Extract a consequence from a rule's output
-/
theorem practice017 (P Q R : Prop) : (P → Q ∧ R) → P → R := by
  intro hpqr
  intro hp
  exact (hpqr hp).right

/-!
PRACTICE 018 — Package two inputs for a rule
-/
theorem practice018 (P Q R : Prop) : (P ∧ Q → R) → P → Q → R := by
  intro hpqr
  intro hp
  intro hq
  exact hpqr ⟨hp, hq⟩

/-!
PRACTICE 019 — Unpack a pair for a rule
-/
theorem practice019 (P Q R : Prop) : (P → Q → R) → P ∧ Q → R := by
  intro hpqr
  intro hpq
  exact hpqr hpq.left hpq.right
