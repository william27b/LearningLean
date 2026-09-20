/-!
PRACTICE 100 — Recover P
-/
theorem practice100 (P Q R S : Prop) : ((P ∧ Q) ∧ (R ∧ S)) → (P) := by
  intro h
  exact h.left.left

/-!
PRACTICE 101 — Recover Q
-/
theorem practice101 (P Q R S : Prop) : ((P ∧ Q) ∧ (R ∧ S)) → (Q) := by
  intro h
  exact h.left.right

/-!
PRACTICE 102 — Recover R
-/
theorem practice102 (P Q R S : Prop) : ((P ∧ Q) ∧ (R ∧ S)) → (R) := by
  intro h
  exact h.right.left

/-!
PRACTICE 103 — Recover S
-/
theorem practice103 (P Q R S : Prop) : ((P ∧ Q) ∧ (R ∧ S)) → (S) := by
  intro h
  exact h.right.right

/-!
PRACTICE 104 — Recover P ∧ R
-/
theorem practice104 (P Q R S : Prop) : ((P ∧ Q) ∧ (R ∧ S)) → (P ∧ R) := by
  intro h
  exact ⟨h.left.left, h.right.left⟩

/-!
PRACTICE 105 — Recover Q ∧ S
-/
theorem practice105 (P Q R S : Prop) : ((P ∧ Q) ∧ (R ∧ S)) → (Q ∧ S) := by
  intro h
  exact ⟨h.left.right, h.right.right⟩

/-!
PRACTICE 106 — Recover P ∧ S
-/
theorem practice106 (P Q R S : Prop) : ((P ∧ Q) ∧ (R ∧ S)) → (P ∧ S) := by
  intro h
  exact ⟨h.left.left, h.right.right⟩

/-!
PRACTICE 107 — Recover Q ∧ R
-/
theorem practice107 (P Q R S : Prop) : ((P ∧ Q) ∧ (R ∧ S)) → (Q ∧ R) := by
  intro h
  exact ⟨h.left.right, h.right.left⟩

/-!
PRACTICE 108 — Recover (P ∧ R) ∧ S
-/
theorem practice108 (P Q R S : Prop) : ((P ∧ Q) ∧ (R ∧ S)) → ((P ∧ R) ∧ S) := by
  intro h
  exact ⟨⟨h.left.left, h.right.left⟩, h.right.right⟩

/-!
PRACTICE 109 — Recover (Q ∧ S) ∧ P
-/
theorem practice109 (P Q R S : Prop) : ((P ∧ Q) ∧ (R ∧ S)) → ((Q ∧ S) ∧ P) := by
  intro h
  exact ⟨⟨h.left.right, h.right.right⟩, h.left.left⟩
