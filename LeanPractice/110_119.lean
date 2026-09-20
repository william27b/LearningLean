/-!
PRACTICE 110 — Order P, Q, S, R
-/
theorem practice110 (P Q R S : Prop) : (P ∧ (Q ∧ (R ∧ S))) → (P ∧ (Q ∧ (S ∧ R))) := by
  intro h
  exact ⟨h.left, ⟨h.right.left, ⟨h.right.right.right, h.right.right.left⟩⟩⟩

/-!
PRACTICE 111 — Order P, R, Q, S
-/
theorem practice111 (P Q R S : Prop) : (P ∧ (Q ∧ (R ∧ S))) → (P ∧ (R ∧ (Q ∧ S))) := by
  intro h
  exact ⟨h.left, ⟨h.right.right.left, ⟨h.right.left, h.right.right.right⟩⟩⟩

/-!
PRACTICE 112 — Order P, R, S, Q
-/
theorem practice112 (P Q R S : Prop) : (P ∧ (Q ∧ (R ∧ S))) → (P ∧ (R ∧ (S ∧ Q))) := by
  intro h
  exact ⟨h.left, ⟨h.right.right.left, ⟨h.right.right.right, h.right.left⟩⟩⟩

/-!
PRACTICE 113 — Order P, S, Q, R
-/
theorem practice113 (P Q R S : Prop) : (P ∧ (Q ∧ (R ∧ S))) → (P ∧ (S ∧ (Q ∧ R))) := by
  intro h
  exact ⟨h.left, ⟨h.right.right.right, ⟨h.right.left, h.right.right.left⟩⟩⟩

/-!
PRACTICE 114 — Order P, S, R, Q
-/
theorem practice114 (P Q R S : Prop) : (P ∧ (Q ∧ (R ∧ S))) → (P ∧ (S ∧ (R ∧ Q))) := by
  intro h
  exact ⟨h.left, ⟨h.right.right.right, ⟨h.right.right.left, h.right.left⟩⟩⟩

/-!
PRACTICE 115 — Order Q, P, R, S
-/
theorem practice115 (P Q R S : Prop) : (P ∧ (Q ∧ (R ∧ S))) → (Q ∧ (P ∧ (R ∧ S))) := by
  intro h
  exact ⟨h.right.left, ⟨h.left, ⟨h.right.right.left, h.right.right.right⟩⟩⟩

/-!
PRACTICE 116 — Order Q, P, S, R
-/
theorem practice116 (P Q R S : Prop) : (P ∧ (Q ∧ (R ∧ S))) → (Q ∧ (P ∧ (S ∧ R))) := by
  intro h
  exact ⟨h.right.left, ⟨h.left, ⟨h.right.right.right, h.right.right.left⟩⟩⟩

/-!
PRACTICE 117 — Order Q, R, P, S
-/
theorem practice117 (P Q R S : Prop) : (P ∧ (Q ∧ (R ∧ S))) → (Q ∧ (R ∧ (P ∧ S))) := by
  intro h
  exact ⟨h.right.left, ⟨h.right.right.left, ⟨h.left, h.right.right.right⟩⟩⟩

/-!
PRACTICE 118 — Order Q, R, S, P
-/
theorem practice118 (P Q R S : Prop) : (P ∧ (Q ∧ (R ∧ S))) → (Q ∧ (R ∧ (S ∧ P))) := by
  intro h
  exact ⟨h.right.left, ⟨h.right.right.left, ⟨h.right.right.right, h.left⟩⟩⟩

/-!
PRACTICE 119 — Order Q, S, P, R
-/
theorem practice119 (P Q R S : Prop) : (P ∧ (Q ∧ (R ∧ S))) → (Q ∧ (S ∧ (P ∧ R))) := by
  intro h
  exact ⟨h.right.left, ⟨h.right.right.right, ⟨h.left, h.right.right.left⟩⟩⟩
