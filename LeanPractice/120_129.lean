/-!
PRACTICE 120 — Route to P, Q, S, R
-/
theorem practice120 (P Q R S : Prop) : (P ∨ (Q ∨ (R ∨ S))) → (P ∨ (Q ∨ (S ∨ R))) := by
  intro h
  rw [or_comm (a := R) (b := S)] at h
  exact h

/-!
PRACTICE 121 — Route to P, R, Q, S
-/
theorem practice121 (P Q R S : Prop) : (P ∨ (Q ∨ (R ∨ S))) → (P ∨ (R ∨ (Q ∨ S))) := by
  intro h
  rw [← or_assoc (a := Q) (b := R) (c := S)] at h
  rw [or_comm (a := Q) (b := R)] at h
  rw [or_assoc (a := R) (b := Q) (c := S)] at h
  exact h

/-!
PRACTICE 122 — Route to P, R, S, Q
-/
theorem practice122 (P Q R S : Prop) : (P ∨ (Q ∨ (R ∨ S))) → (P ∨ (R ∨ (S ∨ Q))) := by
  intro h
  rw [← or_assoc (a := Q) (b := R) (c := S)] at h
  rw [or_comm (a := Q) (b := R)] at h
  rw [or_assoc (a := R) (b := Q) (c := S)] at h
  rw [or_comm (a := Q) (b := S)] at h
  exact h

/-!
PRACTICE 123 — Route to P, S, Q, R
-/
theorem practice123 (P Q R S : Prop) : (P ∨ (Q ∨ (R ∨ S))) → (P ∨ (S ∨ (Q ∨ R))) := by
  intro h
  rw [or_comm (a := Q) (b := (R ∨ S))] at h
  rw [or_comm (a := R) (b := S)] at h
  rw [or_assoc (a := S) (b := R) (c := Q)] at h
  rw [or_comm (a := R) (b := Q)] at h
  exact h

/-!
PRACTICE 124 — Route to P, S, R, Q
-/
theorem practice124 (P Q R S : Prop) : (P ∨ (Q ∨ (R ∨ S))) → (P ∨ (S ∨ (R ∨ Q))) := by
  intro h
  rw [or_comm (a := Q) (b := (R ∨ S))] at h
  rw [or_comm (a := R) (b := S)] at h
  rw [or_assoc (a := S) (b := R) (c := Q)] at h
  exact h

/-!
PRACTICE 125 — Route to Q, P, R, S
-/
theorem practice125 (P Q R S : Prop) : (P ∨ (Q ∨ (R ∨ S))) → (Q ∨ (P ∨ (R ∨ S))) := by
  intro h
  rw [← or_assoc] at h
  rw [or_comm (a := P) (b := Q)] at h
  rw [or_assoc] at h
  exact h

/-!
PRACTICE 126 — Route to Q, P, S, R
-/
theorem practice126 (P Q R S : Prop) : (P ∨ (Q ∨ (R ∨ S))) → (Q ∨ (P ∨ (S ∨ R))) := by
  intro h
  rw [← or_assoc] at h
  rw [or_comm (a := P) (b := Q)] at h
  rw [or_assoc] at h
  rw [or_comm (a := R) (b := S)] at h
  exact h

/-!
PRACTICE 127 — Route to Q, R, P, S
-/
theorem practice127 (P Q R S : Prop) : (P ∨ (Q ∨ (R ∨ S))) → (Q ∨ (R ∨ (P ∨ S))) := by
  intro h
  rw [← or_assoc] at h
  rw [or_comm (a := P) (b := Q)] at h
  rw [or_assoc] at h
  rw [or_comm (a := P) (b := (R ∨ S))] at h
  rw [or_assoc] at h
  rw [or_comm (a := S) (b := P)] at h
  exact h

/-!
PRACTICE 128 — Route to Q, R, S, P
-/
theorem practice128 (P Q R S : Prop) : (P ∨ (Q ∨ (R ∨ S))) → (Q ∨ (R ∨ (S ∨ P))) := by
  intro h
  rw [← or_assoc] at h
  rw [or_comm (a := P) (b := Q)] at h
  rw [or_assoc] at h
  rw [or_comm (a := P) (b := (R ∨ S))] at h
  rw [or_assoc] at h
  exact h

/-!
PRACTICE 129 — Route to Q, S, P, R
-/
theorem practice129 (P Q R S : Prop) : (P ∨ (Q ∨ (R ∨ S))) → (Q ∨ (S ∨ (P ∨ R))) := by
  intro h
  rw [← or_assoc] at h
  rw [or_comm (a := P) (b := Q)] at h
  rw [or_assoc] at h
  rw [or_comm (a := P) (b := (R ∨ S))] at h
  rw [or_comm (a := R) (b := S)] at h
  rw [or_assoc] at h
  rw [or_comm (a := R) (b := P)] at h
  exact h
