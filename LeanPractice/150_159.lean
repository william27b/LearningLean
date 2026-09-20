/-!
PRACTICE 150 — Construct contradictions explicitly: variation 1
-/
theorem practice150 (P Q : Prop) : ¬(P ∨ Q) → ¬P := by
  intro hpq
  intro hp
  apply hpq
  left
  exact hp

/-!
PRACTICE 151 — Construct contradictions explicitly: variation 2
-/
theorem practice151 (P Q : Prop) : ¬(P ∨ Q) → ¬Q := by
  intro hpq
  intro hq
  apply hpq
  right
  exact hq

/-!
PRACTICE 152 — Construct contradictions explicitly: variation 3
-/
theorem practice152 (P Q : Prop) : ¬P → ¬(P ∧ Q) := by
  intro hp
  intro hpq
  apply hp
  exact hpq.left

/-!
PRACTICE 153 — Construct contradictions explicitly: variation 4
-/
theorem practice153 (P Q : Prop) : ¬Q → ¬(P ∧ Q) := by
  intro hq
  intro hpq
  apply hq
  exact hpq.right

/-!
PRACTICE 154 — Construct contradictions explicitly: variation 5
-/
theorem practice154 (P Q : Prop) : (P → Q) → ¬Q → ¬P := by
  intro hpq
  intro hq
  intro hp
  apply hq
  exact hpq hp

/-!
PRACTICE 155 — Construct contradictions explicitly: variation 6
-/
theorem practice155 (P Q : Prop) : (P → ¬Q) → Q → ¬P := by
  intro hpq
  intro hq
  intro hp
  apply (hpq hp)
  exact hq

/-!
PRACTICE 156 — Construct contradictions explicitly: variation 7
-/
theorem practice156 (P Q : Prop) : ¬P → (P → Q) := by
  intro hnp
  intro hp
  exact (hnp hp).elim

/-!
PRACTICE 157 — Construct contradictions explicitly: variation 8
-/
theorem practice157 (P Q : Prop) : (P ∧ ¬Q) → ¬(P → Q) := by
  intro hpanq
  intro hpq
  exact hpanq.right (hpq hpanq.left)

/-!
PRACTICE 158 — Construct contradictions explicitly: variation 9
-/
theorem practice158 (P Q R : Prop) : ¬(P ∨ (Q ∨ R)) → (¬P ∧ ¬Q ∧ ¬R) := by
  intro hpoqor
  constructor
  · intro hnp
    apply hpoqor
    left
    exact hnp
  · constructor
    · intro hnq
      apply hpoqor
      right
      left
      exact hnq
    · intro hnr
      apply hpoqor
      right
      right
      exact hnr

/-!
PRACTICE 159 — Construct contradictions explicitly: variation 10
-/
theorem practice159 (P Q R : Prop) : (¬P ∧ ¬Q ∧ ¬R) → ¬(P ∨ Q ∨ R) := by
  intro hpaqar
  intro hpqr
  cases hpqr with
  | inl hp =>
    exact hpaqar.left hp
  | inr hqr =>
    cases hqr with
    | inl hq =>
      exact hpaqar.right.left hq
    | inr hr =>
      exact hpaqar.right.right hr
