/-!
PRACTICE 170 — Replace equivalent statements inside larger claims: variation 1
-/
theorem practice170 (P Q R : Prop) : (P ↔ Q) → ((P ∧ R) ↔ (Q ∧ R)) := by
  intro hpq

  constructor
  · intro hpar
    rw [hpq] at hpar
    exact hpar
  · intro hqar
    rw [← hpq] at hqar
    exact hqar

/-!
PRACTICE 171 — Replace equivalent statements inside larger claims: variation 2
-/
theorem practice171 (P Q R : Prop) : (P ↔ Q) → ((P ∨ R) ↔ (Q ∨ R)) := by
  intro hpq
  constructor
  · intro hpr
    cases hpr with
    | inl hp =>
      left
      rw [hpq] at hp
      exact hp
    | inr hr =>
      right
      exact hr
  · intro hqr
    cases hqr with
    | inl hq =>
      left
      rw [← hpq] at hq
      exact hq
    | inr hr =>
      right
      exact hr


/-!
PRACTICE 172 — Replace equivalent statements inside larger claims: variation 3
-/
theorem practice172 (P Q : Prop) : (P ↔ Q) → (¬P ↔ ¬Q) := by
  intro hpq
  constructor
  · intro hnp
    rw [hpq] at hnp
    exact hnp
  · intro hnq
    rw [← hpq] at hnq
    exact hnq

/-!
PRACTICE 173 — Replace equivalent statements inside larger claims: variation 4
-/
theorem practice173 (P Q R : Prop) : (P ↔ Q) → ((R → P) ↔ (R → Q)) := by
  intro hpq
  constructor
  · intro hrp
    rw [hpq] at hrp
    exact hrp
  · intro hrq
    rw [← hpq] at hrq
    exact hrq

/-!
PRACTICE 174 — Replace equivalent statements inside larger claims: variation 5
-/
theorem practice174 (P Q R : Prop) : (P ↔ Q) → ((P → R) ↔ (Q → R)) := by
  /-
    literally the exact same as the last problem :(
    except the rewrite command replaces different variables
  -/
  intro hpq
  constructor
  · intro hrp
    rw [hpq] at hrp
    exact hrp
  · intro hrq
    rw [← hpq] at hrq
    exact hrq

/-!
PRACTICE 175 — Replace equivalent statements inside larger claims: variation 6
-/
theorem practice175 (P Q R S : Prop) : (P ↔ Q) → (R ↔ S) → ((P ∧ R) ↔ (Q ∧ S)) := by
  intro hpq
  intro hrs
  constructor
  · intro hpar
    rw [hpq] at hpar
    rw [hrs] at hpar
    exact hpar
  · intro hpar
    rw [← hpq] at hpar
    rw [← hrs] at hpar
    exact hpar

/-!
PRACTICE 176 — Replace equivalent statements inside larger claims: variation 7
-/
theorem practice176 (P Q R S : Prop) : (P ↔ Q) → (R ↔ S) → ((P ∨ R) ↔ (Q ∨ S)) := by
  intro hpq
  intro hrs
  constructor
  · intro hpar
    rw [hpq] at hpar
    rw [hrs] at hpar
    exact hpar
  · intro hpar
    rw [← hpq] at hpar
    rw [← hrs] at hpar
    exact hpar

/-!
PRACTICE 177 — Replace equivalent statements inside larger claims: variation 8
-/
theorem practice177 (P Q R S : Prop) : (P ↔ Q) → (R ↔ S) → ((P → R) ↔ (Q → S)) := by
  intro hpq
  intro hrs
  constructor
  · intro hpar
    rw [hpq] at hpar
    rw [hrs] at hpar
    exact hpar
  · intro hpar
    rw [← hpq] at hpar
    rw [← hrs] at hpar
    exact hpar

/-!
PRACTICE 178 — Replace equivalent statements inside larger claims: variation 9
-/
theorem practice178 (P Q R S : Prop) : (P ↔ Q) → (Q ↔ R) → ((P ∨ S) ↔ (R ∨ S)) := by
  intro hpq
  intro hrs
  constructor
  · intro hpar
    rw [hpq] at hpar
    rw [hrs] at hpar
    exact hpar
  · intro hpar
    rw [← hrs] at hpar
    rw [← hpq] at hpar
    exact hpar

/-!
PRACTICE 179 — Replace equivalent statements inside larger claims: variation 10
-/
theorem practice179 (P Q R S : Prop) : (P ↔ Q) → (Q ↔ R) → ((S → P) ↔ (S → R)) := by
  intro hpq
  intro hrs
  constructor
  · intro hpar
    rw [hpq] at hpar
    rw [hrs] at hpar
    exact hpar
  · intro hpar
    rw [← hrs] at hpar
    rw [← hpq] at hpar
    exact hpar
