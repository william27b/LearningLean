/-!
PRACTICE 030 — Regroup three alternatives to the left
-/
theorem practice030 (P Q R : Prop) : P ∨ (Q ∨ R) → (P ∨ Q) ∨ R := by
  intro hpqr

  cases hpqr with
  | inl hP =>
    left
    left
    exact hP
  | inr hQR =>
    cases hQR with
    | inl hQ =>
      left
      right
      exact hQ
    | inr hR =>
      right
      exact hR

/-!
PRACTICE 031 — Regroup three alternatives to the right
-/
theorem practice031 (P Q R : Prop) : (P ∨ Q) ∨ R → P ∨ (Q ∨ R) := by
  intro hpqr

  cases hpqr with
  | inr hR =>
    right
    right
    exact hR
  | inl hPQ =>
    cases hPQ with
    | inl hP =>
      left
      exact hP
    | inr hQ =>
      right
      left
      exact hQ

/-!
PRACTICE 032 — Distribute an AND over an OR
-/
theorem practice032 (P Q R : Prop) : P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) := by
  intro hpqr

  cases hpqr.right with
  | inl hQ =>
    left
    exact ⟨hpqr.left, hQ⟩
  | inr hR =>
    right
    exact ⟨hpqr.left, hR⟩

/-!
PRACTICE 033 — Factor out a common statement
-/
theorem practice033 (P Q R : Prop) : (P ∧ Q) ∨ (P ∧ R) → P ∧ (Q ∨ R) := by
  intro hpqr

  cases hpqr with
  | inl hPQ =>
    constructor
    · exact hPQ.left
    · left
      exact hPQ.right
  | inr hPR =>
    constructor
    · exact hPR.left
    · right
      exact hPR.right

/-!
PRACTICE 034 — Transform either alternative
-/
theorem practice034 (P Q R S : Prop) : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intro hPR
  intro hQS
  intro hPQ

  cases hPQ with
  | inl hP =>
    left
    exact hPR hP
  | inr hQ =>
    right
    exact hQS hQ

/-!
PRACTICE 035 — Merge two ways of obtaining Q
-/
theorem practice035 (P Q : Prop) : P ∨ Q → (P → Q) → Q := by
  intro hPoQ
  intro hPtQ

  cases hPoQ with
  | inl hP =>
    exact hPtQ hP
  | inr hQ =>
    exact hQ

/-!
PRACTICE 036 — Use the definition of NOT
-/
theorem practice036 (P : Prop) : ¬P → P → False := by
  intro hnP
  intro hP
  exact hnP hP

/-!
PRACTICE 037 — Introduce double negation
-/
theorem practice037 (P : Prop) : P → ¬¬P := by
  intro hP
  intro hnP
  exact hnP hP

/-!
PRACTICE 038 — Use an impossible assumption
-/
theorem practice038 (P : Prop) : False → P := by
  intro hF
  exact hF.elim

/-!
PRACTICE 039 — Rule out one alternative
-/
theorem practice039 (P Q : Prop) : ¬P → P ∨ Q → Q := by
  intro hnP
  intro hPQ
  cases hPQ with
  | inl hP =>
    exact (hnP hP).elim
  | inr hQ =>
    exact hQ
