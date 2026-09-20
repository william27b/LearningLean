/-!
PRACTICE 000 — Keep the first assumption
-/
theorem practice000 (P Q : Prop) : P → (Q → P) := by
  intro h
  intro g
  exact h

/-!
PRACTICE 001 — Use an implication
-/
theorem practice001 (P Q : Prop) : P → (P → Q) → Q := by
  intro hA
  intro hAB
  exact hAB hA

/-!
PRACTICE 002 — Keep the second assumption
-/
theorem practice002 (P Q : Prop) : P → Q → Q := by
  intro hP
  intro hQ
  exact hQ

/-!
PRACTICE 003 — Chain two implications
-/
theorem practice003 (P Q R : Prop) : (P → Q) → (Q → R) → P → R := by
  intro hPQ
  intro hQR
  intro hP
  exact hQR (hPQ hP)

/-!
PRACTICE 004 — Supply arguments in the right order
-/
theorem practice004 (P Q R : Prop) : (P → Q → R) → Q → P → R := by
  intro hPQR
  intro hQ
  intro hP
  exact hPQR hP hQ

/-!
PRACTICE 005 — Reuse a proof
-/
theorem practice005 (P Q : Prop) : (P → P → Q) → P → Q := by
  intro hPPQ
  intro hP
  exact hPPQ hP hP

/-!
PRACTICE 006 — Prove both statements
-/
theorem practice006 (P Q : Prop) : P → Q → P ∧ Q := by
  intro hP
  intro hQ
  constructor
  · exact hP
  · exact hQ

/-!
PRACTICE 007 — Extract the left side
-/
theorem practice007 (P Q : Prop) : P ∧ Q → P := by
  intro hPQ
  exact hPQ.left

/-!
PRACTICE 008 — Extract the right side
-/
theorem practice008 (P Q : Prop) : P ∧ Q → Q := by
  intro hPQ
  exact hPQ.right

/-!
PRACTICE 009 — Swap an AND
-/
theorem practice009 (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro hPQ
  constructor
  · exact hPQ.right
  · exact hPQ.left
