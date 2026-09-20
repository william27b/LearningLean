/-!
PRACTICE 040 — Prove a contrapositive
-/
theorem practice040 (P Q : Prop) : (P → Q) → ¬Q → ¬P := by
  intro hPQ
  intro hnQ
  intro hP
  have hQ: Q := hPQ hP
  exact hnQ hQ

/-!
PRACTICE 041 — An AND cannot contain its own contradiction
-/
theorem practice041 (P : Prop) : ¬(P ∧ ¬P) := by
  intro hPnP
  exact hPnP.right hPnP.left

/-!
PRACTICE 042 — Neither alternative can hold
-/
theorem practice042 (P Q : Prop) : ¬P ∧ ¬Q → ¬(P ∨ Q) := by
  intro hnPnQ
  intro hPoQ
  cases hPoQ with
  | inl hP =>
    exact hnPnQ.left hP
  | inr hQ =>
    exact hnPnQ.right hQ

/-!
PRACTICE 043 — Extract two negations
-/
theorem practice043 (P Q : Prop) : ¬(P ∨ Q) → ¬P ∧ ¬Q := by
  intro hnPoQ
  constructor
  · intro hP
    apply hnPoQ
    left
    exact hP
  · intro hQ
    apply hnPoQ
    right
    exact hQ

/-!
PRACTICE 044 — Refute a possible conclusion
-/
theorem practice044 (P Q : Prop) : ¬(P → Q) → ¬Q := by
  intro hPQ
  intro hQ

  have hRule : P → Q := by
    intro hP
    exact hQ

  exact hPQ hRule

/-!
PRACTICE 045 — Two rules force opposite conclusions
-/
theorem practice045 (P Q : Prop) : (P → Q) → (P → ¬Q) → ¬P := by
  intro hPQ
  intro hPnQ
  intro hnP
  exact (hPnQ hnP) (hPQ hnP)

/-!
PRACTICE 046 — Fix one side of an impossible pair
-/
theorem practice046 (P Q : Prop) : ¬(P ∧ Q) → P → ¬Q := by
  intro hnPaQ
  intro hP
  intro hnQ

  exact hnPaQ ⟨hP, hnQ⟩

/-!
PRACTICE 047 — Eliminate an inconsistent branch
-/
theorem practice047 (P Q R : Prop) : (P → Q) → (P → ¬Q) → P ∨ R → R := by
  intro hPQ
  intro hPnQ
  intro hPoR
  cases hPoR with
  | inl hP =>
    exact ((hPnQ hP) (hPQ hP)).elim
  | inr hR =>
    exact hR

/-!
PRACTICE 048 — A statement is equivalent to itself
-/
theorem practice048 (P : Prop) : P ↔ P := by
  constructor
  · intro hP
    exact hP
  · intro hP
    exact hP

/-!
PRACTICE 049 — Reverse an equivalence
-/
theorem practice049 (P Q : Prop) : (P ↔ Q) → (Q ↔ P) := by
  intro hpq
  exact hpq.symm
