/-!
PRACTICE 130 — Distribute, factor, and absorb: variation 1
-/
theorem practice130 (P Q R : Prop) : (P ∧ (Q ∨ R)) ↔ ((P ∧ Q) ∨ (P ∧ R)) := by
  constructor
  · intro h
    cases h.right with
    | inl hq =>
      left
      exact ⟨h.left, hq⟩
    | inr hr =>
      right
      exact ⟨h.left, hr⟩
  · intro h
    cases h with
    | inl hq =>
      constructor
      · exact hq.left
      · left
        exact hq.right
    | inr hr =>
      constructor
      · exact hr.left
      · right
        exact hr.right

/-!
PRACTICE 131 — Distribute, factor, and absorb: variation 2
-/
theorem practice131 (P Q R : Prop) : (P ∨ (Q ∧ R)) ↔ ((P ∨ Q) ∧ (P ∨ R)) := by
  constructor
  · intro h
    cases h with
    | inl hp =>
      constructor
      · left
        exact hp
      · left
        exact hp
    | inr hqr =>
      constructor
      · right
        exact hqr.left
      · right
        exact hqr.right
  · intro h
    cases h.left with
    | inl hp =>
      left
      exact hp
    | inr hq =>
      cases h.right with
      | inl hp =>
        left
        exact hp
      | inr hr =>
        right
        exact ⟨hq, hr⟩

/-!
PRACTICE 132 — Distribute, factor, and absorb: variation 3
-/
theorem practice132 (P Q : Prop) : (P ∧ (P ∨ Q)) ↔ P := by
  constructor
  · intro mp
    exact mp.left
  · intro h
    constructor
    · exact h
    · left
      exact h

/-!
PRACTICE 133 — Distribute, factor, and absorb: variation 4
-/
theorem practice133 (P Q : Prop) : (P ∨ (P ∧ Q)) ↔ P := by
  constructor
  · intro mp
    cases mp with
    | inl hp =>
      exact hp
    | inr hpq =>
      exact hpq.left
  · intro mpr
    left
    exact mpr

/-!
PRACTICE 134 — Distribute, factor, and absorb: variation 5
-/
theorem practice134 (P Q R : Prop) : ((P ∨ Q) ∧ (P ∨ R)) → (P ∨ (Q ∧ R)) := by
  intro h
  cases h.left with
  | inl hp =>
    left
    exact hp
  | inr hq =>
    cases h.right with
    | inl hp =>
      left
      exact hp
    | inr hr =>
      right
      exact ⟨hq, hr⟩

/-!
PRACTICE 135 — Distribute, factor, and absorb: variation 6
-/
theorem practice135 (P Q R S : Prop) : ((P ∧ Q) ∨ (R ∧ S)) → ((P ∨ R) ∧ (Q ∨ S)) := by
  intro h
  cases h with
  | inl hl =>
    constructor
    · left
      exact hl.left
    · left
      exact hl.right
  | inr hr =>
    constructor
    · right
      exact hr.left
    · right
      exact hr.right

/-!
PRACTICE 136 — Distribute, factor, and absorb: variation 7
-/
theorem practice136 (P Q R : Prop) : (P ∧ (Q ∨ R)) → (Q ∨ (P ∧ R)) := by
  intro h
  cases h.right with
  | inl hq =>
    left
    exact hq
  | inr hr =>
    right
    exact ⟨h.left, hr⟩

/-!
PRACTICE 137 — Distribute, factor, and absorb: variation 8
-/
theorem practice137 (P Q R : Prop) : ((P ∨ Q) ∧ R) ↔ ((P ∧ R) ∨ (Q ∧ R)) := by
  constructor
  · intro h
    cases h.left with
    | inl hp =>
      left
      exact ⟨hp, h.right⟩
    | inr hq =>
      right
      exact ⟨hq, h.right⟩
  · intro h
    cases h with
    | inl hpr =>
      constructor
      · left
        exact hpr.left
      · exact hpr.right
    | inr hqr =>
      constructor
      · right
        exact hqr.left
      · exact hqr.right

/-!
PRACTICE 138 — Distribute, factor, and absorb: variation 9
-/
theorem practice138 (P Q R : Prop) : (P ∨ (Q ∨ R)) ↔ (Q ∨ (P ∨ R)) := by
  constructor
  · intro h
    cases h with
    | inl hp =>
      right
      left
      exact hp
    | inr hqr =>
      cases hqr with
      | inl hq =>
        left
        exact hq
      | inr hr =>
        right
        right
        exact hr
  · intro h
    cases h with
    | inl hp =>
      right
      left
      exact hp
    | inr hqr =>
      cases hqr with
      | inl hq =>
        left
        exact hq
      | inr hr =>
        right
        right
        exact hr

/-!
PRACTICE 139 — Distribute, factor, and absorb: variation 10
-/
theorem practice139 (P Q R : Prop) : ((P ∧ Q) ∨ (P ∧ R)) → (P ∧ (R ∨ Q)) := by
  intro h
  cases h with
  | inl hl =>
    constructor
    · exact hl.left
    · right
      exact hl.right
  | inr hr =>
    constructor
    · exact hr.left
    · left
      exact hr.right
