/-!
PRACTICE 180 — Classical case analysis: variation 1
-/
theorem practice180 (P Q : Prop) : (P → Q) ↔ (¬P ∨ Q) := by
  constructor
  · intro h
    by_cases hp: P
    · right
      exact h hp
    · left
      exact hp
  · intro h
    cases h with
    | inl hl =>
      intro hp
      exact (hl hp).elim
    | inr hr =>
      intro hp
      exact hr

/-!
PRACTICE 181 — Classical case analysis: variation 2
-/
theorem practice181 (P Q : Prop) : ¬(P ∧ Q) ↔ (¬P ∨ ¬Q) := by
  constructor
  · intro h
    by_cases hp: P
    · right
      intro hq
      exact h ⟨hp, hq⟩
    · left
      exact hp
  · intro h
    intro hpq
    cases h with
    | inl hnp =>
      exact hnp hpq.left
    | inr hnq =>
      exact hnq hpq.right

/-!
PRACTICE 182 — Classical case analysis: variation 3
-/
theorem practice182 (P : Prop) : ¬¬P ↔ P := by
  constructor
  · intro hnnp
    by_cases hp: P
    · exact hp
    · exact (hnnp hp).elim
  · intro hp
    intro hnp
    exact hnp hp

/-!
PRACTICE 183 — Classical case analysis: variation 4
-/
theorem practice183 (P Q : Prop) : (¬Q → ¬P) → (P → Q) := by
  intro hnqnp
  intro hp
  by_cases hq: Q
  · exact hq
  · exact ((hnqnp hq) hp).elim

/-!
PRACTICE 184 — Classical case analysis: variation 5
-/
theorem practice184 (P Q : Prop) : ((P → Q) → P) → P := by
  intro hpqp
  by_cases h: P
  · exact h
  · have hpq : P → Q := by
      intro hp
      exact (h hp).elim
    exact hpqp hpq

/-!
PRACTICE 185 — Classical case analysis: variation 6
-/
theorem practice185 (P Q : Prop) : (P → Q) ∨ (Q → P) := by
  by_cases hp: P
  · right
    intro hq
    exact hp
  · left
    intro h
    exact (hp h).elim

/-!
PRACTICE 186 — Classical case analysis: variation 7
-/
theorem practice186 (P Q : Prop) : ¬(P → Q) ↔ (P ∧ ¬Q) := by
  constructor
  · intro hnpq
    by_cases hp: P
    · constructor
      · exact hp
      · intro hq
        apply hnpq
        intro hp
        exact hq
    · constructor
      · have hpq : P → Q := by
          intro hnp
          exact (hp hnp).elim
        exact (hnpq hpq).elim
      · have hpq : P → Q := by
          intro hnp
          exact (hp hnp).elim
        intro hq
        exact hnpq hpq
  · intro mpr
    intro hpq
    exact mpr.right (hpq mpr.left)

/-!
PRACTICE 187 — Classical case analysis: variation 8
-/
theorem practice187 (P Q : Prop) : (P → Q) ∨ (P → ¬Q) := by
  by_cases hq: Q
  · left
    intro t
    exact hq
  · right
    intro t
    exact hq

/-!
PRACTICE 188 — Classical case analysis: variation 9
-/
theorem practice188 (P Q : Prop) : (P ∧ Q) ∨ (P ∧ ¬Q) ∨ (¬P ∧ Q) ∨ (¬P ∧ ¬Q) := by
  by_cases hp: P
  · by_cases hq: Q
    · left
      exact ⟨hp, hq⟩
    · right
      left
      exact ⟨hp, hq⟩
  · by_cases hq: Q
    · right
      right
      left
      exact ⟨hp, hq⟩
    · right
      right
      right
      exact ⟨hp, hq⟩

/-!
PRACTICE 189 — Classical case analysis: variation 10
-/
theorem practice189 (P Q : Prop) : (P ↔ Q) ∨ (P ↔ ¬Q) := by
  by_cases hp: P
  · by_cases hq: Q
    · left
      constructor
      · intro t
        exact hq
      · intro t
        exact hp
    · right
      constructor
      · intro t
        exact hq
      · intro t
        exact hp
  · by_cases hq: Q
    · right
      constructor
      · intro p
        intro q
        exact hp p
      · intro q
        exact (q hq).elim
    · left
      constructor
      · intro p
        exact (hp p).elim
      · intro q
        exact (hq q).elim
