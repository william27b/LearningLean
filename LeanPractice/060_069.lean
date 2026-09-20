/-!
PRACTICE 060 — Use a universal statement at a specific number
-/
theorem practice060 (A : Nat → Prop) : (∀ n, A n) → A 7 := by
  intro h
  exact h 7

/-!
PRACTICE 061 — Prove a statement for every input
-/
theorem practice061 (A B : Nat → Prop) : (∀ n, A n → B n) → (∀ n, A n) → ∀ n, B n := by
  intro hab
  intro ha
  intro n
  exact hab n (ha n)

/-!
PRACTICE 062 — Separate two universal conclusions
-/
theorem practice062 (A B : Nat → Prop) : (∀ n, A n ∧ B n) → (∀ n, A n) ∧ (∀ n, B n) := by
  intro hAaB
  constructor
  · intro n
    exact (hAaB n).left
  · intro n
    exact (hAaB n).right

/-!
PRACTICE 063 — Combine two universal statements
-/
theorem practice063 (A B : Nat → Prop) : (∀ n, A n) → (∀ n, B n) → ∀ n, A n ∧ B n := by
  intro hA
  intro hB
  intro n
  exact ⟨hA n, hB n⟩

/-!
PRACTICE 064 — Give an explicit witness
-/
theorem practice064 (A : Nat → Prop) : A 7 → ∃ n, A n := by
  intro h
  refine ⟨7, ?_⟩
  exact h

/-!
PRACTICE 065 — Use a supplied number as a witness
-/
theorem practice065 (A : Nat → Prop) (k : Nat) : A k → ∃ n, A n := by
  intro h
  refine ⟨k, ?_⟩
  exact h

/-!
PRACTICE 066 — Unpack an existential proof
-/
theorem practice066 (A B : Nat → Prop) : (∃ n, A n ∧ B n) → ∃ n, A n := by
  intro h
  cases h with
  | intro n hw =>
    refine ⟨n, hw.left⟩

/-!
PRACTICE 067 — Transform evidence without changing the witness
-/
theorem practice067 (A B : Nat → Prop) : (∀ n, A n → B n) → (∃ n, A n) → ∃ n, B n := by
  intro h
  intro ha
  cases ha with
  | intro n hw =>
    refine ⟨n, ?_⟩
    exact (h n) hw

/-!
PRACTICE 068 — Use a universal fact at an unknown witness
-/
theorem practice068 (A B : Nat → Prop) : (∃ n, A n) → (∀ n, B n) → ∃ n, A n ∧ B n := by
  intro hA
  intro hB
  cases hA with
  | intro n hw =>
    refine ⟨n, ?_⟩
    exact ⟨hw, hB n⟩

/-!
PRACTICE 069 — Universal negation rules out existence
-/
theorem practice069 (A : Nat → Prop) : (∀ n, ¬A n) → ¬(∃ n, A n) := by
  intro hnA
  intro hAn
  cases hAn with
  | intro n hw =>
    exact (hnA n) hw
