/-!
PRACTICE 070 — No witness means every candidate fails
-/
theorem practice070 (A : Nat → Prop) : ¬(∃ n, A n) → ∀ n, ¬A n := by
  intro hA
  intro n
  intro hnA
  apply hA
  refine ⟨n, ?_⟩
  exact hnA

/-!
PRACTICE 071 — Split an existential alternative
-/
theorem practice071 (A B : Nat → Prop) : (∃ n, A n ∨ B n) → (∃ n, A n) ∨ (∃ n, B n) := by
  intro hAoB
  cases hAoB with
  | intro n hw =>
    cases hw with
    | inl hA =>
      left
      refine ⟨n, ?_⟩
      exact hA
    | inr hB =>
      right
      refine ⟨n, ?_⟩
      exact hB

/-!
PRACTICE 072 — Reflexivity
-/
theorem practice072 (n : Nat) : n = n := by
  rfl

/-!
PRACTICE 073 — Reverse an equality
-/
theorem practice073 (a b : Nat) : a = b → b = a := by
  intro h
  exact h.symm

/-!
PRACTICE 074 — Join two equalities
-/
theorem practice074 (a b c : Nat) : a = b → b = c → a = c := by
  intro ha
  intro hb
  exact ha.trans hb

/-!
PRACTICE 075 — Transport a statement along equality
-/
theorem practice075 (a b : Nat) (A : Nat → Prop) : a = b → A a → A b := by
  intro h
  rw [← h]
  intro ha
  exact ha

/-!
PRACTICE 076 — Apply the same function to equal inputs
-/
theorem practice076 (a b : Nat) (f : Nat → Nat) : a = b → f a = f b := by
  intro h
  exact congrArg f h

/-!
PRACTICE 077 — Rewrite two inputs
-/
theorem practice077 (a b c d : Nat) : a = b → c = d → a + c = b + d := by
  intro hab
  intro hcd
  rw [hab, hcd]

/-!
PRACTICE 078 — Two values equal to the same value
-/
theorem practice078 (a b c : Nat) : a = b → a = c → b = c := by
  intro hab
  rw [hab]
  intro h
  exact h

/-!
PRACTICE 079 — Choose an equal witness
-/
theorem practice079 (n : Nat) : ∃ m : Nat, m = n := by
  refine ⟨n, ?_⟩
  rfl
