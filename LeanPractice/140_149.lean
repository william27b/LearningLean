/-!
PRACTICE 140 — Build and reuse rules with several inputs: variation 1
-/
theorem practice140 (P Q R : Prop) : (P → Q → R) → (Q → P → R) := by
  intro hpqr
  intro hq
  intro hp
  exact hpqr hp hq

/-!
PRACTICE 141 — Build and reuse rules with several inputs: variation 2
-/
theorem practice141 (P Q R S : Prop) : (P → Q) → (P → R) → (Q → R → S) → P → S := by
  intro hpq
  intro hpr
  intro hqrs
  intro hp
  exact hqrs (hpq hp) (hpr hp)

/-!
PRACTICE 142 — Build and reuse rules with several inputs: variation 3
-/
theorem practice142 (P Q R : Prop) : ((P ∧ Q) → R) ↔ (P → Q → R) := by
  constructor
  · intro mp
    intro hp
    intro hq
    exact mp ⟨hp, hq⟩
  · intro mpr
    intro hpq
    exact mpr hpq.left hpq.right

/-!
PRACTICE 143 — Build and reuse rules with several inputs: variation 4
-/
theorem practice143 (P Q R : Prop) : (P → (Q → R)) → ((P → Q) → (P → R)) := by
  intro hpqr
  intro hpq
  intro hp
  exact hpqr hp (hpq hp)

/-!
PRACTICE 144 — Build and reuse rules with several inputs: variation 5
-/
theorem practice144 (P Q R S : Prop) : (P → Q) → (Q → R) → (P → S) → P → (R ∧ S) := by
  intro hpq
  intro hqr
  intro hps
  intro hp
  exact ⟨hqr (hpq hp), hps hp⟩

/-!
PRACTICE 145 — Build and reuse rules with several inputs: variation 6
-/
theorem practice145 (P Q R S : Prop) : (P → Q → R) → (S → P) → (S → Q) → S → R := by
  intro hpqr
  intro hsp
  intro hsq
  intro hs
  exact hpqr (hsp hs) (hsq hs)

/-!
PRACTICE 146 — Build and reuse rules with several inputs: variation 7
-/
theorem practice146 (P Q R S : Prop) : ((P → Q) ∧ (R → S)) → (P ∧ R) → (Q ∧ S) := by
  intro h
  intro hpr
  exact ⟨h.left hpr.left, h.right hpr.right⟩

/-!
PRACTICE 147 — Build and reuse rules with several inputs: variation 8
-/
theorem practice147 (P Q R : Prop) : (P → Q → R) → (P → Q) → P → (Q ∧ R) := by
  intro hpqr
  intro hpq
  intro hp
  exact ⟨hpq hp, hpqr hp (hpq hp)⟩

/-!
PRACTICE 148 — Build and reuse rules with several inputs: variation 9
-/
theorem practice148 (P Q R S : Prop) : (P → Q) → (P → R) → ((Q ∧ R) → S) → P → S := by
  intro hpq
  intro hpr
  intro hqrs
  intro hp
  exact hqrs ⟨hpq hp, hpr hp⟩

/-!
PRACTICE 149 — Build and reuse rules with several inputs: variation 10
-/
theorem practice149 (P Q R : Prop) : (P → Q) → ((Q ∧ P) → R) → P → R := by
  intro hpq
  intro hqpr
  intro hp
  exact hqpr ⟨hpq hp, hp⟩
