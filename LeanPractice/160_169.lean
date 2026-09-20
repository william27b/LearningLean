/-!
PRACTICE 160 — Eliminate inconsistent alternatives: variation 1
-/
theorem practice160 (P Q R : Prop) : (P → Q) → (Q → R) → ¬R → ¬P := by
  intro hpq
  intro hqr
  intro hnr
  intro hp
  apply hnr
  exact hqr (hpq hp)

/-!
PRACTICE 161 — Eliminate inconsistent alternatives: variation 2
-/
theorem practice161 (P Q : Prop) : (P ∨ Q) → ¬Q → P := by
  intro hpq
  intro hnq
  cases hpq with
  | inl hp =>
    exact hp
  | inr hq =>
    exact (hnq hq).elim

/-!
PRACTICE 162 — Eliminate inconsistent alternatives: variation 3
-/
theorem practice162 (P Q R : Prop) : (P ∨ Q ∨ R) → ¬P → ¬Q → R := by
  intro hpqr
  intro hnp
  intro hnq
  cases hpqr with
  | inl hp =>
    exact (hnp hp).elim
  | inr hqr =>
    cases hqr with
    | inl hq =>
      exact (hnq hq).elim
    | inr hr =>
      exact hr

/-!
PRACTICE 163 — Eliminate inconsistent alternatives: variation 4
-/
theorem practice163 (P Q R : Prop) : (P → Q) → (P → ¬Q) → (P ∨ R) → R := by
  intro hpq
  intro hpnq
  intro hpr
  cases hpr with
  | inl hp =>
    exact ((hpnq hp) (hpq hp)).elim
  | inr hr =>
    exact hr

/-!
PRACTICE 164 — Eliminate inconsistent alternatives: variation 5
-/
theorem practice164 (P Q : Prop) : (P ∧ ¬Q) → ¬(Q ∨ ¬P) := by
  intro hpq
  intro hqonp
  cases hqonp with
  | inl hq =>
    exact (hpq.right hq)
  | inr hnp =>
    exact hnp hpq.left

/-!
PRACTICE 165 — Eliminate inconsistent alternatives: variation 6
-/
theorem practice165 (P Q : Prop) : ¬(P ∧ Q) → Q → ¬P := by
  intro hnpq
  intro hq
  intro hp
  exact hnpq ⟨hp, hq⟩

/-!
PRACTICE 166 — Eliminate inconsistent alternatives: variation 7
-/
theorem practice166 (P Q : Prop) : (P → ¬Q) ↔ (Q → ¬P) := by
  constructor
  · intro hpq
    intro hq
    intro hp
    exact hpq hp hq
  · intro hqp
    intro hp
    intro hq
    exact hqp hq hp

/-!
PRACTICE 167 — Eliminate inconsistent alternatives: variation 8
-/
theorem practice167 (P Q R : Prop) : (P → Q) → (R → P) → ¬Q → ¬R := by
  intro hpq
  intro hrp
  intro hnq
  intro hr
  exact hnq (hpq (hrp hr))

/-!
PRACTICE 168 — Eliminate inconsistent alternatives: variation 9
-/
theorem practice168 (P Q R : Prop) : (P ∨ Q) → (P → False) → (Q → R) → R := by
  intro hpoq
  intro hpf
  intro hqr
  cases hpoq with
  | inl hp =>
    exact (hpf hp).elim
  | inr hq =>
    exact hqr hq

/-!
PRACTICE 169 — Eliminate inconsistent alternatives: variation 10
-/
theorem practice169 (P Q R : Prop) : (P ∨ Q) → (P → R) → (Q → ¬R) → ¬(P ∧ Q) := by
  intro hpoq
  intro hpr
  intro hqnr
  intro hpaq

  exact (hqnr hpaq.right) (hpr hpaq.left)
