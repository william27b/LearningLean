/-!
PRACTICE 190 — Combine the propositional tools: variation 1
-/
theorem practice190 (P Q R S : Prop) : ((P → Q) ∧ (Q → R) ∧ (R → S)) → ((P ∧ ¬S) → False) := by
  intro h
  intro q
  rcases h with ⟨hpq, hqr, hrs⟩
  exact q.right (hrs (hqr (hpq q.left)))

/-!
PRACTICE 191 — Combine the propositional tools: variation 2
-/
theorem practice191 (P Q R S : Prop) : ((P ∨ Q) ∧ (R ∨ S)) → ((P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S)) := by
  intro h
  rcases h with ⟨pq, rs⟩
  rcases pq with hp | hq
  · rcases rs with hr | hs
    · left
      exact ⟨hp, hr⟩
    · right
      left
      exact ⟨hp, hs⟩
  · rcases rs with hr | hs
    · right
      right
      left
      exact ⟨hq, hr⟩
    · right
      right
      right
      exact ⟨hq, hs⟩

/-!
PRACTICE 192 — Combine the propositional tools: variation 3
-/
theorem practice192 (P Q R S : Prop) : ((P → R) ∧ (Q → S)) → ((P ∨ Q) → (R ∨ S)) := by
  intro h
  rcases h with ⟨pr, qs⟩
  intro h
  rcases h with p | q
  · left
    exact pr p
  · right
    exact qs q

/-!
PRACTICE 193 — Combine the propositional tools: variation 4
-/
theorem practice193 (P Q R S : Prop) : (P ↔ Q) → (R ↔ S) → ((P ∧ ¬R) ↔ (Q ∧ ¬S)) := by
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
PRACTICE 194 — Combine the propositional tools: variation 5
-/
theorem practice194 (P Q R S : Prop) : (P → Q) → (P → R) → (Q → S) → (R → ¬S) → ¬P := by
  intro hpq
  intro hpr
  intro hqs
  intro hrns

  by_cases hp: P
  · intro hp
    exact (hrns (hpr hp)) (hqs (hpq hp))
  · exact hp

/-!
PRACTICE 195 — Combine the propositional tools: variation 6
-/
theorem practice195 (P Q R S : Prop) : ((P ∧ Q) → R) → (P → (Q ∨ S)) → P → (R ∨ S) := by
  intro hpqr
  intro hpqs
  intro p
  by_cases q: Q
  · left
    exact hpqr ⟨p, q⟩
  · right
    have qs : Q ∨ S := by
      exact hpqs p
    cases qs with
    | inl nq =>
      exact (q nq).elim
    | inr s =>
      exact s

/-!
PRACTICE 196 — Combine the propositional tools: variation 7
-/
theorem practice196 (P Q R : Prop) : (P → Q) → (Q → R) → (R → P) → ((P ↔ Q) ∧ (Q ↔ R)) := by
  intro pq
  intro qr
  intro rp
  constructor
  · constructor
    · exact pq
    · intro q
      exact rp (qr q)
  · constructor
    · exact qr
    · intro r
      exact pq (rp r)


/-!
PRACTICE 197 — Combine the propositional tools: variation 8
-/
theorem practice197 (P Q R : Prop) : ((P ∨ Q) → R) ↔ ((P → R) ∧ (Q → R)) := by
  constructor
  · intro pqr
    constructor
    · intro p
      apply pqr
      left
      exact p
    · intro q
      apply pqr
      right
      exact q
  · intro h
    rcases h with ⟨pr, qr⟩
    intro poq
    cases poq with
    | inl p =>
      exact pr p
    | inr q =>
      exact qr q

/-!
PRACTICE 198 — Combine the propositional tools: variation 9
-/
theorem practice198 (P Q R : Prop) : ((P → R) ∧ (Q → R) ∧ (P ∨ Q)) → R := by
  intro h
  rcases h with ⟨pr, qr, pq⟩
  cases pq with
  | inl p =>
    exact pr p
  | inr q =>
    exact qr q

/-!
PRACTICE 199 — Combine the propositional tools: variation 10
-/
theorem practice199 (P Q R S : Prop) : (P ↔ Q) → (Q ↔ R) → (R ↔ S) → ((P ∨ ¬S) ∧ (¬P ∨ S)) := by
  intro pq
  intro qr
  intro rs
  constructor
  · rw [pq, qr, rs]
    exact Classical.em S
  · rw[pq, qr, rs]
    exact (Classical.em S).symm
