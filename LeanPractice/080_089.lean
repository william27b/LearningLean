/-!
PRACTICE 080 — Symmetry as an equivalence
-/
theorem practice080 (a b : Nat) : (a = b) ↔ (b = a) := by
  constructor
  · intro h
    exact h.symm
  · intro h
    exact h.symm

/-!
PRACTICE 081 — Equal inputs give equivalent predicates
-/
theorem practice081 (a b : Nat) (A : Nat → Prop) : a = b → (A a ↔ A b) := by
  intro h
  constructor
  · rw [h]
    intro ha
    exact ha
  · rw [h]
    intro hb
    exact hb

/-!
PRACTICE 082 — Write an equality chain with calc
-/
theorem practice082 (a b c : Nat) : a = b → b = c → c = a := by
  intro hab
  intro hbc
  calc
    c = b := hbc.symm
    b = a := hab.symm

/-!
PRACTICE 083 — Rewrite evidence to expose a contradiction
-/
theorem practice083 (a b : Nat) (A : Nat → Prop) : a = b → (A a ∧ ¬A b) → False := by
  intro h
  intro hA
  rw [h] at hA
  exact hA.right hA.left

/-!
PRACTICE 084 — Compute addition by zero on the right
-/
theorem practice084 (n : Nat) : n + 0 = n := by
  rfl

/-!
PRACTICE 085 — Use the left-zero theorem
-/
theorem practice085 (n : Nat) : 0 + n = n := by
  exact Nat.zero_add n

/-!
PRACTICE 086 — Use commutativity
-/
theorem practice086 (a b : Nat) : a + b = b + a := by
  exact Nat.add_comm a b

/-!
PRACTICE 087 — Use associativity
-/
theorem practice087 (a b c : Nat) : (a + b) + c = a + (b + c) := by
  exact Nat.add_assoc a b c

/-!
PRACTICE 088 — Simplify and swap
-/
theorem practice088 (a b : Nat) : a + (b + 0) = b + a := by
  rw [Nat.add_zero]
  rw [Nat.add_comm]

/-!
PRACTICE 089 — Exchange the last two addends
-/
theorem practice089 (a b c : Nat) : (a + b) + c = (a + c) + b := by
  rw [Nat.add_assoc]
  rw [Nat.add_comm b c]
  rw [Nat.add_assoc]
