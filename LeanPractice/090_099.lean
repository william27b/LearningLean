/-!
PRACTICE 090 — Combine a hypothesis with a library fact
-/
theorem practice090 (a b c : Nat) : a = b → c + a = b + c := by
  intro hab
  rw [hab]
  rw [Nat.add_comm]

/-!
PRACTICE 091 — Simplify several zero additions
-/
theorem practice091 (a b : Nat) : (a + 0) + (0 + b) = a + b := by
  simp only [Nat.add_zero, Nat.zero_add]

/-!
PRACTICE 092 — Prove left-zero addition by induction
-/
theorem practice092 (n : Nat) : 0 + n = n := by
  induction n with
  | zero =>
    rw [Nat.add_zero]
  | succ k ih =>
    rw [Nat.add_comm]

/-!
PRACTICE 093 — Move a successor through addition
-/
theorem practice093 (a b : Nat) : Nat.succ a + b = Nat.succ (a + b) := by
  induction b with
  | zero =>
    rw [Nat.add_zero]
  | succ k ih =>
    change a.succ + k + 1 = (a + (k + 1)).succ
    simp only [Nat.succ_eq_add_one]
    rw [Nat.add_assoc]
    rw [Nat.add_add_add_comm]
    rw [← Nat.add_assoc]
    rw [← Nat.add_assoc]

/-!
PRACTICE 094 — Prove addition associativity by induction
-/
theorem practice094 (a b c : Nat) : (a + b) + c = a + (b + c) := by
  induction c with
| zero =>
    rw [Nat.add_zero]
    rw [Nat.add_zero]
  | succ k ih =>
    rw [Nat.add_assoc]

/-!
PRACTICE 095 — Appending an empty list
-/
theorem practice095 (xs : List Nat) : xs ++ [] = xs := by
  induction xs with
  | nil =>
    rfl
  | cons x rest ih =>
    change x :: (rest ++ []) = x :: rest
    rw [ih]

/-!
PRACTICE 096 — Count the length of an append
-/
theorem practice096 (xs ys : List Nat) : (xs ++ ys).length = xs.length + ys.length := by
  induction xs with
  | nil =>
    rw [List.nil_append]
    rw [List.length_nil]
    rw [Nat.zero_add]
  | cons x rest ih =>
    rw [List.cons_append]
    rw [List.length_cons]
    rw [ih]
    rw [List.length_cons]
    rw [Nat.succ_add]

/-!
PRACTICE 097 — Mapping the identity function
-/
theorem practice097 (xs : List Nat) : xs.map (fun n => n) = xs := by
    induction xs with
  | nil =>
    rfl
  | cons x rest ih =>
    rw [List.map_cons]
    rw [ih]

/-!
PRACTICE 098 — Mapping preserves length
-/
theorem practice098 (f : Nat → Nat) (xs : List Nat) : (xs.map f).length = xs.length := by
  induction xs with
  | nil =>
    rfl
  | cons x rest ih =>
    rw [List.map_cons]
    rw [List.length_cons]
    rw [ih]
    rw [List.length_cons]

/-!
PRACTICE 099 — Reversing preserves length
-/
theorem practice099 (xs : List Nat) : xs.reverse.length = xs.length := by
  induction xs with
  | nil =>
    rfl
  | cons x rest ih =>
    rw [List.reverse_cons]
    rw [List.length_cons]
    rw [List.length_append]
    rw [ih]
    rw [List.length_singleton]
