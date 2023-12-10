import GMLInit.Data.Basic
import GMLInit.Data.Bool
import GMLInit.Data.Fin.Basic
import GMLInit.Data.Nat
import GMLInit.Meta.Basic

namespace List
open Logic

instance {α} : (xs : List α) → Decidable (xs = [])
| [] => isTrue rfl
| _::_ => isFalse List.noConfusion

instance {α} : (xs : List α) → Decidable ([] = xs)
| [] => isTrue rfl
| _::_ => isFalse List.noConfusion

protected def ext'Aux {α} : (as₁ as₂ : List α) → List Prop
| [], [] => []
| [], _::_ => [False]
| _::_, [] => [False]
| a₁::as₁, a₂::as₂ => (a₁ = a₂) :: List.ext'Aux as₁ as₂

protected theorem ext' {α} : (as₁ as₂ : List α) → All (List.ext'Aux as₁ as₂) → as₁ = as₂
| [], [], _ => rfl
| [], _::_, All.cons h _ => False.elim h
| _::_₁, [], All.cons h _ => False.elim h
| _::as₁, _::as₂, All.cons h hs => h ▸ List.ext' as₁ as₂ hs ▸ rfl

protected theorem ext'Iff {α} (as₁ as₂ : List α) : All (List.ext'Aux as₁ as₂) ↔ as₁ = as₂ := by
  constructor
  exact List.ext' as₁ as₂
  intro h
  cases h
  induction as₁ with
  | nil => exact All.nil
  | cons _ _ H => exact All.cons rfl H

protected theorem ext'Eq {α} (as₁ as₂ : List α) : All (List.ext'Aux as₁ as₂) = (as₁ = as₂) :=
  propext (List.ext'Iff as₁ as₂)

instance (x : α) (xs : List α) : Nat.IsPos (List.length (x :: xs)) := ⟨Nat.zero_lt_succ _⟩

lemma map_pure {α β} (f : α → β) (a : α) : [a].map f = [f a] := rfl

lemma map_comp {α β γ} (f : α → β) (g : β → γ) (as : List α) : as.map (g ∘ f) = (as.map f).map g := (map_map ..).symm

@[simp] lemma pure_bind {α β} (f : α → List β) (a : α) : [a].bind f = f a := by rw [cons_bind, nil_bind, append_nil]

lemma bind_assoc {α β γ} (f : α → List β) (g : β → List γ) (as : List α) : (as.bind f).bind g = as.bind (λ a => (f a).bind g) := by
  induction as with
  | nil => rfl
  | cons a as H => rw [cons_bind, cons_bind, append_bind, H]

lemma all_eq_true_iff_all_true {α} (p : α → Bool) (xs : List α) : xs.all p = true ↔ All (xs.map λ x => p x = true) := by
  induction xs generalizing p with
  | nil => rw [map_nil, all_nil_eq]; simp
  | cons x xs H => rw [all_cons, map_cons, all_cons_eq, ←H, Bool.and_eq_true_iff]

lemma all_eq_false_iff_any_false {α} (p : α → Bool) (xs : List α) : xs.all p = false ↔ Any (xs.map λ x => p x = false) := by
  induction xs generalizing p with
  | nil => rw [map_nil, any_nil_eq]; simp
  | cons x xs H => rw [all_cons, map_cons, any_cons_eq, ←H, Bool.and_eq_false_iff]

lemma any_eq_true_iff_any_true {α} (p : α → Bool) (xs : List α) : xs.any p = true ↔ Any (xs.map λ x => p x = true) := by
  induction xs generalizing p with
  | nil => rw [any_nil, map_nil, any_nil_eq]; simp
  | cons x xs H => rw [any_cons, map_cons, any_cons_eq, ←H, Bool.or_eq_true_iff]

lemma any_eq_false_iff_all_false {α} (p : α → Bool) (xs : List α) : xs.any p = false ↔ All (xs.map λ x => p x = false) := by
  induction xs generalizing p with
  | nil => rw [any_nil, map_nil, all_nil_eq]; simp
  | cons x xs H => rw [any_cons, map_cons, all_cons_eq, ←H, Bool.or_eq_false_iff]

/- take -/

-- assert take_nil {α} (n : Nat) : take n [] = ([] : List α)

theorem take_cons {α} (a : α) (as : List α) (n : Nat) : take (n+1) (a :: as) = a :: take n as := rfl

theorem take_all {α} (as : List α) : take as.length as = as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    rw [length_cons]
    rw [take_cons]
    rw [ih]

theorem take_take (as : List α) (m n) : take m (take n as) = take (min m n) as := by
  induction m, n using Nat.recDiag generalizing as with try trivial
  | succ_succ _ _ ih =>
    cases as with simp [Nat.add_min_add_right]
    | cons _ _ => exact ih ..

theorem take_drop (as : List α) (m n) : take m (drop n as) = drop n (take (m + n) as) := by
  induction n using Nat.recAux generalizing as with try trivial
  | succ n ih =>
    cases as with simp
    | cons a as => exact ih ..

/- drop -/

theorem drop_cons {α} (a : α) (as : List α) (n : Nat) : drop (n+1) (a :: as) = drop n as := rfl

theorem drop_all {α} (as : List α) : as.drop as.length = [] := by
  induction as with
  | nil =>
    rw [drop_nil]
  | cons a as ih =>
    rw [length_cons]
    rw [drop_cons]
    rw [ih]

theorem drop_drop (as : List α) (m n) : drop m (drop n as) = drop (m + n) as := by
  induction n using Nat.recAux generalizing as with try trivial
  | succ _ ih =>
    cases as with simp
    | cons _ _ => exact ih ..

theorem drop_take (as : List α) (m n) : drop m (take n as) = take (n - m) (drop m as) := by
  induction m, n using Nat.recDiagAux generalizing as with simp
  | succ_succ m n ih =>
    cases as with simp
    | cons a as => exact ih ..

theorem drop_get {α} (as : List α) (n : Nat) (hn : n < as.length) : drop n as = as[n] :: drop (n+1) as := by
  induction as generalizing n with
  | nil => absurd hn; exact Nat.not_lt_zero n
  | cons a as ih =>
    match n with
    | 0 =>
      rw [drop_cons]
      rw [drop]
      rw [getElem_eq_get]
      rw [get]
      rw [drop]
    | n+1 =>
      rw [drop_cons]
      rw [drop_cons]
      rw [getElem_eq_get]
      rw [get_cons_succ]
      rw [←getElem_eq_get]
      exact ih ..

/- extract -/

def extract (as : List α) (start stop : Nat) := (as.drop start).take (stop - start)

theorem extract_stop (as : List α) (stop : Nat) : as.extract stop stop = [] := by
  unfold extract
  rw [Nat.sub_self]
  rw [take_zero]

theorem extract_step (as : List α) (start stop : Nat) (hstart : start < stop) (hstop : stop ≤ as.length) :
  as.extract start stop = as.get ⟨start, Nat.lt_of_lt_of_le hstart hstop⟩ :: as.extract (start+1) stop := by
  unfold extract
  induction start, stop using Nat.recDiag generalizing as with
  | zero_zero => contradiction
  | succ_zero start => contradiction
  | zero_succ stop => match as with | a :: as => simp
  | succ_succ start stop ih =>
    match as with
    | a :: as =>
      simp
      rw [ih]
      exact Nat.lt_of_succ_lt_succ hstart
      exact Nat.le_of_succ_le_succ hstop

theorem extract_all (as : List α) : as.extract 0 as.length = as := by
  unfold extract
  rw [Nat.sub_zero]
  rw [List.drop]
  rw [List.take_all]

/- replicate -/

theorem replicate_zero {α} (a : α) : replicate 0 a = [] := rfl

theorem replicate_add {α} (a : α) : (m n : Nat) → replicate n a ++ replicate m a = replicate (m + n) a
| _, 0 => rfl
| _, _+1 => congrArg (a :: .) (replicate_add ..)

end List
