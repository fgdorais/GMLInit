import GMLInit.Data.Basic
import GMLInit.Data.Bool
import GMLInit.Data.Nat
import GMLInit.Logic.ListConnectives
import GMLInit.Meta.Basic

namespace List

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
  constr
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

lemma map_comp {α β γ} (f : α → β) (g : β → γ) (as : List α) : as.map (g ∘ f) = (as.map f).map g := by
  symmetry
  exact map_map ..

@[simp] lemma pure_bind {α β} (f : α → List β) (a : α) : [a].bind f = f a := by rw [cons_bind, nil_bind, append_nil]

lemma bind_assoc {α β γ} (f : α → List β) (g : β → List γ) (as : List α) : (as.bind f).bind g = as.bind (λ a => (f a).bind g) := by
  induction as with
  | nil => rfl
  | cons a as H => rw [cons_bind, cons_bind, append_bind, H]

lemma all_eq_true_iff_all_true {α} (p : α → Bool) (xs : List α) : xs.all p = true ↔ All (xs.map λ x => p x = true) := by
  induction xs generalizing p with
  | nil => rw [all_nil, map_nil]; simp
  | cons x xs H => rw [all_cons, map_cons, All.cons_eq, ←H, Bool.and_eq_true_iff]

lemma all_eq_false_iff_any_false {α} (p : α → Bool) (xs : List α) : xs.all p = false ↔ Any (xs.map λ x => p x = false) := by
  induction xs generalizing p with
  | nil => rw [all_nil, map_nil]; simp
  | cons x xs H => rw [all_cons, map_cons, Any.cons_eq, ←H, Bool.and_eq_false_iff]

lemma any_eq_true_iff_any_true {α} (p : α → Bool) (xs : List α) : xs.any p = true ↔ Any (xs.map λ x => p x = true) := by
  induction xs generalizing p with
  | nil => rw [any_nil, map_nil, Any.nil_eq]; simp
  | cons x xs H => rw [any_cons, map_cons, Any.cons_eq, ←H, Bool.or_eq_true_iff]

lemma any_eq_false_iff_all_false {α} (p : α → Bool) (xs : List α) : xs.any p = false ↔ All (xs.map λ x => p x = false) := by
  induction xs generalizing p with
  | nil => rw [any_nil, map_nil, All.nil_eq]; simp
  | cons x xs H => rw [any_cons, map_cons, All.cons_eq, ←H, Bool.or_eq_false_iff]

/- take -/

theorem take_nil {α} (n : Nat) : take n [] = ([] : List α) := by cases n <;> rfl

theorem take_cons {α} (a : α) (as : List α) (n : Nat) : take (n+1) (a :: as) = a :: take n as := rfl

theorem take_zero {α} (as : List α) : take 0 as = [] := rfl

theorem take_all {α} (as : List α) : take as.length as = as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    rw [length_cons]
    rw [take_cons]
    rw [ih]

/- drop -/

theorem drop_cons {α} (a : α) (as : List α) (n : Nat) : drop (n+1) (a :: as) = drop n as := rfl

theorem drop_zero {α} (as : List α) : drop 0 as = as := rfl

theorem drop_all {α} (as : List α) : as.drop as.length = [] := by
  induction as with
  | nil =>
    rw [drop_nil]
  | cons a as ih =>
    rw [length_cons]
    rw [drop_cons]
    rw [ih]

theorem drop_get {α} (as : List α) (n : Nat) (hn : n < as.length) : drop n as = as[n] :: drop (n+1) as := by
  induction as generalizing n with
  | nil => absurd hn; exact Nat.not_lt_zero n
  | cons a as ih =>
    match n with
    | 0 =>
      rw [drop_cons]
      rw [drop]
      rw [getElem_eq_get]
      rw [get_cons_zero]
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

/- dropLast -/

theorem length_dropLast (as : List α) : as.dropLast.length = as.length - 1 := by
  cases as <;> simp

private theorem get_dropLast.aux {as : List α} {i : Nat} : i < as.dropLast.length → i < as.length :=
  fun h => Nat.lt_of_lt_of_le h (length_dropLast as ▸ Nat.pred_le as.length)

theorem get_dropLast (as : List α) (i : Fin as.dropLast.length) :
  as.dropLast.get i = as.get ⟨i.val, get_dropLast.aux i.isLt⟩ := by
  induction as with
  | nil => exact nomatch i
  | cons a as ih =>
    match as, i with
    | [], i => exact nomatch i
    | _ :: _, ⟨0, _⟩ => simp [dropLast]
    | _ :: _, ⟨i+1, hi⟩ => simp [dropLast, ih]

/- all/any -/

theorem not_all_eq_any_not (p : α → Bool) (as : List α) : (!as.all p) = as.any fun a => !p a := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    rw [all_cons]
    rw [any_cons]
    rw [Bool.not_and]
    rw [ih]

theorem not_any_eq_all_not (p : α → Bool) (as : List α) : (!as.any p) = as.all fun a => !p a := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    rw [any_cons]
    rw [all_cons]
    rw [Bool.not_or]
    rw [ih]

theorem or_all_distrib_left (p : α → Bool) (q : Bool) (as : List α) : (q || as.all p) = as.all fun a => q || p a := by
  induction as with
  | nil =>
    rw [all_nil]
    rw [all_nil]
    rw [Bool.or_true]
  | cons a as ih =>
    rw [all_cons]
    rw [all_cons]
    rw [Bool.or_and_distrib_left]
    rw [ih]

theorem or_all_distrib_right (p : α → Bool) (q : Bool) (as : List α) : (as.all p || q) = as.all fun a => p a || q := by
  induction as with
  | nil =>
    rw [all_nil]
    rw [all_nil]
    rw [Bool.true_or]
  | cons a as ih =>
    rw [all_cons]
    rw [all_cons]
    rw [Bool.or_and_distrib_right]
    rw [ih]

theorem and_any_distrib_left (p : α → Bool) (q : Bool) (as : List α) : (q && as.any p) = as.any fun a => q && p a := by
  induction as with
  | nil =>
    rw [any_nil]
    rw [any_nil]
    rw [Bool.and_false]
  | cons a as ih =>
    rw [any_cons]
    rw [any_cons]
    rw [Bool.and_or_distrib_left]
    rw [ih]

theorem and_any_distrib_right (p : α → Bool) (q : Bool) (as : List α) : (as.any p && q) = as.any fun a => p a && q := by
  induction as with
  | nil =>
    rw [any_nil]
    rw [any_nil]
    rw [Bool.false_and]
  | cons a as ih =>
    rw [any_cons]
    rw [any_cons]
    rw [Bool.and_or_distrib_right]
    rw [ih]

end List
