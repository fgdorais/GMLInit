import GMLInit.Data.Basic
import GMLInit.Logic.Relation
import GMLInit.Meta.Basic

instance : LE Bool := leOfOrd
instance : LT Bool := ltOfOrd

abbrev xor : Bool → Bool → Bool := bne
infixl:30 " ^^ " => xor

namespace Bool
variable (x y z : Bool)

local syntax "bool_tt" (&"using" tactic)? term:max* : tactic
macro_rules
| `(tactic| bool_tt) => `(tactic| rfl)
| `(tactic| bool_tt using $tac) => `(tactic| $tac)
| `(tactic| bool_tt $[using $tac]? $x:term $xs:term*) => `(tactic| cases ($x : Bool) <;> bool_tt $[using $tac]? $xs*)

-- assert not_not : !(!x) = x := by bool_tt x
theorem not_and : !(x && y) = (!x || !y) := by bool_tt x y
theorem not_or : !(x || y) = (!x && !y) := by bool_tt x y

theorem and_false_left : (false && x) = false := by bool_tt x
theorem and_false_right : (x && false) = false := by bool_tt x
theorem and_true_left : (true && x) = x := by bool_tt x
theorem and_true_right : (x && true) = x := by bool_tt x
theorem and_not_self_left : (!x && x) = false := by bool_tt x
theorem and_not_self_right : (x && !x) = false := by bool_tt x
theorem and_idem : (x && x) = x := by bool_tt x
theorem and_comm : (x && y) = (y && x) := by bool_tt x y
theorem and_left_comm : (x && (y && z)) = (y && (x && z)) := by bool_tt x y z
theorem and_right_comm : ((x && y) && z) = ((x && z) && y) := by bool_tt x y z
theorem and_assoc : ((x && y) && z) = (x && (y && z)) := by bool_tt x y z
theorem and_or_distrib_left : (x && (y || z)) = ((x && y) || (x && z)) := by bool_tt x y z
theorem and_or_distrib_right : ((x || y) && z) = ((x && z) || (y && z)) := by bool_tt x y z
theorem and_xor_distrib_left : (x && (y ^^ z)) = ((x && y) ^^ (x && z)) := by bool_tt x y z
theorem and_xor_distrib_right : ((x ^^ y) && z) = ((x && z) ^^ (y && z)) := by bool_tt x y z
theorem and_deMorgan : (!(x && y)) = (!x || !y) := by bool_tt x y
theorem and_eq_true_iff : (x && y) = true ↔ x = true ∧ y = true := by bool_tt using simp x y
theorem and_eq_false_iff : (x && y) = false ↔ x = false ∨ y = false := by bool_tt using simp x y

theorem or_false_left : (false || x) = x := by bool_tt x
theorem or_false_right : (x || false) = x := by bool_tt x
theorem or_true_left : (true || x) = true := by bool_tt x
theorem or_true_right : (x || true) = true := by bool_tt x
theorem or_not_self_left : (!x || x) = true := by bool_tt x
theorem or_not_self_right : (x || !x) = true := by bool_tt x
theorem or_idem : (x || x) = x := by bool_tt x
theorem or_comm : (x || y) = (y || x) := by bool_tt x y
theorem or_left_comm : (x || (y || z)) = (y || (x || z)) := by bool_tt x y z
theorem or_right_comm : ((x || y) || z) = ((x || z) || y) := by bool_tt x y z
theorem or_assoc : ((x || y) || z) = (x || (y || z)) := by bool_tt x y z
theorem or_and_distrib_left : (x || (y && z)) = ((x || y) && (x || z)) := by bool_tt x y z
theorem or_and_distrib_right : ((x && y) || z) = ((x || z) && (y || z)) := by bool_tt x y z
theorem or_deMorgan : (!(x || y)) = (!x && !y) := by bool_tt x y
theorem or_eq_true_iff : (x || y) = true ↔ x = true ∨ y = true := by bool_tt using simp x y
theorem or_eq_false_iff : (x || y) = false ↔ x = false ∧ y = false := by bool_tt using simp x y

theorem xor_false_left : (false ^^ x) = x := by bool_tt x
theorem xor_false_right : (x ^^ false) = x := by bool_tt x
theorem xor_true_left : (true ^^ x) = !x := by bool_tt x
theorem xor_true_right : (x ^^ true) = !x := by bool_tt x
theorem xor_self : (x ^^ x) = false := by bool_tt x
theorem xor_not_self_left : (!x ^^ x) = true := by bool_tt x
theorem xor_not_self_right : (x ^^ !x) = true := by bool_tt x
theorem xor_comm : (x ^^ y) = (y ^^ x) := by bool_tt x y
theorem xor_left_comm : (x ^^ (y ^^ z)) = (y ^^ (x ^^ z)) := by bool_tt x y z
theorem xor_right_comm : ((x ^^ y) ^^ z) = ((x ^^ z) ^^ y) := by bool_tt x y z
theorem xor_assoc : ((x ^^ y) ^^ z) = (x ^^ (y ^^ z)) := by bool_tt x y z

protected abbrev beq := x == y
protected abbrev bne := x != y
protected abbrev bge := x || !y
protected abbrev bgt := x && !y
protected abbrev ble := !x || y
protected abbrev blt := !x && y

theorem beq_eq_decide_eq : Bool.beq x y = decide (x = y) := by bool_tt x y
theorem bne_eq_decide_ne : Bool.bne x y = decide (x ≠ y) := by bool_tt x y
theorem bge_eq_decide_ge : Bool.bge x y = decide (x ≥ y) := by bool_tt x y
theorem bgt_eq_decide_gt : Bool.bgt x y = decide (x > y) := by bool_tt x y
theorem ble_eq_decide_le : Bool.ble x y = decide (x ≤ y) := by bool_tt x y
theorem blt_eq_decide_lt : Bool.blt x y = decide (x < y) := by bool_tt x y

protected theorem le_refl : x ≤ x := by bool_tt x
protected theorem le_trans {x y z : Bool} : x ≤ y → y ≤ z → x ≤ z := by bool_tt using simp x y z
protected theorem le_antisymm {x y : Bool} : x ≤ y → y ≤ x → x = y := by bool_tt using simp x y
protected theorem lt_irrefl : ¬ x < x := by bool_tt using simp x
protected theorem lt_asymm {x y : Bool} : x < y → ¬ y < x := by bool_tt using simp x y
protected theorem lt_trans {x y z : Bool} : x < y → y < z → x < z := by bool_tt using simp x y z
protected theorem lt_of_le_of_lt {x y z : Bool} : x ≤ y → y < z → x < z := by bool_tt using simp x y z
protected theorem lt_of_lt_of_le {x y z : Bool} : x < y → y ≤ z → x < z := by bool_tt using simp x y z
protected theorem le_of_lt {x y : Bool} : x < y → x ≤ y := by bool_tt using simp x y z
protected theorem le_of_eq {x y : Bool} : x = y → x ≤ y := by bool_tt using simp x y z
protected theorem ne_of_lt {x y : Bool} : x < y → x ≠ y := by bool_tt using simp x y z
protected theorem lt_of_le_of_ne {x y : Bool} : x ≤ y → x ≠ y → x < y := by bool_tt using simp x y z
protected theorem le_of_lt_or_eq {x y : Bool} : x < y ∨ x = y → x ≤ y := by bool_tt using simp x y z
protected theorem le_true : x ≤ true := by bool_tt x
protected theorem false_le : false ≤ x := by bool_tt x
protected theorem eq_true_of_true_le {x : Bool} : true ≤ x → x = true := by bool_tt using simp x
protected theorem eq_false_of_le_false {x : Bool} : x ≤ false → x = false := by bool_tt using simp x

instance : Relation.Reflexive (α:=Bool) (.≤.) := ⟨Bool.le_refl⟩
instance : Relation.Irreflexive (α:=Bool) (.<.) := ⟨Bool.lt_irrefl⟩
instance : Relation.Antisymmetric (α:=Bool) (.≤.) := ⟨Bool.le_antisymm⟩
instance : Relation.Asymmetric (α:=Bool) (.<.) := ⟨Bool.lt_asymm⟩
instance : Relation.Transitive (α:=Bool) (.≤.) := ⟨Bool.le_trans⟩
instance : Relation.Transitive (α:=Bool) (.<.) := ⟨Bool.lt_trans⟩
instance : Relation.HTransitive (α:=Bool) (β:=Bool) (γ:=Bool) (.<.) (.≤.) (.<.) := ⟨Bool.lt_of_lt_of_le⟩
instance : Relation.HTransitive (α:=Bool) (β:=Bool) (γ:=Bool) (.≤.) (.<.) (.<.) := ⟨Bool.lt_of_le_of_lt⟩

section
variable (xs ys : List Bool)

abbrev all : Bool := xs.all id

theorem all_nil : all [] = true := rfl
theorem all_one : all [x] = x := Bool.and_true x
theorem all_cons  : all (x :: xs) = (x && all xs) := rfl

theorem all_append : all (xs ++ ys) = (all xs && all ys) := by
  induction xs with
  | nil => rw [List.nil_append, all_nil, true_and]
  | cons x xs ih => rw [List.cons_append, all_cons, all_cons, and_assoc, ih]

theorem all_join (xss : List (List Bool)) : all (xss.map all) = all xss.join := by
  induction xss with
  | nil => rfl
  | cons xs xss ih => rw [List.map, List.join, all_cons, all_append, ih]

abbrev any : Bool := xs.any id

theorem any_nil : any [] = false := rfl
theorem any_one : any [x] = x := Bool.or_false x
theorem any_cons : any (x :: xs) = (x || any xs) := rfl

theorem any_append : any (xs ++ ys) = (any xs || any ys) := by
  induction xs with
  | nil => rw [List.nil_append, any_nil, false_or]
  | cons x xs ih => rw [List.cons_append, any_cons, any_cons, or_assoc, ih]

theorem any_join (xss : List (List Bool)) : any (xss.map any) = any xss.join := by
  induction xss with
  | nil => rfl
  | cons xs xss ih => rw [List.map, List.join, any_cons, any_append, ih]

theorem all_deMorgan : (!all xs) = any (xs.map (!.)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [List.map, all_cons, any_cons, and_deMorgan, ih]

theorem any_deMorgan : (!any xs) = all (xs.map (!.)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [List.map, any_cons, all_cons, or_deMorgan, ih]

end

end Bool
