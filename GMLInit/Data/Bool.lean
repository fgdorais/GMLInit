import GMLInit.Data.Basic

instance : LE Bool := leOfOrd
instance : LT Bool := ltOfOrd

def xor : Bool → Bool → Bool
| true, true => false
| true, false => true
| false, true => true
| false, false => false
infixl:30 " ^^ " => xor

namespace Bool
variable (x y z : Bool)

syntax "boolTT" term:max* : tactic
macro_rules
| `(tactic|boolTT) => `(tactic|rfl)
| `(tactic|boolTT $x:term $xs:term*) => `(tactic|cases ($x : Bool) <;> boolTT $xs*)

theorem not_not : !(!x) = x := by boolTT x
theorem not_and : !(x && y) = (!x || !y) := by boolTT x y
theorem not_or : !(x || y) = (!x && !y) := by boolTT x y

theorem and_false_left : (false && x) = false := by boolTT x
theorem and_false_right : (x && false) = false := by boolTT x
theorem and_true_left : (true && x) = x := by boolTT x
theorem and_true_right : (x && true) = x := by boolTT x
theorem and_not_self_left : (!x && x) = false := by boolTT x
theorem and_not_self_right : (x && !x) = false := by boolTT x
theorem and_idem : (x && x) = x := by boolTT x
theorem and_comm : (x && y) = (y && x) := by boolTT x y
theorem and_left_comm : (x && (y && z)) = (y && (x && z)) := by boolTT x y z
theorem and_right_comm : ((x && y) && z) = ((x && z) && y) := by boolTT x y z
theorem and_assoc : ((x && y) && z) = (x && (y && z)) := by boolTT x y z
theorem and_or_distrib_left : (x && (y || z)) = ((x && y) || (x && z)) := by boolTT x y z
theorem and_or_distrib_right : ((x || y) && z) = ((x && z) || (y && z)) := by boolTT x y z
theorem and_xor_distrib_left : (x && (y ^^ z)) = ((x && y) ^^ (x && z)) := by boolTT x y z
theorem and_xor_distrib_right : ((x ^^ y) && z) = ((x && z) ^^ (y && z)) := by boolTT x y z
theorem and_deMorgan : !(x && y) = (!x || !y) := by boolTT x y

theorem or_false_left : (false || x) = x := by boolTT x
theorem or_false_right : (x || false) = x := by boolTT x
theorem or_true_left : (true || x) = true := by boolTT x
theorem or_true_right : (x || true) = true := by boolTT x
theorem or_not_self_left : (!x || x) = true := by boolTT x
theorem or_not_self_right : (x || !x) = true := by boolTT x
theorem or_idem : (x || x) = x := by boolTT x
theorem or_comm : (x || y) = (y || x) := by boolTT x y
theorem or_left_comm : (x || (y || z)) = (y || (x || z)) := by boolTT x y z
theorem or_right_comm : ((x || y) || z) = ((x || z) || y) := by boolTT x y z
theorem or_assoc : ((x || y) || z) = (x || (y || z)) := by boolTT x y z
theorem or_and_distrib_left : (x || (y && z)) = ((x || y) && (x || z)) := by boolTT x y z
theorem or_and_distrib_right : ((x && y) || z) = ((x || z) && (y || z)) := by boolTT x y z
theorem or_deMorgan : !(x || y) = (!x && !y) := by boolTT x y

theorem xor_false_left : (false ^^ x) = x := by boolTT x
theorem xor_false_right : (x ^^ false) = x := by boolTT x
theorem xor_true_left : (true ^^ x) = !x := by boolTT x
theorem xor_true_right : (x ^^ true) = !x := by boolTT x
theorem xor_self : (x ^^ x) = false := by boolTT x
theorem xor_not_self_left : (!x ^^ x) = true := by boolTT x
theorem xor_not_self_right : (x ^^ !x) = true := by boolTT x
theorem xor_comm : (x ^^ y) = (y ^^ x) := by boolTT x y
theorem xor_left_comm : (x ^^ (y ^^ z)) = (y ^^ (x ^^ z)) := by boolTT x y z
theorem xor_right_comm : ((x ^^ y) ^^ z) = ((x ^^ z) ^^ y) := by boolTT x y z
theorem xor_assoc : ((x ^^ y) ^^ z) = (x ^^ (y ^^ z)) := by boolTT x y z

protected def beq : Bool → Bool → Bool
| true, true => true
| true, false => false
| false, true => false
| false, false => true
instance : BEq Bool := ⟨Bool.beq⟩

protected abbrev bne := x ^^ y
protected abbrev bge := x || !y
protected abbrev bgt := x && !y
protected abbrev ble := !x || y
protected abbrev blt := !x && y

theorem beq_eq_decide_eq : Bool.beq x y = decide (x = y) := by boolTT x y
theorem xor_eq_decide_ne : Bool.bne x y = decide (x ≠ y) := by boolTT x y
theorem bge_eq_decide_ge : Bool.bge x y = decide (x ≥ y) := by boolTT x y
theorem bgt_eq_decide_gt : Bool.bgt x y = decide (x > y) := by boolTT x y
theorem ble_eq_decide_le : Bool.ble x y = decide (x ≤ y) := by boolTT x y
theorem blt_eq_decide_lt : Bool.blt x y = decide (x < y) := by boolTT x y

end Bool
