import GMLInit.Data.Basic
import GMLInit.Data.Ord
import GMLInit.Logic.Relation
import GMLInit.Meta.Basic

-- assert xor : Bool → Bool → Bool := bne
-- assert infixl:30 " ^^ " => xor

namespace Bool
variable (x y z : Bool)

local syntax "bool_tt" (&"using" tactic)? (colGt term:max)* : tactic
macro_rules
| `(tactic| bool_tt) => `(tactic| rfl)
| `(tactic| bool_tt using $tac) => `(tactic| $tac)
| `(tactic| bool_tt $[using $tac]? $x:term $xs:term*) => `(tactic| cases ($x : Bool) <;> bool_tt $[using $tac]? $xs*)

instance : LinearOrd Bool where
  symm (x y) := by bool_tt x y
  le_trans {x y z} _ _ _ := by bool_tt using contradiction x y z
  eq_strict {x y} _ := by bool_tt using first | rfl | contradiction x y

instance : LE Bool := leOfOrd
instance : LT Bool := ltOfOrd

-- assert eq_iff_iff : x = y ↔ (x ↔ y)

-- assert not_not : !(!x) = x
-- assert not_and : (!(x && y)) = (!x || !y)
-- assert not_or : (!(x || y)) = (!x && !y)

-- assert and_false_left : (false && x) = false
-- assert and_false_right : (x && false) = false
-- assert and_true_left : (true && x) = x
-- assert and_true_right : (x && true) = x
-- assert and_not_self_left : (!x && x) = false
-- assert and_not_self_right : (x && !x) = false
theorem and_idem : (x && x) = x := and_self ..
-- assert and_comm : (x && y) = (y && x)
-- assert and_left_comm : (x && (y && z)) = (y && (x && z))
-- assert and_right_comm : ((x && y) && z) = ((x && z) && y)
-- assert and_assoc : ((x && y) && z) = (x && (y && z))
-- assert and_or_distrib_left : (x && (y || z)) = ((x && y) || (x && z))
-- assert and_or_distrib_right : ((x || y) && z) = ((x && z) || (y && z))
-- assert and_xor_distrib_left : (x && (y ^^ z)) = ((x && y) ^^ (x && z))
-- assert and_xor_distrib_right : ((x ^^ y) && z) = ((x && z) ^^ (y && z))
-- assert and_deMorgan : (!(x && y)) = (!x || !y)
-- assert and_eq_true_iff : (x && y) = true ↔ x = true ∧ y = true
-- assert and_eq_false_iff : (x && y) = false ↔ x = false ∨ y = false

-- assert or_false_left : (false || x) = x
-- assert or_false_right : (x || false) = x
-- assert or_true_left : (true || x) = true
-- assert or_true_right : (x || true) = true
-- assert or_not_self_left : (!x || x) = true
-- assert or_not_self_right : (x || !x) = true
theorem or_idem : (x || x) = x := or_self ..
-- assert or_comm : (x || y) = (y || x)
-- assert or_left_comm : (x || (y || z)) = (y || (x || z))
-- assert or_right_comm : ((x || y) || z) = ((x || z) || y)
-- assert or_assoc : ((x || y) || z) = (x || (y || z))
-- assert or_and_distrib_left : (x || (y && z)) = ((x || y) && (x || z))
-- assert or_and_distrib_right : ((x && y) || z) = ((x || z) && (y || z))
-- assert or_deMorgan : (!(x || y)) = (!x && !y)
-- assert or_eq_true_iff : (x || y) = true ↔ x = true ∨ y = true
-- assert or_eq_false_iff : (x || y) = false ↔ x = false ∧ y = false

-- assert xor_false_left : (false ^^ x) = x
-- assert xor_false_right : (x ^^ false) = x
-- assert xor_true_left : (true ^^ x) = !x
-- assert xor_true_right : (x ^^ true) = !x
-- assert xor_self : (x ^^ x) = false
-- assert xor_not_self_left : (!x ^^ x) = true
-- assert xor_not_self_right : (x ^^ !x) = true
-- assert xor_comm : (x ^^ y) = (y ^^ x)
-- assert xor_left_comm : (x ^^ (y ^^ z)) = (y ^^ (x ^^ z))
-- assert xor_right_comm : ((x ^^ y) ^^ z) = ((x ^^ z) ^^ y)
-- assert xor_assoc : ((x ^^ y) ^^ z) = (x ^^ (y ^^ z))

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

-- assert le_refl : x ≤ x
-- assert le_trans {x y z : Bool} : x ≤ y → y ≤ z → x ≤ z
-- assert le_antisymm {x y : Bool} : x ≤ y → y ≤ x → x = y
-- assert lt_irrefl : ¬ x < x
-- assert lt_asymm {x y : Bool} : x < y → ¬ y < x
-- assert lt_trans {x y z : Bool} : x < y → y < z → x < z
-- assert lt_of_le_of_lt {x y z : Bool} : x ≤ y → y < z → x < z
-- assert lt_of_lt_of_le {x y z : Bool} : x < y → y ≤ z → x < z
-- assert le_of_lt {x y : Bool} : x < y → x ≤ y
-- assert le_of_eq {x y : Bool} : x = y → x ≤ y
-- assert ne_of_lt {x y : Bool} : x < y → x ≠ y
-- assert lt_of_le_of_ne {x y : Bool} : x ≤ y → x ≠ y → x < y
-- assert le_of_lt_or_eq {x y : Bool} : x < y ∨ x = y → x ≤ y
-- assert le_true : x ≤ true
-- assert false_le : false ≤ x
-- assert eq_true_of_true_le {x : Bool} : true ≤ x → x = true-- assert eq_false_of_le_false {x : Bool} : x ≤ false → x = false

instance : Relation.Reflexive (α:=Bool) (.≤.) := ⟨Bool.le_refl⟩
instance : Relation.Irreflexive (α:=Bool) (.<.) := ⟨Bool.lt_irrefl⟩
instance : Relation.Antisymmetric (α:=Bool) (.≤.) := ⟨Bool.le_antisymm⟩
instance : Relation.Asymmetric (α:=Bool) (.<.) := ⟨Bool.lt_asymm⟩
instance : Relation.Transitive (α:=Bool) (.≤.) := ⟨Bool.le_trans⟩
instance : Relation.Transitive (α:=Bool) (.<.) := ⟨Bool.lt_trans⟩
instance : Relation.HTransitive (α:=Bool) (β:=Bool) (γ:=Bool) (.<.) (.≤.) (.<.) := ⟨Bool.lt_of_lt_of_le⟩
instance : Relation.HTransitive (α:=Bool) (β:=Bool) (γ:=Bool) (.≤.) (.<.) (.<.) := ⟨Bool.lt_of_le_of_lt⟩

-- assert not_inj {x y : Bool} : (!x) = (!y) → x = y
-- assert and_or_inj_right {m x y : Bool}: (x && m) = (y && m) → (x || m) = (y || m) → x = y
-- assert and_or_inj_left {m x y : Bool} : (m && x) = (m && y) → (m || x) = (m || y) → x = y

section
variable (xs ys : List Bool)

-- assert all : Bool := xs.all id

-- assert all_nil : all [] = true
-- assert all_one : all [x] = x
-- assert all_cons  : all (x :: xs) = (x && all xs)

-- assert all_append : all (xs ++ ys) = (all xs && all ys)

-- assert all_join (xss : List (List Bool)) : all (xss.map all) = all xss.join

-- assert any : Bool := xs.any id

-- assert any_nil : any [] = false
-- assert any_one : any [x] = x
-- assert any_cons : any (x :: xs) = (x || any xs)

-- assert any_append : any (xs ++ ys) = (any xs || any ys)
-- assert any_join (xss : List (List Bool)) : any (xss.map any) = any xss.join
-- assert all_deMorgan : (!all xs) = any (xs.map (!.))
-- assert any_deMorgan : (!any xs) = all (xs.map (!.))

end

end Bool
