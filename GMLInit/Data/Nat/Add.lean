import GMLInit.Data.Nat.Basic
import GMLInit.Data.Nat.IsPos

namespace Nat

protected theorem add_succ' (x y : Nat) : x + (y + 1) = (x + y) + 1 := Nat.add_succ ..

protected theorem succ_add' (x y : Nat) : (x + 1) + y = (x + y) + 1 := Nat.succ_add ..

protected theorem one_add' (x : Nat) : 1 + x = x + 1 := Nat.one_add ..

protected alias add_cross_comm := Nat.add_add_add_comm

@[deprecated Nat.add_left_cancel]
protected theorem add_left_cancel' (x : Nat) {y z : Nat} : x + y = x + z → y = z := Nat.add_left_cancel

@[deprecated Nat.add_right_cancel]
protected theorem add_right_cancel' (x : Nat) {y z : Nat} : y + x = z + x → y = z := Nat.add_right_cancel

@[deprecated Nat.lt_add_of_pos_left]
protected theorem lt_add_left_of_pos (x y : Nat) (h : y > 0 := by nat_is_pos) : x < y + x :=
  Nat.lt_add_of_pos_left h

@[deprecated Nat.lt_add_of_pos_right]
protected theorem lt_add_right_of_pos (x y : Nat) (h : y > 0 := by nat_is_pos) : x < x + y :=
  Nat.lt_add_of_pos_right h ..

theorem pos_add_left (x y : Nat) (h : x > 0 := by nat_is_pos) : x + y > 0 :=
  Nat.lt_of_le_of_lt (Nat.zero_le _) (Nat.lt_add_of_pos_left h)

theorem pos_add_right (x y : Nat) (h : y > 0 := by nat_is_pos) : x + y > 0 :=
  Nat.lt_of_le_of_lt (Nat.zero_le _) (Nat.lt_add_of_pos_right h)

@[deprecated Nat.le_of_add_le_add_left]
protected theorem le_of_add_le_add_left' (x : Nat) {y z : Nat} : x + y ≤ x + z → y ≤ z := Nat.le_of_add_le_add_left

@[deprecated Nat.le_of_add_le_add_right]
protected theorem le_of_add_le_add_right' (x : Nat) {y z : Nat} : y + x ≤ z + x → y ≤ z := Nat.le_of_add_le_add_right

protected theorem le_iff_add_le_add_left (x y z : Nat) : x ≤ y ↔ z + x ≤ z + y :=
  ⟨λ h => Nat.add_le_add_left h z, Nat.le_of_add_le_add_left⟩

protected theorem le_iff_add_le_add_right (x y z : Nat) : x ≤ y ↔ x + z ≤ y + z :=
  ⟨λ h => Nat.add_le_add_right h z, Nat.le_of_add_le_add_right⟩

@[deprecated Nat.lt_of_add_lt_add_left]
protected theorem lt_of_add_lt_add_left' (x : Nat) {y z : Nat} : x + y < x + z → y < z := Nat.lt_of_add_lt_add_left

@[deprecated Nat.lt_of_add_lt_add_right]
protected theorem lt_of_add_lt_add_right' (x : Nat) {y z : Nat} : y + x < z + x → y < z := Nat.lt_of_add_lt_add_right

protected theorem lt_iff_add_lt_add_left (x y z : Nat) : x < y ↔ z + x < z + y :=
  ⟨λ h => Nat.add_lt_add_left h z, Nat.lt_of_add_lt_add_left⟩

protected theorem lt_iff_add_lt_add_right (x y z : Nat) : x < y ↔ x + z < y + z :=
  ⟨λ h => Nat.add_lt_add_right h z, Nat.lt_of_add_lt_add_right⟩
