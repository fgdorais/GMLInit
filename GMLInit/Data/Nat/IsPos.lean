import GMLInit.Data.Nat.Basic
import GMLInit.Data.Nat.Add
import GMLInit.Data.Nat.Mul
import GMLInit.Data.Nat.Pow
import GMLInit.Data.Nat.Order

namespace Nat

class IsPos (n : Nat) : Prop where
  is_pos {} : n > 0

export IsPos (is_pos)

def is_nonzero (n : Nat) [IsPos n] : n ≠ 0 := (Nat.ne_of_lt (is_pos n)).symm

namespace IsPos

instance (n : Nat) : IsPos (Nat.succ n) where
  is_pos := Nat.succ_pos n

instance (m n : Nat) [IsPos m] : IsPos (m + n) where
  is_pos := Nat.lt_of_lt_of_le (is_pos m) (Nat.le_add_right m n)

instance (m n : Nat) [IsPos n] : IsPos (m + n) where
  is_pos := Nat.lt_of_lt_of_le (is_pos n) (Nat.le_add_left n m)

instance (m n : Nat) [IsPos m] [IsPos n] : IsPos (m * n) where
  is_pos := Nat.mul_pos (is_pos m) (is_pos n)

instance (n : Nat) : IsPos (n ^ 0) where
  is_pos := is_pos 1

instance (m n : Nat) [IsPos m] : IsPos (m ^ n) where
  is_pos := Nat.pos_pow_of_pos n (is_pos m)

end IsPos

macro "nat_is_pos" : tactic => `(tactic| show ((_:Nat) > 0); first | assumption | exact Nat.is_pos _)

macro "nat_is_nonzero" : tactic => `(tactic| show ((_:Nat) ≠ 0); first | assumption | symmetry; assumption | exact Nat.is_nonzero _)

end Nat
