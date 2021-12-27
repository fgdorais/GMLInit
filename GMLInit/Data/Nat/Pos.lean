import GMLInit.Data.Nat.Basic
import GMLInit.Data.Nat.Order

namespace Nat

class Pos (n : Nat) : Prop where
  pos {} : n > 0

export Pos (pos)

def nonzero [Pos n] : n ≠ 0 := (Nat.ne_of_lt (pos n)).symm

namespace Pos

instance (n : Nat) : Pos (Nat.succ n) where
  pos := Nat.succ_pos n

instance (m n : Nat) [Pos m] : Pos (m + n) where
  pos := Nat.lt_of_lt_of_le (pos m) (Nat.le_add_right m n)

instance (m n : Nat) [Pos n] : Pos (m + n) where
  pos := Nat.lt_of_lt_of_le (pos n) (Nat.le_add_left n m)

instance (m n : Nat) [Pos m] [Pos n] : Pos (m * n) where
  pos := Nat.mul_pos (pos m) (pos n)

instance (n : Nat) : Pos (n ^ 0) where
  pos := pos 1

instance (m n : Nat) [Pos m] : Pos (m ^ n) where
  pos := Nat.pos_pow_of_pos n (pos m)

end Pos

end Nat
