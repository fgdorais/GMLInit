import GMLInit.Data.Basic
import GMLInit.Meta.Basic
import GMLInit.Meta.Decidable

namespace Nat

attribute [eliminator] Nat.recAux

section clean

attribute [clean] Nat.zero_eq Nat.add_eq Nat.sub_eq Nat.mul_eq Nat.div_eq Nat.mod_eq Nat.pow_eq Nat.add_zero Nat.mul_zero Nat.pow_zero

@[simp,clean] protected lemma succ_eq (x : Nat) : Nat.succ x = x + 1 := rfl

@[simp,clean] protected lemma pred_eq (x : Nat) : Nat.pred x = x - 1 := rfl

end clean

end Nat
