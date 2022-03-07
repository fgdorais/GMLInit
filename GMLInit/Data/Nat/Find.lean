import GMLInit.Data.Nat.Extended

namespace Nat
variable (p : Nat → Bool) (h : ∃ n, p n)
open ENat

def find : Nat := toNat (first p) (first.isFinite_of_exists h)

variable {p} {h}

theorem not_prop_of_lt_find {x} : (x < find p h) → ¬ p x := by
  intro hlt h
  unfold find at hlt
  apply Nat.not_ge_of_lt hlt
  apply toNat_le_of_isLE
  apply first.isLE_of
  exact h

theorem find_le_of_prop {x} : p x → find p h ≤ x := by
  intro h
  apply Nat.le_of_not_gt
  intro (hlt:_ < _)
  apply not_prop_of_lt_find hlt
  exact h

variable (p) (h)

theorem find_prop : p (find p h) := by
  have : (first p).isLE (find p h) := by
    unfold find
    rw [isLE_toNat]
  match first.exists_le_of_isLE _ this with
  | ⟨x, hle, hx⟩ =>
    have heq : x = find p h := by
      antisymmetry using (.≤.:Nat→Nat→Prop)
      · exact hle
      · exact find_le_of_prop hx
      done
    rw [←heq, hx]

end Nat
