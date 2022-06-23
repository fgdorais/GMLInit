import GMLInit.Data.Basic
import GMLInit.Meta.Basic
import GMLInit.Meta.Relation

class EquivBEq (α) [BEq α] : Prop where
  beq_refl (x : α) : (x == x) = true
  beq_subs {x y : α} : (x == y) = true → ∀ z, (x == z) = (y == z)
export EquivBEq (beq_refl beq_subs)

instance (α) [BEq α] [LawfulBEq α] : EquivBEq α where
  beq_refl _ := LawfulBEq.rfl
  beq_subs h _ := eq_of_beq h ▸ rfl

section EquivBEq
variable {α} [inst : BEq α] [self : EquivBEq α]

theorem beq_rfl {x : α} : (x == x) = true := beq_refl x

theorem beq_of_eq {x y : α} : x = y → (x == y) = true := fun | rfl => beq_rfl

theorem beq_symm {x y : α} : (x == y) = true → (y == x) = true := by
  intro hxy
  transitivity (x == x)
  · rw [beq_subs hxy]
  · rw [beq_refl]

theorem beq_comm (x y : α) : (x == y) = (y == x) := by
  match hxy : x == y, hyx : y == x with
  | true, true => rfl
  | true, false => rw [beq_symm hxy] at hyx; contradiction
  | false, true => rw [beq_symm hyx] at hxy; contradiction
  | false, false => rfl

theorem beq_trans {x y z : α} : (x == y) = true → (y == z) = true → (x == z) = true := by
  intro hxy hyz
  transitivity (y == z)
  · rw [beq_subs hxy]
  · rw [hyz]

theorem bne_irrefl (x : α) : ¬ (x != x) = true := by
  rw [Bool.not_eq_true, bne, beq_refl, Bool.not_true]

theorem bne_comm (x y : α) : (x != y) = (y != x) := by
  rw [bne, beq_comm, bne]

theorem bne_symm {x y : α} : (x != y) = true → (y != x) = true := by
  intro h; rw [bne_comm, h]

theorem bne_comp {x y : α} : (x != y) = true → ∀ z, (x != z) = true ∨ (z != y) = true := by
  unfold bne
  intro hxy z
  match hxz : x == z, hyz : z == y with
  | true, true => rw [beq_subs hxz y, hyz] at hxy; contradiction
  | false, _ => left; rfl
  | _, false => right; rfl

instance : Relation.Reflexive (α:=α) (.==.) := ⟨beq_refl⟩
instance : Relation.Symmetric (α:=α) (.==.) := ⟨beq_symm⟩
instance : Relation.Transitive (α:=α) (.==.) := ⟨beq_trans⟩
instance : Relation.Irreflexive (α:=α) (.!=.) := ⟨bne_irrefl⟩
instance : Relation.Symmetric (α:=α) (.!=.) := ⟨bne_symm⟩
instance : Relation.Comparison (α:=α) (.!=.) := ⟨bne_comp⟩

end EquivBEq
