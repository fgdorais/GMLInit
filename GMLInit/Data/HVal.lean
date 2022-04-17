import GMLInit.Data.Basic
import GMLInit.Logic.Eq

inductive HVal.{u} : Type u
| mk {α : Sort u} : α → HVal

protected def HVal.sort : HVal → Type _
| @mk α _ => α

protected def HVal.val : (a : HVal) → a.sort
| mk a => a

theorem HVal.eq_of_val_heq_val : {a b : HVal} → a.val ≅ b.val → a = b
| mk _, mk _, HEq.refl _ => Eq.refl _

theorem HVal.val_heq_val_of_eq : {a b : HVal} → a = b → a.val ≅ b.val
| mk _, mk _, Eq.refl _ => HEq.refl _

theorem HVal.eq_iff_val_heq_val (a b : HVal) : a = b ↔ a.val ≅ b.val :=
  ⟨HVal.val_heq_val_of_eq, HVal.eq_of_val_heq_val⟩

theorem HVal.proof_irrel : (a b : HVal.{0}) → a = b
| @mk a ha, @mk b hb =>
  have h : a = b := propext ⟨λ _ => hb, λ _ => ha⟩
  match a, b, h with
  | _, _, rfl => proofIrrel ha hb ▸ rfl
