import GMLInit.Logic.Basic
import GMLInit.Logic.Decidable
import GMLInit.Logic.Connectives
import GMLInit.Logic.ListConnectives

variable (a b : Prop)

instance : [WeaklyDecidable a] → [WeaklyDecidable b] → WeaklyDecidable (a ∨ b)
| WeaklyDecidable.isIrrefutable ha, _ => WeaklyDecidable.isIrrefutable λ h => ha λ ha => h (Or.inl ha)
| _, WeaklyDecidable.isIrrefutable hb => WeaklyDecidable.isIrrefutable λ h => hb λ hb => h (Or.inr hb)
| WeaklyDecidable.isFalse ha, WeaklyDecidable.isFalse hb => WeaklyDecidable.isFalse λ | Or.inl h => ha h | Or.inr h => hb h

instance : [WeaklyDecidable a] → [WeaklyDecidable b] → WeaklyDecidable (a ∧ b)
| WeaklyDecidable.isFalse ha, _ => WeaklyDecidable.isFalse λ h => ha (And.left h)
| _, WeaklyDecidable.isFalse hb => WeaklyDecidable.isFalse λ h => hb (And.right h)
| WeaklyDecidable.isIrrefutable ha, WeaklyDecidable.isIrrefutable hb => WeaklyDecidable.isIrrefutable λ h => ha λ ha => hb λ hb => h (And.intro ha hb)

instance : [WeaklyDecidable a] → [WeaklyDecidable b] → WeaklyDecidable (a → b)
| WeaklyDecidable.isFalse ha, _ => WeaklyDecidable.isIrrefutable λ h => h λ h => absurd h ha
| _, WeaklyDecidable.isIrrefutable hb => WeaklyDecidable.isIrrefutable λ h => hb λ hb => h λ _ => hb
| WeaklyDecidable.isIrrefutable ha, WeaklyDecidable.isFalse hb => WeaklyDecidable.isFalse λ h => ha λ ha => hb (h ha)

instance : [WeaklyDecidable a] → [Decidable b] → Decidable (a → b)
| WeaklyDecidable.isFalse ha, _ => Decidable.isTrue λ h => absurd h ha
| _, Decidable.isTrue hb => Decidable.isTrue λ _ => hb
| WeaklyDecidable.isIrrefutable ha, Decidable.isFalse hb => Decidable.isFalse λ h => ha λ ha => absurd (h ha) hb

instance [WeaklyDecidable a] [WeaklyDecidable b] : WeaklyDecidable (a ↔ b) :=
  Iff.eq_implies_and_implies a b ▸ inferInstance

instance instWeaklyDecidableAll : (as : List Prop) → [WeaklyDecidableList as] → WeaklyDecidable (All as)
| [], _ => WeaklyDecidable.isIrrefutable (absurd All.nil)
| _::as, inst => match inst.head, @instWeaklyDecidableAll as inst.tail with
  | WeaklyDecidable.isFalse hh, _ => WeaklyDecidable.isFalse λ h => absurd h.head hh
  | _, WeaklyDecidable.isFalse ht => WeaklyDecidable.isFalse λ h => absurd h.tail ht
  | WeaklyDecidable.isIrrefutable hh, WeaklyDecidable.isIrrefutable ht => WeaklyDecidable.isIrrefutable λ h => hh λ hh => ht λ ht => h (All.cons hh ht)

instance instWeaklyDecidableAny : (as : List Prop) → [WeaklyDecidableList as] → WeaklyDecidable (Any as)
| [], _ => WeaklyDecidable.isFalse (λ h => nomatch h)
| _::as, inst => match inst.head, @instWeaklyDecidableAny as inst.tail with
  | WeaklyDecidable.isIrrefutable hh, _ => WeaklyDecidable.isIrrefutable λ h => hh λ hh => h (Any.head hh)
  | _, WeaklyDecidable.isIrrefutable ht => WeaklyDecidable.isIrrefutable λ h => ht λ ht => h (Any.tail ht)
  | WeaklyDecidable.isFalse hh, WeaklyDecidable.isFalse ht => WeaklyDecidable.isFalse λ | Any.head h => absurd h hh | Any.tail h => absurd h ht
