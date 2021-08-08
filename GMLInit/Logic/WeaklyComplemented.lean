import GMLInit.Logic.Basic
import GMLInit.Logic.Complemented
import GMLInit.Logic.Connectives
import GMLInit.Logic.ListConnectives

variable (a b : Prop)

instance instWeaklyComplementedOr : [WeaklyComplemented a] → [WeaklyComplemented b] → WeaklyComplemented (a ∨ b)
| WeaklyComplemented.isIrrefutable ha, _ => WeaklyComplemented.isIrrefutable λ h => ha λ ha => h (Or.inl ha)
| _, WeaklyComplemented.isIrrefutable hb => WeaklyComplemented.isIrrefutable λ h => hb λ hb => h (Or.inr hb)
| WeaklyComplemented.isFalse ha, WeaklyComplemented.isFalse hb => WeaklyComplemented.isFalse λ | Or.inl h => ha h | Or.inr h => hb h

instance instWeaklyComplementedAnd : [WeaklyComplemented a] → [WeaklyComplemented b] → WeaklyComplemented (a ∧ b)
| WeaklyComplemented.isFalse ha, _ => WeaklyComplemented.isFalse λ h => ha (And.left h)
| _, WeaklyComplemented.isFalse hb => WeaklyComplemented.isFalse λ h => hb (And.right h)
| WeaklyComplemented.isIrrefutable ha, WeaklyComplemented.isIrrefutable hb => WeaklyComplemented.isIrrefutable λ h => ha λ ha => hb λ hb => h (And.intro ha hb)

instance instWeaklyComplementedArrow : [WeaklyComplemented a] → [WeaklyComplemented b] → WeaklyComplemented (a → b)
| WeaklyComplemented.isFalse ha, _ => WeaklyComplemented.isIrrefutable λ h => h λ h => absurd h ha
| _, WeaklyComplemented.isIrrefutable hb => WeaklyComplemented.isIrrefutable λ h => hb λ hb => h λ _ => hb
| WeaklyComplemented.isIrrefutable ha, WeaklyComplemented.isFalse hb => WeaklyComplemented.isFalse λ h => ha λ ha => hb (h ha)

instance instWeaklyComplementedIff [WeaklyComplemented a] [WeaklyComplemented b] : WeaklyComplemented (a ↔ b) :=
  Iff.eq_implies_and_implies a b ▸ inferInstance

instance instWeaklyComplementedAll : (as : List Prop) → [WeaklyComplementedList as] → WeaklyComplemented (All as)
| [], _ => WeaklyComplemented.isIrrefutable (absurd All.nil)
| a::as, inst => match inst.head, @instWeaklyComplementedAll as inst.tail with
  | WeaklyComplemented.isFalse hh, _ => WeaklyComplemented.isFalse λ h => absurd h.head hh
  | _, WeaklyComplemented.isFalse ht => WeaklyComplemented.isFalse λ h => absurd h.tail ht
  | WeaklyComplemented.isIrrefutable hh, WeaklyComplemented.isIrrefutable ht => WeaklyComplemented.isIrrefutable λ h => hh λ hh => ht λ ht => h (All.cons hh ht)

instance instWeaklyComplementedAny : (as : List Prop) → [WeaklyComplementedList as] → WeaklyComplemented (Any as)
| [], _ => WeaklyComplemented.isFalse (λ h => nomatch h)
| a::as, inst => match inst.head, @instWeaklyComplementedAny as inst.tail with
  | WeaklyComplemented.isIrrefutable hh, _ => WeaklyComplemented.isIrrefutable λ h => hh λ hh => h (Any.head hh)
  | _, WeaklyComplemented.isIrrefutable ht => WeaklyComplemented.isIrrefutable λ h => ht λ ht => h (Any.tail ht)
  | WeaklyComplemented.isFalse hh, WeaklyComplemented.isFalse ht =>
    WeaklyComplemented.isFalse λ | Any.head h => absurd h hh | Any.tail h => absurd h ht
