import GMLInit.Logic.Basic
import GMLInit.Logic.Connectives
import GMLInit.Logic.ListConnectives

variable (a b : Prop)

instance : [Complemented a] → [Complemented b] → Complemented (a ∨ b)
| Complemented.isTrue ha, _ => Complemented.isTrue (Or.inl ha)
| _, Complemented.isTrue hb => Complemented.isTrue (Or.inr hb)
| Complemented.isFalse na, Complemented.isFalse nb => Complemented.isFalse λ | Or.inl ha => na ha | Or.inr hb => nb hb

instance : [Complemented a] → [Complemented b] → Complemented (a ∧ b)
| Complemented.isFalse na, _ => Complemented.isFalse λ h => na (And.left h)
| _, Complemented.isFalse nb => Complemented.isFalse λ h => nb (And.right h)
| Complemented.isTrue ha, Complemented.isTrue hb => Complemented.isTrue (And.intro ha hb)

instance : [WeaklyComplemented a] → [Complemented b] → Complemented (a → b)
| WeaklyComplemented.isFalse na, _ => Complemented.isTrue λ ha => absurd ha na
| _, Complemented.isTrue hb => Complemented.isTrue λ _ => hb
| WeaklyComplemented.isIrrefutable ha, Complemented.isFalse nb => Complemented.isFalse λ h => ha λ ha => absurd (h ha) nb

instance [WeaklyComplemented a] : Complemented (¬a) := inferInstance

instance [Complemented a] [Complemented b] : Complemented (a ↔ b) :=
  Iff.eq_implies_and_implies a b ▸ inferInstance

instance instComplementedAll : (as : List Prop) → [ComplementedList as] → Complemented (All as)
| [], _ => Complemented.isTrue All.nil
| _::as, inst => match inst.head, @instComplementedAll as inst.tail with
  | Complemented.isFalse hh, _ => Complemented.isFalse λ h => absurd h.head hh
  | _, Complemented.isFalse ht => Complemented.isFalse λ h => absurd h.tail ht
  | Complemented.isTrue hh, Complemented.isTrue ht => Complemented.isTrue (All.cons hh ht)

instance instComplementedAny : (as : List Prop) → [ComplementedList as] → Complemented (Any as)
| [], _ => Complemented.isFalse (λ h => nomatch h)
| _::as, inst => match inst.head, @instComplementedAny as inst.tail with
  | Complemented.isTrue hh, _ => Complemented.isTrue (Any.head hh)
  | _, Complemented.isTrue ht => Complemented.isTrue (Any.tail ht)
  | Complemented.isFalse hh, Complemented.isFalse ht =>
    Complemented.isFalse λ | Any.head h => absurd h hh | Any.tail h => absurd h ht
