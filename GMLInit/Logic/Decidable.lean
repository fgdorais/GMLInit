import GMLInit.Logic.Basic
import GMLInit.Logic.Connectives
import GMLInit.Logic.ListConnectives

protected def Decidable.casesTFOn {motive : Prop → Sort _} (a : Prop) :
  [Decidable a] → (T : motive True) → (F : motive False) → motive a
| Decidable.isTrue ha, ht, _ => eq_true ha ▸ ht
| Decidable.isFalse na, _, hf => eq_false na ▸ hf

instance instDecidableAll : (as : List Prop) → [DecidableList as] → Decidable (All as)
| [], _ => Decidable.isTrue All.nil
| _::as, DecidableList.cons ia ias  => match ia, @instDecidableAll as ias with
  | Decidable.isTrue ha, Decidable.isTrue has => Decidable.isTrue (All.cons ha has)
  | Decidable.isFalse na, _ => Decidable.isFalse λ | All.cons ha _ => na ha
  | _, Decidable.isFalse nas => Decidable.isFalse λ | All.cons _ has => nas has

instance instDecidableAny : (as : List Prop) → [DecidableList as] → Decidable (Any as)
| [], _ => Decidable.isFalse λ h => nomatch h
| _::as, DecidableList.cons ia ias => match ia, @instDecidableAny as ias with
  | Decidable.isTrue ha, _ => Decidable.isTrue (Any.head ha)
  | _, Decidable.isTrue has => Decidable.isTrue (Any.tail has)
  | Decidable.isFalse na, Decidable.isFalse nas => Decidable.isFalse λ | Any.head ha => na ha | Any.tail has => nas has
