import GMLInit.Logic.Basic
import GMLInit.Logic.Connectives
import GMLInit.Logic.ListConnectives

def Stable.by_contrapositive {a b : Prop} [Stable b] : (¬b → ¬a) → (a → b) :=
  λ h ha => Stable.by_contradiction λ hnb => h hnb ha

def Stable.by_no_counterexample {α} {a : α → Prop} [(x : α) → Stable (a x)] :
  ¬ (∃ x, ¬ a x) → (∀ x, a x) :=
  λ h x => Stable.by_contradiction λ hax => h (Exists.intro x hax)

variable (a b : Prop)

instance [Stable b] : Stable (a → b) :=
  Stable.intro λ hnn ha => Stable.by_contradiction λ hnb => hnn λ h => hnb (h ha)

instance : Stable (¬a) := inferInstanceAs (Stable (a → False))

instance {α} (a : α → Prop) [(x : α) → Stable (a x)] : Stable (∀ x, a x) :=
  Stable.intro λ hnn x => Stable.by_contradiction λ hnax => hnn λ h => hnax (h x)

instance [Stable a] [Stable b] : Stable (a ∧ b) :=
  Stable.intro λ hnn =>
  let ha : a := Stable.by_contradiction λ hna => hnn λ h => hna h.left
  let hb : b := Stable.by_contradiction λ hnb => hnn λ h => hnb h.right
  And.intro ha hb

instance (α) (β : α → Sort _) [(x : α) → StableEq (β x)] : StableEq ((x : α) → β x) :=
  fun _ _ => Stable.intro λ hnn => funext λ _ => Stable.by_contradiction λ hn => hnn λ | rfl => hn rfl

instance (α β) [StableEq β] : StableEq (α → β) := inferInstance

instance instComplementedStableOrLeft [Stable a] : [Complemented b] → Stable (a ∨ b)
| Complemented.isTrue hb => Stable.intro (λ _ => Or.inr hb)
| Complemented.isFalse hb => Stable.intro λ hnn => Or.inl $
  Stable.by_contradiction λ ha => hnn (NOr.intro ha hb)

instance instComplementedStableOrRight [Stable b] : [Complemented a] → Stable (a ∨ b)
| Complemented.isTrue ha => Stable.intro (λ _ => Or.inl ha)
| Complemented.isFalse ha => Stable.intro λ hnn => Or.inr $
  Stable.by_contradiction λ hb => hnn (NOr.intro ha hb)

instance instStableAll : (as : List Prop) → [StableList as] → Stable (All as)
| [], _ => Stable.intro (λ _ => All.nil)
| a::as, StableList.cons ia ias => Stable.intro λ hnn =>
  let ha : a := ia.by_contradiction λ hna => hnn λ h => hna h.head
  let has : All as := (@instStableAll as ias).by_contradiction λ hnas => hnn λ h => hnas h.tail
  All.cons ha has
