import GMLInit.Logic.Basic

namespace Function

abbrev curry {α β γ} (f : α × β → γ) (a : α) (b : β) := f (a,b)

abbrev uncurry {α β γ} (f : α → β → γ) (ab : α × β) := f ab.fst ab.snd

abbrev dcurry {α} {β : α → Sort _} {γ : (a : α) × β a → Sort _} (f : (p : (a : α) × β a) → γ p) (a : α) (b : β a) : γ ⟨a, b⟩ := f ⟨a, b⟩

abbrev duncurry {α} {β : α → Sort _} {γ : {a : α} → β a → Sort _} (f : (a : α) → (b : β a) → γ b) (ab : (a : α) × β a) : γ ab.snd := f ab.fst ab.snd

class InjectiveT {α β} (f : α → β) : Prop where
  protected inj {a₁ a₂} : f a₁ = f a₂ → a₁ = a₂

export InjectiveT (inj)

abbrev injection {α β} (f : α → β) [InjectiveT f] {lhs rhs : α} : f lhs = f rhs → lhs = rhs := inj

theorem injectionIff {α β} (f : α → β) [InjectiveT f] {a₁ a₂ : α} : f a₁ = f a₂ ↔ a₁ = a₂ := Iff.intro inj (congrArg f)

theorem injectionEq {α β} (f : α → β) [InjectiveT f] {a₁ a₂ : α} : (f a₁ = f a₂) = (a₁ = a₂) := propext (injectionIff f)

class Injective {α β} (f : α → β) extends InjectiveT f : Prop

protected instance InjectiveT.comp {α β γ} (g : α → β) (f : β → γ) [Injective f] [InjectiveT g] : InjectiveT (f $ g .) where
  inj {x₁ x₂} h := inj (inj h)

instance (α) : Injective (id : α → α) where inj := id
instance (α β) : Injective (Sum.inl : α → Sum α β) where inj := Sum.inl.inj
instance (α β) : Injective (Sum.inr : β → Sum α β) where inj := Sum.inr.inj
instance (α β) (a : α) : Injective ((a,.) : β → α × β) where inj := λ h => (Prod.mk.inj h).right
instance (α β) (b : β) : Injective ((.,b) : α → α × β) where inj := λ h => (Prod.mk.inj h).left
instance (a : α) : Injective (a::.) where inj := λ h => (List.cons.inj h).2
instance (as : List α) : Injective (.::as) where inj := λ h => (List.cons.inj h).left
instance (α) : Injective (some : α → Option α) where inj := Option.some.inj
instance : Injective Nat.succ where inj := Nat.succ.inj
instance (n : Nat) : Injective (n+.: Nat → Nat) where inj := Nat.add_left_cancel
instance (n : Nat) : Injective (.+n: Nat → Nat) where inj := Nat.add_right_cancel

end Function
