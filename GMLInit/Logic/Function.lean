import GMLInit.Logic.Basic

namespace Function

abbrev curry {α β γ} (f : α × β → γ) (a : α) (b : β) := f (a,b)

abbrev uncurry {α β γ} (f : α → β → γ) (ab : α × β) := f ab.fst ab.snd

abbrev dcurry {α} {β : α → Sort _} {γ : (a : α) × β a → Sort _} (f : (p : (a : α) × β a) → γ p) (a : α) (b : β a) : γ ⟨a, b⟩ := f ⟨a, b⟩

abbrev duncurry {α} {β : α → Sort _} {γ : {a : α} → β a → Sort _} (f : (a : α) → (b : β a) → γ b) (ab : (a : α) × β a) : γ ab.snd := f ab.fst ab.snd

class InjectiveT {α β} (f : α → β) : Prop where
  protected elim {a₁ a₂} : f a₁ = f a₂ → a₁ = a₂

class Injective {α β} (f : α → β) extends InjectiveT f : Prop

protected instance Injective.id {α} : Injective (@id α) where
  elim := id

protected instance InjectiveT.comp {α β γ} (f : α → β) (g : β → γ) [InjectiveT f] [Injective g] : InjectiveT (g ∘ f) where
  elim {x₁ x₂} h := InjectiveT.elim (InjectiveT.elim h)

protected def Injective.comp {α β γ} (f : α → β) (g : β → γ) [Injective f] [Injective g] : Injective (g ∘ f) where
  toInjectiveT := inferInstance

theorem injection {α β} (f : α → β) [InjectiveT f] {a₁ a₂ : α} : f a₁ = f a₂ → a₁ = a₂ := InjectiveT.elim

theorem injectionIff {α β} (f : α → β) [InjectiveT f] {a₁ a₂ : α} : f a₁ = f a₂ ↔ a₁ = a₂ := Iff.intro InjectiveT.elim (congrArg f)

theorem injectionEq {α β} (f : α → β) [InjectiveT f] {a₁ a₂ : α} : (f a₁ = f a₂) = (a₁ = a₂) := propext (injectionIff f)

instance : Injective Nat.succ where elim := Nat.succ.inj
instance (α) : Injective (@some α) where elim := Option.some.inj
instance (α β) : Injective (@Sum.inl α β) where elim := Sum.inl.inj
instance (α β) : Injective (@Sum.inr α β) where elim := Sum.inr.inj
instance (a : α) : Injective (a::.) where elim := λ h => (List.cons.inj h).2
instance (as : List α) : Injective (.::as) where elim := λ h => (List.cons.inj h).1
instance (α β) (a : α) : Injective (Prod.mk a : β → α × β) where elim := λ h => (Prod.mk.inj h).2
instance (α β) (b : β) : Injective (Prod.mk . b : α → α × β) where elim := λ h => (Prod.mk.inj h).1

end Function
