import GMLInit.Logic.Basic

namespace Function

abbrev curry {α} {β : α → Sort _} {γ : (a : α) ×' β a → Sort _} (f : (p : (a : α) ×' β a) → γ p) (a : α) (b : β a) : γ ⟨a, b⟩ := f ⟨a, b⟩

abbrev uncurry {α} {β : α → Sort _} {γ : {a : α} → β a → Sort _} (f : (a : α) → (b : β a) → γ b) (ab : (a : α) ×' β a) : γ ab.snd := f ab.fst ab.snd

syntax (name := curryNum) "curry." noWs num term : term
macro_rules
| `(curry.$n:num $f:term) =>
  match n.isNatLit? with
  | some 0 => `($f)
  | some (n+1) =>
    let n := Lean.Syntax.mkNumLit (toString n)
    `(curry.$n (Function.curry $f))
  | _ => Lean.Macro.throwUnsupported

syntax (name := uncurryNum) "uncurry." noWs num term : term
macro_rules
| `(uncurry.$n:num $f:term) =>
  match n.isNatLit? with
  | some 0 => `($f)
  | some (n+1) =>
    let n := Lean.Syntax.mkNumLit (toString n)
    `(uncurry.$n (Function.uncurry $f))
  | _ => Lean.Macro.throwUnsupported

class InjectiveTC {α β} (f : α → β) : Prop where
  protected inj {lhs rhs} : f lhs = f rhs → lhs = rhs

class Injective {α β} (f : α → β) extends InjectiveTC f : Prop

def inj {α β} (f : α → β) [self : InjectiveTC f] {lhs rhs} : f lhs = f rhs → lhs = rhs := self.inj

theorem inj_iff {α β} (f : α → β) [InjectiveTC f] {lhs rhs : α} : f lhs = f rhs ↔ lhs = rhs := Iff.intro (inj f) (congrArg f)

theorem inj_eq {α β} (f : α → β) [InjectiveTC f] {lhs rhs : α} : (f lhs = f rhs) = (lhs = rhs) := propext (inj_iff f)

namespace Injective

instance {α β γ} (g : α → β) (f : β → γ) [Injective f] [InjectiveTC g] : InjectiveTC (λ x => f (g x)) where
  inj h := inj g (inj f h)

instance (α) : Injective (id : α → α) where inj := id
instance (α β) : Injective (Sum.inl : α → Sum α β) where inj | rfl => rfl
instance (α β) : Injective (Sum.inr : β → Sum α β) where inj | rfl => rfl
instance (α β) (b : β) : Injective ((.,b) : α → α × β) where inj | rfl => rfl
instance (α β) (a : α) : Injective ((a,.) : β → α × β) where inj | rfl => rfl
instance (α) (β : α → Type _) (a : α) : Injective (Sigma.mk a : β a → Sigma β) where inj | rfl => rfl
instance (a : α) : Injective (a::.) where inj | rfl => rfl
instance (as : List α) : Injective (.::as) where inj | rfl => rfl
instance (α) : Injective (some : α → Option α) where inj | rfl => rfl
instance : Injective Nat.succ where inj | rfl => rfl
instance (n : Nat) : Injective (n+.: Nat → Nat) where inj := Nat.add_left_cancel
instance (n : Nat) : Injective (.+n: Nat → Nat) where inj := Nat.add_right_cancel

end Injective

end Function
