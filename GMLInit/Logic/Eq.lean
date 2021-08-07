import GMLInit.Meta.Basic

def Eq.toHEq {α} : {a a' : α} → a = a' → a ≅ a'
| _, _, rfl => HEq.rfl

def HEq.toEq {α} : {a a' : α} → a ≅ a' → a = a'
| _, _, HEq.rfl => Eq.refl _

def HEq.eqSort : {α β : Sort _} → {a : α} → {b : β} → a ≅ b → α = β
| _, _, _, _, HEq.rfl => Eq.refl _

def Eq.congr.{u,v} {α : Sort u} {β : Sort v} : {f₁ f₂ : α → β} → {a₁ a₂ : α} → f₁ = f₂ → a₁ = a₂ → f₁ a₁ = f₂ a₂
| _, _, _, _, rfl, rfl => rfl

def Eq.dcongr.{u,v} {α : Sort u} {β : α → Sort v} : {f₁ f₂ : (a : α) → β a} → {a₁ a₂ : α} → f₁ = f₂ → a₁ = a₂ → f₁ a₁ ≅ f₂ a₂
| _, _, _, _, rfl, rfl => HEq.rfl

def HEq.congr.{u,v} {φ : Sort u → Sort v} : {f₁ f₂ : {α : Sort u} → α → φ α} → {α₁ α₂ : Sort u} → {a₁ : α₁} → {a₂ : α₂} → @f₁ = @f₂ → a₁ ≅ a₂ → f₁ a₁ ≅ f₂ a₂
| _, _, _, _, _, _, _root_.rfl, HEq.rfl => HEq.rfl

def HEq.dcongr.{u,v} {φ : {α : Sort u} → α → Sort v} : {f₁ f₂ : {α : Sort u} → (a : α) → φ a} → {α₁ α₂ : Sort u} → {a₁ : α₁} → {a₂ : α₂} → @f₁ = @f₂ → a₁ ≅ a₂ → f₁ a₁ ≅ f₂ a₂
| _, _, _, _, _, _, _root_.rfl, HEq.rfl => HEq.rfl

def Eq.congrArg.{u,v} {α : Sort u} {β : Sort v} (f : α → β) : {a₁ a₂ : α} → a₁ = a₂ → f a₁ = f a₂
| _, _, rfl => rfl

def Eq.dcongrArg.{u,v} {α : Sort u} {β : α → Sort v} (f : (a : α) → β a) : {a₁ a₂ : α} → a₁ = a₂ → f a₁ ≅ f a₂
| _, _, rfl => HEq.rfl

def HEq.congrArg.{u,v} {φ : Sort u → Sort v} (f : {α : Sort u} → α → φ α) : {α₁ α₂ : Sort u} → {a₁ : α₁} → {a₂ : α₂} → a₁ ≅ a₂ → f a₁ ≅ f a₂
| _, _, _, _, HEq.rfl => HEq.rfl

def HEq.dcongrArg.{u,v} {φ : {α : Sort u} → α → Sort v} (f : {α : Sort u} → (a : α) → φ a) : {α₁ α₂ : Sort u} → {a₁ : α₁} → {a₂ : α₂} → (ha : a₁ ≅ a₂) → f a₁ ≅ f a₂
| _, _, _, _, HEq.rfl => HEq.rfl

theorem cast_eq_of_heq {α β} : {a : α} → {b : β} → (heq : a ≅ b) → (h : α = β := heq.eqSort) → (h ▸ a : β) = b
| _, _, HEq.rfl, rfl => rfl

theorem eq_cast_of_heq {α β} : {a : α} → {b : β} → (heq : a ≅ b) → (h : α = β := heq.eqSort) → a = (h ▸ b : α)
| _, _, HEq.rfl, rfl => rfl

theorem cast_heq_of_heq_of_eq {α β γ} : {a : α} → {b : β} → (heq : a ≅ b) → (h : α = γ) → (h ▸ a : γ) ≅ b
| _, _, HEq.rfl, rfl => HEq.rfl

theorem heq_cast_of_heq_of_eq {α β γ} : {a : α} → {b : β} → (heq : a ≅ b) → (h : β = γ) → a ≅ (h ▸ b : γ)
| _, _, HEq.rfl, rfl => HEq.rfl

theorem cast_irrel {α β} (h₁ h₂ : α = β) (a : α) : (h₁ ▸ a : β) = (h₂ ▸ a : β) := rfl

@[simp] theorem cast_refl {α} {h : α = α} (a : α) : h ▸ a = a := rfl

@[simp] theorem cast_trans {α β γ} {h₁ : α = β} {h₂ : β = γ} (a : α) : (h₂ ▸ (h₁ ▸ a : β) : γ) = (Eq.trans h₁ h₂ ▸ a : γ) :=
  match h₁, h₂ with | rfl, rfl => rfl

@[simp] theorem cast_congr {α β} {h₁ h₂ : α = β} (a₁ a₂ : α) : (h₁ ▸ a₁ : β) = (h₂ ▸ a₂ : β) ↔ a₁ = a₂ :=
  match h₁, h₂ with | rfl, rfl => Iff.rfl

theorem dcast_eq_of_heq_of_eq {α} {β : α → Sort _} : {a₁ a₂ : α} → {b₁ : β a₁} → {b₂ : β a₂} → b₁ ≅ b₂ → (h : a₁ = a₂) → (h ▸ b₁ : β a₂) = b₂
| _, _, _, _, HEq.rfl, rfl => rfl

theorem eq_dcast_of_heq_of_eq {α} {β : α → Sort _} : {a₁ a₂ : α} → {b₁ : β a₁} → {b₂ : β a₂} → b₁ ≅ b₂ → (h : a₁ = a₂) → b₁ = (h ▸ b₂ : β a₁)
| _, _, _, _, HEq.rfl, rfl => rfl

theorem dcast_heq_of_heq_of_eq_of_eq {α} {β : α → Sort _} : {a₁ a₂ a₃ : α} → {b₁ : β a₁} → {b₂ : β a₂} → b₁ ≅ b₂ → a₁ = a₂ → (h : a₁ = a₃) → (h ▸ b₁ : β a₃) ≅ b₂
| _, _, _, _, _, HEq.rfl, rfl, rfl => HEq.rfl

theorem heq_dcast_of_heq_of_eq_of_eq {α} {β : α → Sort _} : {a₁ a₂ a₃ : α} → {b₁ : β a₁} → {b₂ : β a₂} → b₁ ≅ b₂ → a₁ = a₂ → (h : a₂ = a₃) → b₁ ≅ (h ▸ b₂ : β a₃)
| _, _, _, _, _, HEq.rfl, rfl, rfl => HEq.rfl

theorem dcast_irrel {α} {β : α → Sort _} {a a' : α} (h₁ h₂ : a = a') (b : β a) : (h₁ ▸ b : β a') = (h₂ ▸ b : β a') := rfl

@[simp] theorem dcast_refl {α} {β : α → Sort _} (a : α) {h : a = a} (b : β a) : (h ▸ b) = b := rfl

@[simp] theorem dcast_trans {α} {β : α → Sort _} {a a' a'' : α} {h₁ : a = a'} {h₂ : a' = a''} (b : β a) : (h₂ ▸ (h₁ ▸ b : β a') : β a'') = (Eq.trans h₁ h₂ ▸ b : β a'') :=
  match h₁, h₂ with | rfl, rfl => rfl

@[simp] theorem dcast_congr {α} {β : α → Sort _} {a a' : α} (h₁ h₂ : a = a') (b₁ b₂ : β a) : (h₁ ▸ b₁ : β a') = (h₂ ▸ b₂ : β a') ↔ b₁ = b₂ :=
  match h₁, h₂ with | rfl, rfl => Iff.rfl