import GMLInit.Meta.Prelude

theorem eqNdrec_eq_cast {α} {a b : α} {motive : α → Sort _} (t : motive a) (h : a = b) : Eq.ndrec t h = cast (h ▸ rfl) t := by cases h; rfl

theorem eqNdrec_symm {α} {motive : α → Sort _} {a b : α} (h : a = b) (x : motive a) (y : motive b) : Eq.ndrec x h = y ↔ x = Eq.ndrec y h.symm := by cases h; exact Iff.rfl

@[elim_casts] theorem cast_irrel {α β} (h₁ h₂ : α = β) (a : α) : cast h₁ a = cast h₂ a := rfl

@[elim_casts] theorem cast_refl {α} (a : α) : cast rfl a = a := rfl

@[elim_casts] theorem cast_trans {α β γ} (h₁ : α = β) (h₂ : β = γ) (a : α) : cast h₂ (cast h₁ a) = cast (Eq.trans h₁ h₂) a := by cases h₁; cases h₂; rfl

@[elim_casts] theorem cast_symm {α β} (h : α = β) (a : α) (b : β) : cast h a = b ↔ a = cast h.symm b := by cases h; exact Iff.rfl
