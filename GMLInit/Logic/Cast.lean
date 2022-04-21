import GMLInit.Prelude

theorem eqrec_eq_cast {α} {a b : α} {motive : (b : α) → a = b → Sort _} (t : motive a rfl) (h : a = b) : Eq.rec t h = cast (show motive a rfl = motive b h by cases h; rfl) t := by cases h; rfl

theorem eqndrec_eq_cast {α} {a b : α} {motive : α → Sort _} (t : motive a) (h : a = b) : Eq.ndrec t h = cast (h ▸ rfl) t := by cases h; rfl

theorem cast_refl {α} (a : α) : cast rfl a = a := rfl

theorem cast_trans {α β γ} (h₁ : α = β) (h₂ : β = γ) (a : α) : cast h₂ (cast h₁ a) = cast (Eq.trans h₁ h₂) a := by cases h₁; cases h₂; rfl

theorem cast_heq_eq_heq {α β γ} (h : α = β) (x : α) (y : γ) : (cast h x ≅ y) = (x ≅ y) := by cases h; rfl

theorem heq_cast_eq_heq {α β γ} (h : β = γ) (x : α) (y : β) : (x ≅ cast h y) = (x ≅ y) := by cases h; rfl