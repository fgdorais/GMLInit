import GMLInit.Meta.Basic

lemma heq_of_eq {α} : {a a' : α} → a = a' → a ≅ a'
| _, _, rfl => HEq.refl _

lemma eq_of_heq {α} : {a a' : α} → a ≅ a' → a = a'
| _, _, HEq.refl _ => rfl

lemma cast_eq_of_eq_of_heq {α β} : (h : α = β) → {a : α} → {b : β} → a ≅ b → h ▸ a = b
| rfl, _, _, HEq.refl _ => rfl

lemma eq_cast_of_eq_of_heq {α β} : (h : α = β) → {a : α} → {b : β} → a ≅ b → a = h ▸ b
| rfl, _, _, HEq.refl _ => rfl

@[simp] lemma cast_refl {α} {h : α = α} (a : α) : h ▸ a = a :=
  match h with | rfl => rfl

@[simp] lemma cast_trans {α β γ} {h : α = β} {h' : β = γ} (a : α) : h' ▸ h ▸ a = (Eq.trans h h' ▸ a : γ) :=
  match h, h' with | rfl, rfl => rfl

@[simp] lemma cast_inj {α β} {h h' : α = β} (a a' : α) : (h ▸ a : β) = (h' ▸ a' : β) ↔ a = a' :=
  match h, h' with | rfl, rfl => Iff.rfl

section
variable {α} {β : α → Sort _}

lemma eqRec_eq_of_heq {x y : α} {t : β x} {u : β y} (h : x = y) : t ≅ u → h ▸ t = u := by
  cases h; intro h; cases h; rfl

lemma eq_eqRec_of_heq {x y : α} {t : β x} {u : β y} (h : y = x) : t ≅ u → t = h ▸ u := by
  cases h; intro h; cases h; rfl

@[simp] lemma eqRec_refl {x : α} {h : x = x} (t : β x) : h ▸ t = t := by
  cases h; rfl

@[simp] lemma eqRec_trans {x y z : α} {hyz : y = z} {hxy : x = y} (t : β x) :
  (hyz ▸ hxy ▸ t : β z) = Eq.trans hxy hyz ▸ t := by
  cases hxy; cases hyz; rfl

@[simp] lemma eqRec_inj {x y : α} {h₁ h₂ : x = y} {t₁ t₂ : β x} : (h₁ ▸ t₁ : β y) = h₂ ▸ t₂ ↔ t₁ = t₂ := by
  cases h₁; cases h₂; split <;> (intro; assumption)

lemma heq_of_eqRec_eq {x y : α} {h : x = y} (t : β x) (u : β y) : h ▸ t = u → t ≅ u := by
  cases h; exact heq_of_eq

lemma heq_of_eq_eqRec {x y : α} {h : x = y} (t : β y) (u : β x) : t = h ▸ u → t ≅ u := by
  cases h; exact heq_of_eq

lemma heq_eqRec_self {x y : α} {h : x = y} (t : β x) : t ≅ (h ▸ t : β y) := by
  cases h; exact HEq.refl t

lemma eqRec_heq_self {x y : α} {h : x = y} (t : β x) : (h ▸ t : β y) ≅ t := by
  cases h; exact HEq.refl t

end
