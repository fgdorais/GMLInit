import GMLInit.Logic.Basic

theorem heq_iff_eq {α} (a a' : α) : a ≅ a' ↔ a = a' := ⟨eq_of_heq, heq_of_eq⟩

namespace HEq

theorem eqRec_heq {α} {a : α} {β : (a' : α) → a = a' → Sort _} {a' : α} (h : a = a') (x : β a rfl) : Eq.rec x h ≅ x := by cases h; exact HEq.rfl

theorem eqNdrec_heq {α} {β : α → Sort _} {a a' : α} (h : a = a') (x : β a) : h ▸ x ≅ x := by cases h; exact HEq.rfl

@[simp, clean, elim_casts] theorem eqRec_heq_iff_heq {α} {a : α} {β : (a' : α) → a = a' → Sort _} {a' : α} (h : a = a') (x : β a rfl) (y : γ) : Eq.rec x h ≅ y ↔ x ≅ y := by cases h; exact Iff.rfl

@[simp, clean, elim_casts] theorem heq_eqRec_iff_heq {α} {a : α} {β : (a' : α) → a = a' → Sort _} {a' : α} (h : a = a') (x : β a rfl) (y : γ) : y ≅ Eq.rec x h ↔ y ≅ x := by cases h; exact Iff.rfl

@[simp, clean, elim_casts] theorem eqNdrec_heq_iff_heq {α} {β : α → Sort _} {a a' : α} (h : a = a') (x : β a) (y : γ) : Eq.ndrec x h ≅ y ↔ x ≅ y := by cases h; exact Iff.rfl

@[simp, clean, elim_casts] theorem heq_eqNdrec_iff_heq {α} {β : α → Sort _} {a a' : α} (h : a = a') (x : β a) (y : γ) : y ≅ Eq.ndrec x h ↔ y ≅ x := by cases h; exact Iff.rfl

@[simp, clean, elim_casts] theorem cast_heq_iff_heq {α β γ} (h : α = β) (x : α) (y : γ) : cast h x ≅ y ↔ x ≅ y := by cases h; exact Iff.rfl

@[simp, clean, elim_casts] theorem heq_cast_iff_heq {α β γ} (h : α = β) (x : α) (y : γ) : y ≅ cast h x ↔ y ≅ x := by cases h; exact Iff.rfl

end HEq
