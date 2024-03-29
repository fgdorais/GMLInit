import GMLInit.Prelude
import GMLInit.Meta.Basic

namespace Prod
variable {α β : Type _}

protected theorem eq : {p q : α × β} → (fst : p.fst = q.fst) → (snd : p.snd = q.snd) → p = q
| (_, _), (_, _), rfl, rfl => rfl

abbrev swap {α β} : α × β → β × α
| (a, b) => (b, a)

end Prod

namespace Sigma
variable {α : Type _} {β : α → Type _}

protected theorem eq : {x₁ x₂ : Sigma β} → x₁.fst = x₂.fst → x₁.snd ≅ x₂.snd → x₁ = x₂
| ⟨_, _⟩, ⟨_, _⟩, rfl, HEq.rfl => rfl

protected theorem eta (p : Sigma β) : p = ⟨p.fst, p.snd⟩ := Sigma.eq rfl HEq.rfl

end Sigma

namespace Ordering

def opp : Ordering → Ordering
| lt => gt
| eq => eq
| gt => lt

theorem opp_opp (x) : opp (opp x) = x := by cases x <;> rfl

theorem opp_inj {x y} : opp x = opp y → x = y := by
  intro h
  rw [←opp_opp x, ←opp_opp y, h]

theorem eq_opp_iff_opp_eq (x y) : opp x = y ↔ x = opp y := by
  constructor
  · intro h; rw [←h, opp_opp]
  · intro h; rw [h, opp_opp]

end Ordering

structure Cached {α} (a : α) where
  value : α
  value_eq : value = a

instance {α} (a : α) : Inhabited (Cached a) := ⟨⟨a, rfl⟩⟩

instance {α} (a : α) : Subsingleton (Cached a) := ⟨fun | ⟨_,rfl⟩, ⟨_,rfl⟩ => rfl⟩

instance {α} (a : α) : DecidableEq (Cached a) | ⟨_,rfl⟩, ⟨_,rfl⟩ => isTrue rfl
