import GMLInit.Data.Basic
import GMLInit.Meta.Basic
import GMLInit.Meta.Relation

namespace Equiv
variable {α β γ δ}

@[scoped simp] lemma fwd_rev (e : Equiv α β) (x) : e.fwd (e.rev x) = x := by rw [Equiv.spec]

@[scoped simp] lemma rev_fwd (e : Equiv α β) (x) : e.rev (e.fwd x) = x := by rw [←Equiv.spec]

@[scoped simp] lemma comp_fwd_rev (e : Equiv α β) : e.fwd ∘ e.rev = id := funext e.fwd_rev

@[scoped simp] lemma comp_rev_fwd (e : Equiv α β) : e.rev ∘ e.fwd = id := funext e.rev_fwd

private theorem eq_aux : {e₁ e₂ : Equiv α β} → e₁.fwd = e₂.fwd → e₁.rev = e₂.rev → e₁ = e₂
| ⟨_,_,_⟩, ⟨_,_,_⟩, rfl, rfl => rfl

protected theorem eq {e₁ e₂ : Equiv α β} : e₁.fwd = e₂.fwd → e₁ = e₂ := by
  intro hfwd
  apply eq_aux
  exact hfwd
  funext x
  rw [← fwd_rev e₁ x, rev_fwd, hfwd, rev_fwd]

protected theorem ext {e₁ e₂ : Equiv α β} : (∀ x, e₁.fwd x = e₂.fwd x) → e₁ = e₂ := by
  intro hext
  apply Equiv.eq
  funext x
  exact hext x

protected def id : Equiv α α where
  fwd := id
  rev := id
  spec := by intros; constr <;> intro | rfl => rfl

@[scoped simp] lemma id_fwd (x : α) : Equiv.id.fwd x = x := rfl

@[scoped simp] lemma id_rev (x : α) : Equiv.id.rev x = x := rfl

protected def comp (f : Equiv β γ) (e : Equiv α β) : Equiv α γ where
  fwd := f.fwd ∘ e.fwd
  rev := e.rev ∘ f.rev
  spec := by
    intros
    unfold Function.comp
    constr
    · intro | rfl => rw [f.rev_fwd, e.rev_fwd]
    · intro | rfl => rw [e.fwd_rev, f.fwd_rev]

@[scoped simp] lemma comp_fwd (f : Equiv β γ) (e : Equiv α β) (x) : (Equiv.comp f e).fwd x = f.fwd (e.fwd x) := rfl

@[scoped simp] lemma comp_rev (f : Equiv β γ) (e : Equiv α β) (x) : (Equiv.comp f e).rev x = e.rev (f.rev x) := rfl

protected def inv (e : Equiv α β) : Equiv β α where
  fwd := e.rev
  rev := e.fwd
  spec := e.spec.symm

@[scoped simp] lemma inv_fwd (e : Equiv α β) (x) : (Equiv.inv e).fwd x = e.rev x := rfl

@[scoped simp] lemma inv_rev (e : Equiv α β) (x) : (Equiv.inv e).rev x = e.fwd x := rfl

protected theorem comp_assoc (g : Equiv γ δ) (f : Equiv β γ) (e : Equiv α β) :
  Equiv.comp (Equiv.comp g f) e = Equiv.comp g (Equiv.comp f e) := by
  apply Equiv.ext; intro x; rfl

@[scoped simp] protected theorem comp_id_right (e : Equiv α β) : Equiv.comp e Equiv.id = e := by
  apply Equiv.ext; intro x; rfl

@[scoped simp] protected theorem comp_id_left (e : Equiv α β) : Equiv.comp e Equiv.id = e := by
  apply Equiv.ext; intro x; rfl

@[scoped simp] protected theorem comp_inv_right (e : Equiv α β) : Equiv.comp e (Equiv.inv e) = Equiv.id := by
  apply Equiv.ext; intro x; simp

@[scoped simp] protected theorem comp_inv_left (e : Equiv α β) : Equiv.comp (Equiv.inv e) e = Equiv.id := by
  apply Equiv.ext; intro x; simp

@[scoped simp] protected theorem inv_id : Equiv.inv (Equiv.id (α:=α)) = Equiv.id := by
  apply Equiv.ext; intro x; rfl

@[scoped simp] protected theorem inv_inv (e : Equiv α β) : Equiv.inv (Equiv.inv e) = e := by
  apply Equiv.ext; intro x; rfl

protected theorem inv_comp (f : Equiv β γ) (e : Equiv α β) : Equiv.inv (Equiv.comp f e) = Equiv.comp (Equiv.inv e) (Equiv.inv f) := by
  apply Equiv.ext; intro x; rfl

end Equiv
