import GMLInit.Data.Nat.Extended

namespace Nat

section
variable (p : Nat → Bool) (h : ∃ n, p n)
open ENat

def bfind : Nat := toNat (first p) (first.isFinite_of_exists h)

variable {p} {h}

theorem not_prop_of_lt_bfind {x} : (x < bfind p h) → ¬ p x := by
  intro hlt h
  unfold bfind at hlt
  apply Nat.not_ge_of_lt hlt
  apply toNat_le_of_isLE
  apply first.isLE_of
  exact h

theorem bfind_le_of_prop {x} : p x → bfind p h ≤ x := by
  intro h
  apply Nat.le_of_not_gt
  intro (hlt:_ < _)
  apply not_prop_of_lt_bfind hlt
  exact h

variable (p) (h)

theorem bfind_prop : p (bfind p h) := by
  have : (first p).isLE (bfind p h) := by
    unfold bfind
    rw [isLE_toNat]
  match first.exists_le_of_isLE _ this with
  | ⟨x, hle, hx⟩ =>
    have heq : x = bfind p h := by
      antisymmetry using (.≤.:Nat→Nat→Prop)
      · exact hle
      · exact bfind_le_of_prop hx
      done
    rw [←heq, hx]

end

def find (p : Nat → Prop) [DecidablePred p] (h : ∃ n, p n) : Nat :=
  let p' := λ n => decide (p n)
  let h' : ∃ n, p' n := match h with | ⟨n,hn⟩ => ⟨n, decide_eq_true hn⟩
  bfind p' h'

theorem find_property (p : Nat → Prop) [DecidablePred p] {h : ∃ n, p n} : p (find p h) := by
  apply of_decide_eq_true
  apply bfind_prop (λ n => decide (p n))
  match h with | ⟨n, hn⟩ => exists n; exact decide_eq_true hn

theorem find_minimal (p : Nat → Prop) [DecidablePred p] {h : ∃ n, p n} {x : Nat} : p x → find p h ≤ x := by
  intro hx
  apply bfind_le_of_prop
  · match h with | ⟨n, hn⟩ => exists n; exact decide_eq_true hn
  · exact decide_eq_true hx

theorem find_eq : {p₁ p₂ : Nat → Prop} → [DecidablePred p₁] → [DecidablePred p₂] → p₁ = p₂ → {h₁ : ∃ n, p₁ n} → {h₂ : ∃ n, p₂ n} → Nat.find p₁ h₁ = Nat.find p₂ h₂
| _, _, _, _, rfl, _, _ => congr (congrArg (@find _) (Subsingleton.elim _ _)) (Subsingleton.elim _ _)

theorem find_ext {p₁ p₂ : Nat → Prop} [DecidablePred p₁] [DecidablePred p₂] : (∀ n, p₁ n ↔ p₂ n) → {h₁ : ∃ n, p₁ n} → {h₂ : ∃ n, p₂ n} → Nat.find p₁ h₁ = Nat.find p₂ h₂ :=
  λ h _ _ => find_eq $ by
    funext n
    apply propext
    exact h n

end Nat
