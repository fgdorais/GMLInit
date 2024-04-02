import GMLInit.Prelude

theorem decide_and (p q : Prop) [decp : Decidable p] [decq : Decidable q] : decide (p ∧ q) = (decide p && decide q) :=
  match decp, decq with
  | isTrue _, isTrue _ => rfl
  | isTrue _, isFalse _ => rfl
  | isFalse _, isTrue _ => rfl
  | isFalse _, isFalse _ => rfl

theorem decide_or (p q : Prop) [decp : Decidable p] [decq : Decidable q] : decide (p ∨ q) = (decide p || decide q) :=
  match decp, decq with
  | isTrue _, isTrue _ => rfl
  | isTrue _, isFalse _ => rfl
  | isFalse _, isTrue _ => rfl
  | isFalse _, isFalse _ => rfl

theorem decide_iff (p q : Prop) [decp : Decidable p] [decq : Decidable q] : decide (p ↔ q) = (decide p == decide q) :=
  match decp, decq with
  | isTrue _, isTrue _ => rfl
  | isTrue _, isFalse _ => rfl
  | isFalse _, isTrue _ => rfl
  | isFalse _, isFalse _ => rfl

theorem decide_eq_decide_of_iff {p q : Prop} [decp : Decidable p] [decq : Decidable q] : (p ↔ q) → decide p = decide q :=
  match decp, decq with
  | isTrue hp, isTrue hq => by simp [hp, hq]
  | isTrue hp, isFalse hq => by simp [hp, hq]
  | isFalse hp, isTrue hq => by simp [hp, hq]
  | isFalse hp, isFalse hq => by simp [hp, hq]

theorem decide_eq_decide_iff_iff {p q : Prop} [decp : Decidable p] [decq : Decidable q] : (p ↔ q) ↔ decide p = decide q :=
  match decp, decq with
  | isTrue hp, isTrue hq => by simp [hp, hq]
  | isTrue hp, isFalse hq => by simp [hp, hq]
  | isFalse hp, isTrue hq => by simp [hp, hq]
  | isFalse hp, isFalse hq => by simp [hp, hq]

class DecLift (b : Bool) where
  toProp : Prop
  instDecidable : Decidable toProp
  decide_eq : decide toProp = b

attribute [instance] DecLift.instDecidable

instance (priority:=low) (p : Prop) [Decidable p] : DecLift (decide p) where
  toProp := p
  instDecidable := inferInstance
  decide_eq := rfl

instance (priority:=low) (b : Bool) : DecLift b where
  toProp := b = true
  instDecidable := inferInstance
  decide_eq := by cases b <;> rfl

instance : DecLift true where
  toProp := True
  instDecidable := inferInstance
  decide_eq := rfl

instance : DecLift false where
  toProp := False
  instDecidable := inferInstance
  decide_eq := rfl

instance [DecLift b] : DecLift (!b) where
  toProp := ¬ DecLift.toProp b
  instDecidable := inferInstance
  decide_eq := by rw [decide_not, DecLift.decide_eq]

instance [DecLift b₁] [DecLift b₂] : DecLift (b₁ && b₂) where
  toProp := DecLift.toProp b₁ ∧ DecLift.toProp b₂
  instDecidable := inferInstance
  decide_eq := by rw [decide_and, DecLift.decide_eq, DecLift.decide_eq]

instance [DecLift b₁] [DecLift b₂] : DecLift (b₁ || b₂) where
  toProp := DecLift.toProp b₁ ∨ DecLift.toProp b₂
  instDecidable := inferInstance
  decide_eq := by rw [decide_or, DecLift.decide_eq, DecLift.decide_eq]

instance [DecLift b₁] [DecLift b₂] : DecLift (b₁ == b₂) where
  toProp := DecLift.toProp b₁ ↔ DecLift.toProp b₂
  instDecidable := inferInstance
  decide_eq := by rw [decide_iff, DecLift.decide_eq, DecLift.decide_eq]

instance (p : Fin n → Bool) [(i : Fin n) → DecLift (p i)] : DecLift (Fin.all p) where
  toProp := ∀ i, DecLift.toProp (p i)
  instDecidable := inferInstance
  decide_eq := by
    rw [Fin.decide_forall_eq_all]
    congr
    funext
    rw [DecLift.decide_eq]

instance (p : Fin n → Bool) [(i : Fin n) → DecLift (p i)] : DecLift (Fin.any p) where
  toProp := ∃ i, DecLift.toProp (p i)
  instDecidable := inferInstance
  decide_eq := by
    rw [Fin.decide_exists_eq_any]
    congr
    funext
    rw [DecLift.decide_eq]

theorem dec_lift_eq_true_of [DecLift b] : DecLift.toProp b → b = true := by
  intro h
  rw [←DecLift.decide_eq (b:=b)]
  exact decide_eq_true h

theorem dec_lift_eq_true_iff (b) [DecLift b] : DecLift.toProp b ↔ b = true := by
  constructor
  · exact dec_lift_eq_true_of
  · intro h
    rw [←DecLift.decide_eq (b:=b)] at h
    exact of_decide_eq_true h

theorem dec_lift_eq_false_of_not [DecLift b] : ¬DecLift.toProp b → b = false := by
  intro h
  rw [←DecLift.decide_eq (b:=b)]
  exact decide_eq_false h

theorem dec_lift_eq_false_iff_not (b) [DecLift b] : ¬DecLift.toProp b ↔ b = false := by
  constructor
  · exact dec_lift_eq_false_of_not
  · intro h
    rw [←DecLift.decide_eq (b:=b)] at h
    exact of_decide_eq_false h

theorem dec_lift_eq_dec_lift_of_iff [DecLift b₁] [DecLift b₂] : (DecLift.toProp b₁ ↔ DecLift.toProp b₂) → b₁ = b₂ := by
  intro h
  rw [←DecLift.decide_eq (b:=b₁)]
  rw [←DecLift.decide_eq (b:=b₂)]
  exact decide_eq_decide_of_iff h

theorem iff_of_dec_lift_eq_dec_lift [DecLift b₁] [DecLift b₂] : b₁ = b₂ → (DecLift.toProp b₁ ↔ DecLift.toProp b₂) := by
  intro h
  rw [←DecLift.decide_eq (b:=b₁)] at h
  rw [←DecLift.decide_eq (b:=b₂)] at h
  rw [decide_eq_decide_iff_iff]
  exact h

theorem dec_lift_eq_dec_lift_iff_iff [DecLift b₁] [DecLift b₂] : (DecLift.toProp b₁ ↔ DecLift.toProp b₂) ↔ b₁ = b₂ := by
  constructor
  · exact dec_lift_eq_dec_lift_of_iff
  · exact iff_of_dec_lift_eq_dec_lift
