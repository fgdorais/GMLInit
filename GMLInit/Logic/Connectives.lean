import GMLInit.Logic.Basic

variable {a b : Prop}

abbrev Implies (a b : Prop) : Prop := a → b

/-- constructor for `Implies`

  This is a fake constructor -- `Implies` is not an inductive type. Cannot be used for pattern matching.
-/
protected def Implies.intro : (a → b) → Implies a b := id

/-- recursor for `Implies`

  This is a fake recursor -- `Implies` is not an inductive type.
-/
protected def Implies.rec.{u} {motive : (a → b) → Sort u} : (a → (h : b) → motive (λ _ => h)) → (t : a → b) → a → motive t :=
  λ h t ha => h ha (t ha)

protected def Implies.recOn.{u} {motive : (a → b) → Sort u} (t : a → b) := Implies.rec (motive:=motive) (t:=t)

protected def Implies.casesOn.{u} {motive : (a → b) → Sort u} := Implies.recOn (motive := motive)

/-- eliminator for `Implies` -/
protected def Implies.elim.{u} {motive : Sort u} := Implies.recOn (motive := λ _ : a → b => motive)

/-- modus ponens -/
protected abbrev Implies.mp : Implies a b → a → b := id

/-- modus tollens -/
protected abbrev Implies.mt : Implies a b → ¬b → ¬a := mt

/-- constructor for `Not`

  This is a fake constructor -- `Not` is not an inductive type. Cannot be used for pattern matching.
-/
protected def Not.intro : (a → False) → ¬a := id

/-- recursor for `Not`

  This is a fake recursor -- `Not` is not an inductive type.
-/
protected def Not.rec.{u} {motive : ¬a → Sort u} (t : ¬a) : a → motive t :=
  λ h => False.casesOn (λ _ => motive t) (t h)

protected def Not.recOn.{u} {motive : ¬a → Sort u} (t : ¬a) := Not.rec (motive:=motive) t

protected def Not.casesOn.{u} {motive : ¬p → Sort u} := Not.recOn (motive:=motive)

/-- eliminator for `Not`

  This is a fake eliminator -- `Not` is not an inductive type.
-/
protected def Not.elim.{u} {motive : Sort u} := Not.casesOn (motive := λ _ : ¬a => motive)

/-- eliminator for `And` -/
protected def And.elim.{u} {motive : Sort u} := And.casesOn (motive := λ _ : a ∧ b => motive)

/-- eliminator for `Iff` -/
protected def Iff.elim.{u} {motive : Sort u} := Iff.casesOn (motive := λ _ : a ↔ b => motive)

theorem Iff.eq_implies_and_implies (a b : Prop) : (a ↔ b) = ((a → b) ∧ (b → a)) :=
  propext (iff_iff_implies_and_implies a b)

protected def Iff.mt : (a ↔ b) → (¬b ↔ ¬a)
| Iff.intro hab hba => Iff.intro (mt hab) (mt hba)

/-- large recursor for `Or`

  In order to eliminate into sorts other than `Prop`, we must assume that the propositions are decidable.
-/
protected def Or.recLarge.{u} {motive : a ∨ b → Sort u} : [Decidable a] → [Decidable b] →
  (inl : (h : a) → motive (Or.inl h)) → (inr : (h : b) → motive (Or.inr h)) → (t : a ∨ b) → motive t
| Decidable.isTrue ha, _, h, _, _ => h ha
| _, Decidable.isTrue hb, _, h, _ => h hb
| Decidable.isFalse ha, Decidable.isFalse hb, _, _, t =>
  absurd t λ | Or.inl h => ha h | Or.inr h => hb h

protected def Or.recLargeOn.{u} [Decidable a] [Decidable b] {motive : a ∨ b → Sort u} (t : a ∨ b) :=
  Or.recLarge (motive:=motive) (t:=t)

protected def Or.casesLargeOn.{u} [Decidable a] [Decidable b] {motive : a ∨ b → Sort u} :=
  Or.recLargeOn (motive:=motive)

/-- large eliminator for `Or`

  In order to eliminate into sorts other than `Prop`, we must assume that the propositions are decidable.
-/
protected def Or.elimLarge.{u} [Decidable a] [Decidable b] {motive : Sort u} := Or.recLargeOn (motive := λ _ : a ∨ b => motive)

/-- modus tollendo ponens -/
theorem Or.mtp : a ∨ b → ¬b → a :=
  λ t => Or.elim t (λ h _ => h) absurd

/-- modus tollendo ponens (reversed) -/
theorem Or.mtpr : a ∨ b → ¬a → b :=
  λ t => Or.elim t absurd (λ h _ => h)

/-- `NOr` connective: `¬(a ∨ b)` -/
abbrev NOr (a b : Prop) : Prop := ¬(a ∨ b)

protected def NOr.eq_def (a b : Prop) : NOr a b = ¬(a ∨ b) := rfl

/-- constructor for `NOr`

  This is a fake constructor -- `NOr` is not an inductive type.
-/
protected def NOr.intro : ¬a → ¬b → NOr a b
| hn, _, Or.inl h => hn h
| _, hn, Or.inr h => hn h

/-- recursor for `NAnd`

  This is a fake recursor -- `NOr` is not an inductive type.
-/
protected def NOr.rec.{u} {motive : NOr a b → Sort u} : (intro : (na : ¬a) → (nb : ¬b) → motive (NOr.intro na nb)) → (t : NOr a b) → motive t :=
  λ h t => h (λ ha => t (Or.inl ha)) (λ hb => t (Or.inr hb))

/-- recursor for `NAnd`

  See `NAnd.rec`.
-/
protected def NOr.recOn.{u} {motive : NOr a b → Sort u} (t : NOr a b) := NOr.rec (motive:=motive) (t:=t)

/-- recursor for `NAnd`

  This is a fake eliminator -- `NOr` is not an inductive type.
-/
protected def NOr.casesOn.{u} {motive : NOr a b → Sort u} := NOr.recOn (motive:=motive)

/-- eliminator for `NOr`

  This is a fake eliminator -- `NOr` is not an inductive type.
-/
protected def NOr.elim.{u} {motive : Sort u} (t : NOr a b) : (intro : ¬a → ¬b → motive) → motive :=
  NOr.recOn (motive := λ _ => motive) t

/-- left projection for `NOr` -/
protected def NOr.left : NOr a b → ¬a :=
  λ h => NOr.elim h (λ ha _ => ha)

/-- right projection for `NOr` -/
protected def NOr.right : NOr a b → ¬b :=
  λ h => NOr.elim h (λ _ hb => hb)

theorem nor_of_not_and_not : ¬a ∧ ¬b → ¬(a ∨ b)
| And.intro ha hb => NOr.intro ha hb

theorem not_and_not_of_nor : ¬(a ∨ b) → ¬a ∧ ¬b :=
  λ h => And.intro (λ ha => h (Or.inl ha)) (λ hb => h (Or.inr hb))

theorem nor_iff_not_and_not (a b : Prop) : ¬(a ∨ b) ↔ ¬a ∧ ¬b :=
  Iff.intro not_and_not_of_nor nor_of_not_and_not

theorem NOr.eq_not_and_not (a b : Prop) : NOr a b = (¬a ∧ ¬b) :=
  propext (nor_iff_not_and_not a b)

/-- de Morgan's law for `Or` -/
protected theorem Or.deMorgan : ¬(a ∨ b) ↔ ¬a ∧ ¬b := nor_iff_not_and_not a b

/-- `NAnd` connective: `¬(a ∧ b)` -/
abbrev NAnd (a b : Prop) : Prop := ¬(a ∧ b)

protected def NAnd.eq_def (a b : Prop) : NAnd a b = ¬(a ∧ b) := rfl

/-- left constructor for `NAnd`

  This is a fake constructor -- `NAnd` is not an inductive type. Cannot be used for pattern matching.
-/
protected def NAnd.inl : ¬a → NAnd a b
| hn, And.intro h _ => hn h

/-- right constructor for `NAnd`

  This is a fake constructor -- `NAnd` is not an inductive type. Cannot be used for pattern matching.
-/
protected def NAnd.inr : ¬b → NAnd a b
| hn, And.intro _ h => hn h

/-- recursor for `NAnd`

  Only valid for weakly complemented propositions.
  Can only eliminate intro `Prop`, see `NAnd.recLarge` to eliminate into other sorts.
  This is a fake recursor -- `NAnd` is not an inductive type.
-/
protected def NAnd.rec {motive : NAnd a b → Prop} : [WeaklyComplemented a] → [WeaklyComplemented b] →
  (inl : (h : ¬a) → motive (NAnd.inl h)) → (inr : (h : ¬b) → motive (NAnd.inr h)) → (t : NAnd a b) → motive t
| WeaklyComplemented.isFalse ha, _, h, _, _ => h ha
| _, WeaklyComplemented.isFalse hb, _, h, _ => h hb
| WeaklyComplemented.isIrrefutable ha, WeaklyComplemented.isIrrefutable hb, _, _, t =>
  absurd t λ h => ha λ ha => hb λ hb => h (And.intro ha hb)

/-- recursor for `NAnd`

  See `NAnd.rec`.
-/
protected def NAnd.recOn {motive : NAnd a b → Prop} (t : NAnd a b) [WeaklyComplemented a] [WeaklyComplemented b] := NAnd.rec (motive:=motive) (t:=t)

/-- recursor for `NAnd`

  See `NAnd.rec`.
-/
protected def NAnd.casesOn {motive : NAnd a b → Prop} := NAnd.recOn (motive:=motive)

/-- eliminator for `NAnd`

  Can only eliminate intro `Prop`, see `NAnd.elimLarge` to eliminate into other sorts.
  This is a fake eliminator -- `NAnd` is not an inductive type.
-/
protected def NAnd.elim {motive : Prop} := NAnd.recOn (motive := λ _ : NAnd a b => motive)

/-- large recursor for `NAnd`

  In order to eliminate into sorts other than `Prop`, we must assume that the propositions are weakly decidable.
  This is a fake recursor -- `NAnd` is not an inductive type.
-/
protected def NAnd.recLarge.{u} {motive : NAnd a b → Sort u} : [WeaklyDecidable a] → [WeaklyDecidable b] →
  (inl : (h : ¬a) → motive (NAnd.inl h)) → (inr : (h : ¬b) → motive (NAnd.inr h)) → (t : NAnd a b) → motive t
| WeaklyDecidable.isFalse ha, _, h, _, _ => h ha
| _, WeaklyDecidable.isFalse hb, _, h, _ => h hb
| WeaklyDecidable.isIrrefutable ha, WeaklyDecidable.isIrrefutable hb, _, _, t =>
  absurd t λ h => ha λ ha => hb λ hb => h (And.intro ha hb)

protected def NAnd.recLargeOn.{u} {motive : NAnd a b → Sort u} (t : NAnd a b) [WeaklyDecidable a] [WeaklyDecidable b] := NAnd.recLarge (motive:=motive) (t:=t)

protected def NAnd.casesLargeOn.{u} {motive : NAnd a b → Sort u} := NAnd.recLargeOn (motive:=motive)

/-- large eliminator for `NAnd`

  In order to eliminate into sorts other than `Prop`, we must assume that the propositions are weakly decidable.
  This is a fake eliminator -- `NAnd` is not an inductive type.
-/
protected def NAnd.elimLarge.{u} {motive : Sort u} := NAnd.recLargeOn (motive := λ _ : NAnd a b => motive)

theorem nand_of_not_or_not : ¬a ∨ ¬b → ¬(a ∧ b)
| Or.inl h => NAnd.inl h
| Or.inr h => NAnd.inr h

theorem not_or_not_of_nand [WeaklyComplemented a] [WeaklyComplemented b] : ¬(a ∧ b) → ¬a ∨ ¬b :=
  λ h => NAnd.elim h Or.inl Or.inr

theorem nand_iff_not_or_not (a b : Prop) [WeaklyComplemented a] [WeaklyComplemented b] : ¬(a ∧ b) ↔ ¬a ∨ ¬b :=
  Iff.intro not_or_not_of_nand nand_of_not_or_not

theorem NAnd.eq_not_or_not (a b : Prop) [WeaklyComplemented a] [WeaklyComplemented b] : NAnd a b = (¬a ∨ ¬b) :=
  propext (nand_iff_not_or_not a b)

/-- de Morgan's law for `Or`

  Only valid for weakly complemented propositions.
-/
protected theorem And.deMorgan [WeaklyComplemented a] [WeaklyComplemented b] : ¬(a ∧ b) ↔ ¬a ∨ ¬b := nand_iff_not_or_not a b
