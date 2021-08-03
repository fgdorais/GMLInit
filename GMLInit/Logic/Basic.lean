
namespace Logic

-- Stable Propositions --

class inductive Stable (a : Prop) : Prop
| protected intro : (¬¬a → a) → Stable a

protected def Stable.by_contradiction {a : Prop} [inst : Stable a] : ¬¬a → a :=
  match inst with | Stable.intro h => h

/-- double negation elimination (DNE) -/
theorem Stable.dne (a : Prop) [inst : Stable a] : ¬¬a → a := 
  match inst with | Stable.intro h => h

/-- Pierces's law -/
theorem Stable.pierce (a b : Prop) [Stable a] : ((a → b) → a) → a :=
  λ h => Stable.by_contradiction λ na => na (h λ ha => absurd ha na)

abbrev StablePred {α} (a : α → Prop) := (x : α) → Stable (a x)

class inductive StableList : List Prop → Prop
| nil : StableList []
| cons {a as} : Stable a → StableList as → StableList (a :: as)

namespace StableList

instance : StableList [] := StableList.nil

instance (a as) [Stable a] [StableList as] : StableList (a :: as) :=
  StableList.cons inferInstance inferInstance

protected def head (a as) : [StableList (a :: as)] → Stable a
| StableList.cons inst _ => inst

protected def tail (a as) : [StableList (a :: as)] → StableList as
| StableList.cons _ inst => inst

end StableList

-- Complemented Propositions --

class inductive Complemented (a : Prop) : Prop
| protected isTrue : a → Complemented a
| protected isFalse : ¬a → Complemented a

/-- eliminator for `Complemented` -/
protected def Complemented.by_cases (a : Prop) [inst : Complemented a] {motive : Prop} (isTrue : a → motive) (isFalse : ¬a → motive) : motive := 
  match inst with
  | Complemented.isTrue h => isTrue h
  | Complemented.isFalse h => isFalse h

/-- excluded middle (EM) -/
theorem Complemented.em (a : Prop) [Complemented a] : a ∨ ¬a := Complemented.by_cases a Or.inl Or.inr

abbrev ComplementedPred {α} (a : α → Prop) := (x : α) → Complemented (a x)

class inductive ComplementedList : List Prop → Prop
| nil : ComplementedList []
| cons {a as} : Complemented a → ComplementedList as → ComplementedList (a :: as)

namespace ComplementedList

instance : ComplementedList [] := ComplementedList.nil

instance (a as) [Complemented a] [ComplementedList as] : ComplementedList (a :: as) :=
  ComplementedList.cons inferInstance inferInstance

protected def head (a as) : [ComplementedList (a :: as)] → Complemented a
| ComplementedList.cons inst _ => inst

protected def tail (a as) : [ComplementedList (a :: as)] → ComplementedList as
| ComplementedList.cons _ inst => inst

instance instMap {α} (a : α → Prop) [ComplementedPred a] : (xs : List α) → ComplementedList (xs.map a)
| [] => ComplementedList.nil
| x::xs => ComplementedList.cons inferInstance (instMap a xs)

end ComplementedList

instance (a : Prop) : [Complemented a] → Stable a
| Complemented.isTrue h => Stable.intro (λ _ => h)
| Complemented.isFalse h => Stable.intro (absurd h)

-- Decidable Propositions --

protected abbrev Decidable (a : Prop) : Type := _root_.Decidable a

@[matchPattern] protected abbrev Decidable.isTrue {a : Prop} : a → Logic.Decidable a := _root_.Decidable.isTrue
@[matchPattern] protected abbrev Decidable.isFalse {a : Prop} : ¬a → Logic.Decidable a := _root_.Decidable.isFalse

protected abbrev DecidablePred {α} (a : α → Prop) := _root_.DecidablePred a

class inductive DecidableList : List Prop → Type
| nil : DecidableList []
| cons {a as} : Logic.Decidable a → DecidableList as → DecidableList (a :: as)

namespace DecidableList

instance : DecidableList [] := DecidableList.nil

instance (a as) [Logic.Decidable a] [DecidableList as] : DecidableList (a :: as) :=
  DecidableList.cons inferInstance inferInstance

protected def head (a as) : [DecidableList (a :: as)] → Logic.Decidable a
| DecidableList.cons inst _ => inst

protected def tail (a as) : [DecidableList (a :: as)] → DecidableList as
| DecidableList.cons _ inst => inst

instance instMap {α} (a : α → Prop) [Logic.DecidablePred a] : (xs : List α) → DecidableList (xs.map a)
| [] => DecidableList.nil
| x::xs => DecidableList.cons inferInstance (instMap a xs)

end DecidableList

instance (a : Prop) : [Logic.Decidable a] → Complemented a
| Decidable.isTrue h => Complemented.isTrue h
| Decidable.isFalse h => Complemented.isFalse h

-- Weakly Complemented Propositions --

abbrev WeaklyComplemented (a : Prop) : Prop := Complemented (¬a)

@[matchPattern] protected abbrev WeaklyComplemented.isFalse {a : Prop} : ¬a → WeaklyComplemented a := Complemented.isTrue
@[matchPattern] protected abbrev WeaklyComplemented.isIrrefutable {a : Prop} : ¬¬a → WeaklyComplemented a := Complemented.isFalse

/-- weak excluded middle (WEM) -/
theorem WeaklyComplemented.wem (a : Prop) : [WeaklyComplemented a] → ¬¬a ∨ ¬a
| WeaklyComplemented.isIrrefutable h => Or.inl h
| WeaklyComplemented.isFalse h => Or.inr h

abbrev WeaklyComplementedPred {α} (a : α → Prop) := (x : α) → WeaklyComplemented (a x)

class inductive WeaklyComplementedList : List Prop → Prop
| nil : WeaklyComplementedList []
| cons {a as} : WeaklyComplemented a → WeaklyComplementedList as → WeaklyComplementedList (a :: as)

namespace WeaklyComplementedList

instance : WeaklyComplementedList [] := WeaklyComplementedList.nil

instance (a as) [WeaklyComplemented a] [WeaklyComplementedList as] : WeaklyComplementedList (a :: as) :=
  WeaklyComplementedList.cons inferInstance inferInstance

protected def head (a as) : [WeaklyComplementedList (a :: as)] → WeaklyComplemented a
| WeaklyComplementedList.cons inst _ => inst

protected def tail (a as) : [WeaklyComplementedList (a :: as)] → WeaklyComplementedList as
| WeaklyComplementedList.cons _ inst => inst

instance instMap {α} (a : α → Prop) [WeaklyComplementedPred a] : (xs : List α) → WeaklyComplementedList (xs.map a)
| [] => WeaklyComplementedList.nil
| x::xs => WeaklyComplementedList.cons inferInstance (instMap a xs)

end WeaklyComplementedList

def complementedOfStableOfWeaklyComplemented (a : Prop) [Stable a] : [WeaklyComplemented a] → Complemented a
| WeaklyComplemented.isFalse h => Complemented.isFalse h
| WeaklyComplemented.isIrrefutable h => Complemented.isTrue (Stable.by_contradiction h)

instance (a : Prop) : [Complemented a] → WeaklyComplemented a
| Complemented.isTrue h => WeaklyComplemented.isIrrefutable (absurd h)
| Complemented.isFalse h => WeaklyComplemented.isFalse h

-- Weakly Decidable Propositions --

abbrev WeaklyDecidable (a : Prop) : Type := _root_.Decidable (¬a)

@[matchPattern] protected abbrev WeaklyDecidable.isFalse {a : Prop} : ¬a → WeaklyDecidable a := Decidable.isTrue
@[matchPattern] protected abbrev WeaklyDecidable.isIrrefutable {a : Prop} : ¬¬a → WeaklyDecidable a := Decidable.isFalse

abbrev WeaklyDecidablePred {α} (a : α → Prop) := (x : α) → WeaklyDecidable (a x)

class inductive WeaklyDecidableList : List Prop → Type
| nil : WeaklyDecidableList []
| cons {a as} : WeaklyDecidable a → WeaklyDecidableList as → WeaklyDecidableList (a :: as)

namespace WeaklyDecidableList

instance : WeaklyDecidableList [] := WeaklyDecidableList.nil

instance (a as) [WeaklyDecidable a] [WeaklyDecidableList as] : WeaklyDecidableList (a :: as) :=
  WeaklyDecidableList.cons inferInstance inferInstance

protected def head (a as) : [WeaklyDecidableList (a :: as)] → WeaklyDecidable a
| WeaklyDecidableList.cons inst _ => inst

protected def tail (a as) : [WeaklyDecidableList (a :: as)] → WeaklyDecidableList as
| WeaklyDecidableList.cons _ inst => inst

instance instMap {α} (a : α → Prop) [WeaklyDecidablePred a] : (xs : List α) → WeaklyDecidableList (xs.map a)
| [] => WeaklyDecidableList.nil
| x::xs => WeaklyDecidableList.cons inferInstance (instMap a xs)

end WeaklyDecidableList

def decidableOfStableOfWeaklyDecidable (a : Prop) [Stable a] : [WeaklyDecidable a] → Logic.Decidable a
| WeaklyDecidable.isFalse h => Decidable.isFalse h
| WeaklyDecidable.isIrrefutable h => Decidable.isTrue (Stable.by_contradiction h)

instance (a : Prop) : [Logic.Decidable a] → WeaklyDecidable a
| Decidable.isTrue h => WeaklyDecidable.isIrrefutable (absurd h)
| Decidable.isFalse h => WeaklyDecidable.isFalse h

end Logic
