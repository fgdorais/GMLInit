import GMLInit.Data.Basic
import GMLInit.Data.Bool.Basic
import GMLInit.Data.Index
import GMLInit.Meta.Decidable

inductive BDD.{u} {α : Type u} : List α → Type u
| tt : BDD []
| ff : BDD []
| lift {x xs} : BDD xs → BDD (x :: xs)
| case {x xs} (t f : BDD xs) : BDD (x :: xs)

namespace BDD

instance decEq {xs : List α} : DecidableEq (BDD xs) :=
  fun a b => match xs, a, b with
  | [], tt, tt => isTrue rfl
  | [], tt, ff => isFalse BDD.noConfusion
  | [], ff, tt => isFalse BDD.noConfusion
  | [], ff, ff => isTrue rfl
  | _::_, lift a, lift b =>
    match decEq a b with
    | isTrue rfl => isTrue rfl
    | isFalse h => isFalse fun | rfl => h rfl
  | _::_, lift _, case _ _ => isFalse BDD.noConfusion
  | _::_, case _ _, lift _ => isFalse BDD.noConfusion
  | _::_, case ta fa, case tb fb =>
    match decEq ta tb, decEq fa fb with
    | isTrue rfl, isTrue rfl => isTrue rfl
    | isFalse h, _ => isFalse fun | rfl => h rfl
    | _, isFalse h => isFalse fun | rfl => h rfl

protected def eval {xs : List α} (a : BDD xs) (v : Index xs → Bool) : Bool :=
  match xs, a with
  | [], tt => true
  | [], ff => false
  | _::_, lift a =>
    BDD.eval a fun i => v i.tail
  | _::_, case t f =>
    if v .head
    then BDD.eval t fun i => v i.tail
    else BDD.eval f fun i => v i.tail

protected def true {xs : List α} : BDD xs :=
  match xs with
  | [] => tt
  | _::_ => lift BDD.true

theorem eval_true {xs : List α} (v : Index xs → Bool) : BDD.true.eval v = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact ih ..

protected def false {xs : List α} : BDD xs :=
  match xs with
  | [] => ff
  | _::_ => lift BDD.false

theorem eval_false {xs : List α} (v : Index xs → Bool) : BDD.false.eval v = false := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact ih ..

theorem true_ne_false {xs : List α} : BDD.true (xs:=xs) ≠ BDD.false (xs:=xs) := by
  induction xs with
  | nil => intro; contradiction
  | cons x xs ih => intro h; injection h; contradiction

protected def var {xs : List α} (i : Index xs) : BDD xs :=
  match xs, i with
  | _::_, .head => case BDD.true BDD.false
  | _::_, .tail i => lift (BDD.var i)

theorem eval_var {xs : List α} (i : Index xs) (v : Index xs → Bool) : (BDD.var i).eval v = v i := by
  induction i with
  | head =>
    unfold BDD.var BDD.eval
    match v .head with
    | true => simp [eval_true]
    | false => simp [eval_false]
  | tail _ ih => exact ih ..

protected def not {xs : List α} (a : BDD xs) : BDD xs :=
  match xs, a with
  | [], tt => ff
  | [], ff => tt
  | _::_, lift a => lift (BDD.not a)
  | _::_, case ta fa => case (BDD.not ta) (BDD.not fa)

theorem not_not {xs : List α} (a : BDD xs) : a.not.not = a := by
  induction xs with
  | nil =>
    match a with
    | tt => rfl
    | ff => rfl
  | cons x xs ih =>
    match a with
    | lift a => unfold BDD.not; rw [ih a]
    | case t f => unfold BDD.not; rw [ih t, ih f]

theorem eval_not {xs : List α} (a : BDD xs) (v : Index xs → Bool) : (BDD.not a).eval v = ! a.eval v := by
  induction xs with
  | nil =>
    match a with
    | tt => rfl
    | ff => rfl
  | cons x xs ih =>
    match a with
    | lift a => exact ih ..
    | case t f =>
      unfold BDD.not BDD.eval
      by_cases v .head = true with
      | isTrue h =>
        rw [if_pos h, if_pos h]
        exact ih ..
      | isFalse h =>
        rw [if_neg h, if_neg h]
        exact ih ..

protected def and {xs : List α} (a b : BDD xs) : BDD xs :=
  match xs, a, b with
  | [], tt, tt => tt
  | [], ff, _ => ff
  | [], _, ff => ff
  | _::_, lift a, lift b => lift (BDD.and a b)
  | _::_, lift a, case tb fb => case (BDD.and a tb) (BDD.and a fb)
  | _::_, case ta fa, lift b => case (BDD.and ta b) (BDD.and fa b)
  | _::_, case ta fa, case tb fb => case (BDD.and ta tb) (BDD.and fa fb)

theorem eval_and {xs : List α} (a b : BDD xs) (v : Index xs → Bool) : (BDD.and a b).eval v = (a.eval v && b.eval v) := by
  induction xs with
  | nil =>
    match a, b with
    | tt, tt => rfl
    | tt, ff => rfl
    | ff, tt => rfl
    | ff, ff => rfl
  | cons x xs ih =>
    match a, b with
    | lift a, lift b =>
      unfold BDD.and BDD.eval
      rw [ih a b]
    | lift a, case tb fb =>
      unfold BDD.and BDD.eval
      split
      next => rw [ih a tb]
      next => rw [ih a fb]
    | case ta fa, lift b =>
      unfold BDD.and BDD.eval
      split
      next => rw [ih ta b]
      next => rw [ih fa b]
    | case ta fa, case tb fb =>
      unfold BDD.and BDD.eval
      split
      next => rw [ih ta tb]
      next => rw [ih fa fb]

protected def or {xs : List α} (a b : BDD xs) : BDD xs :=
  match xs, a, b with
  | [], tt, _ => tt
  | [], _, tt => tt
  | [], ff, ff => ff
  | _::_, lift a, lift b => lift (BDD.or a b)
  | _::_, lift a, case tb fb => case (BDD.or a tb) (BDD.or a fb)
  | _::_, case ta fa, lift b => case (BDD.or ta b) (BDD.or fa b)
  | _::_, case ta fa, case tb fb => case (BDD.or ta tb) (BDD.or fa fb)

theorem eval_or {xs : List α} (a b : BDD xs) (v : Index xs → Bool) : (BDD.or a b).eval v = (a.eval v || b.eval v) := by
  induction xs with
  | nil =>
    match a, b with
    | tt, tt => rfl
    | tt, ff => rfl
    | ff, tt => rfl
    | ff, ff => rfl
  | cons x xs ih =>
    match a, b with
    | lift a, lift b =>
      unfold BDD.or BDD.eval
      rw [ih a b]
    | lift a, case tb fb =>
      unfold BDD.or BDD.eval
      split
      next => rw [ih a tb]
      next => rw [ih a fb]
    | case ta fa, lift b =>
      unfold BDD.or BDD.eval
      split
      next => rw [ih ta b]
      next => rw [ih fa b]
    | case ta fa, case tb fb =>
      unfold BDD.or BDD.eval
      split
      next => rw [ih ta tb]
      next => rw [ih fa fb]

protected def xor {xs : List α} (a b : BDD xs) : BDD xs :=
  match xs, a, b with
  | [], tt, tt => ff
  | [], tt, ff => tt
  | [], ff, tt => tt
  | [], ff, ff => ff
  | _::_, lift a, lift b => lift (BDD.xor a b)
  | _::_, lift a, case tb fb => case (BDD.xor a tb) (BDD.xor a fb)
  | _::_, case ta fa, lift b => case (BDD.xor ta b) (BDD.xor fa b)
  | _::_, case ta fa, case tb fb => case (BDD.xor ta tb) (BDD.xor fa fb)

theorem eval_xor {xs : List α} (a b : BDD xs) (v : Index xs → Bool) : (BDD.xor a b).eval v = (a.eval v ^^ b.eval v) := by
  induction xs with
  | nil =>
    match a, b with
    | tt, tt => rfl
    | tt, ff => rfl
    | ff, tt => rfl
    | ff, ff => rfl
  | cons x xs ih =>
    match a, b with
    | lift a, lift b =>
      unfold BDD.xor BDD.eval
      rw [ih a b]
    | lift a, case tb fb =>
      unfold BDD.xor BDD.eval
      split
      next => rw [ih a tb]
      next => rw [ih a fb]
    | case ta fa, lift b =>
      unfold BDD.xor BDD.eval
      split
      next => rw [ih ta b]
      next => rw [ih fa b]
    | case ta fa, case tb fb =>
      unfold BDD.xor BDD.eval
      split
      next => rw [ih ta tb]
      next => rw [ih fa fb]

def isReduced {xs : List α} (a : BDD xs) : Bool :=
  match xs, a with
  | [], _ => true
  | _::_, lift a => isReduced a
  | _::_, case ta tf => !decide (ta = tf) && (isReduced ta && isReduced tf)

def reduce {xs : List α} (a : BDD xs) : BDD xs :=
  match xs, a with
  | [], a => a
  | _::_, lift a => lift (reduce a)
  | _::_, case t f =>
    let t := reduce t
    let f := reduce f
    if t = f then lift t else case t f

theorem reduce_isReduced {xs : List α} (a : BDD xs) : isReduced (reduce a) := by
  induction xs with
  | nil =>
    match a with
    | tt => rfl
    | ff => rfl
  | cons x xs ih =>
    match a with
    | lift a => exact ih a
    | case t f =>
      unfold reduce
      split
      next => exact ih t
      next h =>
        unfold isReduced
        simp
        constr
        · exact h
        · constr
          · exact ih t
          · exact ih f

theorem reduce_eq_self_of_isReduced {xs : List α} (a : BDD xs) (h : isReduced a) : a.reduce = a := by
  induction xs with
  | nil =>
    match a with
    | tt => rfl
    | ff => rfl
  | cons x xs ih =>
    match a with
    | lift a =>
      unfold isReduced at h
      unfold reduce
      rw [ih a h]
    | case t f =>
      unfold isReduced at h
      simp at h
      match h with
      | ⟨h, ht, hf⟩ =>
        unfold reduce
        rw [ih t ht]
        rw [ih f hf]
        rw [if_neg h]

theorem reduce_reduce {xs : List α} (a : BDD xs) : a.reduce.reduce = a.reduce := by
  apply reduce_eq_self_of_isReduced
  apply reduce_isReduced

theorem true_isReduced {xs : List α} : isReduced (BDD.true (xs:=xs)) := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => exact ih ..

theorem false_isReduced {xs : List α} : isReduced (BDD.false (xs:=xs)) := by
  induction xs with
  | nil => rfl
  | cons _ _ ih => exact ih ..

theorem var_isReduced {xs : List α} (i : Index xs) : isReduced (BDD.var i) := by
  induction i with
  | head => simp [BDD.var, isReduced, true_isReduced, false_isReduced, true_ne_false]
  | tail _ ih => exact ih ..

theorem eval_reduce {xs : List α} (a : BDD xs) (v : Index xs → Bool) : a.reduce.eval v = a.eval v := by
  induction xs with
  | nil =>
    match a with
    | tt => rfl
    | ff => rfl
  | cons x xs ih =>
    match a with
    | lift a => exact ih ..
    | case t f =>
      unfold reduce BDD.eval
      by_cases v .head = true with
      | isTrue ht =>
        rw [if_pos ht]
        split
        next => rw [BDD.eval, ih]
        next => rw [BDD.eval, if_pos ht, ih]
      | isFalse hf =>
        rw [if_neg hf]
        split
        next h => rw [BDD.eval, h, ih]
        next => rw [BDD.eval, if_neg hf, ih]

theorem not_isReduced {xs : List α} (a : BDD xs) : isReduced (BDD.not a) = isReduced a := by
  induction xs with
  | nil =>
    match a with
    | tt => rfl
    | ff => rfl
  | cons x xs ih =>
    match a with
    | lift a =>
      unfold BDD.not
      exact ih a
    | case t f =>
      have : t.not = f.not ↔ t = f := by
        constr
        · intro h
          rw [←BDD.not_not t, ←BDD.not_not f, h]
        · intro | rfl => rfl
      unfold BDD.not isReduced
      simp [ih t, ih f, this]

def delta {xs : List α} (a b : BDD xs) (ha : a.isReduced) (hb : b.isReduced) (hne : a ≠ b) (i : Index xs) : Bool :=
  match xs, a, b with
  | _::_, lift a, lift b =>
    have ha : a.isReduced := ha
    have hb : b.isReduced := hb
    have hne : a ≠ b := fun | rfl => hne rfl
    match i with
    | .head => default
    | .tail i => delta a b ha hb hne i
  | _::_, lift a, case tb fb =>
    have ha : a.isReduced := ha
    have htb : tb.isReduced := by simp [isReduced] at hb; exact hb.2.1
    have hfb : fb.isReduced := by simp [isReduced] at hb; exact hb.2.2
    match decEq a tb, decEq a fb with
    | isTrue h₁, isTrue h₂ => False.elim $ by simp [←h₁, ←h₂, isReduced] at hb
    | isFalse hne, _ =>
      match i with
      | .head => true
      | .tail i => delta a tb ha htb hne i
    | _, isFalse hne =>
      match i with
      | .head => false
      | .tail i => delta a fb ha hfb hne i
  | _::_, case ta fa, lift b =>
    have hta : ta.isReduced := by simp [isReduced] at ha; exact ha.2.1
    have hfa : fa.isReduced := by simp [isReduced] at ha; exact ha.2.2
    have hb : b.isReduced := hb
    match decEq ta b, decEq fa b with
    | isTrue h₁, isTrue h₂ => False.elim $ by simp [h₁, h₂, isReduced] at ha
    | isFalse hne, _ =>
      match i with
      | .head => true
      | .tail i => delta ta b hta hb hne i
    | _, isFalse hne =>
      match i with
      | .head => false
      | .tail i => delta fa b hfa hb hne i
  | _::_, case ta fa, case tb fb =>
    have hta : ta.isReduced := by simp [isReduced] at ha; exact ha.2.1
    have hfa : fa.isReduced := by simp [isReduced] at ha; exact ha.2.2
    have htb : tb.isReduced := by simp [isReduced] at hb; exact hb.2.1
    have hfb : fb.isReduced := by simp [isReduced] at hb; exact hb.2.2
    match decEq ta tb, decEq fa fb with
    | isTrue h₁, isTrue h₂ => False.elim $ by apply hne; rw [h₁, h₂]
    | isFalse hne, _ =>
      match i with
      | .head => true
      | .tail i => delta ta tb hta htb hne i
    | _, isFalse hne =>
      match i with
      | .head => false
      | .tail i => delta fa fb hfa hfb hne i

def eval_delta {xs : List α} (a b : BDD xs) (ha : a.isReduced) (hb : b.isReduced) (hne : a ≠ b) : a.eval (delta a b ha hb hne) ≠ b.eval (delta a b ha hb hne) := by
  induction xs with
  | nil =>
    match a, b with
    | tt, tt => contradiction
    | tt, ff => unfold BDD.eval
    | ff, tt => unfold BDD.eval
    | ff, ff => contradiction
  | cons x xs ih =>
    match a, b with
    | lift a, lift b => apply ih
    | lift a, case tb fb =>
      unfold BDD.eval delta
      match decEq a tb, decEq a fb with
      | isTrue h₁, isTrue h₂ => simp [←h₁, ←h₂, isReduced] at hb
      | isTrue _, isFalse hne => apply ih
      | isFalse hne, isTrue _ => apply ih
      | isFalse hne, isFalse _ => apply ih
    | case ta fa, lift b =>
      unfold BDD.eval delta
      match decEq ta b, decEq fa b with
      | isTrue h₁, isTrue h₂ => simp [h₁, h₂, isReduced] at ha
      | isTrue _, isFalse hne => apply ih
      | isFalse hne, isTrue _ => apply ih
      | isFalse hne, isFalse _ => apply ih
    | case ta fa, case tb fb =>
      unfold BDD.eval delta
      match decEq ta tb, decEq fa fb with
      | isTrue h₁, isTrue h₂ => absurd hne; rw [h₁, h₂]
      | isTrue _, isFalse hne => apply ih
      | isFalse hne, isTrue _ => apply ih
      | isFalse hne, isFalse _ => apply ih

abbrev refute {xs : List α} (a : BDD xs) (h : a.isReduced) : a ≠ BDD.true → Index xs → Bool :=
  delta a BDD.true h true_isReduced

theorem eval_refute {xs : List α} (a : BDD xs) (h : a.isReduced) (hne : a ≠ BDD.true) : a.eval (a.refute h hne) = false := by
  rw [←Bool.not_eq_true]
  rw [←eval_true (xs:=xs) (a.refute h hne)]
  apply eval_delta

abbrev satisfy {xs : List α} (a : BDD xs) (h : a.isReduced) : a ≠ BDD.false → Index xs → Bool :=
  delta a BDD.false h false_isReduced

theorem eval_satisfy {xs : List α} (a : BDD xs) (h : a.isReduced) (hne : a ≠ BDD.false) : a.eval (a.satisfy h hne) = true := by
  rw [←Bool.not_eq_false]
  rw [←eval_false (xs:=xs) (a.satisfy h hne)]
  apply eval_delta

theorem eval_eq_iff_reduce_eq {xs : List α} (a b : BDD xs) : a.eval = b.eval ↔ a.reduce = b.reduce := by
  constr
  · intro heq
    by_contradiction
    | assuming hne =>
      apply eval_delta a.reduce b.reduce a.reduce_isReduced b.reduce_isReduced hne
      rw [eval_reduce, eval_reduce, heq]
  · intro heq
    funext v
    rw [←eval_reduce a, ←eval_reduce b, heq]

end BDD

structure RBDD (xs : List α) where
  toBDD : BDD xs
  isReduced : toBDD.isReduced

namespace RBDD

protected theorem eq : {xs : List α} → {a b : RBDD xs} → a.toBDD = b.toBDD → a = b
| _, ⟨_,_⟩, ⟨_,_⟩, rfl => rfl

protected theorem ext {xs : List α} {a b : RBDD xs} : (∀ v, a.toBDD.eval v = b.toBDD.eval v) → a = b := by
  intro h
  apply RBDD.eq
  rw [←BDD.reduce_eq_self_of_isReduced a.toBDD a.isReduced]
  rw [←BDD.reduce_eq_self_of_isReduced b.toBDD b.isReduced]
  rw [←BDD.eval_eq_iff_reduce_eq]
  funext v
  exact h v

protected abbrev eval {xs : List Bool} (a : RBDD xs) : Bool := a.toBDD.eval Index.val

protected def lift {x : α} {xs : List α} (a : RBDD xs) : RBDD (x :: xs) where
  toBDD := .lift a.toBDD
  isReduced := a.isReduced

protected def true {xs : List α} : RBDD xs where
  toBDD := BDD.true
  isReduced := BDD.true_isReduced

protected def false {xs : List α} : RBDD xs where
  toBDD := BDD.false
  isReduced := BDD.false_isReduced

protected def var {xs : List α} (i : Index xs) : RBDD xs where
  toBDD := BDD.var i
  isReduced := BDD.var_isReduced i

protected def not {xs : List α} (a : RBDD xs) : RBDD xs where
  toBDD := a.toBDD.not
  isReduced := BDD.not_isReduced a.toBDD ▸ a.isReduced

instance instComplement (xs : List α) : Complement (RBDD xs) := ⟨RBDD.not⟩

protected def and {xs : List α} (a b : RBDD xs) : RBDD xs where
  toBDD := (BDD.and a.toBDD b.toBDD).reduce
  isReduced := BDD.reduce_isReduced (BDD.and a.toBDD b.toBDD)

instance instHAnd (xs : List α) : HAnd (RBDD xs) (RBDD xs) (RBDD xs) := ⟨RBDD.and⟩

protected def or {xs : List α} (a b : RBDD xs) : RBDD xs where
  toBDD := (BDD.or a.toBDD b.toBDD).reduce
  isReduced := BDD.reduce_isReduced (BDD.or a.toBDD b.toBDD)

instance instHOr (xs : List α) : HOr (RBDD xs) (RBDD xs) (RBDD xs) := ⟨RBDD.or⟩

protected def xor {xs : List α} (a b : RBDD xs) : RBDD xs where
  toBDD := (BDD.xor a.toBDD b.toBDD).reduce
  isReduced := BDD.reduce_isReduced (BDD.xor a.toBDD b.toBDD)

instance instHXor (xs : List α) : HXor (RBDD xs) (RBDD xs) (RBDD xs) := ⟨RBDD.xor⟩

end RBDD

#exit

class Reflect (xs : List Bool) (a : Bool) extends RBDD xs where
  eval_eq : toBDD.eval Index.val = a

namespace Reflect

instance instReflect (a x : Bool) (xs : List Bool) [Reflect xs a] : Reflect (x :: xs) a where
  toRBDD := .lift (toRBDD a)
  eval_eq := by 
    unfold RBDD.lift BDD.eval
    rw [eval_eq]

instance instSelf (x : Bool) (xs : List Bool) : Reflect (x :: xs) x where
  toRBDD := .var Index.head
  eval_eq := by 
    cases x <;> {
      unfold RBDD.var
      rw [BDD.eval_var]
    }

instance instTrue (xs : List Bool) : Reflect xs true where
  toRBDD := .true
  eval_eq := by
    unfold RBDD.true
    rw [BDD.eval_true]

instance instFalse (xs : List Bool) : Reflect xs false where
  toRBDD := .false
  eval_eq := by 
    unfold RBDD.false
    rw [BDD.eval_false]

instance instNot (a : Bool) (xs : List Bool) [Reflect xs a] : Reflect xs (! a) where
  toRBDD := ~~~ toRBDD a
  eval_eq := by 
    unfold Complement.complement RBDD.not
    rw [BDD.eval_not, eval_eq]

instance instAnd (a b : Bool) (xs : List Bool) [Reflect xs a] [Reflect xs b] : Reflect xs (a && b) where
  toRBDD := toRBDD a &&& toRBDD b
  eval_eq := show ((RBDD.instHAnd xs).hAnd (toRBDD a) (toRBDD b)).eval = (a && b) by
    unfold HAnd.hAnd RBDD.and RBDD.eval
    rw [BDD.eval_reduce, BDD.eval_and, eval_eq, eval_eq]

instance instOr (a b : Bool) (xs : List Bool) [Reflect xs a] [Reflect xs b] : Reflect xs (a || b) where
  toRBDD := toRBDD a ||| toRBDD b
  eval_eq := show ((RBDD.instHOr xs).hOr (toRBDD a) (toRBDD b)).eval = (a || b) by
    unfold HOr.hOr RBDD.or RBDD.eval
    rw [BDD.eval_reduce, BDD.eval_or, eval_eq, eval_eq]

instance instXor (a b : Bool) (xs : List Bool) [Reflect xs a] [Reflect xs b] : Reflect xs (a ^^ b) where
  toRBDD := toRBDD a ^^^ toRBDD b
  eval_eq := show ((RBDD.instHXor xs).hXor (toRBDD a) (toRBDD b)).eval = (a ^^ b) by
    unfold HXor.hXor RBDD.xor RBDD.eval
    rw [BDD.eval_reduce, BDD.eval_xor, eval_eq, eval_eq]

end Reflect

def isTauto (a : Bool) (xs : List Bool) [Reflect xs a] : (Reflect.toRBDD (xs:=xs) a).eval (OBDD.test)

theorem tauto {a : Bool} (xs : List Bool) [Reflect xs a] : (Reflect.toRBDD (xs:=xs) a).toBDD = BDD.true → a = true := by
  intro h
  -- unfold BEq.beq at h
  -- have h := of_decide_eq_true h
  rw [←Reflect.eval_eq (xs:=xs) (a:=a)] 
  rw [h, BDD.eval_true]

variable (a b c : Bool)

def X : RBDD [a,b,c] := Reflect.toRBDD (!c || (c ^^ ((a && (b || !a)) ^^ (a && b))))

#reduce (X a b c).toBDD

example : (!c || (c ^^ ((a && (b || !a)) ^^ (a && b)))) = true := by
  apply tauto [a,b,c]
  apply of_decide_eq_true
  apply Lean.ofReduceBool
  rfl
  done
