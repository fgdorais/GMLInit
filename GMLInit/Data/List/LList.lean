import GMLInit.Data.Fin
import GMLInit.Data.List.Basic
import GMLInit.Data.List.HList
import GMLInit.Data.Nat

def LList (α) (n : Nat) := HList (List.replicate n α)

namespace LList

@[matchPattern] protected def nil {α} : LList α 0 := HList.nil

@[matchPattern] protected def cons {α n} (a : α) : LList α n → LList α (n+1) := HList.cons a

scoped infixr:67 " :: " => LList.cons
scoped syntax (name := llist) "[" term,* "]"  : term
scoped macro_rules (kind := llist)
  | `([ ])           => `(LList.nil)
  | `([ $a ])        => `(LList.cons $a LList.nil)
  | `([ $a, $as,* ]) => `(LList.cons $a [$as,*])

protected theorem cons_hcongr {α β} {n m} {a : α} {b : β} {as : LList α n} {bs : LList β m} : α = β → n = m → a ≅ b → as ≅ bs → LList.cons a as ≅ LList.cons b bs
| rfl, rfl, HEq.rfl, HEq.rfl => HEq.rfl

@[eliminator] protected def rec {α} {motive : (n : Nat) → LList α n → Sort _} (nil : motive 0 LList.nil) (cons : {n : Nat} → (a : α) → (as : LList α n) → motive n as → motive (n+1) (LList.cons a as))
: {n : Nat} → (as : LList α n) → motive n as
| 0, .nil => nil
| _+1, .cons a as => cons a as (LList.rec nil cons as)

protected def recOn {α n} (as : LList α n) {motive : (n : Nat) → LList α n → Sort _} (nil : motive 0 HList.nil) (cons : {n : Nat} → (a : α) → (as : LList α n) → motive n as → motive (n+1) (LList.cons a as)) 
: motive n as := LList.rec nil cons as

protected def casesOn {α n} (as : LList α n) {motive : (n : Nat) → LList α n → Sort _} (nil : motive 0 HList.nil) (cons : {n : Nat} → (a : α) → (as : LList α n) → motive (n+1) (LList.cons a as))
: motive n as := LList.rec nil (fun a as _ => cons a as) as

protected def append {α n} (as : LList α n) (bs : LList α m) : LList α (m + n) :=
show HList (List.replicate (m + n) α) from List.replicate_add α m n ▸ HList.append as bs

protected theorem nil_append {α m} (bs : LList α m) : LList.append [] bs = bs := rfl

protected theorem cons_append {α n m} (a : α) (as : LList α n) (bs : LList α m) : LList.append (a :: as) bs = a :: (LList.append as bs) := by
  apply eq_of_heq
  unfold HAppend.hAppend LList.append LList.cons
  elim_casts
  rw [HList.cons_append]
  apply HList.cons_hcongr
  · reflexivity
  · rw [List.replicate_add]
  · reflexivity using (.≅.)
  · elim_casts
    reflexivity using (.≅.)

protected theorem append_nil {α n} (as : LList α n) : LList.append as [] ≅ as := by
  induction as with
  | nil => 
    rw [LList.nil_append]
    reflexivity using (.≅.)
  | cons _ _ ih => 
    rw [LList.cons_append]
    apply LList.cons_hcongr
    · reflexivity
    · rw [Nat.zero_add]
    · reflexivity using (.≅.)
    · exact ih ..

protected theorem append_assoc {α l m n} (as : LList α l) (bs : LList α m) (cs : LList α n) : LList.append (LList.append as bs) cs ≅ LList.append as (LList.append bs cs) := by
  induction as with
  | nil => 
    repeat rw [LList.nil_append]
    reflexivity using (.≅.)
  | cons _ _ ih => 
    repeat rw [LList.cons_append]
    apply LList.cons_hcongr
    · reflexivity
    · rw [Nat.add_assoc]
    · reflexivity using (.≅.)
    · exact ih ..

protected def mk {α} : {n : Nat} → (Fin n → α) → LList α n
| 0, _ => LList.nil
| _+1, v => v Fin.zero :: LList.mk fun i => v (Fin.succ i)

theorem mk_zero {α} (f : Fin 0 → α) : LList.mk f = LList.nil := rfl

theorem mk_succ {α n} (f : Fin (n+1) → α) : LList.mk f = f Fin.zero :: LList.mk fun i => f (Fin.succ i) := rfl

protected def eval {α} : {n : Nat} → LList α n → (i : Fin n) → α
| _+1, a::_, ⟨0, _⟩ => a
| _+1, _::as, ⟨i+1, hi⟩ => LList.eval as ⟨i, Nat.lt_of_succ_lt_succ hi⟩

theorem eval_cons_zero {α n} (a : α) (as : LList α n) : (a :: as).eval Fin.zero = a := by
  unfold Fin.zero LList.eval

theorem eval_cons_succ {α n} (a : α) (as : LList α n) (i : Fin n) : (a :: as).eval (Fin.succ i) = as.eval i := by
  unfold Fin.succ LList.eval
  apply congrArg
  apply Fin.eq
  rfl

def equiv (α n) : Equiv (LList α n) (Fin n → α) where
  fwd := LList.eval
  rev := LList.mk
  spec := by
    intros as f
    constr
    · intro h
      cases h
      induction as with
      | nil => rfl
      | cons a as ih => 
        rw [LList.mk_succ]
        rw [LList.eval_cons_zero]
        apply congrArg
        transitivity (LList.mk (LList.eval as))
        · apply congrArg
          funext i
          rw [LList.eval_cons_succ]
        · exact ih ..
    · intro h
      cases h
      induction n with
      | zero => 
        funext i
        cases i
        contradiction
      | succ n ih =>
        funext i
        rw [LList.mk_succ]
        cases i using Fin.casesZeroSuccOn with
        | zero => rw [LList.eval_cons_zero]
        | succ i => rw [LList.eval_cons_succ, ih]

end LList
