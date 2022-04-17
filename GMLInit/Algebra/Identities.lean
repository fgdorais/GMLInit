import GMLInit.Prelude

namespace Algebra

section Hom
variable {α β} (hom : α → β)
  (ct₁ : outParam α) (ct₂ : outParam β)
  (fn₁ : outParam (α → α)) (fn₂ : outParam (β → β))
  (op₁ : outParam (α → α → α)) (op₂ : outParam (β → β → β))

class HomCt : Prop where
  protected hom_ct : hom ct₁ = ct₂
def hom_ct {ct₁ ct₂} [self : HomCt hom ct₁ ct₂] := self.hom_ct

class HomFn : Prop where
  protected hom_fn (x) : hom (fn₁ x) = fn₂ (hom x)
def hom_fn {fn₁ fn₂} [self : HomFn hom fn₁ fn₂] := self.hom_fn

class HomOp : Prop where
  protected hom_op (x y) : hom (op₁ x y) = op₂ (hom x) (hom y)
def hom_op {op₁ op₂} [self : HomOp hom op₁ op₂] := self.hom_op

end Hom

section Fn
variable {α} (fn : α → α) (ct : outParam α) (fn' : outParam (α → α))

class FnFix : Prop where
  protected fn_fix : fn ct = ct
def fn_fix {ct} [self : FnFix fn ct] := self.fn_fix

class FnComm : Prop where
  protected fn_comm (x) : fn (fn' x) = fn' (fn x)
def fn_comm {fn'} [self : FnComm fn fn'] := self.fn_comm

class FnLeftInv : Prop where
  protected fn_left_inv (x) : fn' (fn x) = x
def fn_left_inv {fn'} [self : FnLeftInv fn fn'] := self.fn_left_inv

class FnRightInv : Prop where
  protected fn_right_inv (x) : fn (fn' x) = x
def fn_right_inv {fn'} [self : FnRightInv fn fn'] := self.fn_right_inv

class FnIdem : Prop where
  protected fn_idem (x) : fn (fn x) = fn x
def fn_idem [self : FnIdem fn] := self.fn_idem

class FnInvol : Prop where
  protected fn_invol (x) : fn (fn x) = x
def fn_invol [self : FnInvol fn] := self.fn_invol

end Fn

section Op
variable {α} (op : α → α → α) (op' : outParam (α → α → α)) (inv : outParam (α → α)) (id : outParam α) (nil : outParam α)

local infix:70 " ⋆ " => op
local infix:65 " ⊹ " => op'
local postfix:max "⁻¹" => inv
local notation "e" => id

class OpAssoc : Prop where
  protected op_assoc (x y z) : (x ⋆ y) ⋆ z = x ⋆ (y ⋆ z)
def op_assoc [self : OpAssoc op] := self.op_assoc

class OpComm : Prop where
  protected op_comm (x y) : x ⋆ y = y ⋆ x
def op_comm [self : OpComm op] := self.op_comm

class OpLeftComm : Prop where
  protected op_left_comm (x y z) : x ⋆ (y ⋆ z) = y ⋆ (x ⋆ z)
def op_left_comm [self : OpLeftComm op] := self.op_left_comm

class OpRightComm : Prop where
  protected op_right_comm (x y z) : (x ⋆ y) ⋆ z = (x ⋆ z) ⋆ y
export OpRightComm (op_right_comm)
def op_right_comm [self : OpRightComm op] := self.op_right_comm

class OpCrossComm : Prop where
  protected op_cross_comm (x₁ x₂ y₁ y₂) : (x₁ ⋆ x₂) ⋆ (y₁ ⋆ y₂) = (x₁ ⋆ y₁) ⋆ (x₂ ⋆ y₂)
def op_cross_comm [self : OpCrossComm op] := self.op_cross_comm

class OpLeftId : Prop where
  op_left_id (x) : e ⋆ x = x
def op_left_id {id} [self : OpLeftId op id] := self.op_left_id

class OpRightId : Prop where
  protected op_right_id (x) : x ⋆ e = x
def op_right_id {id} [self : OpRightId op id] := self.op_right_id

class OpLeftInv : Prop where
  protected op_left_inv (x) : x⁻¹ ⋆ x = e
def op_left_inv {inv id} [self : OpLeftInv op inv id] := self.op_left_inv

class OpRightInv : Prop where
  protected op_right_inv (x) : x ⋆ x⁻¹ = e
def op_right_inv {inv id} [self : OpRightInv op inv id] := self.op_right_inv

class OpLeftNil : Prop where
  protected op_left_nil (x) : nil ⋆ x = nil
def op_left_nil {nil} [self : OpLeftNil op nil] := self.op_left_nil

class OpRightNil : Prop where
  protected op_right_nil (x) : x ⋆ nil = nil
def op_right_nil {nil} [self : OpRightNil op nil] := self.op_right_nil

class OpLeftCancel : Prop where
  protected op_left_cancel (x) {y z} : x ⋆ y = x ⋆ z → y = z
def op_left_cancel [self : OpLeftCancel op] := self.op_left_cancel

class OpRightCancel : Prop where
  protected op_right_cancel (x) {y z} : y ⋆ x = z ⋆ x → y = z
def op_right_cancel [self : OpRightCancel op] := self.op_right_cancel

class OpLeftDistrib : Prop where
  protected op_left_distrib (x y z) : x ⋆ (y ⊹ z) = x ⋆ y ⊹ x ⋆ z
def op_left_distrib {op'} [self : OpLeftDistrib op op'] := self.op_left_distrib

class OpRightDistrib : Prop where
  protected op_right_distrib (x y z) : (x ⊹ y) ⋆ z = x ⋆ z ⊹ y ⋆ z
def op_right_distrib {op'} [self : OpRightDistrib op op'] := self.op_right_distrib

end Op

section DOp
variable {α} {β : α → α → Sort _} (op : {{a b c : α}} → β b c → β a b → β a c) (inv : outParam ({{a b : α}} → β a b → β b a)) (id : outParam ({a : α} → β a a))

class DOpAssoc : Prop where
  protected dop_assoc {{a b c d}} (x : β c d) (y : β b c) (z : β a b) : op (op x y) z = op x (op y z)
abbrev dop_assoc [self : DOpAssoc op] := self.dop_assoc

class DOpLeftId : Prop where
  protected dop_left_id {{a b}} (x : β a b) : op id x = x
abbrev dop_left_id {id : {a : α} → β a a} [self : DOpLeftId op id] := self.dop_left_id

class DOpRightId : Prop where
  protected dop_right_id {{a b}} (x : β a b) : op x id = x
abbrev dop_right_id (op) {id : {a : α} → β a a} [self : DOpRightId op id] := self.dop_right_id

class DOpLeftInv : Prop where
  protected dop_left_inv {{a b}} (x : β a b) : op (inv x) x = id
abbrev dop_left_inv {inv} {id : {a : α} → β a a} [self : DOpLeftInv op inv id] := self.dop_left_inv

class DOpRightInv : Prop where
  protected dop_right_inv {{a b}} (x : β a b) : op x (inv x) = id
abbrev dop_right_inv {inv} {id : {a : α} → β a a} [self : DOpRightInv op inv id] := self.dop_right_inv

class DOpLeftCancel : Prop where
  protected dop_left_cancel {{a b c}} (x : β b c) {y z : β a b} : op x y = op x z → y = z
abbrev dop_left_cancel [self : DOpLeftCancel op] := self.dop_left_cancel

class DOpRightCancel : Prop where
  protected dop_right_cancel {{a b c}} (x : β a b) {y z : β b c} : op y x = op z x → y = z
abbrev dop_right_cancel [self : DOpRightCancel op] := self.dop_right_cancel

end DOp

section Inv
variable {α} (inv : α → α) (op : outParam (α → α → α)) (id : outParam α)

class InvOp : Prop where
  protected inv_op (x y) : inv (op x y) = op (inv y) (inv x)
def inv_op {op} [self : InvOp inv op] := self.inv_op

class InvHom : Prop where
  protected inv_hom (x y) : inv (op x y) = op (inv x) (inv y)
def inv_hom {op} [self : InvHom inv op] := self.inv_hom

class InvId : Prop where
  protected inv_id : inv id = id
def inv_id {id} [self : InvId inv id] := self.inv_id

end Inv

section Add
variable (α) [HAdd α α α] [Neg α] [OfNat α 0]

abbrev add_assoc [self : OpAssoc (.+.:α→α→α)] := self.op_assoc
abbrev add_comm [self : OpComm (.+.:α→α→α)] := self.op_comm
abbrev add_left_comm [self : OpLeftComm (.+.:α→α→α)] := self.op_left_comm
abbrev add_right_comm [self : OpRightComm (.+.:α→α→α)] := self.op_right_comm
abbrev add_cross_comm [self : OpCrossComm (.+.:α→α→α)] := self.op_cross_comm
abbrev add_zero_left [self : OpLeftId (.+.:α→α→α) 0] := self.op_left_id
abbrev add_zero_right [self : OpRightId (.+.:α→α→α) 0] := self.op_right_id
abbrev add_neg_left [self : OpLeftInv (.+.:α→α→α) (-.) 0] := self.op_left_inv
abbrev add_neg_right [self : OpRightInv (.+.:α→α→α) (-.) 0] := self.op_right_inv

abbrev neg_add [self : InvHom (-.:α→α) (.+.)] := self.inv_hom
abbrev neg_neg [self : FnInvol (-.:α→α)] := self.fn_invol
abbrev neg_zero [self : InvId (-.:α→α) 0] := self.inv_id

end Add

section Mul
variable (α) [HMul α α α] [HAdd α α α] [Inv α] [OfNat α 1] [OfNat α 0]

abbrev mul_assoc [self : OpAssoc (.*.:α→α→α)] := self.op_assoc
abbrev mul_comm [self : OpComm (.*.:α→α→α)] := self.op_comm
abbrev mul_left_comm [self : OpLeftComm (.*.:α→α→α)] := self.op_left_comm
abbrev mul_right_comm [self : OpRightComm (.*.:α→α→α)] := self.op_right_comm
abbrev mul_cross_comm [self : OpCrossComm (.*.:α→α→α)] := self.op_cross_comm
abbrev mul_one_left [self : OpLeftId (.*.:α→α→α) 1] := self.op_left_id
abbrev mul_one_right [self : OpRightId (.*.:α→α→α) 1] := self.op_right_id
abbrev mul_inv_left [self : OpLeftInv (.*.:α→α→α) (.⁻¹) 1] := self.op_left_inv
abbrev mul_inv_right [self : OpRightInv (.*.:α→α→α) (.⁻¹) 1] := self.op_right_inv
abbrev mul_left_distrib [self : OpLeftDistrib (.*.:α→α→α) (.+.)] := self.op_left_distrib
abbrev mul_right_distrib [self : OpRightDistrib (.*.:α→α→α) (.+.)] := self.op_right_distrib
abbrev mul_zero_left [self : OpLeftNil (.*.:α→α→α) 0] := self.op_left_nil
abbrev mul_zero_right [self : OpRightNil (.*.:α→α→α) 0] := self.op_right_nil

abbrev inv_mul [self : InvOp (.⁻¹:α→α) (.*.)] := self.inv_op
abbrev inv_inv [self : FnInvol (.⁻¹:α→α)] := self.fn_invol
abbrev inv_one [self : InvId (.⁻¹:α→α) 1] := self.inv_id

end Mul

end Algebra
