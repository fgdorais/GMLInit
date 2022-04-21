import Lean

infix:50 " ≅ " => HEq

class Inv (α : Type _) where
  inv : α → α
postfix:max "⁻¹" => Inv.inv

class Apart (α : Type _) where
  apart : α → α → Prop
infix:50 " ≶ " => Apart.apart

register_simp_attr elim_casts "simp attribute for `elim_casts` tactic"
