
class Inv (α : Type _) where
  inv : α → α

postfix:max "⁻¹" => Inv.inv
