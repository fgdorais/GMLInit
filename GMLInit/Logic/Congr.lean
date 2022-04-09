import GMLInit.Logic.ListConnectives

class Congr {α} (lhs rhs : α) where
  protected hyps : List Prop
  protected eq : All hyps → lhs = rhs

class CongrRefl {α} (lhs rhs : α) where
  protected eq : lhs = rhs

namespace CongrRefl

instance toCongr {α} (lhs rhs : α) [CongrRefl lhs rhs] : Congr lhs rhs where
  hyps := []
  eq _ := CongrRefl.eq

instance {α} (x : α) : CongrRefl x x where
  eq := rfl

end CongrRefl

class CongrArgs {α} (lhs rhs : α) extends Congr lhs rhs

namespace CongrArgs

instance {α β} (f₁ f₂ : α → β) (x₁ x₂ : α) [CongrArgs f₁ f₂] : CongrArgs (f₁ x₁) (f₂ x₂) where
  hyps := (x₁ = x₂) :: Congr.hyps f₁ f₂
  eq | All.cons hx hf => Congr.eq hf ▸ hx ▸ rfl

instance {α β} (f₁ f₂ : α → β) (x₁ x₂ : α) [inst : CongrRefl f₁ f₂] : CongrArgs (f₁ x₁) (f₂ x₂) where
  hyps := [x₁ = x₂]
  eq h := inst.eq ▸ (All.head h) ▸ rfl

syntax "congrArgs" (term:max <|> hole <|> syntheticHole)+ : term
macro_rules
| `(congrArgs $hs*) => `(CongrArgs.eq (All.intro [$hs,*]))

end CongrArgs
