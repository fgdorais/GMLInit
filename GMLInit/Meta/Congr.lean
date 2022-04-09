import GMLInit.Logic.Congr
import GMLInit.Meta.ListConnectives

macro "congr_args" : tactic => `(tactic| apply CongrArgs.eq; constr_all)
