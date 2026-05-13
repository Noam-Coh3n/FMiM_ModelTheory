import FMiM.ElementarySystems
import Mathlib.ModelTheory.Satisfiability

open FirstOrder Language

variable {L E₁ E₂ : Language}


variable {T : L.Theory} {T₁ : (L.sum E₁).Theory} {T₂ : (L.sum E₂).Theory}
variable {T_sub₁ : LHom.sumInl.onTheory T ⊆ T₁} {T_sub₂ : LHom.sumInl.onTheory T ⊆ T₂}
variable {T_complete : T.IsComplete}

theorem Robinson (sat₁ : T₁.IsSatisfiable) (sat₂ : T₂.IsSatisfiable) : T.IsSatisfiable := sorry
