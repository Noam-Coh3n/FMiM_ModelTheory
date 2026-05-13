import FMiM.ElementarySystems

open FirstOrder

variable {L E₁ E₂ : Language}

abbrev L₁ := L.sum E₁
abbrev L₂ := L.sum E₂

variable {T : L.Theory} {T₁ : L₁.Theory} {T₂ : L₂.Theory}
