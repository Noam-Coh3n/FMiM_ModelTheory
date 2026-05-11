import Mathlib.ModelTheory.DirectLimit
import Mathlib.ModelTheory.ElementaryMaps

open FirstOrder

variable {L : Language} {ι : Type v} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
variable {G : ι → Type w} [∀ i, L.Structure (G i)] (f : ∀ i j, i ≤ j → G i ↪ₑ[L] G j)
variable [DirectedSystem G (f · · ·)]

abbrev system : ∀ i j, i ≤ j → G i ↪[L] G j := fun _ _ h => (f _ _ h).toEmbedding

instance : DirectedSystem G (system f · · ·) := ‹_›

noncomputable def ofₑ (i : ι) : G i ↪ₑ[L] L.DirectLimit G (system f) := sorry
