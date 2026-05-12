import Mathlib.ModelTheory.Bundled
import Mathlib.CategoryTheory.ConcreteCategory.Basic

open FirstOrder CategoryTheory

namespace FirstOrder.Language

variable {L : Language}

-- The category of first order structures with embeddings
structure Struc where
  of ::
  carrier : Type*
  [str : L.Structure carrier]

attribute [instance] Struc.str

initialize_simps_projections Struc (carrier → coe, -str)

instance {L : FirstOrder.Language} : CoeSort L.Struc (Type _) :=
  ⟨Struc.carrier⟩

attribute [coe] Struc.carrier

instance : CategoryTheory.Category (L.Struc) where
  Hom M N := M ↪[L] N
  id M := .refl L M
  comp f g := g.comp f

end FirstOrder.Language
