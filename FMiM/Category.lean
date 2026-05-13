import Mathlib.ModelTheory.Bundled
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.ModelTheory.DirectLimit
import Mathlib.CategoryTheory.Filtered.Basic

open FirstOrder CategoryTheory

namespace FirstOrder.Language

variable {L : Language}

-- The category of first order structures with embeddings
structure Struc where
  of ::
  carrier : Type
  [str : L.Structure carrier]

attribute [instance] Struc.str

initialize_simps_projections Struc (carrier → coe, -str)

instance {L : Language} : CoeSort L.Struc (Type _) :=
  ⟨Struc.carrier⟩

attribute [coe] Struc.carrier

instance : Category L.Struc where
  Hom M N := M ↪[L] N
  id M := .refl L M
  comp f g := g.comp f

instance : ConcreteCategory L.Struc (L.Embedding · ·) where
  hom := id
  ofHom := id

variable {L : Language} {J : Type} [Preorder J] [IsDirectedOrder J] [Nonempty J]
variable (G : J → Type) [∀ i, L.Structure (G i)] (f : ∀ ⦃i j⦄, i ≤ j → G i ↪[L] G j)
variable [DirectedSystem G fun _ _ => (f ·)]

def as_functor : J ⥤ L.Struc where
  obj i        := .of <| G i
  map ij       := f <| ij.le
  map_id _     := Embedding.ext fun _ => DirectedSystem.map_self _ _
  map_comp _ _ := Embedding.ext fun _ => (DirectedSystem.map_map _ _ _ _).symm

noncomputable def DirectLimit' : Limits.Cocone (as_functor G f) where
  pt := .of <| DirectLimit G f
  ι := ⟨DirectLimit.of L J G f, fun _ _ _ => Embedding.ext fun _ => DirectLimit.of_f⟩

noncomputable def DirectLimit.isColimit : Limits.IsColimit (DirectLimit' G f) where
  desc c := lift _ _ _ _ c.ι.app (comm c)
  uniq t m h := by
    apply Eq.trans <| Embedding.ext <| lift_unique m
    congr
    ext1
    apply h
where comm c := fun _ _ ij => Embedding.ext_iff.mp (c.ι.naturality (homOfLE ij))

end FirstOrder.Language
