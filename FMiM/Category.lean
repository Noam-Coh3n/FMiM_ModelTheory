import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.ModelTheory.DirectLimit

open FirstOrder CategoryTheory Language

variable {L : Language}

-- The category of first order structures with embeddings
structure FirstOrder.Language.Struc where
  carrier : Type
  [str : L.Structure carrier]
  [nonempty : Nonempty carrier]

attribute [instance] Struc.str Struc.nonempty

initialize_simps_projections Struc (carrier → coe, -str, -nonempty)

def FirstOrder.Language.mkStruc := Struc.mk (L := L)

instance : CoeSort L.Struc (Type _) :=
  ⟨Struc.carrier⟩

attribute [coe] Struc.carrier

-- variable {E : Language} {M : (L.sum E).Struc}

-- instance : L.Structure M := LHom.sumInl.reduct (L' := L.sum E) M

-- instance : E.Structure M := LHom.sumInr.reduct (L' := L.sum E) M

instance : Category L.Struc where
  Hom M N := M ↪[L] N
  id M := .refl L M
  comp f g := g.comp f

instance : ConcreteCategory L.Struc (L.Embedding · ·) where
  hom := id
  ofHom := id

def iso_eq_equiv {M N : L.Struc} : Equiv (M ≅ N) (M ≃[L] N) where
  toFun := fun ⟨f, g, fg, gf⟩ => ⟨⟨f, g, Embedding.ext_iff.1 fg, Embedding.ext_iff.1 gf⟩, f.2, f.3⟩
  invFun := fun f => ⟨f.toEmbedding, f.symm.toEmbedding,
    Equiv.symm_comp_self_toEmbedding f, Equiv.self_comp_symm_toEmbedding f⟩

variable {J : Type} [Preorder J] [IsDirectedOrder J] [Nonempty J]
variable (G : J → Type) [∀ i, L.Structure (G i)] [∀ i, Nonempty (G i)]
variable (f : ∀ ⦃i j⦄, i ≤ j → G i ↪[L] G j) [DirectedSystem G fun _ _ => (f ·)]

def as_functor : J ⥤ L.Struc where
  obj i        := .mk <| G i
  map ij       := f <| ij.le
  map_id _     := Embedding.ext fun _ => FirstOrder.Language.DirectedSystem.map_self _ _
  map_comp _ _ := Embedding.ext fun _ => (FirstOrder.Language.DirectedSystem.map_map _ _ _ _).symm

instance : Nonempty (L.DirectLimit G f) :=
  ⟨.of L J G f Classical.ofNonempty Classical.ofNonempty⟩

noncomputable def DirectLimit' : Limits.Cocone (as_functor G f) where
  pt := .mk <| L.DirectLimit G f
  ι := ⟨DirectLimit.of L J G f, fun _ _ _ => Embedding.ext fun _ => DirectLimit.of_f⟩

noncomputable def DirectLimit.isColimit : Limits.IsColimit (DirectLimit' G f) where
  desc c := FirstOrder.Language.DirectLimit.lift _ _ _ _ c.ι.app <| comm c
  uniq t m h := by
    apply Eq.trans <| Embedding.ext <| FirstOrder.Language.DirectLimit.lift_unique m
    congr
    ext1
    apply h
where comm c := fun _ _ ij => Embedding.ext_iff.1 (c.ι.naturality (homOfLE ij))

variable (F : J ⥤ L.Struc)

instance : DirectedSystem (fun i => F.obj i) (fun _ _ ij => F.map ij.hom) where
  map_self := by simp
  map_map k j i ij jk := Embedding.ext_iff.mp (F.4 ij.hom jk.hom).symm
