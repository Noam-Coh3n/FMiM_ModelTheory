import Mathlib.ModelTheory.DirectLimit
import Mathlib.ModelTheory.ElementaryMaps
import Mathlib.Order.Ideal
import Mathlib.CategoryTheory.Filtered.Final
import FMiM.Category

open FirstOrder Language DirectLimit DirectedSystem

variable {L : Language} {J : Type} [Preorder J] [IsDirectedOrder J] [Nonempty J]
variable {G : J → Type} [∀ i, L.Structure (G i)]

section ElementarySystemsLemma

variable (f : ∀ i j, i ≤ j → G i ↪ₑ[L] G j) [DirectedSystem G (f · · ·)]

abbrev system : ∀ i j, i ≤ j → G i ↪[L] G j := fun _ _ h => (f _ _ h).toEmbedding

instance : DirectedSystem G (system f · · ·) := ‹_›

noncomputable def ofₑ (i : J) : G i ↪ₑ[L] L.DirectLimit G (system f) where
  toFun := of L J G (system f) i
  map_formula' := by
    let F := of L J G (system f)
    suffices h : ∀ (n : ℕ) (φ : L.BoundedFormula Empty n) (xs : Fin n → G i),
      φ.Realize (F i ∘ default) (F i ∘ xs) ↔ φ.Realize default xs by
      intro n φ x
      exact φ.realize_relabel_sumInr.symm.trans (_root_.trans (h n _ _) φ.realize_relabel_sumInr)
    intro n φ xs
    induction φ generalizing i with
    | falsum   => rfl
    | equal    => simp [BoundedFormula.Realize, ← Sum.comp_elim, HomClass.realize_term]
    | rel      => simp only [BoundedFormula.Realize, ← Sum.comp_elim, HomClass.realize_term]
                  erw [(F i).map_rel]
    | imp      => simp_all only [BoundedFormula.realize_imp]
    | all _ ih =>
      refine ⟨fun h => ?_, fun h => ?_⟩ <;> simp only [BoundedFormula.realize_all] <;> intro a
      · simp only [← ih, Fin.comp_snoc]
        apply h
      · refine DirectLimit.inductionOn a fun j a' => ?_
        let ⟨k, ik, jk⟩ := exists_ge_ge i j
        let comm {ℓ} (ℓk) : F ℓ = F k ∘ f ℓ k ℓk := funext fun _ => of_f.symm
        let eq_dft := Unique.eq_default (f i k ik ∘ default : Empty → _)
        rw [comm ik, comm jk, Function.comp_assoc, eq_dft]
        simp only [Function.comp_assoc, Function.comp_apply, ← Fin.comp_snoc, ih]
        apply eq_dft ▸ ((f i k ik).map_boundedFormula ..).2 h

end ElementarySystemsLemma

section Cofinal

open Order Cofinal

variable (f : ∀ ⦃i j⦄, i ≤ j → G i ↪[L] G j) [DirectedSystem G fun _ _ => (f ·)] {K : Cofinal J}

namespace Order.Cofinal

open CategoryTheory

instance : SetLike (Cofinal J) J := ⟨carrier, fun ⟨_, _⟩ _ _ => by simp_all only⟩

abbrev restrict {α} (K : Cofinal J) (f : J → α) : K → α := Set.restrict K f

omit [IsDirectedOrder J] [Nonempty J] in
@[simp]
lemma mem_carrier {x} : x ∈ K.carrier ↔ x ∈ (K : Set J) := Iff.rfl

omit [IsDirectedOrder J] [Nonempty J] in
@[simp]
lemma coe_coe : ((K : Set J) : Type) = (K : Type) := rfl

instance : IsDirectedOrder K := by
  constructor
  intro i j
  let ⟨k, ik, jk⟩ := exists_ge_ge i.1 j.1
  let ⟨ℓ, ℓ_mem, kℓ⟩ := K.isCofinal k
  exact ⟨⟨ℓ, ℓ_mem⟩, ⟨ik.trans kℓ, jk.trans kℓ⟩⟩

instance : Nonempty K := Nonempty.elim ‹_› fun i => ⟨K.above i, K.above_mem i⟩

def inclusion_functor (K : Cofinal J) : K ⥤ J := (OrderEmbedding.subtype _).monotone.functor

instance : K.inclusion_functor.Full := instFullFunctor _

instance inclusion_final : K.inclusion_functor.Final :=
  Functor.final_of_exists_of_isFiltered_of_fullyFaithful _ fun i =>
    ⟨⟨K.above i, K.above_mem i⟩, ⟨(K.le_above i).hom⟩⟩

end Order.Cofinal

instance : ∀ (i : K), L.Structure (K.restrict G i) :=
  inferInstanceAs <| ∀ (i : K), L.Structure (G i)

instance restrictDirected : DirectedSystem (K.restrict G) fun _ _ => (f ·) where
  map_self _ _        := map_self' f _
  map_map _ _ _ _ _ _ := map_map'  f _ _ _

namespace FirstOrder.Language.DirectLimit

theorem of_f' {i j ij} : (of L J G f j).comp (f ij) = of L J G f i :=
  Embedding.ext fun _ => of_f

omit [IsDirectedOrder J] [Nonempty J] in
theorem map_map'' {i j k} {ij : i ≤ j} {jk : j ≤ k} {ik : i ≤ k} : (f jk).comp (f ij) = f ik :=
  Embedding.ext <| map_map f _ _

end FirstOrder.Language.DirectLimit

open CategoryTheory

variable (G K)

noncomputable def cofinal_colim : Limits.ColimitCocone (as_functor (K.restrict G) fun _ _ => (f ·))
  := (K.inclusion_final).colimitCoconeComp _ ⟨DirectLimit' G f, DirectLimit.isColimit G f⟩

end Cofinal
