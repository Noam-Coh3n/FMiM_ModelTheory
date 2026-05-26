import Mathlib.ModelTheory.ElementaryMaps
import FMiM.Category
import Mathlib.Order.Ideal
import Mathlib.CategoryTheory.Filtered.Final

open FirstOrder Language

variable {L : Language} {J : Type} [Preorder J] [IsDirectedOrder J] [Nonempty J]
variable {G : J → Type} [∀ i, L.Structure (G i)] [∀ i, Nonempty (G i)]
variable (f : ∀ i j, i ≤ j → G i ↪ₑ[L] G j) [DirectedSystem G (f · · ·)]

namespace FirstOrder.Language.DirectedSystem

/-- Cast a system of elementary embeddings to a system of embeddings. -/
abbrev system : ∀ i j, i ≤ j → G i ↪[L] G j := fun _ _ h => (f _ _ h).toEmbedding

instance : DirectedSystem G (system f · · ·) := ‹_›

variable {G' : ℕ → Type w} [∀ i, L.Structure (G' i)] (f' : ∀ n, G' n ↪ₑ[L] G' (n + 1))

/-- Elementary analogue of *FirstOrder.Language.DirectedSystem.natLERec*.

Given a chain of elementary embeddings of structures indexed by `ℕ`, defines a `DirectedSystem` by
composing them. -/
def natLERecₑ (m n : ℕ) (h : m ≤ n) : G' m ↪ₑ[L] G' n :=
  Nat.leRecOn h (f' _).comp (.refl ..)

@[simp, push]
theorem coe_natLERecₑ (m n : ℕ) (h : m ≤ n) :
    ⇑(natLERecₑ f' m n h) = Nat.leRecOn h (f' _) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  ext x
  induction k with
  | zero => simp [natLERecₑ, Nat.leRecOn_self]
  | succ k ih =>
    erw [Nat.leRecOn_succ le_self_add, natLERecₑ, Nat.leRecOn_succ le_self_add, ← natLERecₑ,
      ElementaryEmbedding.comp_apply, ih]

theorem coe_natLERecₑ_eq_natLERec (m n : ℕ) (h : m ≤ n) :
  ⇑(natLERecₑ f' m n h) = (natLERec (fun k => (f' k).toEmbedding) m n h) := by
    rw [coe_natLERec, coe_natLERecₑ]
    rfl

instance natLERecₑ.directedSystem : DirectedSystem G' (natLERecₑ f' · · ·) := by
  conv =>
    congr
    ext _ _ _
    rw [coe_natLERecₑ_eq_natLERec]
  infer_instance


end DirectedSystem

namespace DirectLimit

open DirectedSystem

/-- Elementary analogue of *FirstOrder.Language.DirectLimit.of*.

Given a directed system *f* of elementary embeddings, the canonical maps into *L.DirectLimit G f*
are elementary. -/
noncomputable def ofₑ (i : J) : G i ↪ₑ[L] L.DirectLimit G (system f) where
  toFun := of L J G (system f) i
  map_formula' := by
    let F := of L J G (system f)
    suffices h : ∀ (n : ℕ) (φ : L.BoundedFormula Empty n) (xs : Fin n → G i),
      φ.Realize (F i ∘ default) (F i ∘ xs) ↔ φ.Realize default xs by
      intro n φ x
      exact φ.realize_relabel_sumInr.symm.trans (.trans (h n _ _) φ.realize_relabel_sumInr)
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

end FirstOrder.Language.DirectLimit

/- This section is dedicated to proving that, given a cofinal subset of an L-directed system,
its direct limit is L-isomorphic to the direct limit of the entire system. -/
section Cofinal

open Order Cofinal DirectedSystem

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

/- A cofinal subset of a directed order is directed. -/
instance : IsDirectedOrder K := by
  constructor
  intro i j
  let ⟨k, ik, jk⟩ := exists_ge_ge i.1 j.1
  let ⟨ℓ, ℓ_mem, kℓ⟩ := K.isCofinal k
  exact ⟨⟨ℓ, ℓ_mem⟩, ⟨ik.trans kℓ, jk.trans kℓ⟩⟩

instance : Nonempty K := Nonempty.elim ‹_› fun i => ⟨K.above i, K.above_mem i⟩

/- View the inclusion of a cofinal subset as a functor -/
def inclusion_functor (K : Cofinal J) : K ⥤ J := (OrderEmbedding.subtype _).monotone.functor

instance : K.inclusion_functor.Full := instFullFunctor _

/- The inclusion of a cofinal subset into a directed order is a final functor -/
instance inclusion_final : K.inclusion_functor.Final :=
  Functor.final_of_exists_of_isFiltered_of_fullyFaithful _ fun i =>
    ⟨⟨K.above i, K.above_mem i⟩, ⟨(K.le_above i).hom⟩⟩

end Order.Cofinal

instance : ∀ (i : K), L.Structure (K.restrict G i) :=
  inferInstanceAs <| ∀ (i : K), L.Structure (G i)

instance restrictDirected : DirectedSystem (K.restrict G) fun _ _ => (f ·) where
  map_self _ _        := map_self' f _
  map_map _ _ _ _ _ _ := map_map'  f _ _ _

instance restrictNonempty : ∀ (i : K), Nonempty (K.restrict G i) :=
  inferInstanceAs <| ∀ (i : K), Nonempty (G i)

namespace FirstOrder.Language.DirectLimit

omit [∀ i, Nonempty (G i)] in
theorem of_f' {i j ij} : (of L J G f j).comp (f ij) = of L J G f i :=
  Embedding.ext fun _ => of_f

omit [IsDirectedOrder J] [Nonempty J] [∀ i, Nonempty (G i)] in
theorem map_map'' {i j k} {ij : i ≤ j} {jk : j ≤ k} {ik : i ≤ k} : (f jk).comp (f ij) = f ik :=
  Embedding.ext <| map_map f _ _

end FirstOrder.Language.DirectLimit

open CategoryTheory

variable (G K)

/- The direct limit of the entire system is also the colimit of the restricted system. -/
noncomputable def cofinal_colim
  : Limits.ColimitCocone (as_functor (K.restrict G) fun _ _ => (f ·))
  := (K.inclusion_final).colimitCoconeComp _ ⟨DirectLimit' G f, DirectLimit.isColimit G f⟩

/- Note that from *cofinal_colim*, we can prove
*L.DirectLimit G f ≅[L] L.DirectLimit (K.restrict G) (fun _ _ => (f ·)* by isomorphicity of
colimits (e.g. using *CategoryTheory.Limits.IsColimit.coconePointUniqueUpToIso*).
Unfortunately, I ran out of time and have not managed to incorporate this into the proof yet. -/

end Cofinal
