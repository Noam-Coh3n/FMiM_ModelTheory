import Mathlib.ModelTheory.DirectLimit
import Mathlib.ModelTheory.ElementaryMaps
import Mathlib.Order.Ideal

open FirstOrder Language DirectLimit

variable {L : Language} {ι : Type v} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
variable {G : ι → Type w} [∀ i, L.Structure (G i)] (f : ∀ i j, i ≤ j → G i ↪ₑ[L] G j)
variable [DirectedSystem G (f · · ·)]

abbrev system : ∀ i j, i ≤ j → G i ↪[L] G j := fun _ _ h => (f _ _ h).toEmbedding

instance : DirectedSystem G (system f · · ·) := ‹_›

noncomputable def ofₑ (i : ι) : G i ↪ₑ[L] L.DirectLimit G (system f) where
  toFun := of L ι G (system f) i
  map_formula' := by
    letI F := of L ι G (system f)
    suffices h : ∀ (n : ℕ) (φ : L.BoundedFormula Empty n) (xs : Fin n → G i),
      φ.Realize (F i ∘ default) (F i ∘ xs) ↔ φ.Realize default xs by
      intro n φ x
      exact φ.realize_relabel_sumInr.symm.trans (_root_.trans (h n _ _) φ.realize_relabel_sumInr)
    intro n φ xs
    induction φ generalizing i with
    | falsum => rfl
    | equal => simp [BoundedFormula.Realize, ← Sum.comp_elim, HomClass.realize_term]
    | rel =>
      simp only [BoundedFormula.Realize, ← Sum.comp_elim, HomClass.realize_term]
      erw [(F i).map_rel]
    | imp _ _ => unfold F at *; simp_all only [BoundedFormula.realize_imp]
    | all φ ih =>
      refine ⟨fun h => ?_, fun _ => ?_⟩ <;> simp only [BoundedFormula.realize_all] <;> intro a
      · simp only [← ih, Fin.comp_snoc]
        apply h
      · refine DirectLimit.inductionOn a fun j a' => ?_
        let ⟨k, ik, jk⟩ := exists_ge_ge i j
        let comm {ℓ} (ℓk) : F ℓ = F k ∘ f ℓ k ℓk :=
          funext fun _ => DirectLimit.of_f.symm
        let eq_dft := Unique.eq_default (f i k ik ∘ default : Empty → _)
        rw [comm ik, comm jk, Function.comp_assoc, eq_dft]
        simp only [Function.comp_assoc, Function.comp_apply, ← Fin.comp_snoc, ih]
        apply eq_dft ▸ ((f i k ik).map_boundedFormula (∀'φ) ..).2
        assumption

open Order

variable {J : Cofinal ι}

instance : SetLike (Cofinal ι) ι := ⟨Cofinal.carrier, fun ⟨_, _⟩ ⟨_, _⟩ _ => by simp_all only⟩

instance : IsDirectedOrder J := by
  constructor
  intro i j
  let ⟨k, ik, jk⟩ := exists_ge_ge (α := ι) i j
  let ⟨ℓ, ℓ_mem, kℓ⟩ := J.isCofinal k
  exact ⟨⟨ℓ, ℓ_mem⟩, ⟨ik.trans kℓ, jk.trans kℓ⟩⟩

open Classical in
instance : Nonempty J := ⟨J.above ofNonempty, J.above_mem _⟩

instance : ∀ (i : J), L.Structure (Set.restrict J G i) :=
  inferInstanceAs <| ∀ (i : J), L.Structure (G i)

instance [DirectedSystem G (f · · ·)] : DirectedSystem (Set.restrict J G) (f · · ·) where
  map_self _ _        := DirectedSystem.map_self' f _
  map_map _ _ _ _ _ _ := DirectedSystem.map_map'  f _ _ _
