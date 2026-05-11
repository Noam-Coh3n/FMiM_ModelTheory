import Mathlib.ModelTheory.DirectLimit
import Mathlib.ModelTheory.ElementaryMaps

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
      refine ⟨fun h => ?_, fun h => ?_⟩ <;> simp only [BoundedFormula.realize_all] <;> intro a
      · simp only [← ih, Fin.comp_snoc]
        apply h
      · refine DirectLimit.inductionOn a fun j a' => ?_
        let ⟨k, ik, jk⟩ := exists_ge_ge i j
        let comm {ℓ} (ℓk) : F ℓ = F k ∘ f ℓ k ℓk :=
          funext fun _ => DirectLimit.of_f.symm
        let eq_def := Unique.eq_default (f i k ik ∘ default : Empty → _)
        rw [comm ik, comm jk, Function.comp_assoc, eq_def]
        simp only [Function.comp_assoc, Function.comp_apply, ← Fin.comp_snoc, ih]
        exact eq_def ▸ BoundedFormula.realize_all.1 (((f i k ik).map_boundedFormula (∀'φ) ..).2 h) _
