import FMiM.ElementarySystems
import Mathlib.ModelTheory.Satisfiability
import Mathlib.ModelTheory.Bundled

set_option linter.unusedSectionVars false

open FirstOrder Language CategoryTheory

variable {L E E₁ E₂ : Language}

section FreshConstants

variable {α : Type} [DecidableEq α]

noncomputable def exs_consts (φ : L[[α]].Sentence) : L.Sentence :=
  FirstOrder.Language.Formula.iExs φ.constantsVarsEquiv.freeVarFinset <|
    φ.constantsVarsEquiv.restrictFreeVar .inr

variable {φ : L[[α]].Sentence} {M : Type} [L.Structure M] [Nonempty M]

variable (M)

noncomputable def expand_of_sat_exs [h : M ⊨ {exs_consts φ}] : Theory.ModelType {φ} := by
  letI : (constantsOn α).Structure M :=
    constantsOn.structure fun a =>
    if mem : _ then
      (Formula.realize_iExs.mp <| Theory.model_singleton_iff.1 h).choose ⟨.inl a, mem⟩
    else
      Classical.ofNonempty
  refine Theory.ModelType.mk (is_model := ?_) M
  · refine Theory.model_singleton_iff.2 <| BoundedFormula.realize_constantsVarsEquiv.1 ?_
    apply (BoundedFormula.realize_restrictFreeVar _ _).1
    · exact (Formula.realize_iExs.mp (Theory.model_singleton_iff.1 h)).choose_spec
    · exact fun ⟨.inl a, mem⟩ => Eq.symm <| dite_cond_eq_true (eq_true mem)

end FreshConstants

theorem isSatisfiable_union_of_finite_unions {S T : L.Theory}
  (h : ∀ (S0 T0 : Finset L.Sentence), ↑S0 ⊆ S → ↑T0 ⊆ T → (S0 ∪ T0 : L.Theory).IsSatisfiable)
    : (S ∪ T).IsSatisfiable := by
  refine (S ∪ T).isSatisfiable_iff_isFinitelySatisfiable.mpr (fun U hU => ?_)
  rw [← (Set.inter_union_distrib_left _ _ _).symm.trans (Set.inter_eq_self_of_subset_left hU)]
  have := fun X => Set.Finite.coe_toFinset <| (U.finite_toSet).inter_of_left X
  rw [← this S, ← this T]
  apply h <;> simp only [Set.Finite.coe_toFinset, Set.inter_subset_right]

def Theory.ModelType.toStruc {T : L.Theory} (M : T.ModelType) : L.Struc := .mk M

variable {A B : Type} [L.Structure A] [L.Structure B] [(L.sum E).Structure B]
variable [(.sumInl : _ →ᴸ L.sum E).IsExpansionOn B]

private abbrev ℒ₁ : L[[A]] →ᴸ (L.sum E)[[A]][[B]] :=
  .comp .sumInl <| .addConstants _ .sumInl

private abbrev ℒ₂ : (L.sum E)[[B]] →ᴸ (L.sum E)[[A]][[B]] :=
  .addConstants _ .sumInl

namespace FirstOrder.Language.LHom

theorem comp_injective (hg : g.Injective) (hf : f.Injective) : (LHom.comp g f).Injective where
  onFunction h := Function.Injective.comp hg.1 hf.1 h
  onRelation h := Function.Injective.comp hg.2 hf.2 h

theorem sumMap_injective (hf : f.Injective) (hg : g.Injective) : (LHom.sumMap f g).Injective where
  onFunction h := Function.Injective.sumMap hf.1 hg.1 h
  onRelation h := Function.Injective.sumMap hf.2 hg.2 h

theorem id_injective : (LHom.id L).Injective where
  onFunction h := Function.injective_id h
  onRelation h := Function.injective_id h

theorem addConstants_injective (hf : f.Injective) : (LHom.addConstants α f).Injective :=
  f.sumMap_injective hf id_injective

end FirstOrder.Language.LHom

lemma Iℒ₁ : (@ℒ₁ L E A B).Injective := by
  apply LHom.comp_injective
  · exact LHom.sumInl_injective
  · apply LHom.addConstants_injective
    exact LHom.sumInl_injective

lemma Iℒ₂ : (@ℒ₂ L E A B).Injective :=
  LHom.addConstants_injective LHom.sumInl_injective

variable {ϕ : L →ᴸ L'}

theorem onTerm_injective (hf : ϕ.Injective) : ∀ ⦃t s : L.Term α⦄, ϕ.onTerm t = ϕ.onTerm s → t = s
  | var _, var _, h => congrArg _ <| Term.var.inj h
  | func f ts, func g ss, h => by
    let h := Term.func.inj h
    cases h.1
    congr
    · exact hf.1 h.2.1.eq
    · ext i; exact onTerm_injective hf <| congrFun h.2.2.eq i

theorem onBoundedFormula_injective (hf : ϕ.Injective) : ∀ ⦃φ ψ : L.BoundedFormula α k⦄,
  ϕ.onBoundedFormula φ = ϕ.onBoundedFormula ψ → φ = ψ
  | .falsum, .falsum, _ => rfl
  | .equal _ _, .equal _ _, h => by
      congr <;> apply onTerm_injective hf <;> simp only [BoundedFormula.equal.inj h]
  | .rel _ _, .rel _ _, h => by
      let h := BoundedFormula.rel.inj h
      cases h.1
      congr
      · exact hf.2 h.2.1.eq
      · ext i; exact onTerm_injective hf <| congrFun h.2.2.eq i
  | .imp _ _, .imp _ _, h => by
      congr <;> apply onBoundedFormula_injective hf <;> simp only [BoundedFormula.imp.inj h]
  | ∀'_, ∀'_, h => by
      congr
      apply onBoundedFormula_injective hf
      apply BoundedFormula.all.inj h

theorem onSentence_injective : ϕ.Injective → ϕ.onSentence.Injective := onBoundedFormula_injective

private abbrev T : (L.sum E)[[A]][[B]].Theory  :=
  ℒ₁.onTheory (L.elementaryDiagram A) ∪ ℒ₂.onTheory ((L.sum E).elementaryDiagram B)

variable (U : Finset L.Sentence)

@[simp]
noncomputable def Finset.toSentence : L.Sentence := (Formula.iInf fun (φ : U) => φ.val)

theorem pop : B ⊨ (U : L.Theory) ↔ B ⊨ U.toSentence := by simp [Sentence.Realize]


variable [Nonempty A] [Nonempty B] [DecidableEq B]

-- instance {M} {T T' : L.Theory} [L.Structure M] (h : M ⊨ T) (h' : M ⊨ T') : M ⊨ T ∪ T' :=
--   Theory.Model.union h h'

open Classical in
noncomputable def amalg₁ (h : L.ElementarilyEquivalent A B) : (T : (L.sum E)[[A]][[B]].Theory).ModelType := by
  refine Classical.choice <| isSatisfiable_union_of_finite_unions fun S0 T0 hS hT =>
    let φ := (
      S0.finite_toSet.preimage (Set.injOn_of_injective <| onSentence_injective Iℒ₁)
    ).toFinset.toSentence
    letI : (L.sum E)[[A]][[B]].Structure B := sorry
    ⟨@Theory.ModelType.mk _ _ B _ ?_ _⟩
  -- · sorry
    -- exact @FirstOrder.Language.withConstantsSelfStructure _ _ (expand_of_sat_exs (φ := S0.toSentence) B).struc
  · apply Theory.Model.union
    · sorry
    · sorry
-- def amalg₁ {A B} [Nonempty A] [Nonempty B] [L.Structure A] [L.Structure B] [E.Structure B]
--     (h : L.ElementarilyEquivalent A B) : (L.sum E).Struc :=
--   let L' := (L.sum E)[[A]][[B]]
--   let ℒ₁ : L[[A]]         →ᴸ L' := .comp .sumInl <| .addConstants _ .sumInl
--   let ℒ₂ : (L.sum E)[[B]] →ᴸ L' := .addConstants _ .sumInl
--   let T : L'.Theory := ℒ₁.onTheory (L.elementaryDiagram A) ∪ ℒ₂.onTheory ((L.sum E).elementaryDiagram B)
  -- @Struc.mk _ (Theory.ModelType.Carrier <| Classical.choice (isSatisfiable_union_of_finite_unions ?_ : T.IsSatisfiable)) <| Theory.ModelType.struc (L := L.sum E) (Classical.choice _)

    -- Theory.ModelType.Carrier <| Classical.choice <| T.isSatisfiable_iff_isFinitelySatisfiable.mpr
  --   fun T0 sub => by
  -- have : L'.Structure B := sorry
  -- refine ⟨@Theory.ModelType.mk _ _ B _ ?_ _⟩
  -- · rw [← (Set.inter_union_distrib_left _ _ _).symm.trans (Set.inter_eq_self_of_subset_left sub)]
  --   apply FirstOrder.Language.Theory.Model.union
  --   · exact ⟨fun _ => sorry⟩
  --   · sorry

variable {T : L.Theory} {T₁ : (L.sum E₁).Theory} {T₂ : (L.sum E₂).Theory}
variable {T_sub₁ : LHom.sumInl.onTheory T ⊆ T₁} {T_sub₂ : LHom.sumInl.onTheory T ⊆ T₂}
variable {T_complete : T.IsComplete}

theorem Robinson (sat₁ : T₁.IsSatisfiable) (sat₂ : T₂.IsSatisfiable) : T.IsSatisfiable := by
  sorry
