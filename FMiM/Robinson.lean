import FMiM.ElementarySystems
import Mathlib.ModelTheory.Satisfiability
import Mathlib.ModelTheory.Bundled

set_option linter.unusedSectionVars false

open FirstOrder Language CategoryTheory

variable {L : Language}

section FreshConstants

variable {α : Type} [DecidableEq α] (φ : L[[α]].Sentence)

noncomputable def exs_consts : L.Sentence :=
  FirstOrder.Language.Formula.iExs φ.constantsVarsEquiv.freeVarFinset <|
    φ.constantsVarsEquiv.restrictFreeVar .inr

variable {φ} {M : Type} [L.Structure M] [Nonempty M]

@[reducible]
noncomputable def expand_of_sat_exs_const [h : M ⊨ {exs_consts φ}] : (constantsOn α).Structure M :=
  constantsOn.structure fun a =>
    if mem : _ then
      (Formula.realize_iExs.mp <| Theory.model_singleton_iff.1 h).choose ⟨.inl a, mem⟩
    else
      Classical.ofNonempty

variable (M)

noncomputable def expand_of_sat_exs [h : M ⊨ {exs_consts φ}] : Theory.ModelType {φ} :=
  letI : (constantsOn α).Structure M := expand_of_sat_exs_const
  letI : M ⊨ {φ} := by
    refine Theory.model_singleton_iff.2 <| BoundedFormula.realize_constantsVarsEquiv.1 ?_
    apply (BoundedFormula.realize_restrictFreeVar _ _).1
    · exact (Formula.realize_iExs.mp (Theory.model_singleton_iff.1 h)).choose_spec
    · exact fun ⟨.inl a, mem⟩ => Eq.symm <| dite_cond_eq_true (eq_true mem)
  ⟨M⟩

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

variable {E : Language} {A B : Type}

private abbrev ℒ₁ : L[[A]] →ᴸ (L.sum E)[[A]][[B]] :=
  .comp .sumInl <| .addConstants _ .sumInl

-- Could generalize to comp, sumInl, etc.
private instance [L.Structure B] [E.Structure B] [(constantsOn A).Structure B]
    : (@ℒ₁ L E A B).IsExpansionOn B where
  map_onFunction f xs := by cases f <;> rfl
  map_onRelation r xs := by cases r <;> rfl

private abbrev ℒ₂ : (L.sum E)[[B]] →ᴸ (L.sum E)[[A]][[B]] :=
  .addConstants _ .sumInl

private instance [L.Structure B] [E.Structure B] [(constantsOn A).Structure B]
    : (@ℒ₂ L E A B).IsExpansionOn B where
  map_onFunction f xs := by cases f <;> rfl
  map_onRelation r xs := by cases r <;> rfl

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

variable {L'} {ϕ : L →ᴸ L'}

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

variable (U : Finset L.Sentence)

@[simp]
noncomputable def Finset.toSentence : L.Sentence := (Formula.iInf fun (φ : U) => φ.val)

theorem Theory.model_iff_model_toSentence [L.Structure B] : B ⊨ (U : L.Theory) ↔ B ⊨ U.toSentence :=
  by simp [Sentence.Realize]

section Amalg₁

variable [DecidableEq A] [Nonempty B]
variable [L.Structure A] [L.Structure B] [E.Structure B] (h : A ≅[L] B)

private abbrev joint_diagₑ : (L.sum E)[[A]][[B]].Theory  :=
  ℒ₁.onTheory (L.elementaryDiagram A) ∪ ℒ₂.onTheory ((L.sum E).elementaryDiagram B)

variable (E)

noncomputable def amalg₁ : (@joint_diagₑ L E A B).ModelType := by
  refine Classical.choice <| isSatisfiable_union_of_finite_unions fun S0 T0 hS hT =>
    let U := (S0.finite_toSet.preimage (Set.injOn_of_injective <| onSentence_injective Iℒ₁))
    let φ := U.toFinset.toSentence
    letI : A ⊨ {exs_consts φ} := by
      apply Theory.model_singleton_iff.2
      apply Formula.realize_iExs.2
      exists fun ⟨.inl a, _⟩ => a
      suffices A ⊨ φ from
       ((BoundedFormula.realize_restrictFreeVar _ fun ⟨Sum.inl _,_⟩ => rfl).trans
          BoundedFormula.realize_constantsVarsEquiv).2 this
      suffices _ ⊆ L.elementaryDiagram A by
        refine (Theory.model_iff_model_toSentence _).1 ?_
        rw [U.coe_toFinset]
        exact Theory.model_iff_subset_completeTheory.2 this
      rw [← Set.preimage_image_eq (L.elementaryDiagram A) <| onSentence_injective Iℒ₁]
      exact Set.preimage_mono hS
    letI : B ⊨ {exs_consts φ} := h.theory_model
    letI : (constantsOn A).Structure B := expand_of_sat_exs_const (φ := φ)
    ⟨@Theory.ModelType.mk _ _ B _ ?_ _⟩
  · apply Theory.Model.union
    · rw [← Set.SurjOn.image_preimage (Set.surjOn_image ..) hS]
      apply (ℒ₁.onTheory_model _).2
      rw [← (S0.finite_toSet.preimage
          (Set.injOn_of_injective <| onSentence_injective Iℒ₁)).coe_toFinset]
      apply (Theory.model_iff_model_toSentence _).2
      apply Theory.model_singleton_iff.1
      exact (expand_of_sat_exs _).is_model
    · rw [← Set.SurjOn.image_preimage (Set.surjOn_image ..) hT]
      apply (ℒ₂.onTheory_model _).2
      suffices _ ⊆ (L.sum E).elementaryDiagram B from Theory.model_iff_subset_completeTheory.2 this
      rw [← Set.preimage_image_eq ((L.sum E).elementaryDiagram B)]
      · exact Set.preimage_mono hT
      · exact onSentence_injective Iℒ₂

private noncomputable def amalg₁_mapl :=
  letI exp := LHom.isExpansionOn_reduct ..
  @ElementaryEmbedding.ofModelsElementaryDiagram L A
    _ (((amalg₁ E h).subtheoryModel Set.subset_union_left).reduct ℒ₁) _ _ exp _

private noncomputable def amalg₁_mapr :=
  letI exp := LHom.isExpansionOn_reduct ..
  @ElementaryEmbedding.ofModelsElementaryDiagram (L.sum E) B
    _ (((amalg₁ E h).subtheoryModel Set.subset_union_right).reduct ℒ₂) _ _ exp _

end Amalg₁

section Amalg₂

variable {C : Type} [DecidableEq B] [Nonempty C]
variable [L.Structure A] [L.Structure B] [L.Structure C] [E.Structure C]
variable (f : A ↪ₑ[L] B) (g : A ↪ₑ[L] C)

def structure_of_embedding : (constantsOn A).Structure B where
  funMap := fun {n} c _ => match n with | 0 => f c


noncomputable def amalg₂ :=
  letI := structure_of_embedding f
  letI := structure_of_embedding g
  by
    refine @amalg₁ L[[A]] E B C _ _ _ _ _ ?_
    sorry -- B ≅[L[[A]]] A ≅[[L[[A]]]] C through f and g

end Amalg₂

variable {T : L.Theory} {T₁ : (L.sum E₁).Theory} {T₂ : (L.sum E₂).Theory}
variable {T_sub₁ : LHom.sumInl.onTheory T ⊆ T₁} {T_sub₂ : LHom.sumInl.onTheory T ⊆ T₂}
variable {T_complete : T.IsComplete}

theorem Robinson (sat₁ : T₁.IsSatisfiable) (sat₂ : T₂.IsSatisfiable) : T.IsSatisfiable := by
  sorry
