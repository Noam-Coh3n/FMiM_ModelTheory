import FMiM.Category
import FMiM.ElementarySystems
import Mathlib.ModelTheory.Satisfiability
import Mathlib.ModelTheory.Bundled

set_option linter.style.longLine false

open FirstOrder Language CategoryTheory

variable {L : Language.{0, 0}}

section FreshConstants

variable {α : Type} [DecidableEq α] (φ : L[[α]].Sentence)

noncomputable def exs_consts : L.Sentence :=
  FirstOrder.Language.Formula.iExs φ.constantsVarsEquiv.freeVarFinset <|
    φ.constantsVarsEquiv.restrictFreeVar .inr

variable {φ} {M : Type} [L.Structure M] [Nonempty M]

@[implicit_reducible]
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

variable {L' : Language.{0, 0}} (ϕ : L →ᴸ L') {A B : Type}

abbrev ℒ₁ : L[[A]] →ᴸ L'[[A]][[B]] :=
  .comp (L'[[A]].lhomWithConstants B) <| ϕ.addConstants _

-- Upstream to mathlib?
instance {F : L →ᴸ L'} {G : L' →ᴸ L''}
  [L.Structure α] [L'.Structure α] [L''.Structure α] [F.IsExpansionOn α] [G.IsExpansionOn α]
    : (G.comp F).IsExpansionOn α where
  map_onFunction _ _ := (G.map_onFunction ..).trans <| F.map_onFunction ..
  map_onRelation _ _ := (G.map_onRelation ..).trans <| F.map_onRelation ..

-- variable (L') in
abbrev ℒ₂ : L'[[B]] →ᴸ L'[[A]][[B]] :=
  .addConstants _ <| L'.lhomWithConstants A


-- private instance [L.Structure B] [L'.Structure B] [(constantsOn A).Structure B]
    -- : (ℒ₂ L' A B).IsExpansionOn B := inferInstance

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

theorem addConstants_injective {α : Type} (hf : f.Injective) : (LHom.addConstants α f).Injective :=
  f.sumMap_injective hf id_injective

end FirstOrder.Language.LHom

variable {ϕ}

lemma Iℒ₁ (Iϕ : ϕ.Injective) : (@ℒ₁ _ _ ϕ A B).Injective :=
  LHom.comp_injective LHom.sumInl_injective <| LHom.addConstants_injective Iϕ

lemma Iℒ₂ : (@ℒ₂ L' A B).Injective :=
  LHom.addConstants_injective LHom.sumInl_injective

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

variable (ϕ) (Iϕ : ϕ.Injective)
variable [L.Structure A] [L.Structure B] [L'.Structure B]
variable [Nonempty B] [ϕ.IsExpansionOn B] (h : A ≅[L] B)

variable (A B) in
abbrev joint_diagₑ : L'[[A]][[B]].Theory  :=
  (ℒ₁ ϕ).onTheory (L.elementaryDiagram A) ∪ ℒ₂.onTheory (L'.elementaryDiagram B)

open scoped Classical in
include Iϕ h in
theorem joint_diag_satisfiable_of_reduct_elementaryEquivalent : (joint_diagₑ ϕ A B).IsSatisfiable := by
  refine isSatisfiable_union_of_finite_unions fun S0 T0 hS hT =>
    let U := (S0.finite_toSet.preimage (Set.injOn_of_injective <| onSentence_injective <| Iℒ₁ Iϕ))
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
      rw [← Set.preimage_image_eq (L.elementaryDiagram A) <| onSentence_injective <| Iℒ₁ Iϕ]
      exact Set.preimage_mono hS
    letI : B ⊨ {exs_consts φ} := h.theory_model
    letI : (constantsOn A).Structure B := expand_of_sat_exs_const (φ := φ)
    ⟨@Theory.ModelType.mk _ _ B _ ?_ _⟩
  apply Theory.Model.union
  · rw [← Set.SurjOn.image_preimage (Set.surjOn_image ..) hS]
    apply ((ℒ₁ ϕ).onTheory_model _).2
    rw [← (S0.finite_toSet.preimage
        (Set.injOn_of_injective <| onSentence_injective <| Iℒ₁ Iϕ)).coe_toFinset]
    apply (Theory.model_iff_model_toSentence _).2
    apply Theory.model_singleton_iff.1
    exact (expand_of_sat_exs _).is_model
  · rw [← Set.SurjOn.image_preimage (Set.surjOn_image ..) hT]
    apply (ℒ₂.onTheory_model _).2
    suffices _ ⊆ L'.elementaryDiagram B from Theory.model_iff_subset_completeTheory.2 this
    rw [← Set.preimage_image_eq (L'.elementaryDiagram B)]
    · exact Set.preimage_mono hT
    · exact onSentence_injective Iℒ₂

variable (A B) in
structure Amalg where
  carrier : Type
  [str  : L.Structure carrier]
  [str' : L'.Structure carrier]
  [exp  : ϕ.IsExpansionOn carrier]
  mapl : A ↪ₑ[L ] carrier
  mapr : B ↪ₑ[L'] carrier

attribute [instance] Amalg.str Amalg.str' Amalg.exp

initialize_simps_projections Amalg (carrier → coe, -str, -str', -exp)

instance : CoeSort (Amalg ϕ A B) (Type _) :=
  ⟨Amalg.carrier⟩

attribute [coe] Amalg.carrier

include ϕ Iϕ h in
theorem amalg_of_equivalence : Nonempty <| Amalg ϕ A B :=
  Nonempty.elim (joint_diag_satisfiable_of_reduct_elementaryEquivalent ϕ Iϕ h) fun a =>
    letI : L[[A]].Structure a := (@ℒ₁ L L' ϕ A B).reduct a
    letI : L.Structure a := (L.lhomWithConstants A).reduct a
    letI : L'[[B]].Structure a := (@ℒ₂ L' A B).reduct a
    letI : L'.Structure a := (L'.lhomWithConstants B).reduct a
    letI := ((L.lhomWithConstants A).isExpansionOn_reduct a).1
    letI : ϕ.IsExpansionOn a := ⟨
      fun {n} f xs =>
      letI x1 := ((L.lhomWithConstants A).isExpansionOn_reduct a).1 f xs
      letI x2 := ((@ℒ₁ L L' ϕ A B).isExpansionOn_reduct a).1 (((L.lhomWithConstants A).onFunction f)) xs
      letI xx := x2.trans x1
      letI y1 := ((L'.lhomWithConstants B).isExpansionOn_reduct a).1 (ϕ.onFunction f) xs
      letI y2 := ((@ℒ₂ L' A B).isExpansionOn_reduct a).1 ((L'.lhomWithConstants B).onFunction (ϕ.onFunction f)) xs
      letI yy := y2.trans y1
      by
        rw [← yy, ← xx]
        simp [LHom.addConstants],
      fun {n} r xs =>
      letI x1 := ((L.lhomWithConstants A).isExpansionOn_reduct a).2 r xs
      letI x2 := ((@ℒ₁ L L' ϕ A B).isExpansionOn_reduct a).2 (((L.lhomWithConstants A).onRelation r)) xs
      letI xx := x2.trans x1
      letI y1 := ((L'.lhomWithConstants B).isExpansionOn_reduct a).2 (ϕ.onRelation r) xs
      letI y2 := ((@ℒ₂ L' A B).isExpansionOn_reduct a).2 ((L'.lhomWithConstants B).onRelation (ϕ.onRelation r)) xs
      letI yy := y2.trans y1
      by
        rw [← yy, ← xx]
        simp [LHom.addConstants]⟩
    .intro {
      carrier := a,
      mapl := @ElementaryEmbedding.ofModelsElementaryDiagram _ _ _ _ _ _ _
        ⟨fun _ => (((ℒ₁ ϕ).realize_onSentence ..).1 <| a.3.1 _ <| Set.mem_union_left _ <| Set.mem_image_of_mem _ ·)⟩
      mapr := @ElementaryEmbedding.ofModelsElementaryDiagram _ _ _ _ _ _ _
        ⟨fun _ => ((ℒ₂.realize_onSentence ..).1 <| a.3.1 _ <| Set.mem_union_right _ <| Set.mem_image_of_mem _ ·)⟩
    }

end Amalg₁


section Amalg₂

variable {C : Type} [Nonempty C]
variable [L.Structure A] [L.Structure B] [L.Structure C] [L'.Structure C] [ϕ.IsExpansionOn C]
variable (f : A ↪ₑ[L] B) (g : A ↪ₑ[L] C)


@[implicit_reducible]
def FirstOrder.Language.Embedding.withDom (_f : A ↪[L] B) : Type := B
deriving L.Structure

instance (f : A ↪[L] B) : (constantsOn A).Structure f.withDom :=
  constantsOn.structure fun a => f a

def FirstOrder.Language.Embedding.liftWithDom (f : A ↪[L] B) : A ↪[L[[A]]] f.withDom := by
  refine ⟨f.toEmbedding, ?_, ?_⟩
  · intro
    | _, .inl _, _ => exact f.map_fun' ..
    | 0, .inr _, _ => rfl
  · intro
    | _, .inl R, _ => exact f.map_rel' ..

def FirstOrder.Language.ElementaryEmbedding.liftWithDom (f : A ↪ₑ[L] B) : A ↪ₑ[L[[A]]] f.toEmbedding.withDom := by
  refine ⟨f, ?_⟩
  intro n φ x
  have h : (Sum.elim (fun a ↦ L.con a) (f ∘ x) : ↑A ⊕ Fin n → f.toEmbedding.withDom) = f ∘ Sum.elim (fun a ↦ ↑(L.con a)) x := (Sum.comp_elim _ _ _).symm
  simpa only [Formula.Realize, ← BoundedFormula.realize_constantsVarsEquiv, h] using
    f.map_formula ..

-- unif_hint where
-- |- f.toEmbedding.withDom =?= B

def FirstOrder.Language.ElementaryEmbedding.reduct (ψ : L →ᴸ L')
  [L.Structure M] [L'.Structure M] [ψ.IsExpansionOn M]
  [L.Structure N] [L'.Structure N] [ψ.IsExpansionOn N]
  (b : M ↪ₑ[L'] N)
    : M ↪ₑ[L] N :=
  ⟨b, fun _ _ _ => by calc
    _ ↔ _ := (ψ.realize_onFormula _).symm
    _ ↔ _ := b.2 _ _
    _ ↔ _ := ψ.realize_onFormula _
  ⟩

theorem amalg_of_embeddings (Iϕ : ϕ.Injective) : ∃ (D : Amalg ϕ B C), ∀ (a : A), D.mapl (f a) = D.mapr (g a) := by
  have ⟨D'⟩ := amalg_of_equivalence (ϕ.addConstants A) (ϕ.addConstants_injective Iϕ)
    (f.liftWithDom.elementarilyEquivalent.symm.trans g.liftWithDom.elementarilyEquivalent)
  letI := (L'.lhomWithConstants A).reduct D'
  letI := ϕ.reduct D'
  letI : (L.lhomWithConstants A).IsExpansionOn D' := ⟨
    fun _ _ => by calc
    _ = _ := (D'.exp.1 ..).symm
    _ = _ := ((LHom.isExpansionOn_reduct ..).1 ..),
    fun _ _ => by calc
    _ = _ := ((D'.exp.2 ..).symm)
    _ = _ := (LHom.isExpansionOn_reduct ..).2 ..
  ⟩
  exists ⟨D', (D'.mapl.reduct <| L.lhomWithConstants A), (D'.mapr.reduct <| L'.lhomWithConstants A)⟩
  intro
  calc
  _ = _ := Embedding.map_constants D'.mapl.toEmbedding _
  _ = _ := (D'.exp.1 (L.con _) default).symm
  _ = _ := (Embedding.map_constants D'.mapr.toEmbedding _).symm

-- theorem elementaryDiagram_mono {M} [L.Structure M] [L'.Structure M] [exp : ϕ.IsExpansionOn M]
--     : (ϕ.addConstants M).onTheory (L.elementaryDiagram M) ⊆ L'.elementaryDiagram M :=
--   fun _ ⟨_, Mψ, φψ⟩ => φψ ▸ (LHom.realize_onSentence M (LHom.addConstants M ϕ) _).2 Mψ

-- def FirstOrder.Language.Struc.reduct (ϕ : L →ᴸ L') (M : L'.Struc) : L.Struc :=
--   mk (str := ϕ.reduct M)

-- -- unif_hint where
-- -- |- f.toEmbedding.withDom =?= B

end Amalg₂

-- variable {E₁ E₂ : Language} {T : L.Theory} {T₁ : (L.sum E₁).Theory} {T₂ : (L.sum E₂).Theory}
-- variable {T_sub₁ : LHom.sumInl.onTheory T ⊆ T₁} {T_sub₂ : LHom.sumInl.onTheory T ⊆ T₂}
-- variable {T_complete : T.IsComplete}

-- theorem Robinson (sat₁ : T₁.IsSatisfiable) (sat₂ : T₂.IsSatisfiable) : T.IsSatisfiable := by
--   sorry
