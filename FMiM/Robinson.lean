import FMiM.Category
import FMiM.ElementarySystems
import Mathlib.ModelTheory.Satisfiability
import Mathlib.ModelTheory.Bundled

set_option linter.style.longLine false

open FirstOrder Language CategoryTheory

variable {L : Language}

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

variable {L' : Language} (ϕ : L →ᴸ L') {A B : Type}

abbrev ℒ₁ : L[[A]] →ᴸ L'[[A]][[B]] :=
  .comp (L'[[A]].lhomWithConstants B) <| ϕ.addConstants _

-- Upstream to mathlib?
instance {F : L →ᴸ L'} {G : L' →ᴸ L''}
  [L.Structure α] [L'.Structure α] [L''.Structure α] [F.IsExpansionOn α] [G.IsExpansionOn α]
    : (G.comp F).IsExpansionOn α where
  map_onFunction _ _ := (G.map_onFunction ..).trans <| F.map_onFunction ..
  map_onRelation _ _ := (G.map_onRelation ..).trans <| F.map_onRelation ..

-- set_option trace.Meta.synthInstance true in
-- private instance [L.Structure B] [L'.Structure B] [ϕ.IsExpansionOn B] [(constantsOn A).Structure B]
--     : (@ℒ₁ _ _ ϕ A B).IsExpansionOn B :=
--   inferInstance

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

variable [DecidableEq A] [Nonempty B]
variable (ϕ) (Iϕ : ϕ.Injective)
variable [L.Structure A] [L.Structure B] [L'.Structure B] [ϕ.IsExpansionOn B] (h : A ≅[L] B)

variable (A B) in
abbrev joint_diagₑ : L'[[A]][[B]].Theory  :=
  (ℒ₁ ϕ).onTheory (L.elementaryDiagram A) ∪ ℒ₂.onTheory (L'.elementaryDiagram B)



noncomputable opaque amalg₁ : (joint_diagₑ ϕ A B).ModelType := by
  refine Classical.choice <| isSatisfiable_union_of_finite_unions fun S0 T0 hS hT =>
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

noncomputable instance : L'.Structure (amalg₁ ϕ Iϕ h) :=
  (.comp .sumInl .sumInl : _ →ᴸ L'[[A]][[B]]).reduct _

noncomputable instance : L.Structure (amalg₁ ϕ Iϕ h) := ϕ.reduct _

noncomputable instance : (constantsOn A).Structure (amalg₁ ϕ Iϕ h) :=
  (.comp .sumInl .sumInr : _ →ᴸ L'[[A]][[B]]).reduct _

noncomputable def amalg₁_mapl : A ↪ₑ[L] amalg₁ ϕ Iϕ h :=
  letI exp := LHom.isExpansionOn_reduct ..
  @ElementaryEmbedding.ofModelsElementaryDiagram _ _ _
    (((amalg₁ ϕ Iϕ h).subtheoryModel Set.subset_union_left).reduct (ℒ₁ ϕ)) _ _ exp _

noncomputable def amalg₁_mapr : B ↪ₑ[L'] amalg₁ ϕ Iϕ h :=
  letI exp := LHom.isExpansionOn_reduct ..
  @ElementaryEmbedding.ofModelsElementaryDiagram _ _ _
    (((amalg₁ ϕ Iϕ h).subtheoryModel Set.subset_union_right).reduct ℒ₂) _ _ exp _

end Amalg₁

-- instance {M : (L.sum E).Struc} : L.Structure M := LHom.sumInl.reduct (L' := L.sum E) M
-- instance {M : (L.sum E).Struc} : E.Structure M := LHom.sumInr.reduct (L' := L.sum E) M

-- noncomputable def amalg_of_equivalence : Σ (C : (L.sum E).Struc), (A ↪ₑ[L] C) × (B ↪ₑ[L.sum E] C) :=
--   letI := (LHom.comp .sumInl .sumInl).reduct (L' := (L.sum E)[[A]][[B]])
--   ⟨.mk <| amalg₁ E h, amalg₁_mapl E h, amalg₁_mapr E h⟩


-- noncomputable def amalg_of_equivalence' : Σ (C : Type) (LC : L.Structure C) (L'C : L'.Structure C) (), (A ↪ₑ[L] C) × (B ↪ₑ[L'] C) :=
--   letI := (LHom.comp .sumInl .sumInl).reduct (L' := (L.sum E)[[A]][[B]])
--   ⟨.mk <| amalg₁ E h, amalg₁_mapl E h, amalg₁_mapr E h⟩


-- end Amalg₁

-- section Amalg₂

-- variable {C : Type} [DecidableEq B] [Nonempty C]
-- variable [L.Structure A] [L.Structure B] [L.Structure C] [E.Structure C]
-- variable (f : A ↪ₑ[L] B) (g : A ↪ₑ[L] C)

-- @[implicit_reducible]
-- def FirstOrder.Language.Embedding.withDom (_f : A ↪[L] B) : Type := B
-- deriving L.Structure

-- instance (f : A ↪[L] B) : (constantsOn A).Structure f.withDom :=
--   constantsOn.structure fun a => f a

-- def FirstOrder.Language.Embedding.liftWithDom (f : A ↪[L] B) : A ↪[L[[A]]] f.withDom := by
--   refine ⟨f.toEmbedding, ?_, ?_⟩
--   · intro
--     | _, .inl _, _ => exact f.map_fun' ..
--     | 0, .inr _, _ => rfl
--   · intro
--     | _, .inl R, _ => exact f.map_rel' ..

-- def prot (b : α ≃ β) : (constantsOn α) ≃ᴸ (constantsOn β) where
--   toLHom  := ⟨fun 0 c => b c, default⟩
--   invLHom := ⟨fun 0 c => b.symm c, default⟩
--   left_inv  := by ext ⟨⟩ <;> first | trivial | exact b.3 _
--   right_inv := by ext ⟨⟩ <;> first | trivial | exact b.4 _

-- -- #check prot (Equiv.Set.univ A)

-- def FirstOrder.Language.ElementaryEmbedding.liftWithDom (f : A ↪ₑ[L] B) : A ↪ₑ[L[[A]]] f.toEmbedding.withDom := by
--   refine ⟨f, ?_⟩
--   intro n φ x
--   have h : (Sum.elim (fun a ↦ L.con a) (f ∘ x) : ↑A ⊕ Fin n → f.toEmbedding.withDom) = f ∘ Sum.elim (fun a ↦ ↑(L.con a)) x := (Sum.comp_elim _ _ _).symm
--   simpa only [Formula.Realize, ← BoundedFormula.realize_constantsVarsEquiv, h] using
--     f.map_formula ..

-- -- noncomputable def amalg₂ :=
-- --   letI : L[[↑Set.univ]].Structure B := L.instStructureWithConstantsElemWithConstants _ f.toEmbedding
-- --   letI : L[[↑Set.univ]].Structure C := L.instStructureWithConstantsElemWithConstants _ g.toEmbedding
-- --   amalg₁ E <| ((f.liftWithConstants .univ).elementarilyEquivalent (N := B)).symm.trans <|
-- --     (g.liftWithConstants .univ).elementarilyEquivalent (N := C)

-- -- #check
-- --   letI : L[[↑Set.univ]].Structure B := L.instStructureWithConstantsElemWithConstants _ f.toEmbedding
-- --   letI : L[[↑Set.univ]].Structure C := L.instStructureWithConstantsElemWithConstants _ g.toEmbedding
-- --   @amalg₁_mapl L[[Set.univ (α := A)]] E B C _ _
-- --   (L.instStructureWithConstantsElemWithConstants _ f.toEmbedding)
-- --   (L.instStructureWithConstantsElemWithConstants _ g.toEmbedding) _
-- --   (((f.liftWithConstants .univ).elementarilyEquivalent (N := B)).symm.trans <|
-- --     (g.liftWithConstants .univ).elementarilyEquivalent (N := C))

-- -- theorem pop : ∃ (D : (L.sum E).Struc) (h : B ↪ₑ[L] D) (k : C ↪ₑ[L.sum E] D), ∀ (a : A), h (f a) = k (g a) :=
-- --   ⟨⟩

-- theorem elementaryDiagram_mono {M} [L.Structure M] [L'.Structure M] [exp : ϕ.IsExpansionOn M]
--     : (ϕ.addConstants M).onTheory (L.elementaryDiagram M) ⊆ L'.elementaryDiagram M :=
--   fun _ ⟨_, Mψ, φψ⟩ => φψ ▸ (LHom.realize_onSentence M (LHom.addConstants M ϕ) _).2 Mψ

-- def FirstOrder.Language.Struc.reduct (ϕ : L →ᴸ L') (M : L'.Struc) : L.Struc :=
--   mk (str := ϕ.reduct M)

-- -- unif_hint where
-- -- |- f.toEmbedding.withDom =?= B

-- #check
--   let ⟨D, ff, gg⟩ := amalg_of_equivalence E <| (f.liftWithDom.elementarilyEquivalent).symm.trans g.liftWithDom.elementarilyEquivalent
--   D
-- -- #check amalg_of_equivalence E
-- -- (((f.liftWithConstants .univ).elementarilyEquivalent (N := B)).symm.trans <|
-- --     (g.liftWithConstants .univ).elementarilyEquivalent (N := C))

-- -- theorem amalg_of_embeddings
-- --     : ∃ (D : (L.sum E).Struc) (h : B ↪ₑ[L] D) (k : C ↪ₑ[L.sum E] D), ∀ (a : A), h (f a) = k (g a) :=
-- --   letI : (constantsOn Set.univ).Structure B := L.instStructureConstantsOnElemWithConstants _ f.toEmbedding
-- --   letI : (constantsOn Set.univ).Structure C := L.instStructureConstantsOnElemWithConstants _ g.toEmbedding
-- --   have ⟨D, BD, CD⟩ := amalg_of_equivalence E (((f.liftWithConstants .univ).elementarilyEquivalent (N := B)).symm.trans <|
-- --     (g.liftWithConstants .univ).elementarilyEquivalent (N := C))
-- --   ⟨
-- --     D.reduct <| .sumMap (lhomWithConstants _ _) (.id _),
-- --     ⟨BD.1, fun n φ xs => by
-- --       letI : L.Structure D := ((D.reduct <| .sumMap (lhomWithConstants _ _) (.id _)).reduct .sumInl).str
-- --       letI := (LHom.sumInl (L := L) (L' := constantsOn <| Set.univ (α := A))).isExpansionOn_reduct D
-- --       calc
-- --         _ ↔ _ := (@LHom.sumInl.realize_onFormula L _ _ _ _ _ ((LHom.sumInl (L' := constantsOn <| Set.univ)).isExpansionOn_reduct D) _).symm
-- --         _ ↔ _ := BD.2 (LHom.sumInl.onFormula φ) xs
-- --         _ ↔ _ := @LHom.sumInl.realize_onFormula L _ _ _ _ _ (LHom.sumInl_isExpansionOn _) _ _
-- --     ⟩,
-- --     ⟨CD.1, fun n φ xs => by
-- --       letI : L.Structure D := ((D.reduct <| .sumMap (lhomWithConstants _ _) (.id _)).reduct .sumInl).str
-- --       -- letI := (LHom.sumInl (L := L) (L' := constantsOn <| Set.univ (α := A))).isExpansionOn_reduct D
-- --       calc
-- --         _ ↔ _ := (@LHom.sumInl.realize_onFormula (L.sum E) _ _ _ _ _ ((LHom.sumInl (L' := constantsOn <| Set.univ)).isExpansionOn_reduct D) _).symm
-- --         _ ↔ _ := CD.2 _ xs
-- --         _ ↔ _ := @LHom.sumInl.realize_onFormula L _ _ _ _ _ (LHom.sumInl_isExpansionOn _) _ _
-- --     ⟩,
-- --     _
-- --   ⟩

-- end Amalg₂

-- variable {E₁ E₂ : Language} {T : L.Theory} {T₁ : (L.sum E₁).Theory} {T₂ : (L.sum E₂).Theory}
-- variable {T_sub₁ : LHom.sumInl.onTheory T ⊆ T₁} {T_sub₂ : LHom.sumInl.onTheory T ⊆ T₂}
-- variable {T_complete : T.IsComplete}

-- theorem Robinson (sat₁ : T₁.IsSatisfiable) (sat₂ : T₂.IsSatisfiable) : T.IsSatisfiable := by
--   sorry
