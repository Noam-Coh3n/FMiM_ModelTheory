import FMiM.ElementarySystems
import Mathlib.ModelTheory.Bundled
import Mathlib.ModelTheory.Satisfiability

open FirstOrder Language CategoryTheory

-- TODO: Generalize to universes
variable {L : Language.{0, 0}}

section FreshConstants

variable {α : Type} [DecidableEq α] (φ : L[[α]].Sentence)

/-- Convert an *L[[α]]* sentence into an L.sentence by existentially quantifying over
the constants of *α* that actually appear in *ϕ*. -/
noncomputable def exs_consts : L.Sentence :=
  FirstOrder.Language.Formula.iExs φ.constantsVarsEquiv.freeVarFinset <|
    φ.constantsVarsEquiv.restrictFreeVar .inr

variable {φ} {M : Type} [L.Structure M] [Nonempty M]


/-- If an *L*-model satisfies the sentence *exs_conts ϕ*, we can interpret the constants in *α*
in a way such that ϕ holds in the resulting model (see *expand_of_sat_exs*). -/
@[implicit_reducible]
noncomputable def expand_of_sat_exs_const [h : M ⊨ {exs_consts φ}] : (constantsOn α).Structure M :=
  constantsOn.structure fun a =>
    if mem : _ then
      (Formula.realize_iExs.mp <| Theory.model_singleton_iff.1 h).choose ⟨.inl a, mem⟩
    else
      Classical.ofNonempty

variable (M)

/-- *ϕ* holds in the model obtained from *expand_of_sat_exs_const*. -/
noncomputable def expand_of_sat_exs [h : M ⊨ {exs_consts φ}] : Theory.ModelType {φ} :=
  letI : (constantsOn α).Structure M := expand_of_sat_exs_const
  letI : M ⊨ {φ} := by
    refine Theory.model_singleton_iff.2 <| BoundedFormula.realize_constantsVarsEquiv.1 ?_
    apply (BoundedFormula.realize_restrictFreeVar _ _).1
    · exact (Formula.realize_iExs.mp (Theory.model_singleton_iff.1 h)).choose_spec
    · exact fun ⟨.inl a, mem⟩ => Eq.symm <| dite_cond_eq_true (eq_true mem)
  ⟨M⟩

end FreshConstants

/-- Compactness specialized to unions. -/
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

/-- The composition of language homomorphisms that are expansions on *α* is an expansion on *a*. -/
instance {F : L →ᴸ L'} {G : L' →ᴸ L''}
  [L.Structure α] [L'.Structure α] [L''.Structure α] [F.IsExpansionOn α] [G.IsExpansionOn α]
    : (G.comp F).IsExpansionOn α where
  map_onFunction _ _ := (G.map_onFunction ..).trans <| F.map_onFunction ..
  map_onRelation _ _ := (G.map_onRelation ..).trans <| F.map_onRelation ..

abbrev ℒ₂ : L'[[B]] →ᴸ L'[[A]][[B]] :=
  .addConstants _ <| L'.lhomWithConstants A

namespace FirstOrder.Language.LHom

/-- Composition of language homomorphisms preserves injectivity. -/
theorem comp_injective (hg : g.Injective) (hf : f.Injective) : (LHom.comp g f).Injective where
  onFunction h := Function.Injective.comp hg.1 hf.1 h
  onRelation h := Function.Injective.comp hg.2 hf.2 h

/-- *LHom.sumMap* preserves injectivity. -/
theorem sumMap_injective (hf : f.Injective) (hg : g.Injective) : (LHom.sumMap f g).Injective where
  onFunction h := Function.Injective.sumMap hf.1 hg.1 h
  onRelation h := Function.Injective.sumMap hf.2 hg.2 h

/-- The identity language homomorphisms is injective. -/
theorem id_injective : (LHom.id L).Injective where
  onFunction h := Function.injective_id h
  onRelation h := Function.injective_id h

/-- Adding constants to a language homomorphisms preserves injectivity. -/
theorem addConstants_injective {α : Type} (hf : f.Injective) : (LHom.addConstants α f).Injective :=
  f.sumMap_injective hf id_injective

end FirstOrder.Language.LHom

variable {ϕ}

lemma Iℒ₁ (Iϕ : ϕ.Injective) : (@ℒ₁ _ _ ϕ A B).Injective :=
  LHom.comp_injective LHom.sumInl_injective <| LHom.addConstants_injective Iϕ

lemma Iℒ₂ : (@ℒ₂ L' A B).Injective :=
  LHom.addConstants_injective LHom.sumInl_injective

/-- Prove *φ.onTerm* is injective when *φ* is. -/
theorem onTerm_injective (I : ϕ.Injective) : ∀ ⦃t s : L.Term α⦄, ϕ.onTerm t = ϕ.onTerm s → t = s
| var _, var _, h => congrArg _ <| Term.var.inj h
| func .., func .., h => by
  obtain ⟨⟨⟩, hf, ht⟩ := Term.func.inj h
  congr
  · exact I.1 hf.eq
  · ext i
    exact onTerm_injective I <| congrFun ht.eq i

/-- Prove *φ.onBoundedFormula* is injective when *φ* is. -/
theorem onBoundedFormula_injective (I : ϕ.Injective) : ∀ ⦃φ ψ : L.BoundedFormula α k⦄,
    ϕ.onBoundedFormula φ = ϕ.onBoundedFormula ψ → φ = ψ
| .falsum, .falsum, _ => rfl
| .equal _ _, .equal _ _, h => by
    congr <;> apply onTerm_injective I <;> simp only [BoundedFormula.equal.inj h]
| .rel _ _, .rel _ _, h => by
    obtain ⟨⟨⟩, hr, ht⟩ := BoundedFormula.rel.inj h
    congr
    · exact I.2 hr.eq
    · ext i; exact onTerm_injective I <| congrFun ht.eq i
| .imp _ _, .imp _ _, h => by
    congr <;> apply onBoundedFormula_injective I <;> simp only [BoundedFormula.imp.inj h]
| ∀'_, ∀'_, h => by
    congr
    apply onBoundedFormula_injective I
    exact BoundedFormula.all.inj h

/-- Prove *φ.onSentence* is injective when *φ* is. -/
theorem onSentence_injective : ϕ.Injective → ϕ.onSentence.Injective := onBoundedFormula_injective

variable (U : Finset L.Sentence)

/-- The conjunction of a finite theory. -/
@[simp]
noncomputable def Finset.toSentence : L.Sentence := (Formula.iInf fun (φ : U) => φ.val)

@[simp]
theorem Theory.model_iff_model_toSentence [L.Structure B] : B ⊨ U.toSentence ↔ B ⊨ (U : L.Theory) :=
  by simp [Sentence.Realize]

section Amalg₁

variable (ϕ) (Iϕ : ϕ.Injective)
variable [L.Structure A] [L.Structure B] [L'.Structure B]
variable [Nonempty B] [ϕ.IsExpansionOn B] (h : A ≅[L] B)

variable (A B) in
/-- The theory of a model in which both A and B can embed elementarily. -/
abbrev joint_diagₑ : L'[[A]][[B]].Theory  :=
  (ℒ₁ ϕ).onTheory (L.elementaryDiagram A) ∪ ℒ₂.onTheory (L'.elementaryDiagram B)

open scoped Classical in
include Iϕ h in
/-- If *A ≅[L] B*, then their joint diagram is satisfiable. -/
theorem joint_diag_satisfiable_of_reduct_equivalent : (joint_diagₑ ϕ A B).IsSatisfiable := by
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
        refine (Theory.model_iff_model_toSentence _).2 ?_
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
    apply (Theory.model_iff_model_toSentence _).1
    apply Theory.model_singleton_iff.1
    exact (expand_of_sat_exs _).is_model
  · rw [← Set.SurjOn.image_preimage (Set.surjOn_image ..) hT]
    apply (ℒ₂.onTheory_model _).2
    suffices _ ⊆ L'.elementaryDiagram B from Theory.model_iff_subset_completeTheory.2 this
    rw [← Set.preimage_image_eq (L'.elementaryDiagram B)]
    · exact Set.preimage_mono hT
    · exact onSentence_injective Iℒ₂

variable (A B) in
/-- An amalgam of *A* and *B* is an *L'*-model *C* with elementary embeddings
*A ↪ₑ[L] C* and *B ↪ₑ[L'] C*. -/
structure Amalg where
  carrier : Type
  [str  : L.Structure carrier]
  [str' : L'.Structure carrier]
  [exp  : ϕ.IsExpansionOn carrier]
  [nonempty : Nonempty carrier]
  mapl : A ↪ₑ[L ] carrier
  mapr : B ↪ₑ[L'] carrier

attribute [instance] Amalg.str Amalg.str' Amalg.exp Amalg.nonempty

instance : CoeSort (Amalg ϕ A B) (Type _) :=
  ⟨Amalg.carrier⟩

attribute [coe] Amalg.carrier

include ϕ Iϕ h in
-- TODO: Needs cleaning up
theorem amalg_of_equivalence : Nonempty <| Amalg ϕ A B :=
  Nonempty.elim (joint_diag_satisfiable_of_reduct_equivalent ϕ Iϕ h) fun a =>
    letI : L[[A]].Structure a := (@ℒ₁ L L' ϕ A B).reduct a
    letI : L.Structure a := (L.lhomWithConstants A).reduct a
    letI : L'[[B]].Structure a := (@ℒ₂ L' A B).reduct a
    letI : L'.Structure a := (L'.lhomWithConstants B).reduct a
    letI := ((L.lhomWithConstants A).isExpansionOn_reduct a).1
    -- Very ugly, will find a better way to prove this later
    letI : ϕ.IsExpansionOn a := ⟨
      fun _ _ =>
      letI x1 := ((L.lhomWithConstants A).isExpansionOn_reduct a).1 ..
      letI x2 := ((@ℒ₁ L L' ϕ A B).isExpansionOn_reduct a).1 ..
      letI xx := x2.trans x1
      letI y1 := ((L'.lhomWithConstants B).isExpansionOn_reduct a).1 ..
      letI y2 := ((@ℒ₂ L' A B).isExpansionOn_reduct a).1 ..
      letI yy := y2.trans y1
      by
        rw [← yy, ← xx]
        simp [LHom.addConstants],
      fun _ _ =>
      letI x1 := ((L.lhomWithConstants A).isExpansionOn_reduct a).2 ..
      letI x2 := ((@ℒ₁ L L' ϕ A B).isExpansionOn_reduct a).2 ..
      letI xx := x2.trans x1
      letI y1 := ((L'.lhomWithConstants B).isExpansionOn_reduct a).2 ..
      letI y2 := ((@ℒ₂ L' A B).isExpansionOn_reduct a).2 ..
      letI yy := y2.trans y1
      by
        rw [← yy, ← xx]
        simp [LHom.addConstants]⟩
    .intro {
      carrier := a,
      mapl := @ElementaryEmbedding.ofModelsElementaryDiagram _ _ _ _ _ _ _
        ⟨fun _ => (((ℒ₁ ϕ).realize_onSentence ..).1 <| a.3.1 _ <| Set.mem_union_left _ <|
          Set.mem_image_of_mem _ ·)⟩
      mapr := @ElementaryEmbedding.ofModelsElementaryDiagram _ _ _ _ _ _ _
        ⟨fun _ => ((ℒ₂.realize_onSentence ..).1 <| a.3.1 _ <| Set.mem_union_right _ <|
          Set.mem_image_of_mem _ ·)⟩
    }

end Amalg₁

section Amalg₂

variable {C : Type} [Nonempty C]
variable [L.Structure A] [L.Structure B] [L.Structure C] [L'.Structure C] [ϕ.IsExpansionOn C]
variable (f : A ↪ₑ[L] B) (g : A ↪ₑ[L] C)

/-- A type synonym to provide an interpretation to the constants *A* in *B* from an embedding
*A ↪[L] B*. -/
@[implicit_reducible]
def FirstOrder.Language.Embedding.withDom (_f : A ↪[L] B) : Type := B
deriving L.Structure

instance (f : A ↪[L] B) : (constantsOn A).Structure f.withDom :=
  constantsOn.structure fun a => f a

/-- Lift an embedding to the expanded language with the constants of the domain. -/
def FirstOrder.Language.Embedding.liftWithDom (f : A ↪[L] B) : A ↪[L[[A]]] f.withDom := by
  refine ⟨f.toEmbedding, ?_, ?_⟩
  · intro
    | _, .inl _, _ => exact f.map_fun' ..
    | 0, .inr _, _ => rfl
  · intro
    | _, .inl R, _ => exact f.map_rel' ..

namespace FirstOrder.Language.ElementaryEmbedding

/-- Elementary analogue of *FirstOrder.Language.Embedding.liftWithDom*. -/
def liftWithDom (f : A ↪ₑ[L] B) : A ↪ₑ[L[[A]]] f.toEmbedding.withDom := by
  refine ⟨f, ?_⟩
  intro n φ x
  have h :
    (Sum.elim (fun a ↦ L.con a) (f ∘ x) :
      ↑A ⊕ Fin n → f.toEmbedding.withDom) =
    f ∘ Sum.elim (fun a ↦ ↑(L.con a)) x :=
      (Sum.comp_elim _ _ _).symm
  simpa only [Formula.Realize, ← BoundedFormula.realize_constantsVarsEquiv, h] using
    f.map_formula ..

/-- The reduct of an elementary embedding *b* along an expansion *ψ*. -/
protected def reduct (ψ : L →ᴸ L')
  [L.Structure M] [L'.Structure M] [ψ.IsExpansionOn M]
  [L.Structure N] [L'.Structure N] [ψ.IsExpansionOn N]
  (b : M ↪ₑ[L'] N)
    : M ↪ₑ[L] N :=
  ⟨b, fun _ _ _ => by calc
    _ ↔ _ := (ψ.realize_onFormula _).symm
    _ ↔ _ := b.2 _ _
    _ ↔ _ := ψ.realize_onFormula _
  ⟩

@[simp]
theorem reduct_apply {ψ : L →ᴸ L'}
  [L.Structure M] [L'.Structure M] [ψ.IsExpansionOn M]
  [L.Structure N] [L'.Structure N] [ψ.IsExpansionOn N]
  (b : M ↪ₑ[L'] N)
  : ∀ x, (b.reduct ψ) x = b x :=
  fun _ => rfl

end FirstOrder.Language.ElementaryEmbedding

/-- Any pair of embeddings *A ↪[L] B* and *A ↪[L] C* fit into a commuting square with
*B ↪[L]* -/
theorem amalg_of_embeddings (Iϕ : ϕ.Injective)
  : ∃ (D : Amalg ϕ B C), ∀ (a : A), D.mapl (f a) = D.mapr (g a) := by
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

theorem elementaryDiagram_mono {M} [L.Structure M] [L'.Structure M] [exp : ϕ.IsExpansionOn M]
    : (ϕ.addConstants M).onTheory (L.elementaryDiagram M) ⊆ L'.elementaryDiagram M :=
  fun _ ⟨_, Mψ, φψ⟩ => φψ ▸ (LHom.realize_onSentence M (LHom.addConstants M ϕ) _).2 Mψ

end Amalg₂

variable {L₁ L₂ : Language} {ϕ₁ : L →ᴸ L₁} {ϕ₂ : L →ᴸ L₂} (I₁ : ϕ₁.Injective) (I₂ : ϕ₂.Injective)
variable {T : L.Theory} {T₁ : L₁.Theory} {T₂ : L₂.Theory}
variable (T_complete : T.IsComplete) (T_sub₁ : ϕ₁.onTheory T ⊆ T₁) (T_sub₂ : ϕ₂.onTheory T ⊆ T₂)
variable (sat₁ : T₁.IsSatisfiable) (sat₂ : T₂.IsSatisfiable)

def FirstOrder.Language.Struc.reduct (ϕ : L →ᴸ L') (M : L'.Struc) : L.Struc :=
  mk (str := ϕ.reduct M)

-- unif_hint {T' : L'.Theory} {A : T'.ModelType} where
-- |- (Struc.reduct ϕ ⟨A⟩ : Type) =?= A

include T_complete T_sub₁ T_sub₂ in
/-- If *A ⊧ T₁* and *B ⊧ T₂* and *T₁,T₂* both extend a complete *L*-theory *T*,
their reducts are *L*-equivalent. -/
theorem reduct_elementarilyEquivalent_of_extend_completeTheory
  [L.Structure A] [L₁.Structure A] [L.Structure B] [L₂.Structure B] [Nonempty A] [Nonempty B]
  [ϕ₁.IsExpansionOn A] [ϕ₂.IsExpansionOn B] [hA : A ⊨ T₁] [hB : B ⊨ T₂] :
    A ≅[L] B := by
  have := (ϕ₁.onTheory_model _).1 <| hA.mono T_sub₁
  have := (ϕ₂.onTheory_model _).1 <| hB.mono T_sub₂
  calc
    _ = _ := Eq.symm <| T_complete.eq_complete_theory _
    _ = _ := T_complete.eq_complete_theory _
