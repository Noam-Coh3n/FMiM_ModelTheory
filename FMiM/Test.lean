import FMiM.Robinson
import Mathlib.Data.Stream.Defs
import Mathlib.Data.PNat.Basic

open FirstOrder Language LHom DirectedSystem

section

variable {L' L : Language.{0, 0}} (ϕ : L →ᴸ L')

structure FirstOrder.Language.LHom.RedStruc extends L'.Struc where
  [red : L.Structure carrier]
  [exp : ϕ.IsExpansionOn carrier]

attribute [instance] RedStruc.red RedStruc.exp

instance : CoeSort ϕ.RedStruc Type := ⟨fun X => X.carrier⟩

abbrev FirstOrder.Language.LHom.mkRS : L'.Struc → ϕ.RedStruc := (.mk (red := ϕ.reduct ·))

end

class langs where
  L : Language
  E₁ : Language
  E₂ : Language

namespace langs

variable [langs]

abbrev L₁ := L.sum E₁
abbrev L₂ := L.sum E₂
abbrev L' := L.sum (E₁.sum E₂)
abbrev ϕ₁ : L →ᴸ L₁ := .sumInl
abbrev ϕ₂ : L →ᴸ L₂ := .sumInl
abbrev ψ₁ : L₁ →ᴸ L' := .sumMap (.id L) .sumInl
abbrev ψ₂ : L₂ →ᴸ L' := .sumMap (.id L) .sumInr

end langs

open langs

class problem extends langs where
  T : L.Theory
  T_cpl : T.IsComplete
  T₁ : L₁.Theory
  T₂ : L₂.Theory
  T_sub₁ : ϕ₁.onTheory T ⊆ T₁
  T_sub₂ : ϕ₂.onTheory T ⊆ T₂
  sat₁ : T₁.IsSatisfiable
  sat₂ : T₂.IsSatisfiable

noncomputable section Robinson

open problem

variable [problem]

structure layer where
  A : ϕ₁.RedStruc
  B : ϕ₂.RedStruc
  hAB : A ≅[L] B

theorem reduct_elementarilyEquivalent_of_extend_completeTheory'
  {A : ϕ₁.RedStruc} {B : ϕ₂.RedStruc} [hA : A ⊨ T₁] [hB : B ⊨ T₂] :
    A ≅[L] B := by
  have := (onTheory_model _ _).1 <| hA.mono T_sub₁
  have := (onTheory_model _ _).1 <| hB.mono T_sub₂
  calc
    _ = _ := Eq.symm <| T_cpl.eq_complete_theory _
    _ = _ := T_cpl.eq_complete_theory _

theorem amalg_of_equivalence'' (AB : layer) : Nonempty <|
    Σ (B' : ϕ₂.RedStruc), (AB.A ↪ₑ[L] B') × (AB.B ↪ₑ[L₂] B') :=
  (amalg_of_equivalence .sumInl sumInl_injective AB.hAB).elim fun C => ⟨⟨⟨C⟩⟩, C.mapl, C.mapr⟩

theorem amalg_of_embedding {A : ϕ₁.RedStruc} {B : ϕ₂.RedStruc} (f : A ↪ₑ[L] B) :
    ∃ (A' : ϕ₁.RedStruc) (k : A ↪ₑ[L₁] A') (g : B ↪ₑ[L] A'), ∀ a, g (f a) = k a :=
  (amalg_of_embeddings f (.refl L A) sumInl_injective).elim fun C comm =>
    ⟨⟨⟨C⟩⟩, C.mapr, C.mapl, comm⟩

def layer.base : layer := ⟨ϕ₁.mkRS ⟨sat₁.some⟩, ϕ₂.mkRS ⟨sat₂.some⟩,
  reduct_elementarilyEquivalent_of_extend_completeTheory'⟩

def layer.nextA (AB : layer) :=
  (amalg_of_embedding (amalg_of_equivalence'' AB).some.2.1).choose

def layer.nextB (AB : layer) :=
  (amalg_of_equivalence'' AB).some.1

def layer.f (AB : layer) : AB.A ↪ₑ[L] AB.nextB :=
  (amalg_of_equivalence'' AB).some.2.1

def layer.h (AB : layer) : AB.B ↪ₑ[L₂] AB.nextB :=
  (amalg_of_equivalence'' AB).some.2.2

def layer.g (AB : layer) : AB.nextB ↪ₑ[L] AB.nextA :=
  (amalg_of_embedding (amalg_of_equivalence'' AB).some.2.1).choose_spec.choose_spec.choose

def layer.k (AB : layer) : AB.A ↪ₑ[L₁] AB.nextA :=
  (amalg_of_embedding (amalg_of_equivalence'' AB).some.2.1).choose_spec.choose

def layer.next (AB : layer) : layer :=
  ⟨AB.nextA, AB.nextB, AB.g.elementarilyEquivalent.symm⟩

def layers := Stream'.iterate layer.next layer.base

@[reducible]
def A (n : ℕ) : ϕ₁.RedStruc := (layers.get n).A

@[reducible]
def B (n : ℕ) : ϕ₂.RedStruc := (layers.get n).B

@[reducible]
def G : J → Type
| .inl (.inl _) => layers.head.A
| .inl (.inr _) => layers.head.B
| .inr (n,⊤)    => (layers.get n).A
| .inr (n,⊥)    => (layers.get n).B

instance : ∀ i, L.Structure (G i)
| .inl (.inl _) => inferInstance
| .inl (.inr _) => inferInstance
| .inr (_,⊤)    => inferInstance
| .inr (_,⊥)    => inferInstance

instance : ∀ i, Nonempty (G i) := by
  rintro (⟨_ | _⟩ | ⟨_, ⟨⟩⟩) <;> unfold G <;> infer_instance

-- @[reducible]
-- def A (n : ℕ) : Type := (layer.get n).A

-- @[reducible]
-- def B (n : ℕ) : Type := (layer.get n).B

def iA : ℕ → J
| 0   => .inl <| .inl ()
| n+1 => .inr (n.succPNat,⊤)

def iB : ℕ → J
| 0   => .inl <| .inr ()
| n+1 => .inr (n.succPNat,⊥)

theorem G_iA : (n : ℕ) → G (iA n) = A n
| 0   => rfl
| _+1 => rfl

theorem G_iB : (n : ℕ) → G (iB n) = B n
| 0   => rfl
| _+1 => rfl

@[reducible]
def k_sys : (n m : ℕ) → n ≤ m → A n ↪ₑ[L₁] A m :=
  natLERecₑ (layer.k <| layers.get ·)

@[reducible]
def h_sys : (n m : ℕ) → n ≤ m → B n ↪ₑ[L₂] B m :=
  natLERecₑ (layer.h <| layers.get ·)

noncomputable def F (i j : J) (ij : i ≤ j) : G i ↪ₑ[L] G j :=
  if i'j : i = j then
    i'j ▸ .refl ..
  else match i,j with
  | .inl (.inl ()), .inr (m,⊤) => (k_sys 0 m zero_le').reduct ϕ₁
  | .inl (.inr ()), .inr (m,⊥) => (h_sys 0 m zero_le').reduct ϕ₂
  | .inr (n,⊤), .inr (m,⊤) => (k_sys n m (Sum.lex_inr_inr.mp ij).monotone_fst).reduct ϕ₁
  | .inr (n,⊥), .inr (m,⊥) => (h_sys n m (Sum.lex_inr_inr.mp ij).monotone_fst).reduct ϕ₂
  | .inl (.inl ()), .inr (m,⊥) =>
      let f : A m.natPred ↪ₑ[L] B m :=
        m.natPred_add_one ▸ (layers.get _).f
      f.comp <| (k_sys 0 m.natPred zero_le').reduct ϕ₁
  | .inr (n,⊤), .inr (m,⊥) => by
      let f : A m.natPred ↪ₑ[L] B m :=
        m.natPred_add_one ▸ (layers.get _).f
      refine f.comp <| (k_sys n m.natPred ?_).reduct ϕ₁
      · apply Nat.le_sub_one_of_lt
        apply lt_of_le_of_ne (Sum.lex_inr_inr.mp ij).monotone_fst
        intro nm
        refine Bool.false_lt_true.not_gt <| (Prod.Lex.lt_iff'.mp ?_).2 nm
        match lt_of_le_of_ne ij i'j with | .inr _ => assumption
  | .inl (.inr ()), .inr (m,⊤) =>
      let g : B m ↪ₑ[L] A m :=
        m.natPred_add_one ▸ (layers.get _).g
      g.comp <| (h_sys 0 m zero_le').reduct ϕ₂
  | .inr (n,⊥), .inr (m,⊤) =>
      let g : B m ↪ₑ[L] A m :=
        m.natPred_add_one ▸ (layers.get _).g
      g.comp <| (h_sys n m (Sum.lex_inr_inr.mp ij).monotone_fst).reduct ϕ₂

instance : DirectedSystem G (F · · ·) where
  map_self _ _ := by simp only [F, ↓reduceDIte, ElementaryEmbedding.refl_apply]
  map_map k j i ij jk x := by
    by_cases i'j : i = j
    · subst j; simp only [F, ↓reduceDIte, ElementaryEmbedding.refl_apply]
    by_cases j'k : j = k
    · subst j; simp only [F, ↓reduceDIte, ElementaryEmbedding.refl_apply]
    by_cases i = k
    · subst k
      exfalso
      exact i'j <| le_antisymm ij jk
    have kc := map_map k_sys
    have hc := map_map h_sys
    match i,j,k with
    | .inl (.inl ()), .inr (m,⊤), .inr (l,⊤) =>
        simp only [F, ↓reduceDIte, *]
        apply kc
    | .inr (n,⊤), .inr (m,⊤), .inr (l,⊤) =>
        simp only [F, ↓reduceDIte, *]
        apply kc
    | .inl (.inl ()), .inr (m,⊤), .inr (l,⊥) =>
        simp only [F, ↓reduceDIte, *]
        conv => congr <;> rw [ElementaryEmbedding.comp_apply]
        congr 1
        apply kc
    | .inr (n,⊤), .inr (m,⊤), .inr (l,⊥) =>
        simp only [F, ↓reduceDIte, *]
        conv => congr <;> rw [ElementaryEmbedding.comp_apply]
        congr 1
        apply kc
    | .inl (.inr ()), .inr (m,⊥), .inr (l,⊥) =>
        simp only [F, ↓reduceDIte, *]
        apply hc
    | .inr (n,⊥), .inr (m,⊥), .inr (l,⊥) =>
        simp only [F, ↓reduceDIte, *]
        apply hc
    | .inr (n,⊥), .inr (m,⊥), .inr (l,⊤) =>
        simp only [F, ↓reduceDIte, *]
        conv => congr <;> rw [ElementaryEmbedding.comp_apply]
        congr 1
        apply hc
    | .inl (.inr ()), .inr (m,⊥), .inr (l,⊤) =>
        simp only [F, ↓reduceDIte, *]
        conv => congr <;> rw [ElementaryEmbedding.comp_apply]
        congr 1
        apply hc
    | .inl (.inl ()), .inr (m,⊥), .inr (l,⊥) =>
        simp only [F, ↓reduceDIte, *]
        sorry
    | .inl (.inl ()), .inr (m,⊥), .inr (l,⊤) =>
        simp only [F, ↓reduceDIte, *]
        sorry
    | .inr (n,⊤), .inr (m,⊥), .inr (l,⊤) =>
        simp only [F, ↓reduceDIte, *]
        sorry
    | .inl (.inr ()), .inr (m,⊤), .inr (l,⊤) =>
        simp only [F, ↓reduceDIte, *]
        sorry
    | .inr (n,⊥), .inr (m,⊤), .inr (l,⊤) =>
        simp only [F, ↓reduceDIte, *]
        sorry
    | .inr (n,⊤), .inr (m,⊥), .inr (l,⊥) =>
        simp only [F, ↓reduceDIte, *]
        sorry
    | .inl (.inr ()), .inr (m,⊤), .inr (l,⊥) =>
        simp only [F, ↓reduceDIte, *]
        sorry
    | .inr (n,⊥), .inr (m,⊤), .inr (l,⊥) =>
        simp only [F, ↓reduceDIte, *]
        sorry

-- open Classical in
-- theorem Robinson : (ψ₁.onTheory T₁ ∪ ψ₂.onTheory T₂).IsSatisfiable := by
--   refine ⟨@Theory.ModelType.mk _ _ (L.DirectLimit G (system F)) ?_ ?_ _⟩
--   · sorry
--   · sorry
