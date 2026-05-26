import FMiM.Amalgamation
import Mathlib.Data.Stream.Defs
import Mathlib.Data.PNat.Basic

open FirstOrder Language LHom DirectedSystem

section

variable {L' L : Language} (ϕ : L →ᴸ L')

structure FirstOrder.Language.LHom.RedStruc extends L'.Struc where
  [red : L.Structure carrier]
  [exp : ϕ.IsExpansionOn carrier]

attribute [instance] RedStruc.red RedStruc.exp

instance : CoeSort ϕ.RedStruc Type := ⟨fun X => X.carrier⟩

abbrev FirstOrder.Language.LHom.mkRS : L'.Struc → ϕ.RedStruc := (.mk (red := ϕ.reduct ·))

end

noncomputable section Robinson

class langs where
  L : Language
  E₁ : Language
  E₂ : Language

variable [langs]

namespace langs

abbrev L₁ := L.sum E₁
abbrev L₂ := L.sum E₂
abbrev L' := L.sum (E₁.sum E₂)
abbrev ϕ₁ : L →ᴸ L₁ := .sumInl
abbrev ϕ₂ : L →ᴸ L₂ := .sumInl
abbrev ψ₁ : L₁ →ᴸ L' := .sumMap (.id L) .sumInl
abbrev ψ₂ : L₂ →ᴸ L' := .sumMap (.id L) .sumInr

protected instance symm : langs := ⟨L, E₂, E₁⟩

end langs

open langs

structure layer where
  A : ϕ₁.RedStruc
  B : ϕ₂.RedStruc
  f : A ↪ₑ[L] B

theorem amalg_of_equivalence' {A : Type} [L.Structure A] {B : ϕ₂.RedStruc} (hAB : A ≅[L] B)
  : Nonempty <| Σ (B' : ϕ₂.RedStruc), (A ↪ₑ[L] B') × (B ↪ₑ[L₂] B') :=
  (amalg_of_equivalence .sumInl sumInl_injective hAB).elim fun C => ⟨⟨⟨C⟩⟩, C.mapl, C.mapr⟩

theorem layer.amalg (AB : layer) : ∃ (A' : ϕ₁.RedStruc) (g : AB.B ↪ₑ[L] A') (k : AB.A ↪ₑ[L₁] A'),
    ∀ a, g (AB.f a) = k a :=
  (amalg_of_embeddings AB.f (.refl L AB.A) sumInl_injective).elim fun C comm =>
    ⟨⟨⟨C⟩⟩, C.mapl, C.mapr, comm⟩

def layer.nextA (AB : layer) : ϕ₁.RedStruc :=
  AB.amalg.choose

def layer.g (AB : layer) : AB.B ↪ₑ[L] AB.nextA :=
  AB.amalg.choose_spec.choose

def layer.k (AB : layer) : AB.A ↪ₑ[L₁] AB.nextA :=
  AB.amalg.choose_spec.choose_spec.choose

theorem layer.gf_k {AB : layer} : ∀ a, AB.g (AB.f a) = AB.k a :=
  AB.amalg.choose_spec.choose_spec.choose_spec

def layer.nextB (AB : layer) : ϕ₂.RedStruc :=
  (@layer.amalg .symm <| @mk .symm AB.B AB.nextA AB.g).choose

def layer.nextf (AB : layer) : AB.nextA ↪ₑ[L] AB.nextB :=
  (@layer.amalg .symm <| @mk .symm AB.B AB.nextA AB.g).choose_spec.choose

def layer.h (AB : layer) : AB.B ↪ₑ[L₂] AB.nextB :=
  (@layer.amalg .symm <| @mk .symm AB.B AB.nextA AB.g).choose_spec.choose_spec.choose

theorem layer.fg_h {AB : layer} : ∀ b, AB.nextf (AB.g b) = AB.h b :=
  (@layer.amalg .symm <| @mk .symm AB.B AB.nextA AB.g).choose_spec.choose_spec.choose_spec

abbrev layer.next (AB : layer) : layer := ⟨AB.nextA, AB.nextB, AB.nextf⟩

@[simp]
theorem layer.fk_hf {AB : layer} : ∀ a, AB.next.f (AB.k a) = AB.h (AB.f a) := by
  intro
  rw [← AB.gf_k, AB.fg_h]

@[simp]
theorem layer.gh_kg {AB : layer} : ∀ b, AB.next.g (AB.h b) = AB.next.k (AB.g b) := by
  intro
  rw [← AB.fg_h, AB.next.gf_k]

class problem [langs] where
  T : L.Theory
  T_cpl : T.IsComplete
  T₁ : L₁.Theory
  T₂ : L₂.Theory
  T_sub₁ : ϕ₁.onTheory T ⊆ T₁
  T_sub₂ : ϕ₂.onTheory T ⊆ T₂
  sat₁ : T₁.IsSatisfiable
  sat₂ : T₂.IsSatisfiable

variable [problem]

namespace problem

abbrev T' := ψ₁.onTheory T₁ ∪ ψ₂.onTheory T₂

protected instance symm : @problem .symm :=
  @mk .symm T T_cpl T₂ T₁ T_sub₂ T_sub₁ sat₂ sat₁

end problem

open problem

theorem reduct_elementarilyEquivalent_of_extend_completeTheory'
  {A : ϕ₁.RedStruc} {B : ϕ₂.RedStruc} [hA : A ⊨ T₁] [hB : B ⊨ T₂] :
    A ≅[L] B := by
  have := (onTheory_model _ _).1 <| hA.mono T_sub₁
  have := (onTheory_model _ _).1 <| hB.mono T_sub₂
  calc
    _ = _ := Eq.symm <| T_cpl.eq_complete_theory _
    _ = _ := T_cpl.eq_complete_theory _

def layer.base : layer :=
  letI A  := ϕ₁.mkRS ⟨sat₁.some⟩
  letI B' := ϕ₂.mkRS ⟨sat₂.some⟩
  letI Bfh := Nonempty.some <|
    amalg_of_equivalence' (reduct_elementarilyEquivalent_of_extend_completeTheory' : A ≅[L] B')
  ⟨A, Bfh.1, Bfh.2.1⟩

def layers := Stream'.iterate layer.next layer.base

@[implicit_reducible]
def A (n : ℕ) : ϕ₁.RedStruc := (layers.get n).A

@[implicit_reducible]
def B (n : ℕ) : ϕ₂.RedStruc := (layers.get n).B

-- unif_hint {n : ℕ} where

@[reducible]
def G : ℕ ×ₗ Bool → Type
| (n,⊥) => A n
| (n,⊤) => B n

instance : ∀ i, L.Structure (G i)
| (_,⊥)    => inferInstanceAs <| L.Structure (A _)
| (_,⊤)    => inferInstanceAs <| L.Structure (B _)

instance : ∀ i, Nonempty (G i)
| (_,⊥)    => inferInstanceAs <| Nonempty (A _)
| (_,⊤)    => inferInstanceAs <| Nonempty (B _)

def iA : ℕ → ℕ ×ₗ Bool := (·, ⊥)

def iB : ℕ → ℕ ×ₗ Bool := (·, ⊤)

theorem G_iA (n : ℕ) : G (iA n) = A n := rfl

theorem G_iB (n : ℕ) : G (iB n) = B n := rfl

def k_sys : (n m : ℕ) → n ≤ m → A n ↪ₑ[L₁] A m :=
  natLERecₑ (layer.k <| layers.get ·)

def h_sys : (n m : ℕ) → n ≤ m → B n ↪ₑ[L₂] B m :=
  natLERecₑ (layer.h <| layers.get ·)

instance : DirectedSystem _ (k_sys · · ·) :=
  inferInstanceAs (DirectedSystem _ (natLERecₑ _ · · ·))

instance : DirectedSystem _ (h_sys · · ·) :=
  inferInstanceAs (DirectedSystem _ (natLERecₑ _ · · ·))

-- set_option trace.Meta.isDefEq true in
@[simp]
theorem k_sys_succ {n m : ℕ} (nm : n ≤ m)
  : ∀ a, k_sys _ _ nm.step a = (layers.get m).k (k_sys _ _ nm a) := by
  intro a
  rw [k_sys, coe_natLERecₑ, coe_natLERecₑ]
  apply Nat.leRecOn_succ

@[simp]
theorem h_sys_succ {n m : ℕ} (nm : n ≤ m)
  : ∀ b, h_sys _ _ nm.step b = (layers.get m).h (h_sys _ _ nm b) := by
  intro b
  rw [h_sys, coe_natLERecₑ, coe_natLERecₑ]
  apply Nat.leRecOn_succ

@[simp]
theorem fk_hf_sys {n m : ℕ} {nm : n ≤ m}
  : ∀ a, (layers.get m).f (k_sys n m nm a) = h_sys n m nm ((layers.get n).f a) := by
  intro a
  induction m, nm using Nat.le_induction with
  | base => rw [map_self k_sys, map_self h_sys]
  | succ l nl ih =>
    rw [k_sys_succ nl, h_sys_succ nl, ← ih]
    apply layer.fk_hf

@[simp]
theorem gh_kg_sys {n m : ℕ} {nm : n ≤ m} {nm' : n + 1 ≤ m + 1}
  : ∀ b, (layers.get m).g (h_sys n m nm b) = k_sys _ _ nm' ((layers.get n).g b) := by
  intro a
  induction m, nm using Nat.le_induction with
  | base => rw [map_self k_sys, map_self h_sys]
  | succ l nl ih =>
    rw [h_sys_succ nl, k_sys_succ <| Nat.succ_le_succ nl, ← ih]
    apply layer.gh_kg

noncomputable def F (i j : ℕ ×ₗ Bool) (ij : i ≤ j) : G i ↪ₑ[L] G j := match i,j with
| (n,⊥), (m,⊥) => (k_sys n m ij.monotone_fst).reduct ϕ₁
| (n,⊤), (m,⊤) => (h_sys n m ij.monotone_fst).reduct ϕ₂
| (n,⊥), (m,⊤) => (layers.get m).f.comp <| (k_sys n m ij.monotone_fst).reduct ϕ₁
| (n,⊤), (m,⊥) =>
  have nm : n < m := (Prod.Lex.le_iff.mp ij).resolve_right <|
    not_and_of_not_right _ <| not_le.mpr Bool.false_lt_true
  ((k_sys _ _ (Nat.succ_le_of_lt nm)).reduct ϕ₁).comp (layers.get n).g

open ElementaryEmbedding

instance : DirectedSystem G (F · · ·) where
  map_self
  | (n,⊥) => (map_self k_sys ·)
  | (m,⊤) => (map_self h_sys ·)

  map_map := by
    have : ¬ ⊤ ≤ ⊥ := not_le.mpr Bool.false_lt_true
    rintro ⟨l, ⟨⟩⟩ ⟨m, ⟨⟩⟩ ⟨n, ⟨⟩⟩ ⟨_, _, nm⟩ ⟨_, _, ml⟩ x
    <;> first
    | contradiction
    | simp only [F]
    ; first
    | apply map_map k_sys
    | apply map_map h_sys
    | repeat (rw [comp_apply]; try rw [reduct_apply])
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
