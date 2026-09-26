import StringDiagrams.Super.TwoFunctor
import StringDiagrams.Super.Graded
import Mathlib.Tactic.CategoryTheory.Bicategory.Basic

/-!
# Graded 2-supercategories and graded (Q, Π)-2-supercategories

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §6,
Definitions 6.2, 6.3, 6.5 and Lemma 6.11.

* A *graded 2-supercategory* (`StringDiagrams.GradedTwoSupercategory`, Definition 6.2 and its
  weak version) is a 2-supercategory whose morphism supercategories are graded
  supercategories, such that horizontal composition preserves degrees and the coherence maps
  have degree `0`. In the unpacked form of `TwoSupercategory`: whiskering preserves degrees
  (`whiskerLeft_mem_degree`, `whiskerRight_mem_degree`) and the associator and unitors have
  degree `0`. A *strict graded 2-supercategory* (a category enriched in `GSCat`, Definition
  6.2) is a graded 2-supercategory with `BicategoryStruct.Strict`.
* A *graded 2-superfunctor* (`TwoSuperfunctor.IsGraded`, Definition 6.3): a 2-superfunctor
  whose superfunctors on morphism supercategories are graded and whose coherence maps `c`, `i`
  have degree `0`. The graded versions of 2-natural transformations and supermodifications,
  which the paper leaves to the reader, are `TwoNatTrans.IsGraded` (the `x_F` have degree
  `0`) and `Supermodification.IsHomogeneous` (homogeneous of a given parity and degree).
* A *graded `(Q, Π)`-2-supercategory* (`StringDiagrams.QPiTwoSupercategory`, Definition 6.5):
  a graded 2-supercategory with families of 1-morphisms `q_λ`, `q_λ⁻¹`, `π_λ` and
  2-isomorphisms `σ_λ : q_λ ⇒ 1_λ`, `σ̄_λ : q_λ⁻¹ ⇒ 1_λ`, `ζ_λ : π_λ ⇒ 1_λ`, which are even,
  even and odd of degrees `-1`, `1` and `0`. It extends `PiTwoSupercategory`
  (Definition 3.1).
* **Lemma 6.11**, stated (like Lemma 3.2 in `StringDiagrams.Super.PiTwo`) for not necessarily
  strict 2-supercategories, the unitors and associators being inserted:
  (i) `β` and `ξ` of Lemma 3.2 are even of degree zero (`β_hom_mem_degree`,
  `ξ_hom_mem_degree`); (ii) `γ_F := σ_μ F σ_λ⁻¹ : q_μ F ≅ F q_λ`
  (`QPiTwoSupercategory.γ`) is even of degree zero, supernatural (`γ_naturality`), and
  satisfies `γ_{GF} = G γ_F ∘ γ_G F` (`γ_comp`), `γ_{1_λ} = 1_{q_λ}` (`γ_id`),
  `γ_{q_λ} = 1_{q_λ²}` (`γ_q`) and `γ_{π_λ} = β_{q_λ}⁻¹` (`γ_pi`); (iii)
  `ii_λ := σ̄_λσ_λ : q_λ⁻¹ q_λ ≅ 1_λ` and `jj_λ := σ_λσ̄_λ : q_λ q_λ⁻¹ ≅ 1_λ` are even of
  degree zero with `q_λ ii_λ = jj_λ q_λ` (`q_ii`) and `ii_λ q_λ⁻¹ = q_λ⁻¹ jj_λ` (`ii_qinv`).

The identities of (ii)–(iii) involve only even 2-morphisms; they are proved in the underlying
bicategory `Underlying2 R B`, where Mathlib's bicategorical coherence applies, and transported
back.

Compositions of 1-morphisms are written in diagrammatic order: `f ≫ g` is the paper's `g f`.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory

universe w v u w₁ w₂ v₂ u₂

/-! ## Isomorphisms `q ≅ 1` in a bicategory

Generic identities for a family of 2-isomorphisms `s_λ : q_λ ≅ 1_λ` in a (Mathlib) bicategory,
used for Lemma 6.11(ii)–(iii) through the underlying bicategory of even 2-morphisms. -/

namespace UnitIso

open Bicategory

variable {𝔅 : Type*} [Bicategory 𝔅] {a b c : 𝔅}

/-- For `s : q ≅ 1`, the two ways of contracting `q q` agree:
`s q = q s` up to unitors. -/
theorem swap (q : a ⟶ a) (s : q ≅ 𝟙 a) :
    s.hom ▷ q ≫ (λ_ q).hom = q ◁ s.hom ≫ (ρ_ q).hom := by
  rw [← cancel_mono s.hom]
  simp only [Category.assoc]
  rw [← leftUnitor_naturality, ← rightUnitor_naturality, unitors_equal]
  rw [← whisker_exchange_assoc]

variable (q : ∀ a : 𝔅, a ⟶ a) (s : ∀ a, q a ≅ 𝟙 a)

/-- The half-braiding `F q_μ ≅ q_λ F` (diagrammatic order) determined by `s`:
`F ◁ s_μ ≫ ρ_F ≫ λ_F⁻¹ ≫ s_λ⁻¹ ▷ F`. -/
def halfBraid (f : a ⟶ b) : f ≫ q b ≅ q a ≫ f :=
  whiskerLeftIso f (s b) ≪≫ ρ_ f ≪≫ (λ_ f).symm ≪≫ whiskerRightIso (s a).symm f

theorem halfBraid_hom (f : a ⟶ b) : (halfBraid q s f).hom =
    f ◁ (s b).hom ≫ (ρ_ f).hom ≫ (λ_ f).inv ≫ (s a).inv ▷ f := by
  simp [halfBraid]

theorem halfBraid_self (a : 𝔅) : (halfBraid q s (q a)).hom = 𝟙 _ := by
  rw [halfBraid_hom, ← reassoc_of% (swap (q a) (s a))]
  simp

theorem halfBraid_id (a : 𝔅) :
    (halfBraid q s (𝟙 a)).hom = (λ_ (q a)).hom ≫ (ρ_ (q a)).inv := by
  rw [halfBraid_hom, ← cancel_mono ((ρ_ (q a)).hom), ← cancel_mono (s a).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [rightUnitor_naturality_assoc, ← unitors_equal, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id, leftUnitor_naturality]

theorem halfBraid_comp (f : a ⟶ b) (g : b ⟶ c) :
    (halfBraid q s (f ≫ g)).hom = (α_ f g (q c)).hom ≫ f ◁ (halfBraid q s g).hom ≫
      (α_ f (q b) g).inv ≫ (halfBraid q s f).hom ▷ g ≫ (α_ (q a) f g).hom := by
  rw [halfBraid_hom, halfBraid_hom, halfBraid_hom]
  simp only [Bicategory.whiskerLeft_comp, Bicategory.comp_whiskerRight, Category.assoc]
  rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc, ← Bicategory.whiskerLeft_comp]
  simp only [Iso.inv_hom_id, Bicategory.whiskerLeft_id, Bicategory.id_whiskerRight, Category.id_comp]
  bicategory

variable {x : 𝔅} {q' qi : x ⟶ x} (s' : q' ≅ 𝟙 x) (t : qi ≅ 𝟙 x)

/-- `ii := s̄ s : q q⁻¹ ≅ 1` (diagrammatic order: `q` first). -/
def ii : q' ≫ qi ≅ 𝟙 x := whiskerRightIso s' qi ≪≫ λ_ qi ≪≫ t

/-- `jj := s s̄ : q⁻¹ q ≅ 1` (diagrammatic order: `q⁻¹` first). -/
def jj : qi ≫ q' ≅ 𝟙 x := whiskerRightIso t q' ≪≫ λ_ q' ≪≫ s'

/-- The paper's `q ii = jj q`. -/
theorem q_ii : (ii s' t).hom ▷ q' ≫ (λ_ q').hom =
    (α_ q' qi q').hom ≫ q' ◁ (jj s' t).hom ≫ (ρ_ q').hom := by
  simp only [ii, jj, Iso.trans_hom, whiskerRightIso_hom, Bicategory.whiskerLeft_comp, Bicategory.comp_whiskerRight,
    Category.assoc]
  rw [← swap q' s', whisker_exchange_assoc, whisker_exchange_assoc]
  bicategory

/-- The paper's `ii q⁻¹ = q⁻¹ jj`. -/
theorem ii_qinv : qi ◁ (ii s' t).hom ≫ (ρ_ qi).hom =
    (α_ qi q' qi).inv ≫ (jj s' t).hom ▷ qi ≫ (λ_ qi).hom := by
  simp only [ii, jj, Iso.trans_hom, whiskerRightIso_hom, Bicategory.whiskerLeft_comp, Bicategory.comp_whiskerRight,
    Category.assoc]
  rw [← swap qi t, whisker_exchange_assoc, whisker_exchange_assoc]
  bicategory

end UnitIso


open Supercategory GradedSupercategory BicategoryStruct TwoSupercategory

section Defs

variable (R : Type w₁) [CommRing R] (B : Type u) [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [∀ a b : B, GradedSupercategory R (a ⟶ b)]

/-- A graded 2-supercategory (Brundan–Ellis, Definition 6.2 and the weak version after it):
a 2-supercategory whose morphism supercategories are graded, such that whiskering preserves
degrees and the coherence maps have degree `0`. It is strict if `BicategoryStruct.Strict B`
holds. -/
class GradedTwoSupercategory [TwoSupercategory R B] : Prop where
  whiskerLeft_mem_degree {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} {n : ℤ} {η : g ⟶ h} :
    η ∈ degree (R := R) g h n → f ◁ η ∈ degree (R := R) (f ≫ g) (f ≫ h) n
  whiskerRight_mem_degree {a b c : B} {f g : a ⟶ b} {n : ℤ} {η : f ⟶ g} (h : b ⟶ c) :
    η ∈ degree (R := R) f g n → η ▷ h ∈ degree (R := R) (f ≫ h) (g ≫ h) n
  associator_hom_mem_degree {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (associator f g h).hom ∈ degree (R := R) ((f ≫ g) ≫ h) (f ≫ g ≫ h) 0
  leftUnitor_hom_mem_degree {a b : B} (f : a ⟶ b) :
    (leftUnitor f).hom ∈ degree (R := R) (𝟙 a ≫ f) f 0
  rightUnitor_hom_mem_degree {a b : B} (f : a ⟶ b) :
    (rightUnitor f).hom ∈ degree (R := R) (f ≫ 𝟙 b) f 0

end Defs

namespace GradedTwoSupercategory

variable {R : Type w₁} [CommRing R] {B : Type u} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [∀ a b : B, GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R B] [GradedTwoSupercategory R B]

/-- Horizontal composition adds degrees. -/
theorem hcomp_mem_degree {a b c : B} {f g : a ⟶ b} {h i : b ⟶ c} {m n : ℤ} {x : f ⟶ g}
    {y : h ⟶ i} (hx : x ∈ degree (R := R) f g m) (hy : y ∈ degree (R := R) h i n) :
    hcomp x y ∈ degree (R := R) (f ≫ h) (g ≫ i) (m + n) :=
  comp_mem_degree (whiskerRight_mem_degree h hx) (whiskerLeft_mem_degree g hy)

theorem associator_inv_mem_degree {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (associator f g h).inv ∈ degree (R := R) (f ≫ g ≫ h) ((f ≫ g) ≫ h) 0 := by
  simpa using inv_mem_degree _ (associator_hom_mem_degree (R := R) f g h)

theorem leftUnitor_inv_mem_degree {a b : B} (f : a ⟶ b) :
    (leftUnitor f).inv ∈ degree (R := R) f (𝟙 a ≫ f) 0 := by
  simpa using inv_mem_degree _ (leftUnitor_hom_mem_degree (R := R) f)

theorem rightUnitor_inv_mem_degree {a b : B} (f : a ⟶ b) :
    (rightUnitor f).inv ∈ degree (R := R) f (f ≫ 𝟙 b) 0 := by
  simpa using inv_mem_degree _ (rightUnitor_hom_mem_degree (R := R) f)

end GradedTwoSupercategory

/-! ## Graded 2-superfunctors, 2-natural transformations and supermodifications -/

section Functors

variable {R : Type w} [CommRing R]
  {B : Type u} [BicategoryStruct.{w₁, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [∀ a b : B, GradedSupercategory R (a ⟶ b)]
  {C : Type u₂} [BicategoryStruct.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ a b : C, Supercategory R (a ⟶ b)] [∀ a b : C, GradedSupercategory R (a ⟶ b)]

/-- A graded 2-superfunctor (Brundan–Ellis, Definition 6.3): the superfunctors
`ℋom(λ, μ) → ℋom(ℝλ, ℝμ)` are graded, and the coherence isomorphisms `c` and `i` (which are
even) have degree `0`. -/
structure TwoSuperfunctor.IsGraded (F : TwoSuperfunctor R B C) : Prop where
  map₂_mem_degree {a b : B} {f g : a ⟶ b} {n : ℤ} {η : f ⟶ g} :
    η ∈ degree (R := R) f g n → F.map₂ η ∈ degree (R := R) (F.map f) (F.map g) n
  mapComp_hom_mem_degree {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    (F.mapComp f g).hom ∈ degree (R := R) (F.map f ≫ F.map g) (F.map (f ≫ g)) 0
  mapId_hom_mem_degree (a : B) : (F.mapId a).hom ∈ degree (R := R) (𝟙 (F.obj a)) (F.map (𝟙 a)) 0

/-- The superfunctors on morphism supercategories of a graded 2-superfunctor are graded. -/
theorem TwoSuperfunctor.IsGraded.isGradedSuperfunctor {F : TwoSuperfunctor R B C}
    (hF : F.IsGraded) (a b : B) : IsGradedSuperfunctor R (F.mapFunctor a b) where
  map_mem_degree := hF.map₂_mem_degree

/-- The identity 2-superfunctor is graded. -/
theorem TwoSuperfunctor.id_isGraded [TwoSupercategory R B] : (TwoSuperfunctor.id R B).IsGraded where
  map₂_mem_degree h := h
  mapComp_hom_mem_degree _ _ := id_mem_degree _
  mapId_hom_mem_degree _ := id_mem_degree _

/-- A graded 2-natural transformation: the even 2-morphisms `x_F` have degree `0` (the graded
version of Definition 2.2(iii), left to the reader in §6). -/
def TwoNatTrans.IsGraded {F G : TwoSuperfunctor R B C} (θ : TwoNatTrans F G) : Prop :=
  ∀ {a b : B} (f : a ⟶ b), θ.x f ∈ degree (R := R) (F.map f ≫ θ.X b) (θ.X a ≫ G.map f) 0

/-- A supermodification homogeneous of parity `p` and degree `n` (the graded version of
Definition 2.2(iv), left to the reader in §6). -/
def Supermodification.IsHomogeneous {F G : TwoSuperfunctor R B C} {θ θ' : TwoNatTrans F G}
    (α : Supermodification θ θ') (p : ZMod 2) (n : ℤ) : Prop :=
  ∀ a : B, α.app a ∈ parity (R := R) (θ.X a) (θ'.X a) p ∧
    α.app a ∈ degree (R := R) (θ.X a) (θ'.X a) n

end Functors

/-! ## Graded (Q, Π)-2-supercategories -/

section QPiDef

variable (R : Type w₁) [CommRing R] (B : Type u) [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [∀ a b : B, GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R B]

/-- A graded `(Q, Π)`-2-supercategory (Brundan–Ellis, Definition 6.5): a graded
2-supercategory with 1-morphisms `q_λ, q_λ⁻¹, π_λ : λ → λ` and 2-isomorphisms
`σ_λ : q_λ ⇒ 1_λ`, `σ̄_λ : q_λ⁻¹ ⇒ 1_λ`, `ζ_λ : π_λ ⇒ 1_λ` which are even, even and odd of
degrees `-1`, `1` and `0`. -/
class QPiTwoSupercategory [GradedTwoSupercategory R B] extends PiTwoSupercategory R B where
  ζ_hom_mem_degree : ∀ a : B, (ζ a).hom ∈ degree (R := R) (pi a) (𝟙 a) 0
  /-- The 1-morphisms `q_λ`. -/
  q : ∀ a : B, a ⟶ a
  /-- The 1-morphisms `q_λ⁻¹`. -/
  qinv : ∀ a : B, a ⟶ a
  /-- The 2-isomorphisms `σ_λ : q_λ ⇒ 1_λ`. -/
  σ : ∀ a : B, q a ≅ 𝟙 a
  /-- The 2-isomorphisms `σ̄_λ : q_λ⁻¹ ⇒ 1_λ`. -/
  σbar : ∀ a : B, qinv a ≅ 𝟙 a
  σ_hom_mem : ∀ a : B, (σ a).hom ∈ parity (R := R) (q a) (𝟙 a) 0
  σ_hom_mem_degree : ∀ a : B, (σ a).hom ∈ degree (R := R) (q a) (𝟙 a) (-1)
  σbar_hom_mem : ∀ a : B, (σbar a).hom ∈ parity (R := R) (qinv a) (𝟙 a) 0
  σbar_hom_mem_degree : ∀ a : B, (σbar a).hom ∈ degree (R := R) (qinv a) (𝟙 a) 1

end QPiDef

/-! ## Lemma 6.11 -/

namespace QPiTwoSupercategory

variable {R : Type w₁} [CommRing R] {B : Type u} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [∀ a b : B, GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R B] [GradedTwoSupercategory R B] [QPiTwoSupercategory R B]

open GradedTwoSupercategory PiTwoSupercategory

variable {a b c : B}

theorem σ_inv_mem (a : B) : (σ (R := R) a).inv ∈ parity (R := R) (𝟙 a) (q (R := R) a) 0 :=
  inv_mem _ (σ_hom_mem a)

theorem σ_inv_mem_degree (a : B) :
    (σ (R := R) a).inv ∈ degree (R := R) (𝟙 a) (q (R := R) a) 1 := by
  simpa using inv_mem_degree _ (σ_hom_mem_degree (R := R) a)

theorem σbar_inv_mem (a : B) :
    (σbar (R := R) a).inv ∈ parity (R := R) (𝟙 a) (qinv (R := R) a) 0 :=
  inv_mem _ (σbar_hom_mem a)

theorem σbar_inv_mem_degree (a : B) :
    (σbar (R := R) a).inv ∈ degree (R := R) (𝟙 a) (qinv (R := R) a) (-1) :=
  inv_mem_degree _ (σbar_hom_mem_degree (R := R) a)

theorem ζ_inv_mem_degree' (a : B) :
    (ζ (R := R) a).inv ∈ degree (R := R) (𝟙 a) (pi (R := R) a) 0 := by
  simpa using inv_mem_degree _ (ζ_hom_mem_degree (R := R) a)

/-! ### (i) `β` and `ξ` have degree zero -/

/-- **Lemma 6.11(i).** `β_F` (Lemma 3.2) is even of degree zero. -/
theorem β_hom_mem_degree (f : a ⟶ b) :
    (β (R := R) f).hom ∈ degree (R := R) (f ≫ pi (R := R) b) (pi (R := R) a ≫ f) 0 := by
  rw [β_hom]
  have h := comp_mem_degree (comp_mem_degree (comp_mem_degree
    (whiskerLeft_mem_degree f (ζ_hom_mem_degree (R := R) b))
    (rightUnitor_hom_mem_degree (R := R) f)) (leftUnitor_inv_mem_degree (R := R) f))
    (whiskerRight_mem_degree f (ζ_inv_mem_degree' (R := R) a))
  simpa [Category.assoc] using h

/-- **Lemma 6.11(i).** `ξ_λ` (Lemma 3.2(iv)) is even of degree zero. -/
theorem ξ_hom_mem_degree (a : B) :
    (ξ (R := R) a).hom ∈ degree (R := R) (pi (R := R) a ≫ pi (R := R) a) (𝟙 a) 0 := by
  rw [ξ_hom]
  have h := comp_mem_degree (comp_mem_degree
    (whiskerRight_mem_degree (pi (R := R) a) (ζ_hom_mem_degree (R := R) a))
    (leftUnitor_hom_mem_degree (R := R) (pi (R := R) a))) (ζ_hom_mem_degree (R := R) a)
  simpa [Category.assoc] using h

/-! ### (ii) The half-braiding `γ` -/

/-- **Lemma 6.11(ii).** `γ_F := σ_μ F σ_λ⁻¹ : q_μ F ⇒ F q_λ` for `F : λ → μ`, in the
diagrammatic order: `F ◁ σ_μ ≫ ρ_F ≫ λ_F⁻¹ ≫ σ_λ⁻¹ ▷ F : F ≫ q_μ ≅ q_λ ≫ F`. (All maps being
even, this is the horizontal composite of `σ_λ⁻¹` and `F σ_μ` up to unitors, without sign.) -/
def γ (f : a ⟶ b) : f ≫ q (R := R) b ≅ q (R := R) a ≫ f :=
  whiskerLeftIso (R := R) f (σ (R := R) b) ≪≫ rightUnitor f ≪≫ (leftUnitor f).symm ≪≫
    whiskerRightIso (R := R) (σ (R := R) a).symm f

theorem γ_hom (f : a ⟶ b) : (γ (R := R) f).hom =
    f ◁ (σ (R := R) b).hom ≫ (rightUnitor f).hom ≫ (leftUnitor f).inv ≫
      (σ (R := R) a).inv ▷ f := by
  simp [γ]

/-- **Lemma 6.11(ii).** `γ_F` is even. -/
theorem γ_hom_mem (f : a ⟶ b) :
    (γ (R := R) f).hom ∈ parity (R := R) (f ≫ q (R := R) b) (q (R := R) a ≫ f) 0 := by
  rw [γ_hom]
  have h := comp_mem (comp_mem (comp_mem (whiskerLeft_mem f (σ_hom_mem (R := R) b))
    (rightUnitor_hom_mem (R := R) f)) (inv_mem _ (leftUnitor_hom_mem (R := R) f)))
    (whiskerRight_mem f (σ_inv_mem (R := R) a))
  simpa [Category.assoc] using h

/-- **Lemma 6.11(ii).** `γ_F` has degree zero. -/
theorem γ_hom_mem_degree (f : a ⟶ b) :
    (γ (R := R) f).hom ∈ degree (R := R) (f ≫ q (R := R) b) (q (R := R) a ≫ f) 0 := by
  rw [γ_hom]
  have h := comp_mem_degree (comp_mem_degree (comp_mem_degree
    (whiskerLeft_mem_degree f (σ_hom_mem_degree (R := R) b))
    (rightUnitor_hom_mem_degree (R := R) f)) (leftUnitor_inv_mem_degree (R := R) f))
    (whiskerRight_mem_degree f (σ_inv_mem_degree (R := R) a))
  simpa [Category.assoc] using h

/-- **Lemma 6.11(ii).** `γ` is natural for all 2-morphisms `x : F ⇒ G` (of either parity):
`x q_λ ∘ γ_F = γ_G ∘ q_μ x`. Together with `γ_hom_mem`, `γ_{μ,λ}` is an even supernatural
isomorphism `q_μ - ⇒ - q_λ`. -/
theorem γ_naturality {f g : a ⟶ b} (x : f ⟶ g) :
    (γ (R := R) f).hom ≫ q (R := R) a ◁ x = x ▷ q (R := R) b ≫ (γ (R := R) g).hom := by
  refine induction_on (R := R) x (by simp [zero_whiskerRight R, whiskerLeft_zero R])
    (fun p x hx => ?_) (fun x y hx hy => ?_)
  · rw [γ_hom, γ_hom]
    simp only [Category.assoc]
    have h1 := super_interchange (R := R) (σ_inv_mem (R := R) a) hx
    have h2 := super_interchange (R := R) hx (σ_hom_mem (R := R) b)
    rw [koszulSign_zero_left, one_smul] at h1
    rw [koszulSign_zero_right, one_smul] at h2
    rw [h1, ← leftUnitor_inv_naturality_assoc R, ← rightUnitor_naturality_assoc R,
      ← reassoc_of% h2]
  · rw [whiskerLeft_add (R := R), add_whiskerRight (R := R), Preadditive.comp_add,
      Preadditive.add_comp, hx, hy]

/-! #### Transport to the underlying bicategory -/

/-- `q_λ` as a 1-morphism of the underlying bicategory. -/
abbrev qU (a : Underlying2 R B) : a ⟶ a := Underlying2.hom1 (q (R := R) a.obj)

/-- `q_λ⁻¹` as a 1-morphism of the underlying bicategory. -/
abbrev qinvU (a : Underlying2 R B) : a ⟶ a := Underlying2.hom1 (qinv (R := R) a.obj)

/-- `σ_λ` as a 2-isomorphism of the underlying bicategory. -/
def σU (a : Underlying2 R B) : qU a ≅ 𝟙 a :=
  Underlying.isoMk (σ (R := R) a.obj) (σ_hom_mem a.obj)

/-- `σ̄_λ` as a 2-isomorphism of the underlying bicategory. -/
def σbarU (a : Underlying2 R B) : qinvU a ≅ 𝟙 a :=
  Underlying.isoMk (σbar (R := R) a.obj) (σbar_hom_mem a.obj)

@[simp] theorem σU_hom_val (a : Underlying2 R B) : (σU a).hom.1 = (σ (R := R) a.obj).hom := rfl

@[simp] theorem σU_inv_val (a : Underlying2 R B) : (σU a).inv.1 = (σ (R := R) a.obj).inv := rfl

@[simp] theorem σbarU_hom_val (a : Underlying2 R B) :
    (σbarU a).hom.1 = (σbar (R := R) a.obj).hom := rfl

theorem halfBraid_val (f : a ⟶ b) :
    (UnitIso.halfBraid (qU (R := R) (B := B)) σU (Underlying2.hom1 (a := a) (b := b) f)).hom.1 =
      (γ (R := R) f).hom := by
  rw [UnitIso.halfBraid_hom, γ_hom]
  rfl

/-- **Lemma 6.11(ii).** `γ_{GF} = G γ_F ∘ γ_G F` (with associators). -/
theorem γ_comp (f : a ⟶ b) (g : b ⟶ c) :
    (γ (R := R) (f ≫ g)).hom = (associator f g (q (R := R) c)).hom ≫ f ◁ (γ (R := R) g).hom ≫
      (associator f (q (R := R) b) g).inv ≫ (γ (R := R) f).hom ▷ g ≫
        (associator (q (R := R) a) f g).hom := by
  have h := congrArg Subtype.val (UnitIso.halfBraid_comp (qU (R := R) (B := B)) σU
    (Underlying2.hom1 (a := a) (b := b) f) (Underlying2.hom1 (a := b) (b := c) g))
  rw [← halfBraid_val, ← halfBraid_val, ← halfBraid_val]
  exact h

/-- **Lemma 6.11(ii).** `γ_{1_λ} = 1_{q_λ}` (up to unitors). -/
theorem γ_id (a : B) :
    (γ (R := R) (𝟙 a)).hom = (leftUnitor (q (R := R) a)).hom ≫ (rightUnitor (q (R := R) a)).inv := by
  have h := congrArg Subtype.val (UnitIso.halfBraid_id (qU (R := R) (B := B)) σU ⟨a⟩)
  rw [← halfBraid_val]
  exact h

/-- **Lemma 6.11(ii).** `γ_{q_λ} = 1_{q_λ²}`. -/
theorem γ_q (a : B) : (γ (R := R) (q (R := R) a)).hom = 𝟙 _ := by
  have h := congrArg Subtype.val (UnitIso.halfBraid_self (qU (R := R) (B := B)) σU ⟨a⟩)
  rw [← halfBraid_val]
  exact h

/-- **Lemma 6.11(ii).** `γ_{π_λ} = β_{q_λ}⁻¹`. -/
theorem γ_pi (a : B) : (γ (R := R) (pi (R := R) a)).hom = (β (R := R) (q (R := R) a)).inv := by
  rw [← cancel_mono (β (R := R) (q (R := R) a)).hom, Iso.inv_hom_id, γ_hom, β_hom]
  simp only [Category.assoc]
  have h1 := super_interchange (R := R) (σ_inv_mem (R := R) a) (ζ_hom_mem (R := R) a)
  rw [koszulSign_zero_left, one_smul] at h1
  have h2 := super_interchange (R := R) (ζ_hom_mem (R := R) a) (σ_hom_mem (R := R) a)
  rw [koszulSign_zero_right, one_smul] at h2
  rw [reassoc_of% h1, ← leftUnitor_inv_naturality_assoc R, rightUnitor_naturality_assoc R,
    ← unitors_equal R, Iso.inv_hom_id_assoc, ← rightUnitor_naturality_assoc R,
    ← reassoc_of% h2, ← unitors_equal R, leftUnitor_naturality_assoc R, Iso.hom_inv_id_assoc,
    Iso.hom_inv_id_assoc, hom_inv_whiskerRight R]

/-! ### (iii) `ii` and `jj` -/

/-- **Lemma 6.11(iii).** `ii_λ := σ̄_λ σ_λ : q_λ⁻¹ q_λ ≅ 1_λ`, in the diagrammatic order
`q_λ ≫ q_λ⁻¹ ≅ 𝟙`: `σ_λ ▷ q_λ⁻¹ ≫ λ ≫ σ̄_λ`. -/
def ii (a : B) : q (R := R) a ≫ qinv (R := R) a ≅ 𝟙 a :=
  whiskerRightIso (R := R) (σ (R := R) a) (qinv (R := R) a) ≪≫ leftUnitor _ ≪≫ σbar (R := R) a

/-- **Lemma 6.11(iii).** `jj_λ := σ_λ σ̄_λ : q_λ q_λ⁻¹ ≅ 1_λ`, in the diagrammatic order
`q_λ⁻¹ ≫ q_λ ≅ 𝟙`: `σ̄_λ ▷ q_λ ≫ λ ≫ σ_λ`. -/
def jj (a : B) : qinv (R := R) a ≫ q (R := R) a ≅ 𝟙 a :=
  whiskerRightIso (R := R) (σbar (R := R) a) (q (R := R) a) ≪≫ leftUnitor _ ≪≫ σ (R := R) a

theorem ii_hom (a : B) : (ii (R := R) a).hom = (σ (R := R) a).hom ▷ qinv (R := R) a ≫
    (leftUnitor (qinv (R := R) a)).hom ≫ (σbar (R := R) a).hom := by
  simp [ii]

theorem jj_hom (a : B) : (jj (R := R) a).hom = (σbar (R := R) a).hom ▷ q (R := R) a ≫
    (leftUnitor (q (R := R) a)).hom ≫ (σ (R := R) a).hom := by
  simp [jj]

/-- **Lemma 6.11(iii).** `ii_λ` is even. -/
theorem ii_hom_mem (a : B) : (ii (R := R) a).hom ∈ parity (R := R) _ (𝟙 a) 0 := by
  rw [ii_hom]
  simpa [Category.assoc] using comp_mem (comp_mem (whiskerRight_mem _ (σ_hom_mem (R := R) a))
    (leftUnitor_hom_mem (R := R) _)) (σbar_hom_mem (R := R) a)

/-- **Lemma 6.11(iii).** `ii_λ` has degree zero. -/
theorem ii_hom_mem_degree (a : B) : (ii (R := R) a).hom ∈ degree (R := R) _ (𝟙 a) 0 := by
  rw [ii_hom]
  have h := comp_mem_degree (comp_mem_degree
    (whiskerRight_mem_degree _ (σ_hom_mem_degree (R := R) a))
    (leftUnitor_hom_mem_degree (R := R) _)) (σbar_hom_mem_degree (R := R) a)
  simpa [Category.assoc] using h

/-- **Lemma 6.11(iii).** `jj_λ` is even. -/
theorem jj_hom_mem (a : B) : (jj (R := R) a).hom ∈ parity (R := R) _ (𝟙 a) 0 := by
  rw [jj_hom]
  simpa [Category.assoc] using comp_mem (comp_mem (whiskerRight_mem _ (σbar_hom_mem (R := R) a))
    (leftUnitor_hom_mem (R := R) _)) (σ_hom_mem (R := R) a)

/-- **Lemma 6.11(iii).** `jj_λ` has degree zero. -/
theorem jj_hom_mem_degree (a : B) : (jj (R := R) a).hom ∈ degree (R := R) _ (𝟙 a) 0 := by
  rw [jj_hom]
  have h := comp_mem_degree (comp_mem_degree
    (whiskerRight_mem_degree _ (σbar_hom_mem_degree (R := R) a))
    (leftUnitor_hom_mem_degree (R := R) _)) (σ_hom_mem_degree (R := R) a)
  simpa [Category.assoc] using h

/-- **Lemma 6.11(iii).** `q_λ ii_λ = jj_λ q_λ` in `Hom(q_λ q_λ⁻¹ q_λ, q_λ)` (with unitors and
the associator). -/
theorem q_ii (a : B) : (ii (R := R) a).hom ▷ q (R := R) a ≫ (leftUnitor (q (R := R) a)).hom =
    (associator (q (R := R) a) (qinv (R := R) a) (q (R := R) a)).hom ≫
      q (R := R) a ◁ (jj (R := R) a).hom ≫ (rightUnitor (q (R := R) a)).hom := by
  exact congrArg Subtype.val (UnitIso.q_ii (σU (R := R) (B := B) ⟨a⟩) (σbarU ⟨a⟩))

/-- **Lemma 6.11(iii).** `ii_λ q_λ⁻¹ = q_λ⁻¹ jj_λ` in `Hom(q_λ⁻¹ q_λ q_λ⁻¹, q_λ⁻¹)` (with
unitors and the associator). -/
theorem ii_qinv (a : B) : qinv (R := R) a ◁ (ii (R := R) a).hom ≫
    (rightUnitor (qinv (R := R) a)).hom =
      (associator (qinv (R := R) a) (q (R := R) a) (qinv (R := R) a)).inv ≫
        (jj (R := R) a).hom ▷ qinv (R := R) a ≫ (leftUnitor (qinv (R := R) a)).hom := by
  exact congrArg Subtype.val (UnitIso.ii_qinv (σU (R := R) (B := B) ⟨a⟩) (σbarU ⟨a⟩))

end QPiTwoSupercategory

end StringDiagrams

end
