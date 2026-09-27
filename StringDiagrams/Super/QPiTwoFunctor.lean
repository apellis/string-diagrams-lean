import StringDiagrams.Super.QPiTwoHom
import StringDiagrams.Super.AssociatedTwoNat

/-!
# (Q, Π)-2-functors, (Q, Π)-2-natural transformations and the 2-functor `𝔼` on them

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §6, the
discussion after Definition 6.14 ("we leave it to the reader to formalize this statement by
writing down the appropriate analog of Theorem 5.5").

## Definition (not in the paper)

The paper does not define the 1- and 2-morphisms between `(Q, Π)`-2-categories. We use the
2-categorical analogue of the `(Q, Π)`-functors of Definition 6.12(ii) (with the compatibility
axiom adopted in `StringDiagrams.Super.QPiCategory`, see erratum 4 of `README.md`), modelled on
Definition 5.2(ii)–(iii). For `(Q, Π)`-2-categories `𝔄`, `𝔅` (Definition 6.14):

* A **`(Q, Π)`-2-functor** `𝔄 → 𝔅` (`StringDiagrams.QPiTwoFunctor`) is a Π-2-functor
  `(ℝ, j)` (Definition 5.2(ii), `StringDiagrams.PiTwoFunctor`) together with 2-isomorphisms
  `k_λ : q_{ℝλ} ≅ ℝ q_λ` compatible with the half-braidings `γ` of Definition 6.14(i): for every
  1-morphism `F : λ → μ`,
  `ℝγ_F ∘ c ∘ (ℝF) k_μ = c ∘ k_λ (ℝF) ∘ γ_{ℝF}` in `Hom(q_{ℝμ} ℝF, ℝ(F q_λ))`
  (`QPiTwoFunctor.γ_comm`, the analogue for `(q, γ)` of the first axiom of Definition 5.2(ii)).
* A **`(Q, Π)`-2-natural transformation** `(X, x) : ℝ ⇒ 𝕊` (`QPiTwoFunctor.IsQPiTwoNatural`) is a
  Π-2-natural transformation (Definition 5.2(iii)) with
  `x_{q_λ} ∘ X_λ k ∘ γ_{X_λ} = k X_λ` in `Hom(q_{𝕊λ} X_λ, X_λ (ℝ q_λ))` (the analogue for
  `(q, γ, k)` of the axiom of Definition 5.2(iii), and the 2-categorical form of the condition
  `xQ ∘ γ_F = γ_G ∘ Q'x` of Definition 6.12(iii)).

These are the minimal conditions for the analogue of Theorem 5.5
(`StringDiagrams.Super.QAssociatedTwoMap`, `StringDiagrams.Super.QAssociatedTwoNat`):

* `γ_comm` is satisfied by `𝔼 ℝ` for every graded 2-superfunctor `ℝ`
  (`TwoSuperfunctor.kγ_comm`), and it is used to show that the coherence maps `c` of `𝔻 ℝ` are
  natural with respect to the 2-morphisms `σ` of degree `-1`; so it is necessary for
  `𝔼 ∘ 𝔻 = 𝕀`.
* The **compatibility of `k` with `j`** (the 2-categorical form of the compatibility of `γ_F`
  with `β` adopted in Definition 6.12(ii)): `k` is Π-natural,
  `ℝβ_{q_λ} ∘ c ∘ (ℝq_λ) j ∘ k π_{ℝλ} = c ∘ (ℝπ_λ) k ∘ j q_{ℝλ} ∘ β_{q_{ℝλ}}`
  (`QPiTwoFunctor.j_comm`). Unlike Definition 6.12(ii), this need not be imposed: it follows
  from the first axiom of Definition 5.2(ii) at `F = q_λ` and the naturality of `β`, because
  `β` is a half-braiding defined on all 1-morphisms, including `q_λ`. It is what makes the
  functors `ℋom(λ, μ) → ℋom(ℝλ, ℝμ)` into `(Q, Π)`-functors in the adopted sense
  (`QPiTwoFunctor.homQPi`, with `γ = c ∘ (ℝG) k`), which is used for the naturality of
  `γ̂` with respect to odd 2-morphisms in `𝔻 ℝ`.
* No compatibility of `k` with `ii`, `jj` is imposed (as in Definition 6.12(ii), where `γ_F`
  is not required to be compatible with `ii`, `jj`): the orbit construction uses only `q`.
* The condition on `(X, x)` holds for `𝔼(X, x)` (`TwoNatTrans.isQPiTwoNatural`) and is what
  makes `𝔻(X, x)` supernatural with respect to the 2-morphisms `σ`.

`(Q, Π)`-2-natural transformations are closed under identities and vertical composition
(`QPiTwoFunctor.isQPiTwoNatural_id`, `QPiTwoFunctor.IsQPiTwoNatural.vcomp`).

## The 2-functor `𝔼`

For graded `(Q, Π)`-2-supercategories, the underlying `(Q, Π)`-2-category is
`GUnderlying2 R 𝔄` (`StringDiagrams.Super.QPiTwoCategory`). A graded 2-superfunctor `ℝ`
restricts to the 2-morphisms of degree zero (`TwoSuperfunctor.toDegreeZero2`), and `𝔼 ℝ` is the
Π-2-functor `E₂` of (5.4) of this restriction together with
`k := (ℝσ_λ)⁻¹ ∘ i ∘ σ_{ℝλ}` (`TwoSuperfunctor.kIso`, even of degree zero;
`TwoSuperfunctor.toQPiTwoFunctor`). A graded 2-natural transformation restricts likewise
(`TwoNatTrans.toDegreeZero2`), and `𝔼 (X, x)` is `(Q, Π)`-2-natural
(`TwoNatTrans.isQPiTwoNatural`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Bicategory

universe w w₁ v₁ u₁ w₂ v₂ u₂

section Defs

variable (R : Type w) [CommRing R] {B : Type u₁} [Bicategory.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)] [PreadditiveBicategory B]
  [LinearBicategory R B] [QPiTwoCategory R B]
  {C : Type u₂} [Bicategory.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)] [PreadditiveBicategory C]
  [LinearBicategory R C] [QPiTwoCategory R C]

/-- A `(Q, Π)`-2-functor (a definition not given in the paper; see the module documentation):
a Π-2-functor `(ℝ, j)` (Definition 5.2(ii)) with 2-isomorphisms `k_λ : q_{ℝλ} ≅ ℝ q_λ` such that
`ℝγ_F ∘ c ∘ (ℝF) k_μ = c ∘ k_λ (ℝF) ∘ γ_{ℝF}`. Here `c` is the inverse of Mathlib's `mapComp`. -/
structure QPiTwoFunctor (F : Pseudofunctor B C) extends PiTwoFunctor R F where
  /-- The coherence 2-isomorphisms `k_λ : q_{ℝλ} ≅ ℝ q_λ`. -/
  k (a : B) : QPiTwoCategory.q (R := R) (F.obj a) ≅ F.map (QPiTwoCategory.q (R := R) a)
  /-- The compatibility of `k` with the half-braidings `γ`. -/
  γ_comm {a b : B} (f : a ⟶ b) :
    F.map f ◁ (k b).hom ≫ (F.mapComp f (QPiTwoCategory.q (R := R) b)).inv ≫
        F.map₂ (QPiTwoCategory.γ (R := R) f).hom =
      (QPiTwoCategory.γ (R := R) (F.map f)).hom ≫ (k a).hom ▷ F.map f ≫
        (F.mapComp (QPiTwoCategory.q (R := R) a) f).inv

variable {R}

/-- A `(Q, Π)`-2-natural transformation (a definition not given in the paper; see the module
documentation): a Π-2-natural transformation `(X, x)` (Definition 5.2(iii)) with
`x_{q_λ} ∘ X_λ k ∘ γ_{X_λ} = k X_λ`. -/
def QPiTwoFunctor.IsQPiTwoNatural {F G : Pseudofunctor B C} (hF : QPiTwoFunctor R F)
    (hG : QPiTwoFunctor R G) (η : Oplax.OplaxTrans F.toOplax G.toOplax) : Prop :=
  hF.toPiTwoFunctor.IsPiTwoNatural hG.toPiTwoFunctor η ∧
    ∀ a : B, (QPiTwoCategory.γ (R := R) (η.app a)).hom ≫ (hF.k a).hom ▷ η.app a ≫
      η.naturality (QPiTwoCategory.q (R := R) a) = η.app a ◁ (hG.k a).hom

end Defs

namespace QPiTwoFunctor

variable {R : Type w} [CommRing R] {B : Type u₁} [Bicategory.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)] [PreadditiveBicategory B]
  [LinearBicategory R B] [QPiTwoCategory R B]
  {C : Type u₂} [Bicategory.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)] [PreadditiveBicategory C]
  [LinearBicategory R C] [QPiTwoCategory R C]

open PiTwoCategory QPiTwoCategory

local notation "𝛑" => PiTwoCategory.pi (R := R)
local notation "𝛃" => PiTwoCategory.β (R := R)
local notation "𝐪" => QPiTwoCategory.q (R := R)
local notation "𝛄" => QPiTwoCategory.γ (R := R)

section Functor

variable {F : Pseudofunctor B C} (hF : QPiTwoFunctor R F)

/-- **The compatibility of `k` with `j`** (the 2-categorical form of the compatibility of `γ_F`
with `β` in the adopted Definition 6.12(ii)): `k` is Π-natural,
`ℝβ_{q_λ} ∘ c ∘ (ℝq_λ) j ∘ k π_{ℝλ} = c ∘ (ℝπ_λ) k ∘ j q_{ℝλ} ∘ β_{q_{ℝλ}}`. It follows from
the first axiom of Definition 5.2(ii) at `F = q_λ` and the naturality of `β`. -/
theorem j_comm (a : B) :
    (𝛃 (𝐪 (F.obj a))).hom ≫ (hF.j a).hom ▷ 𝐪 (F.obj a) ≫ F.map (𝛑 a) ◁ (hF.k a).hom ≫
        (F.mapComp (𝛑 a) (𝐪 a)).inv =
      (hF.k a).hom ▷ 𝛑 (F.obj a) ≫ F.map (𝐪 a) ◁ (hF.j a).hom ≫
        (F.mapComp (𝐪 a) (𝛑 a)).inv ≫ F.map₂ (𝛃 (𝐪 a)).hom := by
  rw [hF.β_comm (𝐪 a), ← reassoc_of% (β_naturality (R := R) (hF.k a).hom), whisker_exchange_assoc]

/-- The isomorphism `c ∘ (ℝG) k : (ℝG) q_{ℝμ} ≅ ℝ(G q_μ)`: the `γ` of `ℝ` on a hom category. -/
def γHom {a b : B} (g : a ⟶ b) : F.map g ≫ 𝐪 (F.obj b) ≅ F.map (g ≫ 𝐪 b) :=
  whiskerLeftIso (F.map g) (hF.k b) ≪≫ (F.mapComp g (𝐪 b)).symm

theorem γHom_hom {a b : B} (g : a ⟶ b) :
    (hF.γHom g).hom = F.map g ◁ (hF.k b).hom ≫ (F.mapComp g (𝐪 b)).inv := rfl

theorem γHom_inv {a b : B} (g : a ⟶ b) :
    (hF.γHom g).inv = (F.mapComp g (𝐪 b)).hom ≫ F.map g ◁ (hF.k b).inv := by
  simp [γHom]

@[reassoc]
theorem γHom_naturality {a b : B} {g g' : a ⟶ b} (η : g ⟶ g') :
    F.map₂ η ▷ 𝐪 (F.obj b) ≫ (hF.γHom g').hom = (hF.γHom g).hom ≫ F.map₂ (η ▷ 𝐪 b) := by
  rw [γHom_hom, γHom_hom, ← whisker_exchange_assoc]
  simp

/-- The compatibility of `γHom` with the Π-functor structure `βHom` of `ℝ` on a hom category
(from `j_comm`). -/
theorem γHom_comm {a b : B} (g : a ⟶ b) :
    (QPiTwoCategory.βQHom (R := R) (F.map g)).hom ≫ (hF.βHom g).hom ▷ 𝐪 (F.obj b) ≫
        (hF.γHom (g ≫ 𝛑 b)).hom =
      (hF.γHom g).hom ▷ 𝛑 (F.obj b) ≫ (hF.βHom (g ≫ 𝐪 b)).hom ≫
        F.map₂ (QPiTwoCategory.βQHom (R := R) g).hom := by
  have hj := hF.j_comm b
  rw [QPiTwoCategory.βQHom_hom, QPiTwoCategory.βQHom_hom, PiTwoFunctor.βHom_hom, PiTwoFunctor.βHom_hom, γHom_hom,
    γHom_hom, F.map₂_comp, F.map₂_comp, Pseudofunctor.map₂_associator,
    Pseudofunctor.map₂_whisker_left, Pseudofunctor.map₂_associator_inv']
  simp only [Bicategory.comp_whiskerRight, Category.assoc, Iso.inv_hom_id_assoc]
  have hj' : (hF.k b).hom ▷ 𝛑 (F.obj b) ≫ F.map (𝐪 b) ◁ (hF.j b).hom ≫
      (F.mapComp (𝐪 b) (𝛑 b)).inv ≫ F.map₂ (𝛃 (𝐪 b)).hom ≫ (F.mapComp (𝛑 b) (𝐪 b)).hom =
      (𝛃 (𝐪 (F.obj b))).hom ≫ (hF.j b).hom ▷ 𝐪 (F.obj b) ≫ F.map (𝛑 b) ◁ (hF.k b).hom := by
    rw [← cancel_mono (F.mapComp (𝛑 b) (𝐪 b)).inv]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact hj.symm
  rw [← whisker_exchange_assoc (F.mapComp g (𝛑 b)).inv (hF.k b).hom,
    ← whisker_exchange_assoc (F.mapComp g (𝐪 b)).inv (hF.j b).hom,
    Bicategory.inv_hom_whiskerRight_assoc]
  calc _ = (α_ (F.map g) (𝐪 (F.obj b)) (𝛑 (F.obj b))).hom ≫
        F.map g ◁ ((𝛃 (𝐪 (F.obj b))).hom ≫ (hF.j b).hom ▷ 𝐪 (F.obj b) ≫
          F.map (𝛑 b) ◁ (hF.k b).hom) ≫ (α_ (F.map g) (F.map (𝛑 b)) (F.map (𝐪 b))).inv ≫
        (F.mapComp g (𝛑 b)).inv ▷ F.map (𝐪 b) ≫ (F.mapComp (g ≫ 𝛑 b) (𝐪 b)).inv := by
        bicategory
    _ = (α_ (F.map g) (𝐪 (F.obj b)) (𝛑 (F.obj b))).hom ≫
        F.map g ◁ ((hF.k b).hom ▷ 𝛑 (F.obj b) ≫ F.map (𝐪 b) ◁ (hF.j b).hom ≫
          (F.mapComp (𝐪 b) (𝛑 b)).inv ≫ F.map₂ (𝛃 (𝐪 b)).hom ≫ (F.mapComp (𝛑 b) (𝐪 b)).hom) ≫
        (α_ (F.map g) (F.map (𝛑 b)) (F.map (𝐪 b))).inv ≫
        (F.mapComp g (𝛑 b)).inv ▷ F.map (𝐪 b) ≫ (F.mapComp (g ≫ 𝛑 b) (𝐪 b)).inv := by
        rw [hj']
    _ = _ := by bicategory

variable (R) in
/-- **The hom functors of a `(Q, Π)`-2-functor are `(Q, Π)`-functors** in the adopted sense of
Definition 6.12(ii) (for the `(Q, Π)`-categories `ℋom(λ, μ)` of
`QPiTwoCategory.homQPiCategory`): `β = c ∘ (ℝG) j` (`PiTwoFunctor.homPi`), `γ = c ∘ (ℝG) k`,
and the compatibility of `γ` with `β` is `γHom_comm`, a consequence of `j_comm`. -/
def homQPi (a b : B) : QPiFunctor R (hF.toPiTwoFunctor.homFunctor a b) where
  toPiFunctor := hF.toPiTwoFunctor.homPi R a b
  γ := NatIso.ofComponents (fun g => hF.γHom g) fun η => hF.γHom_naturality η
  isCompatible := by
    rw [QPiFunctorData.IsCompatible.iff]
    intro g
    exact hF.γHom_comm g

@[simp] theorem homQPi_γ_hom_app {a b : B} (g : a ⟶ b) :
    (hF.homQPi R a b).γ.hom.app g = (hF.γHom g).hom := rfl

@[simp] theorem homQPi_γ_inv_app {a b : B} (g : a ⟶ b) :
    (hF.homQPi R a b).γ.inv.app g = (hF.γHom g).inv := rfl

end Functor

/-! ### Identities and vertical composition of `(Q, Π)`-2-natural transformations -/

section Nat

variable {F G H : Pseudofunctor B C} {hF : QPiTwoFunctor R F} {hG : QPiTwoFunctor R G}
  {hH : QPiTwoFunctor R H}

/-- The identity oplax transformation is `(Q, Π)`-2-natural. -/
theorem isQPiTwoNatural_id (hF : QPiTwoFunctor R F) :
    hF.IsQPiTwoNatural hF (Oplax.OplaxTrans.id F.toOplax) :=
  ⟨PiTwoFunctor.isPiTwoNatural_id hF.toPiTwoFunctor, fun a => by
    simp only [Oplax.OplaxTrans.id, γ_id, Pseudofunctor.toOplax_toPrelaxFunctor]
    bicategory⟩

/-- The vertical composite of `(Q, Π)`-2-natural transformations is `(Q, Π)`-2-natural. -/
theorem IsQPiTwoNatural.vcomp {η : Oplax.OplaxTrans F.toOplax G.toOplax}
    {θ : Oplax.OplaxTrans G.toOplax H.toOplax} (hη : hF.IsQPiTwoNatural hG η)
    (hθ : hG.IsQPiTwoNatural hH θ) : hF.IsQPiTwoNatural hH (Oplax.OplaxTrans.vcomp η θ) :=
  ⟨hη.1.vcomp hθ.1, fun a => by
    simp only [Oplax.OplaxTrans.vcomp, γ_comp, Pseudofunctor.toOplax_toPrelaxFunctor,
      Category.assoc]
    have c1 : (α_ (η.app a) (θ.app a) (𝐪 (H.obj a))).hom ≫ η.app a ◁ (𝛄 (θ.app a)).hom ≫
        (α_ (η.app a) (𝐪 (G.obj a)) (θ.app a)).inv ≫ (𝛄 (η.app a)).hom ▷ θ.app a ≫
          (α_ (𝐪 (F.obj a)) (η.app a) (θ.app a)).hom ≫ (hF.k a).hom ▷ (η.app a ≫ θ.app a) ≫
            (α_ (F.map (𝐪 a)) (η.app a) (θ.app a)).inv ≫ η.naturality (𝐪 a) ▷ θ.app a ≫
              (α_ (η.app a) (G.map (𝐪 a)) (θ.app a)).hom ≫ η.app a ◁ θ.naturality (𝐪 a) ≫
                (α_ (η.app a) (θ.app a) (H.map (𝐪 a))).inv =
        (α_ (η.app a) (θ.app a) (𝐪 (H.obj a))).hom ≫ η.app a ◁ (𝛄 (θ.app a)).hom ≫
          (α_ (η.app a) (𝐪 (G.obj a)) (θ.app a)).inv ≫
            ((𝛄 (η.app a)).hom ≫ (hF.k a).hom ▷ η.app a ≫ η.naturality (𝐪 a)) ▷ θ.app a ≫
              (α_ (η.app a) (G.map (𝐪 a)) (θ.app a)).hom ≫ η.app a ◁ θ.naturality (𝐪 a) ≫
                (α_ (η.app a) (θ.app a) (H.map (𝐪 a))).inv := by
      bicategory
    rw [c1, hη.2 a]
    have c2 : (α_ (η.app a) (θ.app a) (𝐪 (H.obj a))).hom ≫ η.app a ◁ (𝛄 (θ.app a)).hom ≫
        (α_ (η.app a) (𝐪 (G.obj a)) (θ.app a)).inv ≫ (η.app a ◁ (hG.k a).hom) ▷ θ.app a ≫
          (α_ (η.app a) (G.map (𝐪 a)) (θ.app a)).hom ≫ η.app a ◁ θ.naturality (𝐪 a) ≫
            (α_ (η.app a) (θ.app a) (H.map (𝐪 a))).inv =
        (α_ (η.app a) (θ.app a) (𝐪 (H.obj a))).hom ≫
          η.app a ◁ ((𝛄 (θ.app a)).hom ≫ (hG.k a).hom ▷ θ.app a ≫ θ.naturality (𝐪 a)) ≫
            (α_ (η.app a) (θ.app a) (H.map (𝐪 a))).inv := by
      bicategory
    rw [c2, hθ.2 a]
    bicategory⟩

end Nat

end QPiTwoFunctor

/-! ## The 2-functor `𝔼` on graded 2-superfunctors and graded 2-natural transformations -/

namespace TwoSuperfunctor

open Supercategory GradedSupercategory BicategoryStruct TwoSupercategory

variable {R : Type w} [CommRing R] {A : Type u₁} [BicategoryStruct.{w₁, v₁} A]
  [∀ a b : A, Preadditive (a ⟶ b)] [∀ a b : A, Linear R (a ⟶ b)]
  [∀ a b : A, Supercategory R (a ⟶ b)] [∀ a b : A, GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R A] [GradedTwoSupercategory R A]
  {A' : Type u₂} [BicategoryStruct.{w₂, v₂} A']
  [∀ a b : A', Preadditive (a ⟶ b)] [∀ a b : A', Linear R (a ⟶ b)]
  [∀ a b : A', Supercategory R (a ⟶ b)] [∀ a b : A', GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R A'] [GradedTwoSupercategory R A']
  (F : TwoSuperfunctor R A A') (hF : F.IsGraded)

/-- The restriction of a graded 2-superfunctor to the 2-morphisms of degree zero. -/
@[simps]
def toDegreeZero2 : TwoSuperfunctor R (DegreeZero2 R A) (DegreeZero2 R A') where
  obj a := ⟨F.obj a.as⟩
  map f := ⟨F.map f.obj⟩
  map₂ η := ⟨F.map₂ η.1, hF.map₂_mem_degree η.2⟩
  map₂_id f := DegreeZero.hom_ext (F.map₂_id f.obj)
  map₂_comp η θ := DegreeZero.hom_ext (F.map₂_comp η.1 θ.1)
  map₂_add η θ := DegreeZero.hom_ext (F.map₂_add η.1 θ.1)
  map₂_smul r η := DegreeZero.hom_ext (F.map₂_smul r η.1)
  map₂_mem hη := F.map₂_mem (R := R) hη
  mapComp f g := DegreeZero.isoMk (F.mapComp f.obj g.obj) (hF.mapComp_hom_mem_degree _ _)
  mapId a := DegreeZero.isoMk (F.mapId a.as) (hF.mapId_hom_mem_degree _)
  mapComp_hom_mem f g := F.mapComp_hom_mem f.obj g.obj
  mapId_hom_mem a := F.mapId_hom_mem a.as
  mapComp_naturality_left η g := DegreeZero.hom_ext (F.mapComp_naturality_left η.1 g.obj)
  mapComp_naturality_right f _ _ η := DegreeZero.hom_ext (F.mapComp_naturality_right f.obj η.1)
  map₂_associator f g h := DegreeZero.hom_ext (F.map₂_associator f.obj g.obj h.obj)
  map₂_leftUnitor f := DegreeZero.hom_ext (F.map₂_leftUnitor f.obj)
  map₂_rightUnitor f := DegreeZero.hom_ext (F.map₂_rightUnitor f.obj)

variable [QPiTwoSupercategory R A] [QPiTwoSupercategory R A']

local notation "𝐪" => QPiTwoSupercategory.q (R := R)
local notation "𝛔" => QPiTwoSupercategory.σ (R := R)
local notation "𝛄" => QPiTwoSupercategory.γ (R := R)

/-- The coherence map `k := (ℝσ_λ)⁻¹ ∘ i ∘ σ_{ℝλ} : q_{ℝλ} ≅ ℝq_λ` of `𝔼 ℝ` (the analogue for `σ`
of the `j` of (5.4), `TwoSuperfunctor.jIso`). -/
def kIso (a : A) : 𝐪 (F.obj a) ≅ F.map (𝐪 a) :=
  𝛔 (F.obj a) ≪≫ F.mapId a ≪≫ F.map₂Iso (𝛔 a).symm

theorem kIso_hom (a : A) :
    (F.kIso a).hom = (𝛔 (F.obj a)).hom ≫ (F.mapId a).hom ≫ F.map₂ (𝛔 a).inv := rfl

theorem kIso_hom_mem (a : A) :
    (F.kIso a).hom ∈ parity (R := R) (𝐪 (F.obj a)) (F.map (𝐪 a)) 0 := by
  have := comp_mem (comp_mem (QPiTwoSupercategory.σ_hom_mem (R := R) (F.obj a))
    (F.mapId_hom_mem a)) (F.map₂_mem (QPiTwoSupercategory.σ_inv_mem (R := R) a))
  simpa [kIso_hom] using this

include hF in
theorem kIso_hom_mem_degree (a : A) :
    (F.kIso a).hom ∈ degree (R := R) (𝐪 (F.obj a)) (F.map (𝐪 a)) 0 := by
  have := comp_mem_degree (comp_mem_degree
    (QPiTwoSupercategory.σ_hom_mem_degree (R := R) (F.obj a)) (hF.mapId_hom_mem_degree a))
    (hF.map₂_mem_degree (QPiTwoSupercategory.σ_inv_mem_degree (R := R) a))
  simpa [kIso_hom] using this

/-- `ℝσ_λ ∘ k = i ∘ σ_{ℝλ}`: the defining property of `k`. -/
@[reassoc]
theorem kIso_hom_comp_map₂_σ (a : A) :
    (F.kIso a).hom ≫ F.map₂ (𝛔 a).hom = (𝛔 (F.obj a)).hom ≫ (F.mapId a).hom := by
  rw [kIso_hom, Category.assoc, Category.assoc, ← F.map₂_comp, Iso.inv_hom_id, F.map₂_id,
    Category.comp_id]

@[reassoc]
theorem mapId_hom_comp_map₂_σ_inv (a : A) :
    (F.mapId a).hom ≫ F.map₂ (𝛔 a).inv = (𝛔 (F.obj a)).inv ≫ (F.kIso a).hom := by
  rw [kIso_hom, Iso.inv_hom_id_assoc]

/-- The axiom `γ_comm` of a `(Q, Π)`-2-functor for `𝔼 ℝ` (the analogue of
`TwoSuperfunctor.jβ_comm`). -/
theorem kγ_comm {a b : A} (f : a ⟶ b) :
    F.map f ◁ (F.kIso b).hom ≫ (F.mapComp f (𝐪 b)).hom ≫ F.map₂ (𝛄 f).hom =
      (𝛄 (F.map f)).hom ≫ (F.kIso a).hom ▷ F.map f ≫ (F.mapComp (𝐪 a) f).hom := by
  have hl := F.map₂_leftUnitor f
  have hr := F.map₂_rightUnitor f
  rw [QPiTwoSupercategory.γ_hom, QPiTwoSupercategory.γ_hom, F.map₂_comp, F.map₂_comp,
    F.map₂_comp]
  rw [← reassoc_of% (F.mapComp_naturality_right f (𝛔 b).hom), ← whiskerLeft_comp'_assoc R,
    kIso_hom_comp_map₂_σ, whiskerLeft_comp'_assoc R]
  have e1 : F.map f ◁ (F.mapId b).hom ≫ (F.mapComp f (𝟙 b)).hom ≫
      F.map₂ (rightUnitor f).hom = (rightUnitor (F.map f)).hom := hr
  have e2' : (leftUnitor (F.map f)).hom ≫ F.map₂ (leftUnitor f).inv =
      (F.mapId a).hom ▷ F.map f ≫ (F.mapComp (𝟙 a) f).hom := by
    rw [← hl]
    simp only [Category.assoc]
    rw [← F.map₂_comp, Iso.hom_inv_id, F.map₂_id, Category.comp_id]
  have e2 : F.map₂ (leftUnitor f).inv = (leftUnitor (F.map f)).inv ≫
      (F.mapId a).hom ▷ F.map f ≫ (F.mapComp (𝟙 a) f).hom := by
    rw [← e2', Iso.inv_hom_id_assoc]
  rw [reassoc_of% e1, e2]
  simp only [Category.assoc]
  rw [← F.mapComp_naturality_left, ← comp_whiskerRight'_assoc R, mapId_hom_comp_map₂_σ_inv,
    comp_whiskerRight'_assoc R]

/-- **`𝔼` on 1-morphisms.** A graded 2-superfunctor `ℝ` between graded
`(Q, Π)`-2-supercategories gives a `(Q, Π)`-2-functor `𝔼 ℝ` between the underlying
`(Q, Π)`-2-categories: the Π-2-functor `E₂` of (5.4) of its restriction to degree zero, with
`k := (ℝσ)⁻¹ ∘ i ∘ σ`. -/
def toQPiTwoFunctor : QPiTwoFunctor R (F.toDegreeZero2 hF).toPseudofunctor where
  toPiTwoFunctor := (F.toDegreeZero2 hF).toPiTwoFunctor
  k a := GUnderlying2.isoU (F.kIso a.obj.as) (F.kIso_hom_mem _) (F.kIso_hom_mem_degree hF _)
  γ_comm f := Subtype.ext (DegreeZero.hom_ext (F.kγ_comm f.obj.obj))

@[simp] theorem toQPiTwoFunctor_k_hom_val (a : GUnderlying2 R A) :
    ((F.toQPiTwoFunctor hF).k a).hom.1.1 = (F.kIso a.obj.as).hom := rfl

@[simp] theorem toQPiTwoFunctor_j_hom_val (a : GUnderlying2 R A) :
    ((F.toQPiTwoFunctor hF).j a).hom.1.1 = (F.jIso a.obj.as).hom := rfl

end TwoSuperfunctor

namespace TwoNatTrans

open Supercategory GradedSupercategory BicategoryStruct TwoSupercategory

variable {R : Type w} [CommRing R] {A : Type u₁} [BicategoryStruct.{w₁, v₁} A]
  [∀ a b : A, Preadditive (a ⟶ b)] [∀ a b : A, Linear R (a ⟶ b)]
  [∀ a b : A, Supercategory R (a ⟶ b)] [∀ a b : A, GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R A] [GradedTwoSupercategory R A]
  {A' : Type u₂} [BicategoryStruct.{w₂, v₂} A']
  [∀ a b : A', Preadditive (a ⟶ b)] [∀ a b : A', Linear R (a ⟶ b)]
  [∀ a b : A', Supercategory R (a ⟶ b)] [∀ a b : A', GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R A'] [GradedTwoSupercategory R A']
  {F G : TwoSuperfunctor R A A'} (hF : F.IsGraded) (hG : G.IsGraded) (θ : TwoNatTrans F G)
  (hθ : θ.IsGraded)

/-- The restriction of a graded 2-natural transformation to the 2-morphisms of degree zero. -/
@[simps]
def toDegreeZero2 : TwoNatTrans (F.toDegreeZero2 hF) (G.toDegreeZero2 hG) where
  X a := ⟨θ.X a.as⟩
  x f := ⟨θ.x f.obj, hθ f.obj⟩
  x_mem f := θ.x_mem f.obj
  naturality η := DegreeZero.hom_ext (θ.naturality η.1)
  x_comp f g := DegreeZero.hom_ext (θ.x_comp f.obj g.obj)
  x_id a := DegreeZero.hom_ext (θ.x_id a.as)

variable [QPiTwoSupercategory R A] [QPiTwoSupercategory R A']

local notation "𝐪" => QPiTwoSupercategory.q (R := R)
local notation "𝛔" => QPiTwoSupercategory.σ (R := R)
local notation "𝛄" => QPiTwoSupercategory.γ (R := R)

/-- The `(Q, Π)`-2-naturality condition `x_{q_λ} ∘ X_λ k ∘ γ_{X_λ} = k X_λ` for `𝔼(X, x)` (the
analogue for `σ` of `TwoNatTrans.isPiTwoNatural`). -/
theorem kNat (a : A) :
    (𝛄 (θ.X a)).hom ≫ (F.kIso a).hom ▷ θ.X a ≫ θ.x (𝐪 a) = θ.X a ◁ (G.kIso a).hom := by
  have hn := θ.naturality (𝛔 a).inv
  have hid := θ.x_id a
  rw [TwoSuperfunctor.kIso_hom, comp_whiskerRight'_assoc R, comp_whiskerRight'_assoc R, hn,
    QPiTwoSupercategory.γ_hom_comp_σ_assoc]
  rw [reassoc_of% hid, TwoSuperfunctor.kIso_hom, whiskerLeft_comp' R, whiskerLeft_comp' R]

/-- **`𝔼` on 2-morphisms.** For a graded 2-natural transformation `(X, x)` between graded
2-superfunctors of graded `(Q, Π)`-2-supercategories, `𝔼(X, x)` (the oplax transformation of
(5.6) of its restriction to degree zero) is `(Q, Π)`-2-natural. -/
theorem isQPiTwoNatural :
    (F.toQPiTwoFunctor hF).IsQPiTwoNatural (G.toQPiTwoFunctor hG)
      (θ.toDegreeZero2 hF hG hθ).toOplaxTrans :=
  ⟨(θ.toDegreeZero2 hF hG hθ).isPiTwoNatural, fun a =>
    Subtype.ext (DegreeZero.hom_ext (θ.kNat a.obj.as))⟩

end TwoNatTrans

end StringDiagrams

end
