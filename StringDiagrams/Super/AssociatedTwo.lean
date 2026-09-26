import StringDiagrams.Super.PiTwoCategory
import StringDiagrams.Super.MonoidalAssociated

/-!
# The Π-2-supercategory associated to a Π-2-category (the functor `D₂` on objects)

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, (5.5).

Let `(𝔄, π, β, ξ)` be a Π-2-category (`StringDiagrams.PiTwoCategory`, Definition 5.2(i)). Its
hom categories are Π-categories (`PiTwoCategory.homPiCategory`), and the associated
2-supercategory `𝔄̂` (`StringDiagrams.Associated2 R 𝔄`) has:

* the objects and 1-morphisms of `𝔄`, and the associated supercategories
  `ℋom_𝔄(λ, μ)^` (`StringDiagrams.Associated`) as morphism supercategories: an even 2-morphism
  `F ⇒ G` is a 2-morphism `F ⇒ G` of `𝔄`, an odd one is a 2-morphism `F ⇒ π_μ G`;
* horizontal composition with a 1-morphism given by `D₁` of the Π-functors `F ≫ -`
  (`PiTwoCategory.precompPi`, `β = a`) and `- ≫ H` (`PiTwoCategory.postcompPi`,
  `β = a⁻¹ ∘ (F β_H) ∘ a`; the Π-functor axiom is the last axiom of Definition 5.2(i));
* the coherence maps of `𝔄`, viewed as even 2-isomorphisms.

The axioms of a 2-supercategory (`Associated2.twoSupercategory`) reduce, via the Π-naturality of
the coherence maps (`Associated2.lNat_isPiNatural`, …, which use (i) and (ii) of
Definition 5.2(i)), to the functoriality of `D₁` and the super interchange law
(`Associated2.super_interchange'`, which uses `β_π = -1`). `𝔄̂` is a Π-2-supercategory with
`π̂ = π` and `ζ_λ = λ⁻¹_{π_λ}` viewed as an odd 2-morphism `π_λ ⇒ 1_λ`
(`Associated2.instPiTwoSupercategory`), and the `β` and `ξ` of Lemma 3.2 for `𝔄̂` are those of `𝔄`
(`Associated2.β_hom_eq`, `Associated2.ξ_hom_eq`; part of `E₂ ∘ D₂ = I` in Lemma 5.4).

## Sign corrections

As in `StringDiagrams.Super.Associated` (the erratum to Lemma 5.1), the vertical composite of two
odd 2-morphisms `x̂ : F ⇒ G`, `ŷ : G ⇒ H` is `-ξ_μ H ∘ π_μ y ∘ x` (`Associated2.comp₂_fst`), not
`ξ_μ H ∘ π_μ y ∘ x` as used in the proof of Lemma 5.4. Correspondingly, the horizontal composite
of two odd 2-morphisms is `+ξ_ν KH ∘ π_ν (β_{ν,μ})⁻¹_K H ∘ yx` (`Associated2.hcomp_odd_odd`),
not `-ξ_ν KH ∘ π_ν (β_{ν,μ})⁻¹_K H ∘ yx` as printed in (5.5). Both printed signs are those of
the construction applied to `(𝔄, π, β, -ξ)`, which is again a Π-2-category; with them, the
isomorphism `ξ̂ = ζ̂ζ̂` of `𝔄̂` would be `-ξ` rather than `ξ`, and `𝕋_𝔄` of Lemma 5.4 would
not be a 2-superfunctor.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Bicategory Supercategory

universe w w₁ v₁ u₁ w₂ v₂ u₂

/-! ## Whiskering functors of a Π-2-category are Π-functors -/

namespace PiTwoCategory

variable {R : Type w} [CommRing R] {B : Type u₁} [Bicategory.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)] [PreadditiveBicategory B]
  [LinearBicategory R B] [PiTwoCategory R B]

local notation "𝛑" => PiTwoCategory.pi (R := R)
local notation "𝛃" => PiTwoCategory.β (R := R)
local notation "𝛏" => PiTwoCategory.ξ (R := R)

/-- The Π-functor axiom for `F ≫ -` (a coherence statement). -/
theorem precomp_comm {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    (ξHom (R := R) (f ≫ g)).hom ≫ f ◁ (ξHom (R := R) g).inv =
      (α_ f g (𝛑 c)).hom ▷ 𝛑 c ≫ (α_ f (g ≫ 𝛑 c) (𝛑 c)).hom := by
  have key : (ξHom (R := R) (f ≫ g)).hom ≫ f ◁ (ξHom (R := R) g).inv =
      (α_ (f ≫ g) (𝛑 c) (𝛑 c)).hom ≫ (α_ f g (𝛑 c ≫ 𝛑 c)).hom ≫
        f ◁ g ◁ ((𝛏 c).hom ≫ (𝛏 c).inv) ≫ f ◁ (α_ g (𝛑 c) (𝛑 c)).inv := by
    rw [ξHom_hom, ξHom_inv]; bicategory
  rw [key, Iso.hom_inv_id]
  bicategory

variable (R) in
/-- `F ≫ -` is a Π-functor with `β := a`. -/
def precompPi (c : B) {a b : B} (f : a ⟶ b) : PiFunctor R (precomp c f) where
  β := NatIso.ofComponents (fun g => α_ f g (𝛑 c)) fun η => by
    simp [associator_naturality_middle]
  comm g := precomp_comm f g

@[simp] theorem precompPi_β_hom_app (c : B) {a b : B} (f : a ⟶ b) (g : b ⟶ c) :
    (precompPi R c f).β.hom.app g = (α_ f g (𝛑 c)).hom := rfl

@[simp] theorem precompPi_β_inv_app (c : B) {a b : B} (f : a ⟶ b) (g : b ⟶ c) :
    (precompPi R c f).β.inv.app g = (α_ f g (𝛑 c)).inv := rfl

/-- The isomorphism `(F ≫ H) ≫ π ≅ (F ≫ π) ≫ H` built from `β_H`: the structure making `- ≫ H`
a Π-functor. -/
def βR {a b c : B} (f : a ⟶ b) (h : b ⟶ c) : (f ≫ h) ≫ 𝛑 c ≅ (f ≫ 𝛑 b) ≫ h :=
  α_ f h (𝛑 c) ≪≫ whiskerLeftIso f (𝛃 h) ≪≫ (α_ f (𝛑 b) h).symm

theorem βR_hom {a b c : B} (f : a ⟶ b) (h : b ⟶ c) :
    (βR (R := R) f h).hom = (α_ f h (𝛑 c)).hom ≫ f ◁ (𝛃 h).hom ≫ (α_ f (𝛑 b) h).inv := rfl

theorem βR_inv {a b c : B} (f : a ⟶ b) (h : b ⟶ c) :
    (βR (R := R) f h).inv = (α_ f (𝛑 b) h).hom ≫ f ◁ (𝛃 h).inv ≫ (α_ f h (𝛑 c)).inv := by
  simp [βR]

@[reassoc]
theorem βR_naturality {a b c : B} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    η ▷ h ▷ 𝛑 c ≫ (βR (R := R) g h).hom = (βR (R := R) f h).hom ≫ η ▷ 𝛑 b ▷ h := by
  simp only [βR_hom, Category.assoc]
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc,
    associator_inv_naturality_left]

/-- `β_{H ≫ π} = -(a⁻¹ ∘ (β_H ⊗ 1))`, from Lemma 3.2(i) and `β_π = -1`. -/
theorem β_pi_comp_hom {b c : B} (h : b ⟶ c) :
    (𝛃 (h ≫ 𝛑 c)).hom = -((𝛃 h).hom ▷ 𝛑 c ≫ (α_ (𝛑 b) h (𝛑 c)).hom) := by
  rw [β_comp, β_pi, PreadditiveBicategory.whiskerLeft_neg, Bicategory.whiskerLeft_id]
  simp

theorem β_pi_comp_inv {b c : B} (h : b ⟶ c) :
    (𝛃 (h ≫ 𝛑 c)).inv = -((α_ (𝛑 b) h (𝛑 c)).inv ≫ (𝛃 h).inv ▷ 𝛑 c) := by
  rw [← cancel_epi (𝛃 (h ≫ 𝛑 c)).hom, Iso.hom_inv_id, β_pi_comp_hom]
  simp

/-- `βR` is natural in the second variable (by the naturality of `β`). -/
@[reassoc]
theorem βR_inv_naturality_right {a b c : B} (f : a ⟶ b) {h i : b ⟶ c} (θ : h ⟶ i) :
    (f ≫ 𝛑 b) ◁ θ ≫ (βR (R := R) f i).inv = (βR (R := R) f h).inv ≫ (f ◁ θ) ▷ 𝛑 c := by
  simp only [βR_inv, Category.assoc]
  rw [associator_naturality_right_assoc, ← Bicategory.whiskerLeft_comp_assoc,
    β_inv_naturality, Bicategory.whiskerLeft_comp_assoc, associator_inv_naturality_middle]

/-- The Π-functor axiom for `- ≫ H`: `ξ_{π_c} ... = ...`, from the last axiom of
Definition 5.2(i). -/
theorem βR_comm {a b c : B} (f : a ⟶ b) (h : b ⟶ c) :
    (ξHom (R := R) (f ≫ h)).hom ≫ (ξHom (R := R) f).inv ▷ h =
      (βR (R := R) f h).hom ▷ 𝛑 c ≫ (βR (R := R) (f ≫ 𝛑 b) h).hom := by
  have hc := ξ_comm (R := R) h
  have key : (ξHom (R := R) (f ≫ h)).hom ≫ (ξHom (R := R) f).inv ▷ h =
      (α_ (f ≫ h) (𝛑 c) (𝛑 c)).hom ≫ (α_ f h (𝛑 c ≫ 𝛑 c)).hom ≫
        f ◁ (h ◁ (𝛏 c).hom ≫ (ρ_ h).hom ≫ (λ_ h).inv ≫ (𝛏 b).inv ▷ h) ≫
          (α_ f (𝛑 b ≫ 𝛑 b) h).inv ≫ (α_ f (𝛑 b) (𝛑 b)).inv ▷ h := by
    rw [ξHom_hom, ξHom_inv]; bicategory
  rw [key, hc, βR_hom, βR_hom]
  bicategory

variable (R) in
/-- `- ≫ H` is a Π-functor with `β := a⁻¹ ∘ (F β_H) ∘ a`. -/
def postcompPi (a : B) {b c : B} (h : b ⟶ c) : PiFunctor R (postcomp a h) where
  β := NatIso.ofComponents (fun f => βR (R := R) f h) fun η => βR_naturality η h
  comm f := βR_comm f h

@[simp] theorem postcompPi_β_hom_app (a : B) {b c : B} (h : b ⟶ c) (f : a ⟶ b) :
    (postcompPi R a h).β.hom.app f = (βR (R := R) f h).hom := rfl

@[simp] theorem postcompPi_β_inv_app (a : B) {b c : B} (h : b ⟶ c) (f : a ⟶ b) :
    (postcompPi R a h).β.inv.app f = (βR (R := R) f h).inv := rfl

end PiTwoCategory

/-! ## The associated 2-supercategory -/

/-- The objects of the 2-supercategory `𝔄̂` associated to a Π-2-category `𝔄` (Brundan–Ellis,
(5.5)): the objects of `𝔄`. -/
@[ext]
structure Associated2 (R : Type w) (B : Type u₁) where
  /-- The object of `𝔄`. -/
  obj : B

namespace Associated2

open PiTwoCategory

variable {R : Type w} [CommRing R] {B : Type u₁} [Bicategory.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)] [PreadditiveBicategory B]
  [LinearBicategory R B] [PiTwoCategory R B]

local notation "𝛑" => PiTwoCategory.pi (R := R)
local notation "𝛃" => PiTwoCategory.β (R := R)
local notation "𝛏" => PiTwoCategory.ξ (R := R)

/-- The bicategory data of `𝔄̂` (Brundan–Ellis, (5.5)): the morphism supercategories are the
associated supercategories `ℋom_𝔄(λ, μ)^` of the morphism Π-categories; horizontal composition
with a 1-morphism is `D₁` of the Π-functors `F ≫ -` and `- ≫ H`; the coherence maps are those of
`𝔄`, viewed as even 2-isomorphisms. -/
instance instBicategoryStruct : BicategoryStruct (Associated2 R B) where
  Hom a b := Associated R (a.obj ⟶ b.obj)
  id a := ⟨𝟙 a.obj⟩
  comp f g := ⟨f.obj ≫ g.obj⟩
  homCategory _ _ := inferInstance
  whiskerLeft f _ _ η := (Associated.map (precompPi R _ f.obj)).map η
  whiskerRight η h := (Associated.map (postcompPi R _ h.obj)).map η
  associator f g h := Associated.evenIso (α_ f.obj g.obj h.obj)
  leftUnitor f := Associated.evenIso (λ_ f.obj)
  rightUnitor f := Associated.evenIso (ρ_ f.obj)

instance (a b : Associated2 R B) : Preadditive (a ⟶ b) :=
  inferInstanceAs (Preadditive (Associated R (a.obj ⟶ b.obj)))

instance (a b : Associated2 R B) : Linear R (a ⟶ b) :=
  inferInstanceAs (Linear R (Associated R (a.obj ⟶ b.obj)))

instance (a b : Associated2 R B) : Supercategory R (a ⟶ b) :=
  inferInstanceAs (Supercategory R (Associated R (a.obj ⟶ b.obj)))

open BicategoryStruct

variable {a b c d : Associated2 R B}

@[simp] theorem id_obj (a : Associated2 R B) : (𝟙 a : a ⟶ a).obj = 𝟙 a.obj := rfl

@[ext] theorem hom₂_ext {f g : a ⟶ b} {η θ : f ⟶ g} (h₁ : η.1 = θ.1) (h₂ : η.2 = θ.2) :
    η = θ :=
  Prod.ext h₁ h₂

@[simp] theorem comp₂_fst {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) :
    (η ≫ θ).1 = η.1 ≫ θ.1 - η.2 ≫ θ.2 ▷ 𝛑 b.obj ≫ (ξHom (R := R) h.obj).hom := rfl

@[simp] theorem comp₂_snd {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) :
    (η ≫ θ).2 = η.1 ≫ θ.2 + η.2 ≫ (PiCategory.pi (R := R)).map θ.1 := rfl

@[simp] theorem id₂_fst (f : a ⟶ b) : (𝟙 f : f ⟶ f).1 = 𝟙 f.obj := rfl

@[simp] theorem id₂_snd (f : a ⟶ b) : (𝟙 f : f ⟶ f).2 = 0 := rfl

@[simp] theorem add₂_fst {f g : a ⟶ b} (η θ : f ⟶ g) : (η + θ).1 = η.1 + θ.1 := rfl

@[simp] theorem add₂_snd {f g : a ⟶ b} (η θ : f ⟶ g) : (η + θ).2 = η.2 + θ.2 := rfl

@[simp] theorem neg₂_fst {f g : a ⟶ b} (η : f ⟶ g) : (-η).1 = -η.1 := rfl

@[simp] theorem neg₂_snd {f g : a ⟶ b} (η : f ⟶ g) : (-η).2 = -η.2 := rfl

@[simp] theorem zero₂_fst {f g : a ⟶ b} : (0 : f ⟶ g).1 = 0 := rfl

@[simp] theorem zero₂_snd {f g : a ⟶ b} : (0 : f ⟶ g).2 = 0 := rfl

@[simp] theorem smul₂_fst {f g : a ⟶ b} (r : R) (η : f ⟶ g) : (r • η).1 = r • η.1 := rfl

@[simp] theorem smul₂_snd {f g : a ⟶ b} (r : R) (η : f ⟶ g) : (r • η).2 = r • η.2 := rfl

@[simp] theorem comp_obj (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).obj = f.obj ≫ g.obj := rfl

@[simp] theorem whiskerLeft_fst (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    (f ◁ η).1 = f.obj ◁ η.1 := rfl

@[simp] theorem whiskerLeft_snd (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    (f ◁ η).2 = f.obj ◁ η.2 ≫ (α_ f.obj h.obj (𝛑 c.obj)).inv := rfl

@[simp] theorem whiskerRight_fst {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    (η ▷ h).1 = η.1 ▷ h.obj := rfl

@[simp] theorem whiskerRight_snd {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    (η ▷ h).2 = η.2 ▷ h.obj ≫ (βR (R := R) g.obj h.obj).inv := rfl

@[simp] theorem associator_hom_fst (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (associator f g h).hom.1 = (α_ f.obj g.obj h.obj).hom := rfl

@[simp] theorem associator_hom_snd (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (associator f g h).hom.2 = 0 := rfl

@[simp] theorem associator_inv_fst (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (associator f g h).inv.1 = (α_ f.obj g.obj h.obj).inv := rfl

@[simp] theorem associator_inv_snd (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (associator f g h).inv.2 = 0 := rfl

@[simp] theorem leftUnitor_hom_fst (f : a ⟶ b) : (leftUnitor f).hom.1 = (λ_ f.obj).hom := rfl

@[simp] theorem leftUnitor_hom_snd (f : a ⟶ b) : (leftUnitor f).hom.2 = 0 := rfl

@[simp] theorem leftUnitor_inv_fst (f : a ⟶ b) : (leftUnitor f).inv.1 = (λ_ f.obj).inv := rfl

@[simp] theorem leftUnitor_inv_snd (f : a ⟶ b) : (leftUnitor f).inv.2 = 0 := rfl

@[simp] theorem rightUnitor_hom_fst (f : a ⟶ b) : (rightUnitor f).hom.1 = (ρ_ f.obj).hom := rfl

@[simp] theorem rightUnitor_hom_snd (f : a ⟶ b) : (rightUnitor f).hom.2 = 0 := rfl

@[simp] theorem rightUnitor_inv_fst (f : a ⟶ b) : (rightUnitor f).inv.1 = (ρ_ f.obj).inv := rfl

@[simp] theorem rightUnitor_inv_snd (f : a ⟶ b) : (rightUnitor f).inv.2 = 0 := rfl

/-! ### Naturality of the coherence maps -/

section Naturality

open PiFunctor

variable (R)

/-- `λ` as a Π-natural transformation `1 ≫ - ⟶ -`. -/
def lNat (b c : B) : precomp c (𝟙 b) ⟶ 𝟭 (b ⟶ c) where
  app g := (λ_ g).hom
  naturality _ _ η := leftUnitor_naturality η

theorem lNat_isPiNatural (b c : B) :
    IsPiNatural R (precompPi R c (𝟙 b)) (PiFunctor.id R (b ⟶ c)) (lNat b c) := fun g => by
  simp only [lNat, precompPi_β_hom_app, PiFunctor.id_β, Iso.refl_hom, NatTrans.id_app,
    Functor.id_obj, Category.comp_id, pi_obj, pi_map]
  bicategory

/-- `ρ` as a Π-natural transformation `- ≫ 1 ⟶ -` (this uses `β_{1} = 1`). -/
def rNat (a b : B) : postcomp a (𝟙 b) ⟶ 𝟭 (a ⟶ b) where
  app f := (ρ_ f).hom
  naturality _ _ η := rightUnitor_naturality η

theorem rNat_isPiNatural (a b : B) :
    IsPiNatural R (postcompPi R a (𝟙 b)) (PiFunctor.id R (a ⟶ b)) (rNat a b) := fun f => by
  simp only [rNat, postcompPi_β_hom_app, PiFunctor.id_β, Iso.refl_hom, NatTrans.id_app,
    Functor.id_obj, Category.comp_id, pi_obj, pi_map, βR_hom, β_id]
  bicategory

/-- `α_{F,G,-}` as a Π-natural transformation `(F ≫ G) ≫ - ⟶ F ≫ G ≫ -`. -/
def αNatRight (d : B) {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    precomp d (f ≫ g) ⟶ precomp d g ⋙ precomp d f where
  app h := (α_ f g h).hom
  naturality _ _ η := associator_naturality_right f g η

theorem αNatRight_isPiNatural (d : B) {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    IsPiNatural R (precompPi R d (f ≫ g)) ((precompPi R d g).comp (precompPi R d f))
      (αNatRight d f g) := fun h => by
  simp only [αNatRight, precompPi_β_hom_app, PiFunctor.comp_β, NatIso.ofComponents_hom_app,
    Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.comp_obj, precomp_obj, precomp_map,
    pi_obj, pi_map]
  bicategory

/-- `α_{-,G,H}` as a Π-natural transformation `(- ≫ G) ≫ H ⟶ - ≫ G ≫ H` (this uses (i) of
Definition 5.2(i)). -/
def αNatLeft (a : B) {b c d : B} (g : b ⟶ c) (h : c ⟶ d) :
    postcomp a g ⋙ postcomp a h ⟶ postcomp a (g ≫ h) where
  app f := (α_ f g h).hom
  naturality _ _ η := associator_naturality_left η g h

theorem αNatLeft_isPiNatural (a : B) {b c d : B} (g : b ⟶ c) (h : c ⟶ d) :
    IsPiNatural R ((postcompPi R a g).comp (postcompPi R a h)) (postcompPi R a (g ≫ h))
      (αNatLeft a g h) := fun f => by
  simp only [αNatLeft, postcompPi_β_hom_app, PiFunctor.comp_β, NatIso.ofComponents_hom_app,
    Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.comp_obj, postcomp_obj,
    postcomp_map, pi_obj, pi_map, βR_hom, β_comp]
  bicategory

/-- `α_{F,-,H}` as a Π-natural transformation `(F ≫ -) ≫ H ⟶ F ≫ (- ≫ H)`. -/
def αNatMiddle {a b c d : B} (f : a ⟶ b) (h : c ⟶ d) :
    precomp c f ⋙ postcomp a h ⟶ postcomp b h ⋙ precomp d f where
  app g := (α_ f g h).hom
  naturality _ _ η := associator_naturality_middle f η h

theorem αNatMiddle_isPiNatural {a b c d : B} (f : a ⟶ b) (h : c ⟶ d) :
    IsPiNatural R ((precompPi R c f).comp (postcompPi R a h))
      ((postcompPi R b h).comp (precompPi R d f)) (αNatMiddle f h) := fun g => by
  simp only [αNatMiddle, postcompPi_β_hom_app, precompPi_β_hom_app, PiFunctor.comp_β,
    NatIso.ofComponents_hom_app, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.comp_obj, postcomp_obj, postcomp_map, precomp_obj, precomp_map, pi_obj, pi_map,
    βR_hom]
  bicategory

end Naturality

theorem map_map_map {C D E : Type*} [Category C] [Preadditive C] [Linear R C] [PiCategory R C]
    [Category D] [Preadditive D] [Linear R D] [PiCategory R D] [Category E] [Preadditive E]
    [Linear R E] [PiCategory R E] {F : C ⥤ D} {G : D ⥤ E} [F.Additive] [G.Additive]
    (hF : PiFunctor R F) (hG : PiFunctor R G) {X Y : Associated R C} (f : X ⟶ Y) :
    (Associated.map hG).map ((Associated.map hF).map f) = (Associated.map (hF.comp hG)).map f := by
  ext <;> simp

theorem map_id_map {C : Type*} [Category C] [Preadditive C] [Linear R C] [PiCategory R C]
    {X Y : Associated R C} (f : X ⟶ Y) : (Associated.map (PiFunctor.id R C)).map f = f := by
  ext <;> simp

/-! ### The super interchange law -/

/-- The key identity for the super interchange law on two odd 2-morphisms (it uses
`β_{π_c} = -1` and the naturality of `β`). -/
theorem odd_odd_key {a b c : B} {f g : a ⟶ b} {h i : b ⟶ c} (η : f ⟶ g ≫ 𝛑 b)
    (θ : h ⟶ i ≫ 𝛑 c) :
    (η ▷ h ≫ (βR (R := R) g h).inv) ≫ (g ◁ θ ≫ (α_ g i (𝛑 c)).inv) ▷ 𝛑 c =
      -((f ◁ θ ≫ (α_ f i (𝛑 c)).inv) ≫ (η ▷ i ≫ (βR (R := R) g i).inv) ▷ 𝛑 c) := by
  have e1 : f ◁ θ ≫ (α_ f i (𝛑 c)).inv ≫ (η ▷ i) ▷ 𝛑 c =
      η ▷ h ≫ (g ≫ 𝛑 b) ◁ θ ≫ (α_ (g ≫ 𝛑 b) i (𝛑 c)).inv := by
    rw [← associator_inv_naturality_left, whisker_exchange_assoc]
  simp only [Category.assoc, Bicategory.comp_whiskerRight]
  rw [reassoc_of% e1, ← βR_inv_naturality_right_assoc, βR_inv, βR_inv, β_pi_comp_inv]
  simp only [PreadditiveBicategory.whiskerLeft_neg, Preadditive.neg_comp, Preadditive.comp_neg]
  congr 1
  bicategory

theorem mem_parity_zero' {f g : a ⟶ b} {η : f ⟶ g} :
    η ∈ parity (R := R) f g 0 ↔ η.2 = 0 := Associated.mem_parity_zero

theorem mem_parity_one' {f g : a ⟶ b} {η : f ⟶ g} :
    η ∈ parity (R := R) f g 1 ↔ η.1 = 0 := Associated.mem_parity_one

theorem super_interchange' {f g : a ⟶ b} {h i : b ⟶ c} {p q : ZMod 2} {η : f ⟶ g}
    {θ : h ⟶ i} (hη : η ∈ parity (R := R) f g p) (hθ : θ ∈ parity (R := R) h i q) :
    η ▷ h ≫ g ◁ θ = koszulSign p q • (f ◁ θ ≫ η ▷ i) := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    rcases parity_eq_zero_or_one q with rfl | rfl
  · rw [mem_parity_zero'] at hη hθ
    rw [koszulSign_zero_left, one_smul]
    ext
    · simp [hη, hθ, whisker_exchange]
    · simp [hη, hθ]
  · rw [mem_parity_zero'] at hη; rw [mem_parity_one'] at hθ
    rw [koszulSign_zero_left, one_smul]
    ext
    · simp [hη, hθ]
    · simp only [comp₂_snd, whiskerRight_fst, whiskerLeft_snd, whiskerRight_snd,
        whiskerLeft_fst, hη, hθ, PreadditiveBicategory.zero_whiskerRight,
        PreadditiveBicategory.whiskerLeft_zero, Limits.zero_comp, add_zero, zero_add,
        Category.assoc, pi_map]
      rw [← whisker_exchange_assoc]
      erw [associator_inv_naturality_left]
  · rw [mem_parity_one'] at hη; rw [mem_parity_zero'] at hθ
    rw [koszulSign_zero_right, one_smul]
    ext
    · simp [hη, hθ]
    · simp only [comp₂_snd, whiskerRight_fst, whiskerLeft_snd, whiskerRight_snd,
        whiskerLeft_fst, hη, hθ, PreadditiveBicategory.zero_whiskerRight,
        PreadditiveBicategory.whiskerLeft_zero, Limits.zero_comp, add_zero, zero_add,
        Limits.comp_zero, Category.assoc, pi_map]
      rw [← βR_inv_naturality_right, whisker_exchange_assoc]
      rfl
  · rw [mem_parity_one'] at hη hθ
    rw [koszulSign_one_one, neg_one_smul]
    ext
    · simp only [comp₂_fst, whiskerRight_fst, whiskerLeft_snd, whiskerRight_snd,
        whiskerLeft_fst, neg₂_fst, hη, hθ, PreadditiveBicategory.zero_whiskerRight,
        PreadditiveBicategory.whiskerLeft_zero, Limits.zero_comp, zero_sub, neg_neg]
      rw [← Category.assoc, ← Category.assoc, odd_odd_key]
      simp
    · simp [hη, hθ]

/-- **Brundan–Ellis, (5.5), `D₂` on objects.** The associated `𝔄̂` of a Π-2-category is a
2-supercategory. -/
instance twoSupercategory : TwoSupercategory R (Associated2 R B) where
  whiskerLeft_id f g := (Associated.map (precompPi R _ f.obj)).map_id g
  whiskerLeft_comp f _ _ _ η θ := (Associated.map (precompPi R _ f.obj)).map_comp η θ
  id_whiskerLeft {a b f g} η := by
    have h := Associated.map_naturality (lNat_isPiNatural R a.obj b.obj) η
    rw [map_id_map] at h
    change (𝟙 a) ◁ η ≫ (leftUnitor g).hom = (leftUnitor f).hom ≫ η at h
    rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  comp_whiskerLeft {a b c d} f g h h' η := by
    have e := Associated.map_naturality (αNatRight_isPiNatural R d.obj f.obj g.obj) η
    rw [← map_map_map] at e
    change (f ≫ g) ◁ η ≫ (associator f g h').hom = (associator f g h).hom ≫ f ◁ g ◁ η at e
    rw [← Category.assoc, ← e, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  id_whiskerRight f g := (Associated.map (postcompPi R _ g.obj)).map_id f
  comp_whiskerRight η θ i := (Associated.map (postcompPi R _ i.obj)).map_comp η θ
  whiskerRight_id {a b f g} η := by
    have h := Associated.map_naturality (rNat_isPiNatural R a.obj b.obj) η
    rw [map_id_map] at h
    change η ▷ (𝟙 b) ≫ (rightUnitor g).hom = (rightUnitor f).hom ≫ η at h
    rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  whiskerRight_comp {a b c d f f'} η g h := by
    have e := Associated.map_naturality (αNatLeft_isPiNatural R a.obj g.obj h.obj) η
    rw [← map_map_map] at e
    change η ▷ g ▷ h ≫ (associator f' g h).hom = (associator f g h).hom ≫ η ▷ (g ≫ h) at e
    rw [e, Iso.inv_hom_id_assoc]
  whisker_assoc {a b c d} f g g' η h := by
    have e := Associated.map_naturality (αNatMiddle_isPiNatural R f.obj h.obj) η
    rw [← map_map_map, ← map_map_map] at e
    change (f ◁ η) ▷ h ≫ (associator f g' h).hom = (associator f g h).hom ≫ f ◁ (η ▷ h) at e
    rw [← Category.assoc, ← e, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  pentagon f g h i := by ext <;> simp [Associated.homMk_comp_homMk_even]
  triangle f g := by ext <;> simp
  whiskerLeft_add f _ _ η θ := (Associated.map (precompPi R _ f.obj)).map_add
  add_whiskerRight η θ h := (Associated.map (postcompPi R _ h.obj)).map_add
  whiskerLeft_smul f _ _ r η := Functor.Linear.map_smul (F := Associated.map (precompPi R _ f.obj)) η r
  smul_whiskerRight r η h := Functor.Linear.map_smul (F := Associated.map (postcompPi R _ h.obj)) η r
  whiskerLeft_mem f _ _ _ _ hη := IsSuperfunctor.map_mem (F := Associated.map (precompPi R _ f.obj)) hη
  whiskerRight_mem h hη := IsSuperfunctor.map_mem (F := Associated.map (postcompPi R _ h.obj)) hη
  super_interchange hη hθ := super_interchange' hη hθ
  associator_hom_mem _ _ _ := Associated.mem_parity_zero.2 rfl
  leftUnitor_hom_mem _ := Associated.mem_parity_zero.2 rfl
  rightUnitor_hom_mem _ := Associated.mem_parity_zero.2 rfl

/-- **The corrected odd–odd horizontal rule of (5.5).** For odd `x̂ : F ⇒ H` and `ŷ : G ⇒ K`
coming from `x : F ⇒ π_μ H` and `y : G ⇒ π_ν K`, the horizontal composite `ŷx̂` in `𝔄̂` is the
even 2-morphism `ξ_ν KH ∘ π_ν (β_{ν,μ})⁻¹_K H ∘ yx` (with associators), *without* the minus
sign printed in (5.5). -/
theorem hcomp_odd_odd {f h : a ⟶ b} {g k : b ⟶ c} {x : f ⟶ h} {y : g ⟶ k} (hx : x.1 = 0)
    (hy : y.1 = 0) :
    TwoSupercategory.hcomp x y =
      Associated.homMk (R := R) (X := ⟨f.obj ≫ g.obj⟩) (Y := ⟨h.obj ≫ k.obj⟩)
        ((x.2 ▷ g.obj ≫ (h.obj ≫ 𝛑 b.obj) ◁ y.2) ≫ (α_ h.obj (𝛑 b.obj) (k.obj ≫ 𝛑 c.obj)).hom ≫
          h.obj ◁ (α_ (𝛑 b.obj) k.obj (𝛑 c.obj)).inv ≫ h.obj ◁ ((𝛃 k.obj).inv ▷ 𝛑 c.obj) ≫
          (α_ h.obj (k.obj ≫ 𝛑 c.obj) (𝛑 c.obj)).inv ≫ (α_ h.obj k.obj (𝛑 c.obj)).inv ▷ 𝛑 c.obj ≫
          (ξHom (R := R) (h.obj ≫ k.obj)).hom) 0 := by
  ext
  · simp only [TwoSupercategory.hcomp, comp₂_fst, whiskerRight_fst, whiskerLeft_fst,
      whiskerRight_snd, whiskerLeft_snd, hx, hy, PreadditiveBicategory.zero_whiskerRight,
      PreadditiveBicategory.whiskerLeft_zero, Limits.zero_comp, zero_sub,
      Associated.homMk_fst, pi_map, Bicategory.comp_whiskerRight, Category.assoc]
    rw [← Category.assoc ((βR (R := R) h.obj g.obj).inv), ← βR_inv_naturality_right, βR_inv]
    erw [β_pi_comp_inv]
    simp only [PreadditiveBicategory.whiskerLeft_neg, Preadditive.neg_comp, Preadditive.comp_neg,
      neg_neg, Category.assoc, Bicategory.whiskerLeft_comp]
    rfl
  · simp [TwoSupercategory.hcomp, hx, hy]

/-! ### The Π-2-supercategory structure -/

/-- The odd 2-isomorphism `ζ_λ : π_λ ⇒ 1_λ` of `𝔄̂`: the 2-morphism `l⁻¹ : π_λ ⇒ 1_λ π_λ` of
`𝔄`, viewed as an odd 2-morphism (Brundan–Ellis, (5.5): `ζ_λ := 1_{π_λ}` viewed as odd). -/
def ζ (a : Associated2 R B) : (⟨𝛑 a.obj⟩ : a ⟶ a) ≅ 𝟙 a :=
  Associated.evenIso (λ_ (𝛑 a.obj)).symm ≪≫ Associated.ζIso (X := (⟨𝟙 a.obj⟩ : Associated R _))

@[simp] theorem ζ_hom_fst (a : Associated2 R B) : (ζ (R := R) a).hom.1 = 0 := by
  simp [ζ, Associated.ζIso]

@[simp] theorem ζ_hom_snd (a : Associated2 R B) : (ζ (R := R) a).hom.2 = (λ_ (𝛑 a.obj)).inv := by
  simp [ζ, Associated.ζIso]

@[simp] theorem ζ_inv_fst (a : Associated2 R B) : (ζ (R := R) a).inv.1 = 0 := by
  simp [ζ, Associated.ζIso]

@[simp] theorem ζ_inv_snd (a : Associated2 R B) :
    (ζ (R := R) a).inv.2 = -((ξHom (R := R) (𝟙 a.obj)).inv ≫ (λ_ (𝛑 a.obj)).hom ▷ 𝛑 a.obj) := by
  simp [ζ, Associated.ζIso]

/-- **Brundan–Ellis, (5.5).** `𝔄̂` is a Π-2-supercategory with `π̂_λ = π_λ` and `ζ_λ` the identity
of `π_λ` viewed as an odd 2-isomorphism `π_λ ⇒ 1_λ`. -/
instance instPiTwoSupercategory : PiTwoSupercategory R (Associated2 R B) where
  pi a := ⟨𝛑 a.obj⟩
  ζ := ζ
  ζ_hom_mem a := Associated.mem_parity_one.2 (ζ_hom_fst a)

@[simp] theorem pi_obj' (a : Associated2 R B) :
    (PiTwoSupercategory.pi (R := R) a).obj = 𝛑 a.obj := rfl

theorem ζ_eq (a : Associated2 R B) : PiTwoSupercategory.ζ (R := R) a = ζ a := rfl

/-- **Lemma 5.4, `E₂ ∘ D₂ = I` on `β`.** The `β` of Lemma 3.2 for `𝔄̂` is `β` of `𝔄`, viewed as an
even 2-morphism. -/
theorem β_hom_eq (f : a ⟶ b) :
    (PiTwoSupercategory.β (R := R) f).hom =
      Associated.homMk (R := R) (X := ⟨f.obj ≫ 𝛑 b.obj⟩) (Y := ⟨𝛑 a.obj ≫ f.obj⟩)
        (𝛃 f.obj).hom 0 := by
  rw [← cancel_mono (TwoSupercategory.whiskerRightIso (R := R) (PiTwoSupercategory.ζ (R := R) a)
    f).hom, TwoSupercategory.whiskerRightIso_hom, PiTwoSupercategory.β_hom_comp_ζ]
  ext
  · simp [ζ_eq]
  · simp [ζ_eq]
    rw [βR_inv]
    simp only [Iso.inv_hom_id_assoc]
    rw [← leftUnitor_inv_naturality_assoc, Iso.hom_inv_id_assoc]

/-- **Lemma 5.4, `E₂ ∘ D₂ = I` on `ξ`.** The `ξ = ζζ` of Lemma 3.2(iv) for `𝔄̂` is `ξ` of `𝔄`,
viewed as an even 2-morphism. This uses the corrected signs of (5.5). -/
theorem ξ_hom_eq (a : Associated2 R B) :
    (PiTwoSupercategory.ξ (R := R) a).hom =
      Associated.homMk (R := R) (X := ⟨𝛑 a.obj ≫ 𝛑 a.obj⟩) (Y := ⟨𝟙 a.obj⟩) (𝛏 a.obj).hom 0 := by
  ext
  · simp [PiTwoSupercategory.ξ_hom, ζ_eq]
    rw [βR_inv, β_pi_inv]
    simp [ξHom_hom]
  · simp [PiTwoSupercategory.ξ_hom, ζ_eq]

end Associated2

end StringDiagrams

end
