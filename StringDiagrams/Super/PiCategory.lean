import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Π-categories

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Definition 1.6.

* A Π-category `(A, Π, ξ)` is an `R`-linear category `A` with an `R`-linear endofunctor `Π`
  and a natural isomorphism `ξ : Π² ≅ 𝟭` such that `ξΠ = Πξ` (`StringDiagrams.PiCategory`).
* A Π-functor is an `R`-linear functor `F` with a natural isomorphism `β_F : Π F ≅ F Π` such
  that `ξ F ∘ F ξ⁻¹ = β_F Π ∘ Π β_F` (`StringDiagrams.PiFunctor`).
* A Π-natural transformation is a natural transformation `x : F ⟶ G` with
  `x Π ∘ β_F = β_G ∘ Π x` (`StringDiagrams.PiFunctor.IsPiNatural`).

We also record the examples given in Definition 1.6(ii): the identity functor is a Π-functor
with `β = 1`, `Π` is a Π-functor with `β_Π = -1`, and Π-functors compose with
`β_{GF} = G β_F ∘ β_G F`.

All compositions are written in diagrammatic order `f ≫ g` (`= g ∘ f`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory

universe w w₁ w₂ w₃ w₄ w₅ w₆

variable (R : Type w) [CommRing R]

/-- A Π-category (Brundan–Ellis, Definition 1.6(i)): an `R`-linear endofunctor `pi` and a
natural isomorphism `ξ : Π² ≅ 𝟭` with `ξ_{Π X} = Π(ξ_X)`. -/
class PiCategory (C : Type w₁) [Category.{w₂} C] [Preadditive C] [Linear R C] where
  /-- The parity-switching functor `Π`. -/
  pi : C ⥤ C
  [pi_additive : pi.Additive]
  [pi_linear : pi.Linear R]
  /-- The isomorphism `ξ : Π² ≅ 𝟭`. -/
  ξ : pi ⋙ pi ≅ 𝟭 C
  ξ_pi : ∀ X : C, ξ.hom.app (pi.obj X) = pi.map (ξ.hom.app X)

attribute [instance] PiCategory.pi_additive PiCategory.pi_linear

namespace PiCategory

variable {R} {C : Type w₁} [Category.{w₂} C] [Preadditive C] [Linear R C] [PiCategory R C]
  {D : Type w₃} [Category.{w₄} D] [Preadditive D] [Linear R D] [PiCategory R D]
  {E : Type w₅} [Category.{w₆} E] [Preadditive E] [Linear R E] [PiCategory R E]

/-- The component `ξ_X : Π² X ≅ X`. -/
def ξApp (X : C) : (pi (R := R)).obj ((pi (R := R)).obj X) ≅ X := (ξ (R := R)).app X

theorem ξApp_hom (X : C) : (ξApp (R := R) X).hom = (ξ (R := R)).hom.app X := rfl

theorem ξApp_inv (X : C) : (ξApp (R := R) X).inv = (ξ (R := R)).inv.app X := rfl

@[reassoc]
theorem ξApp_naturality {X Y : C} (f : X ⟶ Y) :
    (pi (R := R)).map ((pi (R := R)).map f) ≫ (ξApp (R := R) Y).hom = (ξApp (R := R) X).hom ≫ f :=
  (ξ (R := R)).hom.naturality f

theorem ξApp_pi (X : C) :
    (ξApp (R := R) ((pi (R := R)).obj X)).hom = (pi (R := R)).map (ξApp (R := R) X).hom :=
  ξ_pi X

theorem ξ_inv_pi (X : C) :
    (ξ (R := R)).inv.app ((pi (R := R)).obj X) = (pi (R := R)).map ((ξ (R := R)).inv.app X) := by
  rw [← cancel_mono ((ξ (R := R)).hom.app _), Iso.inv_hom_id_app, ξ_pi, ← Functor.map_comp,
    Iso.inv_hom_id_app]
  simp

end PiCategory

open PiCategory

variable {R} {C : Type w₁} [Category.{w₂} C] [Preadditive C] [Linear R C] [PiCategory R C]
  {D : Type w₃} [Category.{w₄} D] [Preadditive D] [Linear R D] [PiCategory R D]
  {E : Type w₅} [Category.{w₆} E] [Preadditive E] [Linear R E] [PiCategory R E]

variable (R) in
/-- A Π-functor structure on a functor (Brundan–Ellis, Definition 1.6(ii)): a natural
isomorphism `β : Π_B F ≅ F Π_A` with `ξ_B F ∘ F ξ_A⁻¹ = β Π_A ∘ Π_B β` in
`Hom(Π_B² F, F Π_A²)`. -/
structure PiFunctor (F : C ⥤ D) where
  /-- The isomorphism `β_F : Π F ≅ F Π`. -/
  β : F ⋙ pi (R := R) ≅ pi (R := R) ⋙ F
  comm : ∀ X : C, (ξ (R := R)).hom.app (F.obj X) ≫ F.map ((ξ (R := R)).inv.app X) =
    (pi (R := R)).map (β.hom.app X) ≫ β.hom.app ((pi (R := R)).obj X)

namespace PiFunctor

variable (R C) in
/-- The identity functor is a Π-functor with `β = 1`. -/
@[simps]
def id : PiFunctor R (𝟭 C) where
  β := Iso.refl _
  comm X := by simp

/-- The composite of Π-functors, with `β_{GF} = G β_F ∘ β_G F`. -/
@[simps]
def comp {F : C ⥤ D} {G : D ⥤ E} (hF : PiFunctor R F) (hG : PiFunctor R G) :
    PiFunctor R (F ⋙ G) where
  β := NatIso.ofComponents (fun X => hG.β.app (F.obj X) ≪≫ G.mapIso (hF.β.app X)) (fun f => by
    have n1 := hF.β.hom.naturality f
    have n2 := hG.β.hom.naturality (F.map f)
    simp only [Functor.comp_obj, Functor.comp_map] at n1 n2 ⊢
    simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
    rw [reassoc_of% n2]
    congr 1
    rw [← G.map_comp, ← G.map_comp, n1])
  comm X := by
    simp only [Functor.comp_obj, Functor.comp_map, NatIso.ofComponents_hom_app, Iso.trans_hom,
      Iso.app_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
    have h1 := hG.comm (F.obj X)
    have h2 := congrArg G.map (hF.comm X)
    simp only [Functor.map_comp] at h2
    have n1 := hG.β.hom.naturality (hF.β.hom.app X)
    simp only [Functor.comp_obj, Functor.comp_map] at n1
    rw [reassoc_of% n1, ← reassoc_of% h1, ← h2, ← G.map_comp_assoc]
    simp

/-- The functor `Π` is a Π-functor with `β_Π = -1`. -/
@[simps]
def pi : PiFunctor R (pi (R := R) (C := C)) where
  β := NatIso.ofComponents (fun X => { hom := -𝟙 _, inv := -𝟙 _ }) (fun f => by simp)
  comm X := by
    simp only [Functor.comp_obj, NatIso.ofComponents_hom_app, Functor.map_neg, Functor.map_id,
      Preadditive.neg_comp, Preadditive.comp_neg, Category.id_comp, neg_neg]
    rw [ξ_pi, ← Functor.map_comp, Iso.hom_inv_id_app]
    simp

variable (R) in
/-- A Π-natural transformation (Brundan–Ellis, Definition 1.6(iii)):
`x Π_A ∘ β_F = β_G ∘ Π_B x`. -/
def IsPiNatural {F G : C ⥤ D} (hF : PiFunctor R F) (hG : PiFunctor R G) (x : F ⟶ G) : Prop :=
  ∀ X : C, hF.β.hom.app X ≫ x.app ((PiCategory.pi (R := R)).obj X) =
    (PiCategory.pi (R := R)).map (x.app X) ≫ hG.β.hom.app X

theorem isPiNatural_id {F : C ⥤ D} (hF : PiFunctor R F) : IsPiNatural R hF hF (𝟙 F) :=
  fun X => by simp

theorem IsPiNatural.comp {F G H : C ⥤ D} {hF : PiFunctor R F} {hG : PiFunctor R G}
    {hH : PiFunctor R H} {x : F ⟶ G} {y : G ⟶ H} (hx : IsPiNatural R hF hG x)
    (hy : IsPiNatural R hG hH y) : IsPiNatural R hF hH (x ≫ y) := fun X => by
  simp only [NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hx X, hy X]

end PiFunctor

end StringDiagrams

end
