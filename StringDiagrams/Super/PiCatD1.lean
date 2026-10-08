import StringDiagrams.Super.PiCatE1
import StringDiagrams.Super.QPiTwoSCat
import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic

/-!
# Theorem 5.3: `𝔻₁` and `𝔼₁` are mutually inverse Π-2-equivalences

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, (5.3) and
Theorem 5.3 (with its proof), as a statement about bundled Π-2-functors and Π-2-natural
transformations between the strict Π-2-categories `Π-ℭ𝔞𝔱` (`StringDiagrams.Super.PiCatBicategory`)
and `E₂(Π-𝔖ℭ𝔞𝔱) = Π-𝔖ℭ𝔞𝔱̲` (Π-supercategories, superfunctors and even supernatural
transformations, `Underlying2 R (PiSCat R)`).

* `PiCat.D₁Strict`, `PiCat.D₁Pseudo`: the strict 2-functor `𝔻₁ : Π-ℭ𝔞𝔱 → E₂(Π-𝔖ℭ𝔞𝔱)` of (5.3),
  `A ↦ Â`, `F ↦ F̂`, `y ↦ ŷ` (a strict pseudofunctor, Mathlib's `StrictPseudofunctor`);
  `PiCat.D₁PiTwoFunctor`: it is a strict Π-2-functor (`j = 1`, from `π̂ = 𝔻₁ π`,
  `Associated.pi_eq_map_pi`; the axioms are `β_{F̂} = 𝔻₁ β_F`, `Associated.β_map`, and `ξ̂ = 𝔻₁ ξ`).
  `𝔼₁` is `PiSCat.E₁Pseudo`, `PiSCat.E₁PiTwoFunctor` (`StringDiagrams.Super.PiCatE1`).
* `PiCat.unitStrong`: the isomorphisms `A ≅ E₁(D₁ A)` of Lemma 5.1 as a strong transformation
  `𝕀 ⇒ 𝔼₁ ∘ 𝔻₁` with identity naturality 2-morphisms, Π-2-natural
  (`PiCat.unitStrong_isPiTwoNatural`). The paper's equality `𝔼₁ ∘ 𝔻₁ = 𝕀` holds up to this
  identification (the identity on objects and morphisms of the underlying data).
* `PiSCat.counitStrong`: the isomorphisms `T_A : D₁(E₁ A) ≅ A` as a strong transformation
  `𝔻₁ ∘ 𝔼₁ ⇒ 𝕀` with identity naturality 2-morphisms (`t = 1` in the proof), Π-2-natural
  (`PiSCat.counitStrong_isPiTwoNatural`, from `β_{T_A} = 1`, `Associated.β_T`).
* **Theorem 5.3** (`PiCat.theorem53`): both transformations are Π-2-natural isomorphisms (their
  components are invertible 1-morphisms and their naturality 2-morphisms are identities), so
  `𝔻₁` and `𝔼₁` are mutually inverse Π-2-equivalences; as the proof observes, `𝔻₁ ∘ 𝔼₁` is even
  isomorphic, not only equivalent, to the identity. The local form (`𝔼₁` full, faithful and essentially surjective on morphism
  categories) is in `StringDiagrams.Super.PiCatE1`.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Bicategory Supercategory

universe w w₁ v₁ u₁ v u

/-! ## The underlying bicategory of a strict 2-supercategory is strict -/

namespace Underlying2

variable {R : Type w} [CommRing R] {B : Type u₁} [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]

theorem eqToHom_val {a b : Underlying2 R B} {f g : a ⟶ b} (h : f = g) :
    (eqToHom h).1 = eqToHom (congrArg Underlying.obj h) := by
  subst h
  rfl

theorem hom1_eq {a b : Underlying2 R B} {f g : a ⟶ b} (h : f.obj = g.obj) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- The underlying bicategory of a strict 2-supercategory is strict. -/
instance instStrict [BicategoryStruct.Strict B] : Bicategory.Strict (Underlying2 R B) where
  id_comp f := hom1_eq (BicategoryStruct.Strict.id_comp f.obj)
  comp_id f := hom1_eq (BicategoryStruct.Strict.comp_id f.obj)
  assoc f g h := hom1_eq (BicategoryStruct.Strict.assoc f.obj g.obj h.obj)
  leftUnitor_eqToIso f := Iso.ext (Subtype.ext (by
    rw [eqToIso.hom, eqToHom_val]
    exact congrArg Iso.hom (BicategoryStruct.Strict.leftUnitor_eqToIso f.obj)))
  rightUnitor_eqToIso f := Iso.ext (Subtype.ext (by
    rw [eqToIso.hom, eqToHom_val]
    exact congrArg Iso.hom (BicategoryStruct.Strict.rightUnitor_eqToIso f.obj)))
  associator_eqToIso f g h := Iso.ext (Subtype.ext (by
    rw [eqToIso.hom, eqToHom_val]
    exact congrArg Iso.hom (BicategoryStruct.Strict.associator_eqToIso f.obj g.obj h.obj)))

end Underlying2

namespace Superfunctor

variable {R : Type w} [CommRing R] {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear R C]
  [Supercategory R C] {D : Type u} [Category.{v} D] [Preadditive D] [Linear R D]
  [Supercategory R D]

@[simp] theorem eqToHom_app_zero {F G : Superfunctor R C D} (h : F = G) (X : C) :
    (eqToHom h : F ⟶ G).app 0 X = eqToHom (by rw [h]) := by
  subst h
  rfl

@[simp] theorem eqToHom_app_one {F G : Superfunctor R C D} (h : F = G) (X : C) :
    (eqToHom h : F ⟶ G).app 1 X = 0 := by
  subst h
  rfl

end Superfunctor

namespace PiSCat

variable {R : Type w} [CommRing R] {A B : PiSCat.{w, v, u} R}

@[simp] theorem eqToHom_app_zero {F G : A ⟶ B} (h : F = G) (X : A.carrier) :
    (eqToHom h : F ⟶ G).app 0 X = eqToHom (by rw [h]) := by
  subst h
  rfl

@[simp] theorem eqToHom_app_one {F G : A ⟶ B} (h : F = G) (X : A.carrier) :
    (eqToHom h : F ⟶ G).app 1 X = 0 := by
  subst h
  rfl

/-! ### Even 2-morphisms of `Π-𝔖ℭ𝔞𝔱` -/

section Even

variable {A B C : Underlying2 R (PiSCat.{w, v, u} R)}

@[simp] theorem app_one_eq_zero {F G : A ⟶ B} (x : F ⟶ G) (X : A.obj.carrier) : x.1.app 1 X = 0 :=
  Superfunctor.app_eq_zero_of_mem x.2 (by decide) X

/-- Even 2-morphisms of `E₂(Π-𝔖ℭ𝔞𝔱)` are determined by their even components. -/
theorem hom₂_ext {F G : A ⟶ B} {x y : F ⟶ G} (h : ∀ X : A.obj.carrier, x.1.app 0 X = y.1.app 0 X) :
    x = y :=
  Subtype.ext (Superfunctor.hom_ext_parity h fun X => by
    rw [app_one_eq_zero x X, app_one_eq_zero y X])

@[simp] theorem comp₂_app_zero {F G H : A ⟶ B} (x : F ⟶ G) (y : G ⟶ H) (X : A.obj.carrier) :
    (x ≫ y).1.app 0 X = x.1.app 0 X ≫ y.1.app 0 X := by
  change x.1.app 0 X ≫ y.1.app 0 X + x.1.app 1 X ≫ y.1.app 1 X = _
  rw [app_one_eq_zero x X, Limits.zero_comp, add_zero]

@[simp] theorem id₂_app_zero (F : A ⟶ B) (X : A.obj.carrier) :
    (𝟙 F : F ⟶ F).1.app 0 X = 𝟙 _ := rfl

@[simp] theorem whiskerLeft₂_app_zero (F : A ⟶ B) {G H : B ⟶ C} (y : G ⟶ H)
    (X : A.obj.carrier) : (F ◁ y).1.app 0 X = y.1.app 0 (F.obj.obj X) := rfl

@[simp] theorem whiskerRight₂_app_zero {F G : A ⟶ B} (x : F ⟶ G) (H : B ⟶ C)
    (X : A.obj.carrier) : (x ▷ H).1.app 0 X = H.obj.map (x.1.app 0 X) := rfl

@[simp] theorem leftUnitor₂_hom_app_zero (F : A ⟶ B) (X : A.obj.carrier) :
    (λ_ F).hom.1.app 0 X = 𝟙 _ := rfl

@[simp] theorem leftUnitor₂_inv_app_zero (F : A ⟶ B) (X : A.obj.carrier) :
    (λ_ F).inv.1.app 0 X = 𝟙 _ := rfl

@[simp] theorem rightUnitor₂_hom_app_zero (F : A ⟶ B) (X : A.obj.carrier) :
    (ρ_ F).hom.1.app 0 X = 𝟙 _ := rfl

@[simp] theorem rightUnitor₂_inv_app_zero (F : A ⟶ B) (X : A.obj.carrier) :
    (ρ_ F).inv.1.app 0 X = 𝟙 _ := rfl

@[simp] theorem associator₂_hom_app_zero {D : Underlying2 R (PiSCat.{w, v, u} R)} (F : A ⟶ B)
    (G : B ⟶ C) (H : C ⟶ D) (X : A.obj.carrier) : (α_ F G H).hom.1.app 0 X = 𝟙 _ := rfl

@[simp] theorem associator₂_inv_app_zero {D : Underlying2 R (PiSCat.{w, v, u} R)} (F : A ⟶ B)
    (G : B ⟶ C) (H : C ⟶ D) (X : A.obj.carrier) : (α_ F G H).inv.1.app 0 X = 𝟙 _ := rfl

@[simp] theorem eqToHom₂_app_zero {F G : A ⟶ B} (h : F = G) (X : A.obj.carrier) :
    (eqToHom h : F ⟶ G).1.app 0 X = eqToHom (by rw [h]) := by
  subst h
  rfl

end Even

end PiSCat

/-! ## `𝔻₁` as a strict Π-2-functor -/

namespace PiCat

variable {R : Type w} [CommRing R] {A B C : PiCat.{w, v, u} R}

/-- **Brundan–Ellis, (5.3).** `𝔻₁` on 2-morphisms: `y ↦ ŷ`, `ŷ_λ = (y_λ, 0)`, an even
supernatural transformation. -/
abbrev D₁obj (A : PiCat.{w, v, u} R) : Underlying2 R (PiSCat.{w, v, u} R) :=
  ⟨PiSCat.of R (Associated R A)⟩

/-- `𝔻₁` on 1-morphisms: `F ↦ F̂`. -/
abbrev D₁hom (F : A ⟶ B) : D₁obj A ⟶ D₁obj B :=
  Underlying2.hom1 (R := R) (B := PiSCat.{w, v, u} R)
    (⟨Associated.map F.piFunctor⟩ : Superfunctor R (Associated R A) (Associated R B))

def D₁map₂ {F G : A ⟶ B} (y : F ⟶ G) : D₁hom F ⟶ D₁hom G :=
  ⟨Superfunctor.homMk (Associated.mapNatTrans_isSupernatural (Hom₂.isPiNatural y)).toSuperNatTrans,
    Superfunctor.IsSupernatural.toSuperNatTrans_mem _⟩

@[simp] theorem D₁map₂_app_zero {F G : A ⟶ B} (y : F ⟶ G) (X : Associated R A) :
    (D₁map₂ y).1.app 0 X = Associated.homMk ((Hom₂.natTrans y).app X.obj) 0 := by
  change (if (0 : ZMod 2) = 0 then _ else 0) = _
  rfl

@[simp] theorem D₁map₂_app_one {F G : A ⟶ B} (y : F ⟶ G) (X : Associated R A) :
    (D₁map₂ y).1.app 1 X = 0 := by
  change (if (1 : ZMod 2) = 0 then Associated.homMk ((Hom₂.natTrans y).app X.obj) 0 else 0) = _
  rfl

variable (R) in
/-- **Brundan–Ellis, (5.3).** The strict 2-functor `𝔻₁ : Π-ℭ𝔞𝔱 → E₂(Π-𝔖ℭ𝔞𝔱)`: `A ↦ Â`,
`F ↦ F̂`, `y ↦ ŷ` (a strict pseudofunctor). -/
def D₁Strict : StrictPseudofunctor (PiCat.{w, v, u} R) (Underlying2 R (PiSCat.{w, v, u} R)) :=
  StrictPseudofunctor.mk''
    { obj A := D₁obj A
      map F := D₁hom F
      map₂ y := D₁map₂ y
      map₂_id F := PiSCat.hom₂_ext fun X => by simp; rfl
      map₂_comp x y := PiSCat.hom₂_ext fun X => by
        rw [PiSCat.comp₂_app_zero, D₁map₂_app_zero, D₁map₂_app_zero, D₁map₂_app_zero]
        exact (Associated.homMk_comp_homMk_even _ _).symm
      map_id A := Underlying2.hom1_eq (D₁.map_id A)
      map_comp F G := Underlying2.hom1_eq (D₁.map_comp F G)
      map₂_whisker_left F G H y := PiSCat.hom₂_ext fun X => by
        rw [PiSCat.comp₂_app_zero, PiSCat.comp₂_app_zero, PiSCat.eqToHom₂_app_zero,
          PiSCat.eqToHom₂_app_zero, PiSCat.whiskerLeft₂_app_zero, D₁map₂_app_zero,
          D₁map₂_app_zero]
        erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
        rfl
      map₂_whisker_right x H := PiSCat.hom₂_ext fun X => by
        rw [PiSCat.comp₂_app_zero, PiSCat.comp₂_app_zero, PiSCat.eqToHom₂_app_zero,
          PiSCat.eqToHom₂_app_zero, PiSCat.whiskerRight₂_app_zero, D₁map₂_app_zero,
          D₁map₂_app_zero]
        erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
        exact Associated.mapNatTrans_whiskerRight H.piFunctor (Hom₂.isPiNatural x) X }

@[simp] theorem D₁Strict_obj (A : PiCat.{w, v, u} R) : (D₁Strict R).obj A = D₁obj A := rfl

@[simp] theorem D₁Strict_map {A B : PiCat.{w, v, u} R} (F : A ⟶ B) :
    (D₁Strict R).map F = D₁hom F := rfl

@[simp] theorem D₁Strict_map₂ {A B : PiCat.{w, v, u} R} {F G : A ⟶ B} (y : F ⟶ G) :
    (D₁Strict R).map₂ y = D₁map₂ y := rfl

variable (R) in
/-- `𝔻₁` as a pseudofunctor. -/
abbrev D₁Pseudo : Pseudofunctor (PiCat.{w, v, u} R) (Underlying2 R (PiSCat.{w, v, u} R)) :=
  (D₁Strict R).toPseudofunctor

theorem D₁Pseudo_mapComp_inv {A B C : PiCat.{w, v, u} R} (F : A ⟶ B) (G : B ⟶ C) :
    ((D₁Pseudo R).mapComp F G).inv = eqToHom (Underlying2.hom1_eq (D₁.map_comp F G)).symm := rfl

theorem D₁Pseudo_mapComp_hom {A B C : PiCat.{w, v, u} R} (F : A ⟶ B) (G : B ⟶ C) :
    ((D₁Pseudo R).mapComp F G).hom = eqToHom (Underlying2.hom1_eq (D₁.map_comp F G)) := rfl

theorem D₁Pseudo_mapId_hom (A : PiCat.{w, v, u} R) :
    ((D₁Pseudo R).mapId A).hom = eqToHom (Underlying2.hom1_eq (D₁.map_id A)) := rfl

theorem D₁Pseudo_mapId_inv (A : PiCat.{w, v, u} R) :
    ((D₁Pseudo R).mapId A).inv = eqToHom (Underlying2.hom1_eq (D₁.map_id A)).symm := rfl

theorem D₁_pi_eq (A : PiCat.{w, v, u} R) :
    PiTwoCategory.pi (R := R) ((D₁Pseudo R).obj A) = (D₁Pseudo R).map (PiTwoCategory.pi (R := R) A) :=
  Underlying2.hom1_eq (Superfunctor.ext Associated.pi_eq_map_pi)

set_option backward.isDefEq.respectTransparency false in
variable (R) in
/-- **Brundan–Ellis, (5.3).** `𝔻₁` is a strict Π-2-functor: `j = 1` (`π̂ = 𝔻₁(Π, -1)`,
`Associated.pi_eq_map_pi`), and the axioms of Definition 5.2(ii) are `β_{F̂} = 𝔻₁ β_F`
(`Associated.β_map`) and `ξ̂ = 𝔻₁ ξ`. -/
def D₁PiTwoFunctor : PiTwoFunctor R (D₁Pseudo.{w, v, u} R) where
  map₂_add x y := PiSCat.hom₂_ext fun X => by
    simp
    ext <;> simp
  map₂_smul r x := PiSCat.hom₂_ext fun X => by
    simp
    ext <;> simp
  j A := eqToIso (D₁_pi_eq A)
  β_comm F := PiSCat.hom₂_ext fun X => by
    simp [D₁Pseudo_mapComp_inv, PiSCat.β_app_zero, PiSCat.β_app_one, Associated.β_map]
  ξ_comm A := PiSCat.hom₂_ext fun X => by
    simp [D₁Pseudo_mapComp_inv, D₁Pseudo_mapId_inv, PiSCat.ξ_app_zero, Associated.ξ_hom]
    rfl

/-! ## `𝔼₁ ∘ 𝔻₁ ≅ 𝕀` -/

@[simp] theorem comp₂_natTrans_app' {A B : PiCat.{w, v, u} R} {F G H : A ⟶ B} (x : F ⟶ G)
    (y : G ⟶ H) (X : A) :
    (Hom₂.natTrans (x ≫ y)).app X = (Hom₂.natTrans x).app X ≫ (Hom₂.natTrans y).app X := rfl

@[simp] theorem id₂_natTrans_app' {A B : PiCat.{w, v, u} R} (F : A ⟶ B) (X : A) :
    (Hom₂.natTrans (𝟙 F)).app X = 𝟙 _ := rfl

variable (R) in
/-- The component `A → E₁(D₁ A)` of the unit, as a 1-morphism of the bicategory `Π-ℭ𝔞𝔱`. -/
def unitHom (A : PiCat.{w, v, u} R) :
    (Pseudofunctor.id (PiCat.{w, v, u} R)).obj A ⟶ ((D₁Pseudo R).comp (PiSCat.E₁Pseudo R)).obj A :=
  (unitIsoApp A).hom

theorem E₁D₁_mapId_app (A : PiCat.{w, v, u} R) (X : A) :
    (Hom₂.natTrans (((D₁Pseudo R).comp (PiSCat.E₁Pseudo R)).mapId A).hom).app
      ((unitHom R A).toFunctor.obj X) = 𝟙 _ := by
  apply Underlying.hom_ext
  change (eqToHom (Underlying2.hom1_eq (D₁.map_id A)) : D₁hom (𝟙 A) ⟶ 𝟙 (D₁obj A)).1.app 0
    (⟨X⟩ : Associated R A) ≫ 𝟙 _ = 𝟙 _
  rw [PiSCat.eqToHom₂_app_zero, Category.comp_id]
  rfl

theorem E₁D₁_mapComp_app {A B C : PiCat.{w, v, u} R} (F : A ⟶ B) (G : B ⟶ C) (X : A) :
    (Hom₂.natTrans (((D₁Pseudo R).comp (PiSCat.E₁Pseudo R)).mapComp F G).hom).app
      ((unitHom R A).toFunctor.obj X) = 𝟙 _ := by
  apply Underlying.hom_ext
  change (eqToHom (Underlying2.hom1_eq (D₁.map_comp F G)) : D₁hom (F ≫ G) ⟶ D₁hom F ≫ D₁hom G).1.app 0
    (⟨X⟩ : Associated R A) ≫ 𝟙 _ = 𝟙 _
  rw [PiSCat.eqToHom₂_app_zero, Category.comp_id]
  rfl

theorem unit_naturality_eq {A B : PiCat.{w, v, u} R} (F : A ⟶ B) :
    (Pseudofunctor.id (PiCat.{w, v, u} R)).map F ≫ unitHom R B =
      unitHom R A ≫ ((D₁Pseudo R).comp (PiSCat.E₁Pseudo R)).map F :=
  (unitIso R).hom.naturality F

variable (R) in
/-- **Theorem 5.3, `𝔼₁ ∘ 𝔻₁ = 𝕀`.** The identification `A ≅ E₁(D₁ A)` of Lemma 5.1 as a strong
transformation `𝕀 ⇒ 𝔼₁ ∘ 𝔻₁` with identity naturality 2-morphisms. -/
def unitStrong : Pseudofunctor.StrongTrans (Pseudofunctor.id (PiCat.{w, v, u} R))
    ((D₁Pseudo R).comp (PiSCat.E₁Pseudo R)) where
  app A := unitHom R A
  naturality F := eqToIso (unit_naturality_eq F)
  naturality_naturality {a b f g} y := by
    ext X
    simp [eqToHom_natTrans_app]
    erw [eqToHom_refl, eqToHom_refl, Category.comp_id, Category.id_comp]
    rfl
  naturality_id A := by
    ext X
    simp only [Pseudofunctor.id_mapId, Iso.refl_hom, comp₂_natTrans_app',
      whiskerLeft_natTrans_app, leftUnitor_hom_natTrans_app, rightUnitor_inv_natTrans_app,
      eqToIso.hom, eqToHom_natTrans_app]
    erw [E₁D₁_mapId_app, whiskerRight_natTrans_app, id₂_natTrans_app']
    repeat erw [eqToHom_refl]
    repeat erw [CategoryTheory.Functor.map_id]
    change (𝟙 (⟨⟨X⟩⟩ : Underlying R (Associated R A)) ≫ 𝟙 _) = 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
    simp
  naturality_comp F G := by
    ext X
    simp only [Pseudofunctor.id_mapComp, Iso.refl_hom, comp₂_natTrans_app',
      whiskerLeft_natTrans_app, whiskerRight_natTrans_app,
      associator_hom_natTrans_app, associator_inv_natTrans_app, eqToIso.hom,
      eqToHom_natTrans_app]
    erw [E₁D₁_mapComp_app, whiskerRight_natTrans_app, id₂_natTrans_app']
    repeat erw [eqToHom_refl]
    repeat erw [CategoryTheory.Functor.map_id]
    repeat erw [Category.comp_id]
    rfl

@[simp] theorem unitStrong_app (A : PiCat.{w, v, u} R) : (unitStrong R).app A = unitHom R A := rfl

theorem unitStrong_naturality {A B : PiCat.{w, v, u} R} (F : A ⟶ B) :
    (unitStrong R).naturality F = eqToIso (unit_naturality_eq F) := rfl

theorem E₁D₁_j_app (A : PiCat.{w, v, u} R)
    (Y : (((D₁Pseudo R).comp (PiSCat.E₁Pseudo R)).obj A).carrier) :
    (Hom₂.natTrans (((D₁PiTwoFunctor R).comp (PiSCat.E₁PiTwoFunctor R)).j A).hom).app Y =
      𝟙 _ := by
  apply Underlying.hom_ext
  change 𝟙 _ ≫ (eqToHom (D₁_pi_eq A)).1.app 0 Y.obj = 𝟙 _
  rw [PiSCat.eqToHom₂_app_zero, Category.id_comp]
  rfl

theorem unitHom_β_app (A : PiCat.{w, v, u} R) (X : A) :
    (Hom₂.natTrans (PiTwoCategory.β (R := R) (unitHom R A)).hom).app X = 𝟙 _ := rfl

theorem unitStrong_isPiTwoNatural :
    (PiTwoFunctor.id R (PiCat.{w, v, u} R)).IsPiTwoNatural
      ((D₁PiTwoFunctor R).comp (PiSCat.E₁PiTwoFunctor R)) (unitStrong R).toOplax.toOplax :=
  fun A => by
    ext X
    erw [E₁D₁_j_app]
    simp only [comp₂_natTrans_app', PiTwoFunctor.id_j, Iso.refl_hom]
    erw [unitHom_β_app]
    repeat erw [Category.id_comp]
    erw [show (unitStrong R).toOplax.toOplax.naturality (PiTwoCategory.pi (R := R) A) =
      eqToHom (unit_naturality_eq _) from rfl, eqToHom_natTrans_app, eqToHom_refl]
    rfl

end PiCat

/-! ## `𝔻₁ ∘ 𝔼₁ ≅ 𝕀` -/

namespace PiSCat

open PiCat


variable {R : Type w} [CommRing R]

variable (R) in
/-- The component `T_A : D₁(E₁ A) → A` of the counit (the isomorphism of Lemma 5.1), as a
1-morphism of `E₂(Π-𝔖ℭ𝔞𝔱)`. -/
def counitHom (A : Underlying2 R (PiSCat.{w, v, u} R)) :
    ((E₁Pseudo R).comp (D₁Pseudo R)).obj A ⟶ (Pseudofunctor.id _).obj A :=
  Underlying2.hom1 (R := R) (counitIsoApp A.obj).hom

theorem id_mapComp_hom' {a b c : Underlying2 R (PiSCat.{w, v, u} R)} (F : a ⟶ b) (G : b ⟶ c) :
    ((Pseudofunctor.id (Underlying2 R (PiSCat.{w, v, u} R))).mapComp F G).hom = 𝟙 (F ≫ G) := rfl

theorem counit_naturality_eq {A B : Underlying2 R (PiSCat.{w, v, u} R)} (F : A ⟶ B) :
    ((E₁Pseudo R).comp (D₁Pseudo R)).map F ≫ counitHom R B =
      counitHom R A ≫ (Pseudofunctor.id _).map F :=
  Underlying2.hom1_eq ((counitIso R).hom.naturality F.obj)

theorem counitHom_obj (A : Underlying2 R (PiSCat.{w, v, u} R)) :
    (counitHom R A).obj = (counitIsoApp A.obj).hom := rfl

theorem E₁D₁_mapId_app' (A : Underlying2 R (PiSCat.{w, v, u} R))
    (X : (((E₁Pseudo R).comp (D₁Pseudo R)).obj A).obj.carrier) :
    (((E₁Pseudo R).comp (D₁Pseudo R)).mapId A).hom.1.app 0 X = 𝟙 _ := by
  erw [Pseudofunctor.comp_mapId, Iso.trans_hom, PiSCat.comp₂_app_zero, D₁Pseudo_mapId_hom,
    PiSCat.eqToHom₂_app_zero, PrelaxFunctor.map₂Iso_hom, D₁Strict_map₂, D₁map₂_app_zero,
    eqToHom_refl, Category.comp_id]
  rfl

theorem E₁D₁_mapComp_app' {A B C : Underlying2 R (PiSCat.{w, v, u} R)} (F : A ⟶ B) (G : B ⟶ C)
    (X : (((E₁Pseudo R).comp (D₁Pseudo R)).obj A).obj.carrier) :
    (((E₁Pseudo R).comp (D₁Pseudo R)).mapComp F G).hom.1.app 0 X = 𝟙 _ := by
  erw [Pseudofunctor.comp_mapComp, Iso.trans_hom, PiSCat.comp₂_app_zero, D₁Pseudo_mapComp_hom,
    PiSCat.eqToHom₂_app_zero, PrelaxFunctor.map₂Iso_hom, D₁Strict_map₂, D₁map₂_app_zero,
    eqToHom_refl, Category.comp_id]
  rfl

set_option maxHeartbeats 1000000 in
variable (R) in
/-- **Theorem 5.3, `𝔻₁ ∘ 𝔼₁ ≅ 𝕀`.** The isomorphisms `T_A` of Lemma 5.1 as a strong transformation
`𝔻₁ ∘ 𝔼₁ ⇒ 𝕀` with identity naturality 2-morphisms (`t = 1` in the proof of Theorem 5.3). -/
def counitStrong : Pseudofunctor.StrongTrans ((E₁Pseudo R).comp (D₁Pseudo R))
    (Pseudofunctor.id (Underlying2 R (PiSCat.{w, v, u} R))) where
  app A := counitHom R A
  naturality F := eqToIso (counit_naturality_eq F)
  naturality_naturality {a b f g} η := by
    apply hom₂_ext
    intro X
    erw [comp₂_app_zero, comp₂_app_zero, whiskerRight₂_app_zero, whiskerLeft₂_app_zero,
      eqToIso.hom, eqToIso.hom, eqToHom₂_app_zero (counit_naturality_eq f),
      eqToHom₂_app_zero (counit_naturality_eq g), eqToHom_refl, eqToHom_refl, Category.comp_id,
      Category.id_comp]
    obtain ⟨⟨X⟩⟩ := X
    change (Associated.T R b.obj.carrier).map
      (Associated.homMk ((Hom₂.natTrans ((E₁Pseudo R).map₂ η)).app ⟨X⟩) 0) = η.1.app 0 X
    exact Associated.T_map_homMk (A := b.obj.carrier) _
  naturality_id A := by
    apply hom₂_ext
    intro X
    erw [comp₂_app_zero, whiskerLeft₂_app_zero, eqToIso.hom,
      eqToHom₂_app_zero (counit_naturality_eq (𝟙 A)), Pseudofunctor.id_mapId, Iso.refl_hom,
      id₂_app_zero, eqToHom_refl, Category.id_comp]
    erw [comp₂_app_zero, comp₂_app_zero, whiskerRight₂_app_zero, E₁D₁_mapId_app',
      leftUnitor₂_hom_app_zero]
    obtain ⟨⟨X⟩⟩ := X
    change 𝟙 X = (Associated.T R A.obj.carrier).map
      (𝟙 (⟨⟨X⟩⟩ : Associated R (Underlying R A.obj.carrier))) ≫ 𝟙 X ≫ 𝟙 X
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
    exact (Category.id_comp _).symm
  naturality_comp {a b c} F G := by
    apply hom₂_ext
    intro X
    erw [comp₂_app_zero, whiskerLeft₂_app_zero, eqToIso.hom,
      eqToHom₂_app_zero (counit_naturality_eq (F ≫ G)), id_mapComp_hom', id₂_app_zero]
    erw [eqToHom_refl, Category.id_comp]
    erw [comp₂_app_zero, whiskerRight₂_app_zero, E₁D₁_mapComp_app', comp₂_app_zero,
      associator₂_hom_app_zero, comp₂_app_zero, whiskerLeft₂_app_zero, eqToIso.hom,
      eqToHom₂_app_zero (counit_naturality_eq G), comp₂_app_zero, associator₂_inv_app_zero,
      comp₂_app_zero, whiskerRight₂_app_zero, eqToIso.hom,
      eqToHom₂_app_zero (counit_naturality_eq F), associator₂_hom_app_zero]
    repeat erw [eqToHom_refl]
    obtain ⟨⟨X⟩⟩ := X
    change 𝟙 (G.obj.obj (F.obj.obj X)) = (Associated.T R c.obj.carrier).map
      (𝟙 (⟨⟨G.obj.obj (F.obj.obj X)⟩⟩ : Associated R (Underlying R c.obj.carrier))) ≫
        𝟙 (G.obj.obj (F.obj.obj X)) ≫ 𝟙 (G.obj.obj (F.obj.obj X)) ≫ 𝟙 (G.obj.obj (F.obj.obj X)) ≫
          G.obj.toFunctor.map (𝟙 (F.obj.obj X)) ≫ 𝟙 (G.obj.obj (F.obj.obj X))
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    simp only [Category.id_comp]
    exact (Category.id_comp _).symm

@[simp] theorem counitStrong_app (A : Underlying2 R (PiSCat.{w, v, u} R)) :
    (counitStrong R).app A = counitHom R A := rfl

theorem counitStrong_naturality {A B : Underlying2 R (PiSCat.{w, v, u} R)} (F : A ⟶ B) :
    (counitStrong R).naturality F = eqToIso (counit_naturality_eq F) := rfl

theorem counitHom_β_app (A : Underlying2 R (PiSCat.{w, v, u} R))
    (X : (((E₁Pseudo R).comp (D₁Pseudo R)).obj A).obj.carrier) :
    (PiTwoCategory.β (R := R) (counitHom R A)).hom.1.app 0 X = 𝟙 _ := by
  obtain ⟨⟨X⟩⟩ := X
  exact (PiSCat.β_app_zero (counitIsoApp A.obj).hom _).trans (Associated.β_T _)

theorem E₁D₁_j_app' (A : Underlying2 R (PiSCat.{w, v, u} R))
    (X : (((E₁Pseudo R).comp (D₁Pseudo R)).obj A).obj.carrier) :
    (((PiSCat.E₁PiTwoFunctor R).comp (D₁PiTwoFunctor R)).j A).hom.1.app 0 X = 𝟙 _ := by
  erw [Iso.trans_hom, PiSCat.comp₂_app_zero, PiSCat.eqToHom₂_app_zero (D₁_pi_eq _),
    PrelaxFunctor.map₂Iso_hom,
    D₁Strict_map₂, D₁map₂_app_zero, eqToHom_refl, Category.id_comp]
  rfl

/-- **Theorem 5.3, the coherence axiom of Definition 5.2(iii) for `(T, t)`**: the strong
transformation `𝔻₁ ∘ 𝔼₁ ⇒ 𝕀` is Π-2-natural (`β_{T_A} = 1`, `Associated.β_T`). -/
theorem counitStrong_isPiTwoNatural :
    ((PiSCat.E₁PiTwoFunctor R).comp (D₁PiTwoFunctor R)).IsPiTwoNatural
      (PiTwoFunctor.id R (Underlying2 R (PiSCat.{w, v, u} R))) (counitStrong R).toOplax.toOplax :=
  fun A => by
    apply hom₂_ext
    intro X
    erw [comp₂_app_zero, counitHom_β_app, comp₂_app_zero, whiskerRight₂_app_zero, E₁D₁_j_app',
      show (counitStrong R).toOplax.toOplax.naturality (PiTwoCategory.pi (R := R) A) =
        eqToHom (counit_naturality_eq _) from rfl,
      eqToHom₂_app_zero (counit_naturality_eq _), whiskerLeft₂_app_zero, PiTwoFunctor.id_j,
      Iso.refl_hom, id₂_app_zero]
    repeat erw [eqToHom_refl]
    obtain ⟨⟨X⟩⟩ := X
    change 𝟙 ((PiSupercategory.pi (R := R)).obj X) ≫ (Associated.T R A.obj.carrier).map
        (𝟙 (⟨⟨(PiSupercategory.pi (R := R)).obj X⟩⟩ : Associated R (Underlying R A.obj.carrier))) ≫
          𝟙 ((PiSupercategory.pi (R := R)).obj X) = 𝟙 ((PiSupercategory.pi (R := R)).obj X)
    rw [CategoryTheory.Functor.map_id]
    simp only [Category.id_comp]
    exact Category.id_comp _

theorem counitHom_inv (A : Underlying2 R (PiSCat.{w, v, u} R)) :
    counitHom R A ≫ (Underlying2.hom1 (R := R) (counitIsoApp A.obj).inv :
      (Pseudofunctor.id _).obj A ⟶ ((E₁Pseudo R).comp (D₁Pseudo R)).obj A) = 𝟙 _ ∧
    (Underlying2.hom1 (R := R) (counitIsoApp A.obj).inv :
      (Pseudofunctor.id _).obj A ⟶ ((E₁Pseudo R).comp (D₁Pseudo R)).obj A) ≫ counitHom R A = 𝟙 _ :=
  ⟨Underlying2.hom1_eq (counitIsoApp A.obj).hom_inv_id,
    Underlying2.hom1_eq (counitIsoApp A.obj).inv_hom_id⟩

end PiSCat


/-! ## Theorem 5.3 -/

namespace PiCat

open PiSCat

variable (R : Type w) [CommRing R]

/-- **Brundan–Ellis, Theorem 5.3.** The strict Π-2-functors `𝔻₁ : Π-ℭ𝔞𝔱 → E₂(Π-𝔖ℭ𝔞𝔱)`
(`PiCat.D₁PiTwoFunctor`) and `𝔼₁ : E₂(Π-𝔖ℭ𝔞𝔱) → Π-ℭ𝔞𝔱` (`PiSCat.E₁PiTwoFunctor`) are mutually
inverse Π-2-equivalences: `𝕀 ≅ 𝔼₁ ∘ 𝔻₁` and `𝔻₁ ∘ 𝔼₁ ≅ 𝕀` via Π-2-natural isomorphisms
(`PiCat.unitStrong`, `PiSCat.counitStrong`): strong transformations which are Π-2-natural
(Definition 5.2(iii)), whose naturality 2-morphisms are identities, and whose components are
isomorphisms (`A ≅ E₁(D₁ A)` and `T_A : D₁(E₁ A) ≅ A` of Lemma 5.1), so the composites are
isomorphic, not only equivalent, to the identities. The paper's `E₁ ∘ D₁ = I` holds up to the identification
`A ≅ E₁(D₁ A)` (the identity on objects and 1-morphisms of the underlying data). -/
theorem theorem53 :
    (PiTwoFunctor.id R (PiCat.{w, v, u} R)).IsPiTwoNatural
        ((D₁PiTwoFunctor R).comp (PiSCat.E₁PiTwoFunctor R)) (unitStrong R).toOplax.toOplax ∧
      (∀ {A B : PiCat.{w, v, u} R} (F : A ⟶ B),
        (unitStrong R).naturality F = eqToIso (unit_naturality_eq F)) ∧
      (∀ A : PiCat.{w, v, u} R, ∃ g : ((D₁Pseudo R).comp (PiSCat.E₁Pseudo R)).obj A ⟶ A,
        (unitStrong R).app A ≫ g = 𝟙 _ ∧ g ≫ (unitStrong R).app A = 𝟙 _) ∧
      ((PiSCat.E₁PiTwoFunctor R).comp (D₁PiTwoFunctor R)).IsPiTwoNatural
        (PiTwoFunctor.id R (Underlying2 R (PiSCat.{w, v, u} R))) (counitStrong R).toOplax.toOplax ∧
      (∀ {A B : Underlying2 R (PiSCat.{w, v, u} R)} (F : A ⟶ B),
        (counitStrong R).naturality F = eqToIso (counit_naturality_eq F)) ∧
      (∀ A : Underlying2 R (PiSCat.{w, v, u} R),
        ∃ g : A ⟶ ((PiSCat.E₁Pseudo R).comp (D₁Pseudo R)).obj A,
          (counitStrong R).app A ≫ g = 𝟙 _ ∧ g ≫ (counitStrong R).app A = 𝟙 _) :=
  ⟨unitStrong_isPiTwoNatural, fun _ => rfl,
    fun A => ⟨(unitIsoApp A).inv, (unitIsoApp A).hom_inv_id, (unitIsoApp A).inv_hom_id⟩,
    counitStrong_isPiTwoNatural, fun _ => rfl,
    fun A => ⟨_, (counitHom_inv A).1, (counitHom_inv A).2⟩⟩

end PiCat

end StringDiagrams

end
