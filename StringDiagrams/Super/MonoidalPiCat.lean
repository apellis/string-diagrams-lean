import StringDiagrams.Super.MonoidalAssociated
import StringDiagrams.Super.MonoidalEquivalence
import StringDiagrams.Super.PiCat

/-!
# The categories `Π-SMon` and `Π-Mon`, and Theorem 1.15(2)

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Definitions 1.4(ii), 1.12, 1.14, (1.9), Theorem 1.15 (second part) and Lemma 5.4 (one-object
case).

* `PiSMon R` is the category `Π-SMon` of (small, in fixed universes) monoidal
  Π-supercategories (Definition 1.12) and monoidal superfunctors (Definition 1.4(ii); they are
  not required to preserve `π` or `ζ`), with the composition `MonoidalSuperfunctor.comp`.
* `PiMon R` is the category `Π-Mon` of monoidal Π-categories and monoidal Π-functors
  (Definition 1.14(i), (ii)); composition `MonoidalPiFunctor.comp` has `j_{GF} = G(j_F) ∘ j_G`.
* `PiSMon.E : PiSMon R ⥤ PiMon R` is the functor (2) of (1.9):
  `(A, π, ζ) ↦ (A̲, π, β, ξ)`, `F ↦ (F̲, c, i, j = (F ζ_A)⁻¹ ∘ i ∘ ζ_B)`.
* `PiMon.D : PiMon R ⥤ PiSMon R` is the associated monoidal Π-supercategory construction
  (the one-object case of `D₂` in (5.5), with the corrected signs of
  `StringDiagrams.Super.MonoidalAssociated`): `A ↦ Â`, `(F, j) ↦ F̂`.
* **Theorem 1.15(2) / Lemma 5.4 (one object).** `PiMon.equivalence : PiMon R ≌ PiSMon R`, with
  functor `D` and inverse `E`; the functor (2) of (1.9) is an equivalence of categories
  (instance `PiSMon.E.IsEquivalence`).

## Literal statement vs. formalization

The paper proves `E ∘ D = I` and `D ∘ E ≅ I` (Lemma 5.4, one-object case). Here `E(D(A))` is
the monoidal Π-category `Underlying R (Associated R A)`, which is a different type from `A`, so
`E ∘ D = I` is formalized as the natural isomorphism `PiMon.unitIso : 𝟭 ≅ D ⋙ E` whose
components are the identifications `Associated.unit` / `Associated.counit` (strict monoidal
Π-functors with `j = 1`, mutually inverse on the nose). `D ∘ E ≅ I` is
`PiMon.counitIso : E ⋙ D ≅ 𝟭` with components the isomorphisms `T_A` (`Associated.Tmon`,
strict monoidal superfunctors with strict monoidal inverses). Both are isomorphisms in the
1-categories `Π-Mon`, `Π-SMon` (equalities of functors and coherence data), which is stronger
than an equivalence up to monoidal (super)natural isomorphism.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory MonoidalCategory Supercategory

universe w v u w₁ w₂ w₃ w₄ w₅ w₆

/-! ## Identities and composition of monoidal Π-functors -/

namespace MonoidalPiFunctor

variable {R : Type w} [CommRing R]
  {C : Type w₁} [Category.{w₂} C] [Preadditive C] [Linear R C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear R C] [MonoidalPiCategory R C]
  {D : Type w₃} [Category.{w₄} D] [Preadditive D] [Linear R D] [MonoidalCategory D]
  [MonoidalPreadditive D] [MonoidalLinear R D] [MonoidalPiCategory R D]
  {E : Type w₅} [Category.{w₆} E] [Preadditive E] [Linear R E] [MonoidalCategory E]
  [MonoidalPreadditive E] [MonoidalLinear R E] [MonoidalPiCategory R E]

open Functor.LaxMonoidal

/-- Two monoidal Π-functor structures on the same monoidal functor with the same `j` are
equal. -/
theorem ext {F : C ⥤ D} [F.Monoidal] {hF hG : MonoidalPiFunctor R F}
    (h : hF.j.hom = hG.j.hom) : hF = hG := by
  have hj : hF.j = hG.j := Iso.ext h
  cases hF
  cases hG
  dsimp only at hj
  subst hj
  rfl

variable (R C) in
/-- The identity functor is a monoidal Π-functor with `j = 1`. -/
@[simps]
def id : MonoidalPiFunctor R (𝟭 C) where
  j := Iso.refl _
  β_comm X := by simp
  ξ_comm := by simp

/-- The composite of monoidal Π-functors `F : C → D` and `G : D → E` (in Lean `F ⋙ G`), with
`j_{GF} := G(j_F) ∘ j_G`. -/
@[simps]
def comp {F : C ⥤ D} [F.Monoidal] {G : D ⥤ E} [G.Monoidal] (hF : MonoidalPiFunctor R F)
    (hG : MonoidalPiFunctor R G) : MonoidalPiFunctor R (F ⋙ G) where
  j := hG.j ≪≫ G.mapIso hF.j
  β_comm X := by
    have h1 := hF.β_comm X
    have h2 := hG.β_comm (F.obj X)
    simp only [Functor.comp_obj, Iso.trans_hom, Functor.mapIso_hom, comp_whiskerRight,
      comp_μ, Functor.comp_map, Category.assoc, MonoidalCategory.whiskerLeft_comp]
    rw [μ_natural_left_assoc, ← G.map_comp, ← G.map_comp, h1, G.map_comp, G.map_comp,
      reassoc_of% h2, μ_natural_right_assoc]
  ξ_comm := by
    have h1 := hF.ξ_comm
    have h2 := hG.ξ_comm
    simp only [Functor.comp_obj, Iso.trans_hom, Functor.mapIso_hom, comp_ε, comp_μ,
      Functor.comp_map, Category.assoc]
    rw [reassoc_of% h2, ← G.map_comp, h1, G.map_comp, G.map_comp,
      ← MonoidalCategory.tensorHom_comp_tensorHom, Category.assoc, μ_natural_assoc]

end MonoidalPiFunctor

/-! ## Monoidal superfunctors: extensionality -/

namespace MonoidalSuperfunctor

variable {R : Type w} [CommRing R]
  {C : Type w₁} [Category.{w₂} C] [Preadditive C] [Linear R C] [Supercategory R C]
  [MonoidalCategoryStruct C]
  {D : Type w₃} [Category.{w₄} D] [Preadditive D] [Linear R D] [Supercategory R D]
  [MonoidalCategoryStruct D]

/-- Two monoidal superfunctor structures on the same superfunctor with the same coherence maps
are equal. -/
theorem ext {F : C ⥤ D} [F.Additive] [F.Linear R] [IsSuperfunctor R F]
    {cF cG : MonoidalSuperfunctor R F} (hμ : ∀ X Y, (cF.μIso X Y).hom = (cG.μIso X Y).hom)
    (hε : cF.εIso.hom = cG.εIso.hom) : cF = cG := by
  have hμ' : cF.μIso = cG.μIso := funext₂ fun X Y => Iso.ext (hμ X Y)
  have hε' : cF.εIso = cG.εIso := Iso.ext hε
  cases cF
  cases cG
  dsimp only at hμ' hε'
  subst hμ' hε'
  rfl

end MonoidalSuperfunctor

/-! ## The category `Π-Mon` -/

variable {R : Type w} [CommRing R]

variable (R) in
/-- A monoidal Π-category over `R` (Brundan–Ellis, Definition 1.14(i)), bundled: an `R`-linear
monoidal category with a monoidal Π-category structure. -/
structure PiMon where
  /-- The objects. -/
  carrier : Type u
  [str : Category.{v} carrier]
  [preadditive : Preadditive carrier]
  [linear : Linear R carrier]
  [monoidal : MonoidalCategory carrier]
  [monoidalPreadditive : MonoidalPreadditive carrier]
  [monoidalLinear : MonoidalLinear R carrier]
  [pi : MonoidalPiCategory R carrier]

namespace PiMon

attribute [instance] str preadditive linear monoidal monoidalPreadditive monoidalLinear pi

instance : CoeSort (PiMon.{w, v, u} R) (Type u) := ⟨PiMon.carrier⟩

variable (R) in
/-- The bundled monoidal Π-category of a monoidal Π-category. -/
abbrev of (C : Type u) [Category.{v} C] [Preadditive C] [Linear R C] [MonoidalCategory C]
    [MonoidalPreadditive C] [MonoidalLinear R C] [MonoidalPiCategory R C] :
    PiMon.{w, v, u} R :=
  ⟨C⟩

/-- A morphism of `Π-Mon`: a linear monoidal Π-functor (Brundan–Ellis, Definition 1.14(ii)). -/
structure Hom (A B : PiMon.{w, v, u} R) where
  /-- The underlying functor. -/
  toFunctor : A ⥤ B
  [additive : toFunctor.Additive]
  [linear : toFunctor.Linear R]
  /-- The monoidal structure `(c, i)`. -/
  [monoidal : toFunctor.Monoidal]
  /-- The coherence map `j`. -/
  piFunctor : MonoidalPiFunctor R toFunctor

attribute [instance] Hom.additive Hom.linear Hom.monoidal

open Functor.LaxMonoidal in
/-- Two monoidal Π-functors with the same underlying functor, the same coherence maps `c`, `i`
and the same `j` are equal. -/
theorem Hom.ext {A B : PiMon.{w, v, u} R} {F G : Hom A B} (h : F.toFunctor = G.toFunctor)
    (hε : HEq (ε F.toFunctor) (ε G.toFunctor))
    (hμ : ∀ X Y, HEq (μ F.toFunctor X Y) (μ G.toFunctor X Y))
    (hj : HEq F.piFunctor.j.hom G.piFunctor.j.hom) : F = G := by
  cases F with | mk F pF =>
  cases G with | mk G pG =>
  dsimp only at h hε hμ hj
  subst h
  rename_i _ _ mF _ _ mG
  obtain rfl : mF = mG := Functor.Monoidal.toLaxMonoidal_injective _
    (Functor.LaxMonoidal.ext (eq_of_heq hε) (funext₂ fun X Y => eq_of_heq (hμ X Y)))
  obtain rfl : pF = pG := MonoidalPiFunctor.ext (eq_of_heq hj)
  rfl

/-- The category `Π-Mon` of monoidal Π-categories and monoidal Π-functors (Brundan–Ellis,
after Definition 1.14). -/
instance : Category (PiMon.{w, v, u} R) where
  Hom := Hom
  id A := ⟨𝟭 A, MonoidalPiFunctor.id R A⟩
  comp F G := ⟨F.toFunctor ⋙ G.toFunctor, F.piFunctor.comp G.piFunctor⟩
  id_comp F := Hom.ext rfl (heq_of_eq (by simp)) (fun _ _ => heq_of_eq (by simp))
    (heq_of_eq (by simp))
  comp_id F := Hom.ext rfl (heq_of_eq (by simp)) (fun _ _ => heq_of_eq (by simp))
    (heq_of_eq (by simp))
  assoc F G H := Hom.ext rfl (heq_of_eq (by simp)) (fun _ _ => heq_of_eq (by simp))
    (heq_of_eq (by simp))

variable {A B E : PiMon.{w, v, u} R}

theorem hom_def : (A ⟶ B) = Hom A B := rfl

@[simp] theorem id_toFunctor : (𝟙 A : A ⟶ A).toFunctor = 𝟭 A := rfl

@[simp] theorem comp_toFunctor (F : A ⟶ B) (G : B ⟶ E) :
    (F ≫ G).toFunctor = F.toFunctor ⋙ G.toFunctor := rfl

@[simp] theorem id_piFunctor : (𝟙 A : A ⟶ A).piFunctor = MonoidalPiFunctor.id R A := rfl

@[simp] theorem comp_piFunctor (F : A ⟶ B) (G : B ⟶ E) :
    (F ≫ G).piFunctor = F.piFunctor.comp G.piFunctor := rfl

end PiMon

/-! ## The category `Π-SMon` -/

variable (R) in
/-- A monoidal Π-supercategory over `R` (Brundan–Ellis, Definition 1.12), bundled: a
supercategory with a monoidal supercategory structure and a monoidal Π-supercategory
structure `(π, ζ)`. -/
structure PiSMon extends SCat.{w, v, u} R where
  [monoidalStruct : MonoidalCategoryStruct carrier]
  [monoidal : MonoidalSupercategory R carrier]
  [pi : MonoidalPiSupercategory R carrier]

namespace PiSMon

attribute [instance] monoidalStruct monoidal pi

instance : CoeSort (PiSMon.{w, v, u} R) (Type u) := ⟨fun A => A.carrier⟩

variable (R) in
/-- The bundled monoidal Π-supercategory of a monoidal Π-supercategory. -/
abbrev of (C : Type u) [Category.{v} C] [Preadditive C] [Linear R C] [Supercategory R C]
    [MonoidalCategoryStruct C] [MonoidalSupercategory R C] [MonoidalPiSupercategory R C] :
    PiSMon.{w, v, u} R :=
  ⟨SCat.of R C⟩

/-- A morphism of `Π-SMon`: a monoidal superfunctor (Brundan–Ellis, Definition 1.4(ii)); it
need not preserve `π` or `ζ`. -/
structure Hom (A B : PiSMon.{w, v, u} R) where
  /-- The underlying functor. -/
  toFunctor : A ⥤ B
  [additive : toFunctor.Additive]
  [linear : toFunctor.Linear R]
  [isSuperfunctor : IsSuperfunctor R toFunctor]
  /-- The monoidal structure `(c, i)`. -/
  monoidal : MonoidalSuperfunctor R toFunctor

attribute [instance] Hom.additive Hom.linear Hom.isSuperfunctor

/-- Two monoidal superfunctors with the same underlying functor and the same coherence maps
are equal. -/
theorem Hom.ext {A B : PiSMon.{w, v, u} R} {F G : Hom A B} (h : F.toFunctor = G.toFunctor)
    (hμ : ∀ X Y, HEq (F.monoidal.μIso X Y).hom (G.monoidal.μIso X Y).hom)
    (hε : HEq F.monoidal.εIso.hom G.monoidal.εIso.hom) : F = G := by
  cases F with | mk F cF =>
  cases G with | mk G cG =>
  dsimp only at h hμ hε
  subst h
  obtain rfl : cF = cG :=
    MonoidalSuperfunctor.ext (fun X Y => eq_of_heq (hμ X Y)) (eq_of_heq hε)
  rfl

/-- The category `Π-SMon` of monoidal Π-supercategories and monoidal superfunctors
(Brundan–Ellis, after Definition 1.14). -/
instance : Category (PiSMon.{w, v, u} R) where
  Hom := Hom
  id A := ⟨𝟭 A, MonoidalSuperfunctor.id (R := R)⟩
  comp F G := ⟨F.toFunctor ⋙ G.toFunctor, F.monoidal.comp G.monoidal⟩
  id_comp F := Hom.ext rfl (fun _ _ => heq_of_eq (by simp [MonoidalSuperfunctor.id]))
    (heq_of_eq (by simp [MonoidalSuperfunctor.id]))
  comp_id F := Hom.ext rfl (fun _ _ => heq_of_eq (by simp [MonoidalSuperfunctor.id]))
    (heq_of_eq (by simp [MonoidalSuperfunctor.id]))
  assoc F G H := Hom.ext rfl (fun _ _ => heq_of_eq (by simp)) (heq_of_eq (by simp))

variable {A B E : PiSMon.{w, v, u} R}

theorem hom_def : (A ⟶ B) = Hom A B := rfl

@[simp] theorem id_toFunctor : (𝟙 A : A ⟶ A).toFunctor = 𝟭 A := rfl

@[simp] theorem comp_toFunctor (F : A ⟶ B) (G : B ⟶ E) :
    (F ≫ G).toFunctor = F.toFunctor ⋙ G.toFunctor := rfl

@[simp] theorem id_monoidal : (𝟙 A : A ⟶ A).monoidal = MonoidalSuperfunctor.id (R := R) := rfl

@[simp] theorem comp_monoidal (F : A ⟶ B) (G : B ⟶ E) :
    (F ≫ G).monoidal = F.monoidal.comp G.monoidal := rfl

end PiSMon

/-! ## The functors `E` and `D` -/

namespace PiSMon

open Functor.LaxMonoidal

/-- **Brundan–Ellis, (1.9), functor (2).** The functor `E : Π-SMon → Π-Mon`,
`(A, π, ζ) ↦ (A̲, π, β, ξ)`, `F ↦ (F̲, c, i, j)` with `j := (F ζ_A)⁻¹ ∘ i ∘ ζ_B`. -/
@[simps obj]
def E : PiSMon.{w, v, u} R ⥤ PiMon.{w, v, u} R where
  obj A := PiMon.of R (Underlying R A)
  map F :=
    { toFunctor := Underlying.map F.toFunctor
      monoidal := (MonoidalSuperfunctor.underlyingCoreMonoidal F.monoidal).toMonoidal
      piFunctor := F.monoidal.toMonoidalPiFunctor }
  map_id A := PiMon.Hom.ext rfl (heq_of_eq (Underlying.hom_ext rfl))
    (fun _ _ => heq_of_eq (Underlying.hom_ext rfl))
    (heq_of_eq (Underlying.hom_ext (by
      change (MonoidalSuperfunctor.jIso (MonoidalSuperfunctor.id (R := R) (C := A.carrier))).hom =
        𝟙 _
      simp [MonoidalSuperfunctor.jIso_hom, MonoidalSuperfunctor.id])))
  map_comp {A B C} F G := PiMon.Hom.ext rfl (heq_of_eq (Underlying.hom_ext rfl))
    (fun _ _ => heq_of_eq (Underlying.hom_ext rfl))
    (heq_of_eq (Underlying.hom_ext (by
      change (MonoidalSuperfunctor.jIso (F.monoidal.comp G.monoidal)).hom =
        (MonoidalSuperfunctor.jIso G.monoidal).hom ≫
          G.toFunctor.map (MonoidalSuperfunctor.jIso F.monoidal).hom
      simp only [MonoidalSuperfunctor.jIso_hom, MonoidalSuperfunctor.comp_εIso, Iso.trans_hom,
        Functor.mapIso_hom, Functor.comp_obj, Functor.comp_map, Functor.map_comp,
        Category.assoc]
      rw [← G.toFunctor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
        Category.id_comp])))

end PiSMon

namespace Associated

section MapMonoidal

variable {C : Type w₁} [Category.{w₂} C] [Preadditive C] [Linear R C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear R C] [MonoidalPiCategory R C]
  {D : Type w₃} [Category.{w₄} D] [Preadditive D] [Linear R D] [MonoidalCategory D]
  [MonoidalPreadditive D] [MonoidalLinear R D] [MonoidalPiCategory R D]
  {E : Type w₅} [Category.{w₆} E] [Preadditive E] [Linear R E] [MonoidalCategory E]
  [MonoidalPreadditive E] [MonoidalLinear R E] [MonoidalPiCategory R E]

attribute [local instance] MonoidalPiCategory.toPiCategory

open Functor.LaxMonoidal

set_option backward.isDefEq.respectTransparency false in
variable (R C) in
/-- `D` preserves identities on the coherence map `c`. -/
theorem mapMonoidal_id_μIso_hom (X Y : Associated R C) :
    ((mapMonoidal (MonoidalPiFunctor.id R C)).μIso X Y).hom = 𝟙 _ := by
  ext <;> simp [mapMonoidal]
  rfl

set_option backward.isDefEq.respectTransparency false in
variable (R C) in
/-- `D` preserves identities on the coherence map `i`. -/
theorem mapMonoidal_id_εIso_hom :
    (mapMonoidal (MonoidalPiFunctor.id R C)).εIso.hom = 𝟙 _ := by
  ext <;> simp [mapMonoidal]

variable {F : C ⥤ D} [F.Additive] [F.Linear R] [F.Monoidal] {G : D ⥤ E} [G.Additive]
  [G.Linear R] [G.Monoidal] (hF : MonoidalPiFunctor R F) (hG : MonoidalPiFunctor R G)

set_option backward.isDefEq.respectTransparency false in
/-- `D` preserves composites on the coherence map `c`. -/
theorem mapMonoidal_comp_μIso_hom (X Y : Associated R C) :
    ((mapMonoidal (hF.comp hG)).μIso X Y).hom =
      ((mapMonoidal hG).μIso ((map (hF.toPiFunctor R)).obj X)
        ((map (hF.toPiFunctor R)).obj Y)).hom ≫
        (map (hG.toPiFunctor R)).map ((mapMonoidal hF).μIso X Y).hom := by
  ext <;> simp [mapMonoidal]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- `D` preserves composites on the coherence map `i`. -/
theorem mapMonoidal_comp_εIso_hom :
    (mapMonoidal (hF.comp hG)).εIso.hom =
      (mapMonoidal hG).εIso.hom ≫ (map (hG.toPiFunctor R)).map (mapMonoidal hF).εIso.hom := by
  ext <;> simp [mapMonoidal]

end MapMonoidal

end Associated

namespace PiMon

attribute [local instance] MonoidalPiCategory.toPiCategory

open Functor.LaxMonoidal

variable {A B : PiMon.{w, v, u} R}

/-- The Π-functor underlying the identity monoidal Π-functor is the identity. -/
theorem toPiFunctor_id :
    (MonoidalPiFunctor.id R A).toPiFunctor R = PiFunctor.id R A :=
  PiFunctor.ext fun X => by
    simp [MonoidalPiFunctor.βF_hom]

/-- The Π-functor underlying a composite of monoidal Π-functors is the composite. -/
theorem toPiFunctor_comp {E : PiMon.{w, v, u} R} (F : A ⟶ B) (G : B ⟶ E) :
    (F ≫ G).piFunctor.toPiFunctor R =
      (F.piFunctor.toPiFunctor R).comp (G.piFunctor.toPiFunctor R) :=
  PiFunctor.ext fun X => by
    simp only [comp_piFunctor, MonoidalPiFunctor.toPiFunctor_β_hom_app,
      MonoidalPiFunctor.βF_hom, PiFunctor.comp_β, NatIso.ofComponents_hom_app, Iso.trans_hom,
      Iso.app_hom, Functor.mapIso_hom, MonoidalPiFunctor.comp_j, comp_toFunctor,
      Functor.comp_obj, comp_μ, comp_whiskerRight, Category.assoc, Functor.map_comp]
    rw [μ_natural_left_assoc]

/-- **Brundan–Ellis, Theorem 1.15, the inverse of (2).** The functor `D : Π-Mon → Π-SMon`,
`(A, π, β, ξ) ↦ (Â, π, ζ)`, `(F, c, i, j) ↦ F̂` (the one-object case of `D₂` in (5.5), with the
corrected signs of `StringDiagrams.Super.MonoidalAssociated`). -/
@[simps obj]
def D : PiMon.{w, v, u} R ⥤ PiSMon.{w, v, u} R where
  obj A := PiSMon.of R (Associated R A)
  map F := ⟨Associated.map (F.piFunctor.toPiFunctor R), Associated.mapMonoidal F.piFunctor⟩
  map_id A := PiSMon.Hom.ext (by
      change Associated.map ((MonoidalPiFunctor.id R A).toPiFunctor R) = _
      rw [toPiFunctor_id]
      exact Associated.map_id)
    (fun X Y => heq_of_eq (Associated.mapMonoidal_id_μIso_hom R A X Y))
    (heq_of_eq (Associated.mapMonoidal_id_εIso_hom R A))
  map_comp F G := PiSMon.Hom.ext (by
      change Associated.map ((F ≫ G).piFunctor.toPiFunctor R) = _
      rw [toPiFunctor_comp]
      exact Associated.map_comp _ _)
    (fun X Y => heq_of_eq (Associated.mapMonoidal_comp_μIso_hom F.piFunctor G.piFunctor X Y))
    (heq_of_eq (Associated.mapMonoidal_comp_εIso_hom F.piFunctor G.piFunctor))

end PiMon

/-! ## Theorem 1.15(2): `E` is an equivalence -/

namespace Associated

section Counit

variable {C : Type w₁} [Category.{w₂} C] [Preadditive C] [Linear R C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalLinear R C] [MonoidalPiCategory R C]
  {D : Type w₃} [Category.{w₄} D] [Preadditive D] [Linear R D] [MonoidalCategory D]
  [MonoidalPreadditive D] [MonoidalLinear R D] [MonoidalPiCategory R D]

attribute [local instance] MonoidalPiCategory.toPiCategory

open Functor.LaxMonoidal

set_option backward.isDefEq.respectTransparency false in
variable (R C) in
/-- The identification `counit : E(D(A)) ⥤ A`, `(f, 0) ↦ f`, is strictly monoidal. -/
def counitCoreMonoidal : (counit R C).CoreMonoidal where
  εIso := Iso.refl _
  μIso _ _ := Iso.refl _
  μIso_hom_natural_left f X' := by
    change f.1.1 ▷ X'.obj.obj ≫ 𝟙 _ = 𝟙 _ ≫ (f.1 ▷ X'.obj).1
    simp
  μIso_hom_natural_right X' f := by
    change X'.obj.obj ◁ f.1.1 ≫ 𝟙 _ = 𝟙 _ ≫ (X'.obj ◁ f.1).1
    simp
  associativity X Y Z := by
    change 𝟙 _ ▷ _ ≫ 𝟙 _ ≫ (α_ X.obj Y.obj Z.obj).hom.1 = _ ≫ _ ◁ 𝟙 _ ≫ 𝟙 _
    simp
    rfl
  left_unitality X := by
    change _ = 𝟙 _ ▷ _ ≫ 𝟙 _ ≫ (λ_ X.obj).hom.1
    simp
    rfl
  right_unitality X := by
    change _ = _ ◁ 𝟙 _ ≫ 𝟙 _ ≫ (ρ_ X.obj).hom.1
    simp
    rfl

instance counitMonoidal : (counit R C).Monoidal := (counitCoreMonoidal R C).toMonoidal

@[simp] theorem counit_ε : ε (counit R C) = 𝟙 _ := rfl

@[simp] theorem counit_μ (X Y : Underlying R (Associated R C)) : μ (counit R C) X Y = 𝟙 _ := rfl

set_option backward.isDefEq.respectTransparency false in
variable (R C) in
/-- **`E ∘ D = I`.** The identification `counit : E(D(A)) ⥤ A` is a (strict) monoidal
Π-functor with `j = 1`. -/
def counitMonoidalPiFunctor : MonoidalPiFunctor R (counit R C) where
  j := Iso.refl _
  β_comm X := by
    change 𝟙 _ ▷ _ ≫ 𝟙 _ ≫ (MonoidalPiSupercategory.β (R := R) X.obj).hom.1 =
      _ ≫ _ ◁ 𝟙 _ ≫ 𝟙 _
    rw [β_hom_eq]
    simp
    rfl
  ξ_comm := by
    change _ ≫ 𝟙 _ = (𝟙 _ ⊗ₘ 𝟙 _) ≫ 𝟙 _ ≫
      (MonoidalPiSupercategory.ξ (R := R) (C := Associated R C)).hom.1
    rw [ξ_hom_eq]
    simp

set_option backward.isDefEq.respectTransparency false in
variable (R C) in
theorem unit_comp_counit_ε : ε (unit R C ⋙ counit R C) = 𝟙 _ := by
  simp

set_option backward.isDefEq.respectTransparency false in
variable (R C) in
theorem unit_comp_counit_μ (X Y : C) : μ (unit R C ⋙ counit R C) X Y = 𝟙 _ := by
  simp

set_option backward.isDefEq.respectTransparency false in
variable (R C) in
theorem counit_comp_unit_ε : ε (counit R C ⋙ unit R C) = 𝟙 _ := by
  simp

set_option backward.isDefEq.respectTransparency false in
variable (R C) in
theorem counit_comp_unit_μ (X Y : Underlying R (Associated R C)) :
    μ (counit R C ⋙ unit R C) X Y = 𝟙 _ := by
  simp

variable {F : C ⥤ D} [F.Additive] [F.Linear R] [F.Monoidal] (hF : MonoidalPiFunctor R F)

set_option backward.isDefEq.respectTransparency false in
/-- **`E ∘ D = I` on morphisms**, coherence map `i`. -/
theorem unit_comp_map_ε :
    letI := (MonoidalSuperfunctor.underlyingCoreMonoidal (mapMonoidal hF)).toMonoidal
    ε (F ⋙ unit R D) = ε (unit R C ⋙ Underlying.map (map (hF.toPiFunctor R))) := by
  ext
  · simp
    rfl
  · simp
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- **`E ∘ D = I` on morphisms**, coherence map `c`. -/
theorem unit_comp_map_μ (X Y : C) :
    letI := (MonoidalSuperfunctor.underlyingCoreMonoidal (mapMonoidal hF)).toMonoidal
    μ (F ⋙ unit R D) X Y = μ (unit R C ⋙ Underlying.map (map (hF.toPiFunctor R))) X Y := by
  ext
  · simp
    rfl
  · simp
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- **`E ∘ D = I` on morphisms**, coherence map `j` (from `jIso_mapMonoidal_hom`). -/
theorem unit_comp_map_j :
    letI := (MonoidalSuperfunctor.underlyingCoreMonoidal (mapMonoidal hF)).toMonoidal
    (hF.comp (unitMonoidalPiFunctor (R := R) (D := D))).j.hom =
      ((unitMonoidalPiFunctor (R := R) (D := C)).comp
        (mapMonoidal hF).toMonoidalPiFunctor).j.hom := by
  ext
  · simp [MonoidalSuperfunctor.toMonoidalPiFunctor, jIso_mapMonoidal_hom, unitMonoidalPiFunctor]
  · simp [MonoidalSuperfunctor.toMonoidalPiFunctor, jIso_mapMonoidal_hom, unitMonoidalPiFunctor]

end Counit

section TmonInv

variable {A : Type w₁} [Category.{w₂} A] [Preadditive A] [Linear R A] [Supercategory R A]
  [MonoidalCategoryStruct A] [MonoidalSupercategory R A] [MonoidalPiSupercategory R A]
  {B : Type w₃} [Category.{w₄} B] [Preadditive B] [Linear R B] [Supercategory R B]
  [MonoidalCategoryStruct B] [MonoidalSupercategory R B] [MonoidalPiSupercategory R B]

attribute [local instance] MonoidalPiCategory.toPiCategory

set_option backward.isDefEq.respectTransparency false in
instance : (TmonInv R A).Additive where
  map_add {X Y f g} := Tmon_map_injective (by
    rw [Tmon_map_TmonInv_map, Functor.map_add, Tmon_map_TmonInv_map, Tmon_map_TmonInv_map])

set_option backward.isDefEq.respectTransparency false in
instance : (TmonInv R A).Linear R where
  map_smul {X Y} f r := Tmon_map_injective (by
    rw [Tmon_map_TmonInv_map, Functor.map_smul, Tmon_map_TmonInv_map])

set_option backward.isDefEq.respectTransparency false in
instance : IsSuperfunctor R (TmonInv R A) where
  map_mem {X Y p f} hf := by
    rcases parity_eq_zero_or_one p with rfl | rfl
    · rw [mem_parity_zero]
      exact Subtype.ext (by
        change proj R 1 f ≫ _ = 0
        rw [proj_of_mem_ne hf (by decide), Limits.zero_comp])
    · rw [mem_parity_one]
      exact Subtype.ext (by
        change proj R 0 f = 0
        exact proj_of_mem_ne hf (by decide))

set_option backward.isDefEq.respectTransparency false in
theorem TmonInv_map_associator (X Y Z : A) :
    (TmonInv R A).map (α_ X Y Z).hom =
      (α_ ((TmonInv R A).obj X) ((TmonInv R A).obj Y) ((TmonInv R A).obj Z)).hom :=
  Tmon_map_injective (by rw [Tmon_map_TmonInv_map]; simp [Tmon_map]; rfl)

set_option backward.isDefEq.respectTransparency false in
theorem TmonInv_map_leftUnitor (X : A) :
    (TmonInv R A).map (λ_ X).hom = (λ_ ((TmonInv R A).obj X)).hom :=
  Tmon_map_injective (by rw [Tmon_map_TmonInv_map]; simp [Tmon_map]; rfl)

set_option backward.isDefEq.respectTransparency false in
theorem TmonInv_map_rightUnitor (X : A) :
    (TmonInv R A).map (ρ_ X).hom = (ρ_ ((TmonInv R A).obj X)).hom :=
  Tmon_map_injective (by rw [Tmon_map_TmonInv_map]; simp [Tmon_map]; rfl)

set_option backward.isDefEq.respectTransparency false in
variable (R A) in
/-- **Theorem 1.15, `D ∘ E ≅ I`:** the inverse `T_A⁻¹` of `T_A` is a strict monoidal
superfunctor. -/
def TmonInvMonoidal : MonoidalSuperfunctor R (TmonInv R A) where
  μIso _ _ := Iso.refl _
  εIso := Iso.refl _
  μ_mem _ _ := id_mem _
  ε_mem := id_mem _
  μ_natural_left f X' := Tmon_map_injective (by
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp, Tmon_map_whiskerRight,
      Tmon_map_TmonInv_map]
    rfl)
  μ_natural_right X' f := Tmon_map_injective (by
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp, Tmon_map_whiskerLeft,
      Tmon_map_TmonInv_map]
    rfl)
  associativity X Y Z := by
    simp [MonoidalSupercategory.id_whiskerRight (R := R),
      MonoidalSupercategory.whiskerLeft_id (R := R), TmonInv_map_associator]
  left_unitality X := by
    simp [MonoidalSupercategory.id_whiskerRight (R := R), TmonInv_map_leftUnitor]
  right_unitality X := by
    simp [MonoidalSupercategory.whiskerLeft_id (R := R), TmonInv_map_rightUnitor]

set_option backward.isDefEq.respectTransparency false in
theorem Tmon_comp_TmonInv_μIso_hom (X Y : Associated R (Underlying R A)) :
    (((TmonMonoidal (R := R) (A := A)).comp (TmonInvMonoidal R A)).μIso X Y).hom = 𝟙 _ := by
  simp [TmonMonoidal, TmonInvMonoidal]

set_option backward.isDefEq.respectTransparency false in
theorem Tmon_comp_TmonInv_εIso_hom :
    ((TmonMonoidal (R := R) (A := A)).comp (TmonInvMonoidal R A)).εIso.hom = 𝟙 _ := by
  simp [TmonMonoidal, TmonInvMonoidal]

set_option backward.isDefEq.respectTransparency false in
theorem TmonInv_comp_Tmon_μIso_hom (X Y : A) :
    (((TmonInvMonoidal R A).comp (TmonMonoidal (R := R) (A := A))).μIso X Y).hom = 𝟙 _ := by
  simp [TmonMonoidal, TmonInvMonoidal]

set_option backward.isDefEq.respectTransparency false in
theorem TmonInv_comp_Tmon_εIso_hom :
    ((TmonInvMonoidal R A).comp (TmonMonoidal (R := R) (A := A))).εIso.hom = 𝟙 _ := by
  simp [TmonMonoidal, TmonInvMonoidal]

variable {G : A ⥤ B} [G.Additive] [G.Linear R] [IsSuperfunctor R G]
  (hG : MonoidalSuperfunctor R G)

set_option backward.isDefEq.respectTransparency false in
/-- **Naturality of `T` on coherence maps:** `T_B ∘ (G̲)^ = G ∘ T_A` as monoidal
superfunctors. -/
theorem Tmon_naturality_μIso_hom (X Y : Associated R (Underlying R A)) :
    letI := (MonoidalSuperfunctor.underlyingCoreMonoidal hG).toMonoidal
    (((mapMonoidal hG.toMonoidalPiFunctor).comp (TmonMonoidal (R := R) (A := B))).μIso X Y).hom =
      (((TmonMonoidal (R := R) (A := A)).comp hG).μIso X Y).hom := by
  simp [TmonMonoidal, mapMonoidal]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem Tmon_naturality_εIso_hom :
    letI := (MonoidalSuperfunctor.underlyingCoreMonoidal hG).toMonoidal
    ((mapMonoidal hG.toMonoidalPiFunctor).comp (TmonMonoidal (R := R) (A := B))).εIso.hom =
      ((TmonMonoidal (R := R) (A := A)).comp hG).εIso.hom := by
  simp [TmonMonoidal, mapMonoidal]
  rfl

end TmonInv

end Associated

namespace PiMon

attribute [local instance] MonoidalPiCategory.toPiCategory

set_option backward.isDefEq.respectTransparency false in
/-- **Lemma 5.4 (one object), `E ∘ D = I`.** The identification `A ≅ E(D(A))` in `Π-Mon` given
by the strict monoidal Π-functors `unit` and `counit` (with `j = 1`). -/
def unitIsoApp (A : PiMon.{w, v, u} R) : A ≅ PiMon.of R (Underlying R (Associated R A)) where
  hom := { toFunctor := Associated.unit R A, piFunctor := Associated.unitMonoidalPiFunctor }
  inv := { toFunctor := Associated.counit R A, piFunctor := Associated.counitMonoidalPiFunctor R A }
  hom_inv_id := Hom.ext Associated.unit_comp_counit
    (heq_of_eq (Associated.unit_comp_counit_ε R A))
    (fun X Y => heq_of_eq (Associated.unit_comp_counit_μ R A X Y))
    (heq_of_eq (by simp [Associated.unitMonoidalPiFunctor, Associated.counitMonoidalPiFunctor]))
  inv_hom_id := Hom.ext Associated.counit_comp_unit
    (heq_of_eq (Associated.counit_comp_unit_ε R A))
    (fun X Y => heq_of_eq (Associated.counit_comp_unit_μ R A X Y))
    (heq_of_eq (by simp [Associated.unitMonoidalPiFunctor, Associated.counitMonoidalPiFunctor]))

variable (R) in
/-- **Lemma 5.4 (one object), `E ∘ D = I`.** The natural isomorphism `𝟭 ≅ D ⋙ E`. -/
def unitIso : 𝟭 (PiMon.{w, v, u} R) ≅ D ⋙ PiSMon.E :=
  NatIso.ofComponents unitIsoApp fun F =>
    Hom.ext (Associated.unit_comp_map F.piFunctor).symm
      (heq_of_eq (Associated.unit_comp_map_ε F.piFunctor))
      (fun X Y => heq_of_eq (Associated.unit_comp_map_μ F.piFunctor X Y))
      (heq_of_eq (Associated.unit_comp_map_j F.piFunctor))

/-- **Lemma 5.4 (one object), `D ∘ E ≅ I`.** The isomorphism `T_A : D(E(A)) ≅ A` in `Π-SMon`,
with inverse `T_A⁻¹`, both strict monoidal superfunctors. -/
def counitIsoApp (A : PiSMon.{w, v, u} R) :
    PiSMon.of R (Associated R (Underlying R A)) ≅ A where
  hom := ⟨Associated.Tmon R A, Associated.TmonMonoidal⟩
  inv := ⟨Associated.TmonInv R A, Associated.TmonInvMonoidal R A⟩
  hom_inv_id := PiSMon.Hom.ext Associated.Tmon_comp_TmonInv
    (fun X Y => heq_of_eq (Associated.Tmon_comp_TmonInv_μIso_hom X Y))
    (heq_of_eq Associated.Tmon_comp_TmonInv_εIso_hom)
  inv_hom_id := PiSMon.Hom.ext Associated.TmonInv_comp_Tmon
    (fun X Y => heq_of_eq (Associated.TmonInv_comp_Tmon_μIso_hom X Y))
    (heq_of_eq Associated.TmonInv_comp_Tmon_εIso_hom)

variable (R) in
/-- **Lemma 5.4 (one object), `D ∘ E ≅ I`.** The natural isomorphism `E ⋙ D ≅ 𝟭`, with
components `T_A`. -/
def counitIso : PiSMon.E ⋙ D ≅ 𝟭 (PiSMon.{w, v, u} R) :=
  NatIso.ofComponents counitIsoApp fun G =>
    PiSMon.Hom.ext (Associated.Tmon_naturality G.monoidal)
      (fun X Y => heq_of_eq (Associated.Tmon_naturality_μIso_hom G.monoidal X Y))
      (heq_of_eq (Associated.Tmon_naturality_εIso_hom G.monoidal))

variable (R) in
/-- **Brundan–Ellis, Theorem 1.15 (second part) / Lemma 5.4 (one object).** The functors
`D : Π-Mon → Π-SMon` and `E : Π-SMon → Π-Mon` are mutually inverse equivalences of
categories. -/
def equivalence : PiMon.{w, v, u} R ≌ PiSMon.{w, v, u} R :=
  CategoryTheory.Equivalence.mk D PiSMon.E (unitIso R) (counitIso R)

@[simp] theorem equivalence_functor : (equivalence R).functor = D.{w, v, u} := rfl

@[simp] theorem equivalence_inverse : (equivalence R).inverse = PiSMon.E.{w, v, u} := rfl

/-- **Brundan–Ellis, Theorem 1.15 (second part).** The functor (2) of (1.9),
`E : Π-SMon → Π-Mon`, is an equivalence of categories. -/
instance : PiSMon.E.{w, v, u} (R := R).IsEquivalence :=
  (equivalence R).isEquivalence_inverse

/-- The functor `D : Π-Mon → Π-SMon` is an equivalence of categories. -/
instance : D.{w, v, u} (R := R).IsEquivalence :=
  (equivalence R).isEquivalence_functor

end PiMon

end StringDiagrams

end
