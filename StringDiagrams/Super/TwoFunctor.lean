import StringDiagrams.Super.PiTwo

/-!
# 2-superfunctors, 2-natural transformations and supermodifications

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Definition 2.2(ii)–(iv), in the unpacked form of `TwoSupercategory` (see
`StringDiagrams.Super.Bicategory`). Compositions of 1-morphisms are written in diagrammatic
order: `f ≫ g` is the paper's `g f`, and the paper's `T(y, x) = y x` is `x ▷ _ ≫ _ ◁ y`.

## 2-superfunctors (Definition 2.2(ii))

A 2-superfunctor `ℝ : 𝔄 → 𝔅` (`StringDiagrams.TwoSuperfunctor`) consists of a function on
objects, superfunctors `ℋom_𝔄(λ, μ) → ℋom_𝔅(ℝλ, ℝμ)` (`map`, `map₂` with linearity and
parity axioms; `TwoSuperfunctor.mapFunctor`), even 2-isomorphisms
`c : (ℝ G)(ℝ F) ≅ ℝ(G F)` (`mapComp F G : map F ≫ map G ≅ map (F ≫ G)`) and
`i : 1_{ℝλ} ≅ ℝ 1_λ` (`mapId`). The requirement that `c` be an even supernatural
transformation between superfunctors `ℋom(μ, ν) ⊠ ℋom(λ, μ) → ℋom(λ, ν)` is, since a morphism
`y ⊗ x` of `⊠` is `(y ⊗ 1)(1 ⊗ x)`, naturality in each variable separately
(`mapComp_naturality_left`, `mapComp_naturality_right`); the version for horizontal composites
of homogeneous 2-morphisms is `TwoSuperfunctor.mapComp_naturality`. The three coherence
diagrams of Definition 2.2(ii) are `map₂_associator`, `map₂_leftUnitor`, `map₂_rightUnitor`;
the paper's `a` is `(associator _ _ _).inv`, its `r : - 1 ⇒ -` is `leftUnitor` and its
`l : 1 - ⇒ -` is `rightUnitor` in the diagrammatic order.

## 2-natural transformations (Definition 2.2(iii))

A 2-natural transformation `(X, x) : ℝ ⇒ 𝕊` (`StringDiagrams.TwoNatTrans`) consists of
1-morphisms `X λ : ℝλ ⟶ 𝕊λ` and even 2-morphisms `x F : ℝF ≫ X μ ⟶ X λ ≫ 𝕊F` (the paper's
`(x_{μ,λ})_F : X_μ(ℝF) ⇒ (𝕊F)X_λ`), natural in `F` (`naturality`; this is the even
supernatural transformation `x_{μ,λ}`), with the two coherence diagrams `x_comp`, `x_id`. It
is strong if each `x F` is invertible (`TwoNatTrans.IsStrong`).

## Supermodifications (Definition 2.2(iv))

A supermodification `α : (X, x) ⇛ (Y, y)` (`StringDiagrams.Supermodification`) is a family of
2-morphisms `α_λ : X_λ ⇒ Y_λ` with `(𝕊F)α_λ ∘ x_F = y_F ∘ α_μ(ℝF)` (`naturality`). The
2-natural transformations `ℝ ⇒ 𝕊` and supermodifications form a supercategory
`ℋom(ℝ, 𝕊)` (instances on `TwoNatTrans R F G`): the morphisms of parity `p` are the families
of 2-morphisms of parity `p`, and every supermodification is uniquely `α = α₀ + α₁`
(`Supermodification.proj`).

The composite of 2-superfunctors and the identity and vertical composite of 2-natural
transformations are in `StringDiagrams.Super.TwoFunctorComp`.

## Not formalized

The category `2-𝔖ℭ𝔞𝔱` and the 2-category `2-𝔖ℭ𝔄𝔗` (associativity and unit laws for these
composites), the 2-supercategory `𝔥𝔬𝔪(𝔄, 𝔅)` and the 3-supercategory of 2-supercategories
mentioned in Definition 2.2 (whose details the paper omits), 2-superequivalences of
2-supercategories and the coherence theorem for 2-supercategories are not formalized.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory BicategoryStruct TwoSupercategory

universe w₁ v₁ u₁ w₂ v₂ u₂ w

section Defs

variable (R : Type w) [CommRing R]
  (B : Type u₁) [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)]
  (C : Type u₂) [BicategoryStruct.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ a b : C, Supercategory R (a ⟶ b)]

/-- A 2-superfunctor (Brundan–Ellis, Definition 2.2(ii)); see the module documentation. -/
structure TwoSuperfunctor where
  /-- The function on objects. -/
  obj : B → C
  /-- The superfunctors `ℋom(λ, μ) → ℋom(ℝλ, ℝμ)` on 1-morphisms. -/
  map {a b : B} : (a ⟶ b) → (obj a ⟶ obj b)
  /-- The superfunctors `ℋom(λ, μ) → ℋom(ℝλ, ℝμ)` on 2-morphisms. -/
  map₂ {a b : B} {f g : a ⟶ b} : (f ⟶ g) → (map f ⟶ map g)
  map₂_id {a b : B} (f : a ⟶ b) : map₂ (𝟙 f) = 𝟙 (map f)
  map₂_comp {a b : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) :
    map₂ (η ≫ θ) = map₂ η ≫ map₂ θ
  map₂_add {a b : B} {f g : a ⟶ b} (η θ : f ⟶ g) : map₂ (η + θ) = map₂ η + map₂ θ
  map₂_smul {a b : B} {f g : a ⟶ b} (r : R) (η : f ⟶ g) : map₂ (r • η) = r • map₂ η
  map₂_mem {a b : B} {f g : a ⟶ b} {p : ZMod 2} {η : f ⟶ g} :
    η ∈ parity (R := R) f g p → map₂ η ∈ parity (R := R) (map f) (map g) p
  /-- The even 2-isomorphisms `c : (ℝG)(ℝF) ≅ ℝ(GF)`. -/
  mapComp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : map f ≫ map g ≅ map (f ≫ g)
  /-- The even 2-isomorphisms `i : 1_{ℝλ} ≅ ℝ 1_λ`. -/
  mapId (a : B) : 𝟙 (obj a) ≅ map (𝟙 a)
  mapComp_hom_mem {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    (mapComp f g).hom ∈ parity (R := R) (map f ≫ map g) (map (f ≫ g)) 0
  mapId_hom_mem (a : B) : (mapId a).hom ∈ parity (R := R) (𝟙 (obj a)) (map (𝟙 a)) 0
  /-- Naturality of `c` in the first 1-morphism. -/
  mapComp_naturality_left {a b c : B} {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) :
    map₂ η ▷ map g ≫ (mapComp f' g).hom = (mapComp f g).hom ≫ map₂ (η ▷ g)
  /-- Naturality of `c` in the second 1-morphism. -/
  mapComp_naturality_right {a b c : B} (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') :
    map f ◁ map₂ η ≫ (mapComp f g').hom = (mapComp f g).hom ≫ map₂ (f ◁ η)
  /-- The hexagon of Definition 2.2(ii): `ℝa ∘ c ∘ c(ℝ-) = c ∘ (ℝ-)c ∘ a`. -/
  map₂_associator {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    map f ◁ (mapComp g h).hom ≫ (mapComp f (g ≫ h)).hom ≫ map₂ (associator f g h).inv =
      (associator (map f) (map g) (map h)).inv ≫ (mapComp f g).hom ▷ map h ≫
        (mapComp (f ≫ g) h).hom
  /-- The first unit square of Definition 2.2(ii): `ℝr ∘ c ∘ (ℝ-)i = r`. -/
  map₂_leftUnitor {a b : B} (f : a ⟶ b) :
    (mapId a).hom ▷ map f ≫ (mapComp (𝟙 a) f).hom ≫ map₂ (leftUnitor f).hom =
      (leftUnitor (map f)).hom
  /-- The second unit square of Definition 2.2(ii): `ℝl ∘ c ∘ i(ℝ-) = l`. -/
  map₂_rightUnitor {a b : B} (f : a ⟶ b) :
    map f ◁ (mapId b).hom ≫ (mapComp f (𝟙 b)).hom ≫ map₂ (rightUnitor f).hom =
      (rightUnitor (map f)).hom

namespace TwoSuperfunctor

variable {R B C}

attribute [simp] map₂_id map₂_add map₂_smul
attribute [reassoc] map₂_comp mapComp_naturality_left mapComp_naturality_right
  map₂_associator map₂_leftUnitor map₂_rightUnitor

variable (F : TwoSuperfunctor R B C)

@[simp] theorem map₂_zero {a b : B} (f g : a ⟶ b) : F.map₂ (0 : f ⟶ g) = 0 := by
  rw [← zero_smul R (0 : f ⟶ g), F.map₂_smul, zero_smul]

@[simp] theorem map₂_neg {a b : B} {f g : a ⟶ b} (η : f ⟶ g) : F.map₂ (-η) = -F.map₂ η := by
  rw [← neg_one_smul R η, F.map₂_smul, neg_one_smul]

/-- The superfunctor `ℋom(λ, μ) → ℋom(ℝλ, ℝμ)`. -/
@[simps]
def mapFunctor (a b : B) : (a ⟶ b) ⥤ (F.obj a ⟶ F.obj b) where
  obj := F.map
  map := F.map₂
  map_id := F.map₂_id
  map_comp := F.map₂_comp

instance (a b : B) : (F.mapFunctor a b).Additive where
  map_add := F.map₂_add _ _

instance (a b : B) : (F.mapFunctor a b).Linear R where
  map_smul η r := F.map₂_smul r η

instance (a b : B) : IsSuperfunctor R (F.mapFunctor a b) where
  map_mem hη := F.map₂_mem hη

/-- The image of a 2-isomorphism. -/
@[simps]
def map₂Iso {a b : B} {f g : a ⟶ b} (e : f ≅ g) : F.map f ≅ F.map g where
  hom := F.map₂ e.hom
  inv := F.map₂ e.inv
  hom_inv_id := by rw [← F.map₂_comp, e.hom_inv_id, F.map₂_id]
  inv_hom_id := by rw [← F.map₂_comp, e.inv_hom_id, F.map₂_id]

/-- `c` is an even supernatural transformation on `ℋom(μ, ν) ⊠ ℋom(λ, μ)`: for 2-morphisms
`x : F ⇒ H` and `y : G ⇒ K`, `c ∘ (ℝy)(ℝx) = ℝ(yx) ∘ c`. -/
theorem mapComp_naturality {a b c : B} {f f' : a ⟶ b} {g g' : b ⟶ c} (η : f ⟶ f')
    (θ : g ⟶ g') :
    hcomp (F.map₂ η) (F.map₂ θ) ≫ (F.mapComp f' g').hom =
      (F.mapComp f g).hom ≫ F.map₂ (hcomp η θ) := by
  rw [hcomp, hcomp, Category.assoc, F.mapComp_naturality_right, ← Category.assoc,
    F.mapComp_naturality_left, Category.assoc, ← F.map₂_comp]

variable (R B) in
/-- The identity 2-superfunctor `𝕀`. -/
@[simps]
abbrev id [TwoSupercategory R B] : TwoSuperfunctor R B B where
  obj a := a
  map f := f
  map₂ η := η
  map₂_id _ := rfl
  map₂_comp _ _ := rfl
  map₂_add _ _ := rfl
  map₂_smul _ _ := rfl
  map₂_mem h := h
  mapComp f g := Iso.refl (f ≫ g)
  mapId a := Iso.refl (𝟙 a)
  mapComp_hom_mem _ _ := id_mem _
  mapId_hom_mem _ := id_mem _
  mapComp_naturality_left η g := by simp
  mapComp_naturality_right f _ _ η := by simp
  map₂_associator f g h := by
    simp [whiskerLeft_id (R := R), id_whiskerRight (R := R)]
  map₂_leftUnitor f := by simp [id_whiskerRight (R := R)]
  map₂_rightUnitor f := by simp [whiskerLeft_id (R := R)]

end TwoSuperfunctor

/-! ## 2-natural transformations -/

variable {R B C}

/-- A 2-natural transformation `(X, x) : ℝ ⇒ 𝕊` (Brundan–Ellis, Definition 2.2(iii)); see the
module documentation. -/
structure TwoNatTrans (F G : TwoSuperfunctor R B C) where
  /-- The 1-morphisms `X_λ : ℝλ → 𝕊λ`. -/
  X (a : B) : F.obj a ⟶ G.obj a
  /-- The even 2-morphisms `(x_{μ,λ})_F : X_μ(ℝF) ⇒ (𝕊F)X_λ`. -/
  x {a b : B} (f : a ⟶ b) : F.map f ≫ X b ⟶ X a ≫ G.map f
  x_mem {a b : B} (f : a ⟶ b) : x f ∈ parity (R := R) (F.map f ≫ X b) (X a ≫ G.map f) 0
  /-- `x_{μ,λ}` is a (supernatural) transformation. -/
  naturality {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
    F.map₂ η ▷ X b ≫ x g = x f ≫ X a ◁ G.map₂ η
  /-- The first coherence diagram of Definition 2.2(iii). -/
  x_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    (F.mapComp f g).hom ▷ X c ≫ x (f ≫ g) =
      (associator (F.map f) (F.map g) (X c)).hom ≫ F.map f ◁ x g ≫
        (associator (F.map f) (X b) (G.map g)).inv ≫ x f ▷ G.map g ≫
          (associator (X a) (G.map f) (G.map g)).hom ≫ X a ◁ (G.mapComp f g).hom
  /-- The second coherence diagram of Definition 2.2(iii). -/
  x_id (a : B) :
    (rightUnitor (X a)).hom ≫ (leftUnitor (X a)).inv ≫ (F.mapId a).hom ▷ X a ≫ x (𝟙 a) =
      X a ◁ (G.mapId a).hom

namespace TwoNatTrans

attribute [reassoc] naturality x_comp x_id

variable {F G : TwoSuperfunctor R B C}

/-- A 2-natural transformation is strong if each `x_{μ,λ}` is an isomorphism. -/
def IsStrong (θ : TwoNatTrans F G) : Prop := ∀ {a b : B} (f : a ⟶ b), IsIso (θ.x f)

end TwoNatTrans

/-! ## Supermodifications -/

/-- A supermodification `α : (X, x) ⇛ (Y, y)` (Brundan–Ellis, Definition 2.2(iv)): 2-morphisms
`α_λ : X_λ ⇒ Y_λ` with `(𝕊F)α_λ ∘ x_F = y_F ∘ α_μ(ℝF)` for all `F : λ → μ`. -/
@[ext]
structure Supermodification {F G : TwoSuperfunctor R B C} (θ θ' : TwoNatTrans F G) where
  /-- The 2-morphisms `α_λ`. -/
  app (a : B) : θ.X a ⟶ θ'.X a
  naturality {a b : B} (f : a ⟶ b) : θ.x f ≫ app a ▷ G.map f = F.map f ◁ app b ≫ θ'.x f

namespace Supermodification

variable [TwoSupercategory R B] [TwoSupercategory R C]
  {F G : TwoSuperfunctor R B C} {θ θ' θ'' : TwoNatTrans F G}

/-- The identity supermodification. -/
@[simps]
def id (θ : TwoNatTrans F G) : Supermodification θ θ where
  app a := 𝟙 (θ.X a)
  naturality f := by simp [id_whiskerRight (R := R), whiskerLeft_id (R := R)]

/-- Vertical composition of supermodifications. -/
@[simps]
def vcomp (α : Supermodification θ θ') (β : Supermodification θ' θ'') :
    Supermodification θ θ'' where
  app a := α.app a ≫ β.app a
  naturality f := by
    rw [comp_whiskerRight (R := R), whiskerLeft_comp (R := R), ← Category.assoc,
      α.naturality, Category.assoc, β.naturality, Category.assoc]

end Supermodification

/-! ## The supercategory `ℋom(ℝ, 𝕊)` -/

namespace TwoNatTrans

variable [TwoSupercategory R C] {F G : TwoSuperfunctor R B C}

instance : Category (TwoNatTrans F G) where
  Hom θ θ' := Supermodification θ θ'
  id θ := Supermodification.id θ
  comp α β := α.vcomp β
  id_comp _ := Supermodification.ext (funext fun _ => Category.id_comp _)
  comp_id _ := Supermodification.ext (funext fun _ => Category.comp_id _)
  assoc _ _ _ := Supermodification.ext (funext fun _ => Category.assoc _ _ _)

variable {θ θ' θ'' : TwoNatTrans F G}

@[ext]
theorem hom_ext {α β : θ ⟶ θ'} (h : ∀ a, α.app a = β.app a) : α = β :=
  Supermodification.ext (funext h)

@[simp] theorem id_app (θ : TwoNatTrans F G) (a : B) :
    (𝟙 θ : θ ⟶ θ).app a = 𝟙 (θ.X a) := rfl

@[simp] theorem comp_app (α : θ ⟶ θ') (β : θ' ⟶ θ'') (a : B) :
    (α ≫ β).app a = α.app a ≫ β.app a := rfl

section Linear

instance : Zero (θ ⟶ θ') where
  zero := ⟨fun _ => 0, fun f => by dsimp only; simp [zero_whiskerRight R, whiskerLeft_zero R]⟩

instance : Add (θ ⟶ θ') where
  add α β := ⟨fun a => α.app a + β.app a, fun f => by
    dsimp only; rw [add_whiskerRight (R := R), whiskerLeft_add (R := R), Preadditive.comp_add,
      Preadditive.add_comp, α.naturality, β.naturality]⟩

instance : Neg (θ ⟶ θ') where
  neg α := ⟨fun a => -α.app a, fun f => by
    dsimp only; rw [neg_whiskerRight R, whiskerLeft_neg R, Preadditive.comp_neg, Preadditive.neg_comp,
      α.naturality]⟩

instance : Sub (θ ⟶ θ') where
  sub α β := ⟨fun a => α.app a - β.app a, fun f => by
    dsimp only; rw [sub_eq_add_neg, sub_eq_add_neg, add_whiskerRight (R := R), whiskerLeft_add (R := R),
      neg_whiskerRight R, whiskerLeft_neg R, Preadditive.comp_add, Preadditive.add_comp,
      Preadditive.comp_neg, Preadditive.neg_comp, α.naturality, β.naturality]⟩

instance : SMul R (θ ⟶ θ') where
  smul r α := ⟨fun a => r • α.app a, fun f => by
    dsimp only; rw [smul_whiskerRight (R := R), whiskerLeft_smul (R := R), Linear.comp_smul,
      Linear.smul_comp, α.naturality]⟩

instance : SMul ℕ (θ ⟶ θ') where
  smul n α := ⟨fun a => n • α.app a, fun f => by
    dsimp only; simp only [← Nat.cast_smul_eq_nsmul R]; rw [smul_whiskerRight (R := R), whiskerLeft_smul (R := R),
      Linear.comp_smul, Linear.smul_comp, α.naturality]⟩

instance : SMul ℤ (θ ⟶ θ') where
  smul n α := ⟨fun a => n • α.app a, fun f => by
    dsimp only; simp only [← Int.cast_smul_eq_zsmul R]; rw [smul_whiskerRight (R := R), whiskerLeft_smul (R := R),
      Linear.comp_smul, Linear.smul_comp, α.naturality]⟩

@[simp] theorem zero_app (a : B) : (0 : θ ⟶ θ').app a = 0 := rfl

@[simp] theorem add_app (α β : θ ⟶ θ') (a : B) : (α + β).app a = α.app a + β.app a := rfl

@[simp] theorem neg_app (α : θ ⟶ θ') (a : B) : (-α).app a = -α.app a := rfl

@[simp] theorem sub_app (α β : θ ⟶ θ') (a : B) : (α - β).app a = α.app a - β.app a := rfl

@[simp] theorem smul_app (r : R) (α : θ ⟶ θ') (a : B) : (r • α).app a = r • α.app a := rfl

@[simp] theorem nsmul_app (n : ℕ) (α : θ ⟶ θ') (a : B) : (n • α).app a = n • α.app a := rfl

@[simp] theorem zsmul_app (n : ℤ) (α : θ ⟶ θ') (a : B) : (n • α).app a = n • α.app a := rfl

theorem app_injective : Function.Injective (fun (α : θ ⟶ θ') (a : B) => α.app a) :=
  fun _ _ h => Supermodification.ext h

instance : AddCommGroup (θ ⟶ θ') :=
  app_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

instance : Module R (θ ⟶ θ') :=
  app_injective.module R
    { toFun := fun (α : θ ⟶ θ') (a : B) => α.app a
      map_zero' := rfl
      map_add' := fun _ _ => rfl } (fun _ _ => rfl)

instance : Preadditive (TwoNatTrans F G) where
  homGroup _ _ := inferInstance
  add_comp _ _ _ _ _ _ := hom_ext fun _ => Preadditive.add_comp _ _ _ _ _ _
  comp_add _ _ _ _ _ _ := hom_ext fun _ => Preadditive.comp_add _ _ _ _ _ _

instance : Linear R (TwoNatTrans F G) where
  homModule _ _ := inferInstance
  smul_comp _ _ _ _ _ _ := hom_ext fun _ => Linear.smul_comp _ _ _ _ _ _
  comp_smul _ _ _ _ _ _ := hom_ext fun _ => Linear.comp_smul _ _ _ _ _ _

end Linear

section Super

variable (θ θ') in
/-- The supermodifications of parity `p`: those all of whose components have parity `p`. -/
def parityHom (p : ZMod 2) : Submodule R (θ ⟶ θ') where
  carrier := {α | ∀ a, α.app a ∈ parity (R := R) (θ.X a) (θ'.X a) p}
  zero_mem' _ := Submodule.zero_mem _
  add_mem' hα hβ a := Submodule.add_mem _ (hα a) (hβ a)
  smul_mem' r _ hα a := Submodule.smul_mem _ r (hα a)

theorem mem_parityHom {p : ZMod 2} {α : θ ⟶ θ'} :
    α ∈ parityHom θ θ' p ↔ ∀ a, α.app a ∈ parity (R := R) (θ.X a) (θ'.X a) p := Iff.rfl

/-- The parity-`p` component of a supermodification, componentwise. -/
def projHom (p : ZMod 2) (α : θ ⟶ θ') : θ ⟶ θ' where
  app a := proj R p (α.app a)
  naturality {a b} f := by
    have h1 : proj R p (α.app a) ▷ G.map f = proj R p (α.app a ▷ G.map f) :=
      map_proj (postcomp R (G.map f)) p (α.app a)
    have h2 : F.map f ◁ proj R p (α.app b) = proj R p (F.map f ◁ α.app b) :=
      map_proj (precomp R (F.map f)) p (α.app b)
    have h3 := proj_comp_of_mem_left p (θ.x_mem f) (α.app a ▷ G.map f)
    have h4 := proj_comp_of_mem_right p (F.map f ◁ α.app b) (θ'.x_mem f)
    rw [zero_add] at h3
    rw [add_zero] at h4
    rw [h1, h2, ← h3, ← h4, α.naturality]

@[simp] theorem projHom_app (p : ZMod 2) (α : θ ⟶ θ') (a : B) :
    (projHom p α).app a = proj R p (α.app a) := rfl

instance : Supercategory R (TwoNatTrans F G) where
  parity := parityHom
  isInternal θ θ' := by
    rw [DirectSum.isInternal_submodule_iff_isCompl _ (i := 0) (j := 1) (by decide)
      (by ext p; rcases parity_eq_zero_or_one p with rfl | rfl <;> simp)]
    constructor
    · rw [Submodule.disjoint_def]
      intro α h0 h1
      refine hom_ext fun a => ?_
      rw [mem_parityHom] at h0 h1
      rw [zero_app, ← proj_of_mem (h0 a), proj_of_mem_ne (h1 a) (by decide)]
    · rw [codisjoint_iff, eq_top_iff]
      intro α _
      have : α = projHom 0 α + projHom 1 α := hom_ext fun a => by
        simp [proj_add_proj]
      rw [this]
      exact Submodule.add_mem_sup (fun a => proj_mem 0 _) (fun a => proj_mem 1 _)
  id_mem θ a := id_mem _
  comp_mem hα hβ a := comp_mem (hα a) (hβ a)

theorem mem_parity_iff {p : ZMod 2} {α : θ ⟶ θ'} :
    α ∈ parity (R := R) θ θ' p ↔ ∀ a, α.app a ∈ parity (R := R) (θ.X a) (θ'.X a) p :=
  Iff.rfl

end Super

end TwoNatTrans

end Defs

end StringDiagrams

end
