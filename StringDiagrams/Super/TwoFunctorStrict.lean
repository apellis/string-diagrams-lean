import StringDiagrams.Super.TwoFunctor

/-!
# Strict 2-superfunctors from strict data

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, the
remark after Definition 2.2: a strict 2-superfunctor is a 2-superfunctor whose coherence maps
`c` and `i` are identities.

`TwoSuperfunctor.StrictCore` is the data of a strict 2-superfunctor: functions on objects,
1-morphisms and 2-morphisms which preserve composition and identities of 1-morphisms on the
nose (`map_comp`, `map_id`) and the whiskerings and coherence maps up to these equalities
(heterogeneous equalities `map₂_whiskerLeft`, `map₂_whiskerRight`, `map₂_associator`,
`map₂_leftUnitor`, `map₂_rightUnitor`). `TwoSuperfunctor.StrictCore.toTwoSuperfunctor` is the
corresponding 2-superfunctor, with `c` and `i` the `eqToIso`s of `map_comp` and `map_id`, and it
is strict (`TwoSuperfunctor.StrictCore.isStrict`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory BicategoryStruct TwoSupercategory

universe w₁ v₁ u₁ w₂ v₂ u₂ w

namespace Supercategory

variable {R : Type w} [CommRing R] {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear R C]
  [Supercategory R C]

/-- `eqToHom`s are even. -/
theorem eqToHom_mem {X Y : C} (h : X = Y) : eqToHom h ∈ parity (R := R) X Y 0 := by
  subst h; exact id_mem _

end Supercategory

namespace TwoSupercategory

variable {R : Type w} [CommRing R] {B : Type u₁} [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]

variable (R) in
include R in
theorem whiskerLeft_eqToHom {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (e : g = h) :
    f ◁ eqToHom e = eqToHom (congrArg (f ≫ ·) e) := by
  subst e; simp [whiskerLeft_id (R := R)]

variable (R) in
include R in
theorem eqToHom_whiskerRight {a b c : B} {f g : a ⟶ b} (e : f = g) (h : b ⟶ c) :
    eqToHom e ▷ h = eqToHom (congrArg (· ≫ h) e) := by
  subst e; simp [id_whiskerRight (R := R)]

end TwoSupercategory

/-- The inverses of heterogeneously equal isomorphisms are heterogeneously equal. -/
theorem _root_.CategoryTheory.Iso.inv_heq_of_hom_heq {C : Type u₁} [Category.{v₁} C]
    {X Y X' Y' : C} (e : X ≅ Y) (e' : X' ≅ Y') (hX : X = X') (hY : Y = Y')
    (h : HEq e.hom e'.hom) : HEq e.inv e'.inv := by
  subst hX hY
  exact heq_of_eq (congrArg Iso.inv (Iso.ext (eq_of_heq h)))

namespace TwoSuperfunctor

variable (R : Type w) [CommRing R]
  (B : Type u₁) [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)]
  (C : Type u₂) [BicategoryStruct.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ a b : C, Supercategory R (a ⟶ b)]

/-- The data of a strict 2-superfunctor: functions on objects, 1-morphisms and 2-morphisms
preserving composition and identities of 1-morphisms on the nose, and the whiskerings and
coherence maps up to these equalities. -/
structure StrictCore where
  /-- The function on objects. -/
  obj : B → C
  /-- The function on 1-morphisms. -/
  map {a b : B} : (a ⟶ b) → (obj a ⟶ obj b)
  /-- The function on 2-morphisms. -/
  map₂ {a b : B} {f g : a ⟶ b} : (f ⟶ g) → (map f ⟶ map g)
  map₂_id {a b : B} (f : a ⟶ b) : map₂ (𝟙 f) = 𝟙 (map f)
  map₂_comp {a b : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) :
    map₂ (η ≫ θ) = map₂ η ≫ map₂ θ
  map₂_add {a b : B} {f g : a ⟶ b} (η θ : f ⟶ g) : map₂ (η + θ) = map₂ η + map₂ θ
  map₂_smul {a b : B} {f g : a ⟶ b} (r : R) (η : f ⟶ g) : map₂ (r • η) = r • map₂ η
  map₂_mem {a b : B} {f g : a ⟶ b} {p : ZMod 2} {η : f ⟶ g} :
    η ∈ parity (R := R) f g p → map₂ η ∈ parity (R := R) (map f) (map g) p
  map_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) : map (f ≫ g) = map f ≫ map g
  map_id (a : B) : map (𝟙 a) = 𝟙 (obj a)
  map₂_whiskerLeft {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    HEq (map₂ (f ◁ η)) (map f ◁ map₂ η)
  map₂_whiskerRight {a b c : B} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    HEq (map₂ (η ▷ h)) (map₂ η ▷ map h)
  map₂_associator {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    HEq (map₂ (associator f g h).hom) (associator (map f) (map g) (map h)).hom
  map₂_leftUnitor {a b : B} (f : a ⟶ b) : HEq (map₂ (leftUnitor f).hom) (leftUnitor (map f)).hom
  map₂_rightUnitor {a b : B} (f : a ⟶ b) :
    HEq (map₂ (rightUnitor f).hom) (rightUnitor (map f)).hom

namespace StrictCore

variable {R B C} (F : StrictCore R B C)

/-- The image of a 2-isomorphism. -/
@[simps]
def map₂Iso {a b : B} {f g : a ⟶ b} (e : f ≅ g) : F.map f ≅ F.map g where
  hom := F.map₂ e.hom
  inv := F.map₂ e.inv
  hom_inv_id := by rw [← F.map₂_comp, e.hom_inv_id, F.map₂_id]
  inv_hom_id := by rw [← F.map₂_comp, e.inv_hom_id, F.map₂_id]

theorem map₂_whiskerLeft_eq {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    F.map₂ (f ◁ η) = eqToHom (F.map_comp f g) ≫ F.map f ◁ F.map₂ η ≫
      eqToHom (F.map_comp f h).symm :=
  (conj_eqToHom_iff_heq _ _ (F.map_comp f g) (F.map_comp f h)).2 (F.map₂_whiskerLeft f η)

theorem map₂_whiskerRight_eq {a b c : B} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    F.map₂ (η ▷ h) = eqToHom (F.map_comp f h) ≫ F.map₂ η ▷ F.map h ≫
      eqToHom (F.map_comp g h).symm :=
  (conj_eqToHom_iff_heq _ _ (F.map_comp f h) (F.map_comp g h)).2 (F.map₂_whiskerRight η h)

theorem map_comp_comp_left {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    F.map ((f ≫ g) ≫ h) = (F.map f ≫ F.map g) ≫ F.map h := by
  rw [F.map_comp, F.map_comp]

theorem map_comp_comp_right {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    F.map (f ≫ g ≫ h) = F.map f ≫ F.map g ≫ F.map h := by
  rw [F.map_comp, F.map_comp]

theorem map₂_associator_inv_eq {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    F.map₂ (associator f g h).inv = eqToHom (F.map_comp_comp_right f g h) ≫
      (associator (F.map f) (F.map g) (F.map h)).inv ≫
        eqToHom (F.map_comp_comp_left f g h).symm :=
  (conj_eqToHom_iff_heq _ _ (F.map_comp_comp_right f g h) (F.map_comp_comp_left f g h)).2
    (Iso.inv_heq_of_hom_heq (F.map₂Iso (associator f g h)) (associator (F.map f) (F.map g) (F.map h))
      (F.map_comp_comp_left f g h) (F.map_comp_comp_right f g h) (F.map₂_associator f g h))

theorem map_id_comp {a b : B} (f : a ⟶ b) : F.map (𝟙 a ≫ f) = 𝟙 (F.obj a) ≫ F.map f := by
  rw [F.map_comp, F.map_id]

theorem map_comp_id {a b : B} (f : a ⟶ b) : F.map (f ≫ 𝟙 b) = F.map f ≫ 𝟙 (F.obj b) := by
  rw [F.map_comp, F.map_id]

theorem map₂_leftUnitor_eq {a b : B} (f : a ⟶ b) :
    F.map₂ (leftUnitor f).hom = eqToHom (F.map_id_comp f) ≫ (leftUnitor (F.map f)).hom ≫
      eqToHom rfl :=
  (conj_eqToHom_iff_heq _ _ (F.map_id_comp f) rfl).2 (F.map₂_leftUnitor f)

theorem map₂_rightUnitor_eq {a b : B} (f : a ⟶ b) :
    F.map₂ (rightUnitor f).hom = eqToHom (F.map_comp_id f) ≫ (rightUnitor (F.map f)).hom ≫
      eqToHom rfl :=
  (conj_eqToHom_iff_heq _ _ (F.map_comp_id f) rfl).2 (F.map₂_rightUnitor f)

variable [TwoSupercategory R C]

/-- The strict 2-superfunctor with the given data, with coherence maps `c = eqToIso` and
`i = eqToIso`. -/
def toTwoSuperfunctor : TwoSuperfunctor R B C where
  obj := F.obj
  map := F.map
  map₂ := F.map₂
  map₂_id := F.map₂_id
  map₂_comp := F.map₂_comp
  map₂_add := F.map₂_add
  map₂_smul := F.map₂_smul
  map₂_mem := F.map₂_mem
  mapComp f g := eqToIso (F.map_comp f g).symm
  mapId a := eqToIso (F.map_id a).symm
  mapComp_hom_mem f g := eqToHom_mem (F.map_comp f g).symm
  mapId_hom_mem a := eqToHom_mem (F.map_id a).symm
  mapComp_naturality_left η g := by
    simp [F.map₂_whiskerRight_eq η g]
  mapComp_naturality_right f _ _ η := by
    simp [F.map₂_whiskerLeft_eq f η]
  map₂_associator f g h := by
    simp only [eqToIso.hom, whiskerLeft_eqToHom R, eqToHom_whiskerRight R,
      F.map₂_associator_inv_eq, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      Category.comp_id, Category.assoc, eqToHom_trans]
  map₂_leftUnitor f := by
    simp only [eqToIso.hom, eqToHom_whiskerRight R, F.map₂_leftUnitor_eq, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp, Category.comp_id]
  map₂_rightUnitor f := by
    simp only [eqToIso.hom, whiskerLeft_eqToHom R, F.map₂_rightUnitor_eq, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp, Category.comp_id]

@[simp] theorem toTwoSuperfunctor_obj (a : B) : F.toTwoSuperfunctor.obj a = F.obj a := rfl

@[simp] theorem toTwoSuperfunctor_map {a b : B} (f : a ⟶ b) :
    F.toTwoSuperfunctor.map f = F.map f := rfl

@[simp] theorem toTwoSuperfunctor_map₂ {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
    F.toTwoSuperfunctor.map₂ η = F.map₂ η := rfl

theorem toTwoSuperfunctor_mapComp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    F.toTwoSuperfunctor.mapComp f g = eqToIso (F.map_comp f g).symm := rfl

theorem toTwoSuperfunctor_mapId (a : B) :
    F.toTwoSuperfunctor.mapId a = eqToIso (F.map_id a).symm := rfl

/-- The 2-superfunctor with strict data is strict. -/
theorem isStrict : F.toTwoSuperfunctor.IsStrict where
  map_comp := F.map_comp
  map_id := F.map_id
  mapComp_eq _ _ := rfl
  mapId_eq _ := rfl

end StrictCore

end TwoSuperfunctor

end StringDiagrams

end
