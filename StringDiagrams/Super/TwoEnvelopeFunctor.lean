import StringDiagrams.Super.TwoEnvelopeUniversal

/-!
# Functoriality of the Π-envelope of 2-supercategories

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §4, the
construction (4.7) of the strict 2-functor `-_π : 2-SCAT → Π-2-SCAT` on 2-superfunctors and
2-natural transformations, and on supermodifications as in Remark 4.10:

* `TwoEnvelope.mapPi`: for a 2-superfunctor `ℝ : 𝔄 → 𝔅`, the 2-superfunctor
  `ℝ_π : 𝔄_π → 𝔅_π` equal to `ℝ` on objects, `ΠᵃF ↦ Πᵃ(ℝF)`, `x_a^b ↦ (ℝx)_a^b`, with
  coherence maps `(c_π)_{ΠᵃF, ΠᵇG} = (c_{F,G})_{a+b}^{a+b}` and `i_π = i_0^0`.
* `TwoEnvelope.mapPiNatTrans`: for a 2-natural transformation `(X, x) : ℝ ⇒ 𝕊`, the
  2-natural transformation `(X_π, x_π) : ℝ_π ⇒ 𝕊_π` with `(X_π)_λ = Π⁰ X_λ` and
  `((x_π)_{μ,λ})_{ΠᵃF} = ((x_{μ,λ})_F)_a^a`.
* `TwoEnvelope.mapPiSupermodification`: for a supermodification `α`, `(α_π)_λ = (α_λ)_0^0`
  (Remark 4.10).

The strict functoriality of `-_π` (compatibility with composites and identities) is not
stated.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory BicategoryStruct TwoSupercategory

universe w w₁ v₁ u₁ w₂ v₂ u₂

namespace TwoEnvelope

open Envelope

variable {R : Type w} [CommRing R]
  {B : Type u₁} [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]
  {C : Type u₂} [BicategoryStruct.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ a b : C, Supercategory R (a ⟶ b)] [TwoSupercategory R C]

variable (F : TwoSuperfunctor R B C)

/-- `ℝ_π` on 1-morphisms: `ΠᵃF ↦ Πᵃ(ℝF)`. -/
def mapPiMap {a b : TwoEnvelope R B} (f : a ⟶ b) :
    (⟨F.obj a.as⟩ : TwoEnvelope R C) ⟶ ⟨F.obj b.as⟩ :=
  Envelope.mk f.par (F.map f.obj)

/-- `ℝ_π` on 2-morphisms: `x_a^b ↦ (ℝx)_a^b`. -/
def mapPiMap₂ {a b : TwoEnvelope R B} {f g : a ⟶ b} (η : f ⟶ g) :
    mapPiMap F f ⟶ mapPiMap F g :=
  Envelope.ofHom (F.map₂ (toHom η))

omit [TwoSupercategory R B] [TwoSupercategory R C] in
theorem toHom_mapPiMap₂ {a b : TwoEnvelope R B} {f g : a ⟶ b} (η : f ⟶ g) :
    toHom (mapPiMap₂ F η) = F.map₂ (toHom η) := rfl

omit [TwoSupercategory R B] [TwoSupercategory R C] in
theorem mapPiMap₂_mem {a b : TwoEnvelope R B} {f g : a ⟶ b} {p : ZMod 2} {η : f ⟶ g}
    (hη : η ∈ parity (R := R) f g p) :
    mapPiMap₂ F η ∈ parity (R := R) (mapPiMap F f) (mapPiMap F g) p :=
  F.map₂_mem hη

omit [TwoSupercategory R B] [TwoSupercategory R C] in
@[simp] theorem mapPiMap₂_zero {a b : TwoEnvelope R B} {f g : a ⟶ b} :
    mapPiMap₂ F (0 : f ⟶ g) = 0 := hom_ext (F.map₂_zero _ _)

omit [TwoSupercategory R B] [TwoSupercategory R C] in
theorem mapPiMap₂_add {a b : TwoEnvelope R B} {f g : a ⟶ b} (η θ : f ⟶ g) :
    mapPiMap₂ F (η + θ) = mapPiMap₂ F η + mapPiMap₂ F θ := hom_ext (F.map₂_add _ _)

theorem mapPi_naturality_left {a b c : TwoEnvelope R B} {f f' : a ⟶ b} (η : f ⟶ f')
    (g : b ⟶ c) :
    mapPiMap₂ F η ▷ mapPiMap F g ≫ ofHom (F.mapComp f'.obj g.obj).hom =
      (ofHom (F.mapComp f.obj g.obj).hom : mapPiMap F f ≫ mapPiMap F g ⟶ mapPiMap F (f ≫ g)) ≫
        mapPiMap₂ F (η ▷ g) := by
  refine induction_on' (R := R) η ?_ (fun r η hη => ?_) (fun η θ hη hθ => ?_)
  · rw [mapPiMap₂_zero, TwoEnvelope.zero_whiskerRight', TwoEnvelope.zero_whiskerRight',
      mapPiMap₂_zero, Limits.zero_comp, Limits.comp_zero]
  · apply hom_ext
    rw [toHom_comp, toHom_comp, TwoEnvelope.toHom_whiskerRight_of_mem (F.map₂_mem hη),
      toHom_mapPiMap₂, toHom_mapPiMap₂, TwoEnvelope.toHom_whiskerRight_of_mem hη, F.map₂_smul,
      Linear.smul_comp, Linear.comp_smul]
    erw [F.mapComp_naturality_left]
    rfl
  · rw [mapPiMap₂_add, TwoEnvelope.add_whiskerRight', TwoEnvelope.add_whiskerRight',
      mapPiMap₂_add, Preadditive.add_comp, Preadditive.comp_add, hη, hθ]

theorem mapPi_naturality_right {a b c : TwoEnvelope R B} (f : a ⟶ b) {g g' : b ⟶ c}
    (η : g ⟶ g') :
    mapPiMap F f ◁ mapPiMap₂ F η ≫ ofHom (F.mapComp f.obj g'.obj).hom =
      (ofHom (F.mapComp f.obj g.obj).hom : mapPiMap F f ≫ mapPiMap F g ⟶ mapPiMap F (f ≫ g)) ≫
        mapPiMap₂ F (f ◁ η) := by
  refine induction_on' (R := R) η ?_ (fun r η hη => ?_) (fun η θ hη hθ => ?_)
  · rw [mapPiMap₂_zero, TwoEnvelope.whiskerLeft_zero', TwoEnvelope.whiskerLeft_zero',
      mapPiMap₂_zero, Limits.zero_comp, Limits.comp_zero]
  · apply hom_ext
    rw [toHom_comp, toHom_comp, TwoEnvelope.toHom_whiskerLeft_of_mem _ (F.map₂_mem hη),
      toHom_mapPiMap₂, toHom_mapPiMap₂, TwoEnvelope.toHom_whiskerLeft_of_mem _ hη, F.map₂_smul,
      Linear.smul_comp, Linear.comp_smul]
    erw [F.mapComp_naturality_right]
    rfl
  · rw [mapPiMap₂_add, TwoEnvelope.whiskerLeft_add', TwoEnvelope.whiskerLeft_add',
      mapPiMap₂_add, Preadditive.add_comp, Preadditive.comp_add, hη, hθ]

/-- The even 2-isomorphism `(c_π)_{ΠᵃF, ΠᵇG} = (c_{F,G})_{a+b}^{a+b}`. -/
def mapPiComp {a b c : TwoEnvelope R B} (f : a ⟶ b) (g : b ⟶ c) :
    mapPiMap F f ≫ mapPiMap F g ≅ mapPiMap F (f ≫ g) :=
  isoOfIso (F.mapComp f.obj g.obj)

/-- **§4, (4.7).** The 2-superfunctor `ℝ_π : 𝔄_π → 𝔅_π` induced by a 2-superfunctor
`ℝ : 𝔄 → 𝔅`: `ΠᵃF ↦ Πᵃ(ℝF)`, `x_a^b ↦ (ℝx)_a^b`, `c_π = (c)_{a+b}^{a+b}`, `i_π = i_0^0`. -/
def mapPi : TwoSuperfunctor R (TwoEnvelope R B) (TwoEnvelope R C) where
  obj a := ⟨F.obj a.as⟩
  map f := mapPiMap F f
  map₂ η := mapPiMap₂ F η
  map₂_id f := hom_ext (F.map₂_id f.obj)
  map₂_comp η θ := hom_ext (F.map₂_comp (toHom η) (toHom θ))
  map₂_add η θ := mapPiMap₂_add F η θ
  map₂_smul r η := hom_ext (F.map₂_smul r (toHom η))
  map₂_mem hη := mapPiMap₂_mem F hη
  mapComp f g := mapPiComp F f g
  mapId a := isoOfIso (F.mapId a.as)
  mapComp_hom_mem f g := by
    rw [mem_parity_iff]
    convert F.mapComp_hom_mem f.obj g.obj using 2
    show (0 : ZMod 2) + (f.par + g.par + (f.par + g.par)) = 0
    rw [zmod2_add_self, add_zero]
  mapId_hom_mem a := by
    rw [mem_parity_iff]
    convert F.mapId_hom_mem a.as using 2
  mapComp_naturality_left η g := mapPi_naturality_left F η g
  mapComp_naturality_right f _ _ η := mapPi_naturality_right F f η
  map₂_associator f g h := by
    apply hom_ext
    rw [toHom_comp, toHom_comp, toHom_comp, toHom_comp,
      TwoEnvelope.toHom_whiskerLeft_of_even _ (η := (mapPiComp F g h).hom)
        (F.mapComp_hom_mem g.obj h.obj),
      TwoEnvelope.toHom_whiskerRight_of_even (η := (mapPiComp F f g).hom)
        (F.mapComp_hom_mem f.obj g.obj) _ rfl]
    exact F.map₂_associator f.obj g.obj h.obj
  map₂_leftUnitor {a b} f := by
    apply hom_ext
    rw [toHom_comp, toHom_comp]
    erw [TwoEnvelope.toHom_whiskerRight_of_even (a := ⟨F.obj a.as⟩) (b := ⟨F.obj a.as⟩)
      (f := 𝟙 _) (g := mapPiMap F (𝟙 a)) (η := (isoOfIso (F.mapId a.as)).hom)
        (F.mapId_hom_mem _) _ rfl]
    exact F.map₂_leftUnitor f.obj
  map₂_rightUnitor {a b} f := by
    apply hom_ext
    rw [toHom_comp, toHom_comp]
    erw [TwoEnvelope.toHom_whiskerLeft_of_even (b := ⟨F.obj b.as⟩) (c := ⟨F.obj b.as⟩) _
      (g := 𝟙 _) (h := mapPiMap F (𝟙 b)) (η := (isoOfIso (F.mapId b.as)).hom)
      (F.mapId_hom_mem _)]
    exact F.map₂_rightUnitor f.obj

@[simp] theorem mapPi_obj (a : TwoEnvelope R B) : (mapPi F).obj a = ⟨F.obj a.as⟩ := rfl

theorem mapPi_map {a b : TwoEnvelope R B} (f : a ⟶ b) :
    (mapPi F).map f = Envelope.mk f.par (F.map f.obj) := rfl

theorem toHom_mapPi_map₂ {a b : TwoEnvelope R B} {f g : a ⟶ b} (η : f ⟶ g) :
    toHom ((mapPi F).map₂ η) = F.map₂ (toHom η) := rfl

theorem toHom_mapPi_mapComp {a b c : TwoEnvelope R B} (f : a ⟶ b) (g : b ⟶ c) :
    toHom ((mapPi F).mapComp f g).hom = (F.mapComp f.obj g.obj).hom := rfl

theorem toHom_mapPi_mapId (a : TwoEnvelope R B) :
    toHom ((mapPi F).mapId a).hom = (F.mapId a.as).hom := rfl

variable {F} {G : TwoSuperfunctor R B C}

/-- The 2-morphisms `((x_{μ,λ})_F)_a^a` of `(X_π, x_π)`. -/
def mapPiX (θ : TwoNatTrans F G) {a b : TwoEnvelope R B} (f : a ⟶ b) :
    (mapPi F).map f ≫ Jm (θ.X b.as) ⟶ Jm (θ.X a.as) ≫ (mapPi G).map f :=
  Envelope.ofHom (θ.x f.obj)

theorem toHom_mapPiX (θ : TwoNatTrans F G) {a b : TwoEnvelope R B} (f : a ⟶ b) :
    toHom (mapPiX θ f) ∈ parity (R := R) _ _ 0 := θ.x_mem f.obj

/-- **§4, (4.7).** The 2-natural transformation `(X_π, x_π) : ℝ_π ⇒ 𝕊_π` induced by
`(X, x) : ℝ ⇒ 𝕊`: `(X_π)_λ = Π⁰X_λ` and `((x_π)_{μ,λ})_{ΠᵃF} = ((x_{μ,λ})_F)_a^a`. -/
def mapPiNatTrans (θ : TwoNatTrans F G) : TwoNatTrans (mapPi F) (mapPi G) where
  X a := Jm (θ.X a.as)
  x f := mapPiX θ f
  x_mem f := by
    rw [mem_parity_iff]
    have e : (0 : ZMod 2) + (f.par + 0 + (0 + f.par)) = 0 := by
      simp only [add_zero, zero_add, zmod2_add_self]
    show θ.x f.obj ∈ parity (R := R) _ _ ((0 : ZMod 2) + (f.par + 0 + (0 + f.par)))
    rw [e]
    exact θ.x_mem f.obj
  naturality η := by
    apply hom_ext
    rw [toHom_comp, toHom_comp, TwoEnvelope.toHom_whiskerRight_of_par_zero _ _ rfl,
      TwoEnvelope.toHom_whiskerLeft_of_par_zero _ rfl]
    exact θ.naturality (toHom η)
  x_comp f g := by
    apply hom_ext
    repeat rw [toHom_comp]
    rw [TwoEnvelope.toHom_whiskerRight_of_par_zero _ _ rfl]
    rw [TwoEnvelope.toHom_whiskerLeft_of_even _ (η := mapPiX θ g) (toHom_mapPiX θ g),
      TwoEnvelope.toHom_whiskerRight_of_even (η := mapPiX θ f) (toHom_mapPiX θ f) _
        (by show f.par + 0 = 0 + f.par; rw [add_zero, zero_add])]
    rw [TwoEnvelope.toHom_whiskerLeft_of_par_zero _ rfl]
    exact θ.x_comp f.obj g.obj
  x_id a := by
    apply hom_ext
    repeat rw [toHom_comp]
    rw [TwoEnvelope.toHom_whiskerRight_of_par_zero _ _ rfl,
      TwoEnvelope.toHom_whiskerLeft_of_par_zero _ rfl]
    exact θ.x_id a.as

theorem mapPiNatTrans_X (θ : TwoNatTrans F G) (a : TwoEnvelope R B) :
    (mapPiNatTrans θ).X a = Jm (θ.X a.as) := rfl

theorem toHom_mapPiNatTrans_x (θ : TwoNatTrans F G) {a b : TwoEnvelope R B} (f : a ⟶ b) :
    toHom ((mapPiNatTrans θ).x f) = θ.x f.obj := rfl

theorem mapPi_supermodification_naturality_of_mem {θ θ' : TwoNatTrans F G} {p : ZMod 2}
    (α : ∀ a : B, θ.X a ⟶ θ'.X a) (hα : ∀ a, α a ∈ parity (R := R) _ _ p)
    (nat : ∀ {a b : B} (f : a ⟶ b), θ.x f ≫ α a ▷ G.map f = F.map f ◁ α b ≫ θ'.x f)
    {a b : TwoEnvelope R B} (f : a ⟶ b) :
    (mapPiNatTrans θ).x f ≫ (J2 (α a.as) : Jm (R := R) (θ.X a.as) ⟶ Jm (θ'.X a.as)) ▷
        (mapPi G).map f =
      (mapPi F).map f ◁ (J2 (α b.as) : Jm (R := R) (θ.X b.as) ⟶ Jm (θ'.X b.as)) ≫
        (mapPiNatTrans θ').x f := by
  apply hom_ext
  rw [toHom_comp, toHom_comp, TwoEnvelope.toHom_whiskerRight_of_mem (η := J2 (α a.as)) (hα a.as),
    TwoEnvelope.toHom_whiskerLeft_of_mem _ (η := J2 (α b.as)) (hα b.as), Linear.comp_smul,
    Linear.smul_comp]
  show sign R (f.par * (p + (0 + 0))) • (θ.x f.obj ≫ α a.as ▷ G.map f.obj) =
    sign R (f.par * p) • (F.map f.obj ◁ α b.as ≫ θ'.x f.obj)
  rw [nat, add_zero, add_zero]

/-- **Remark 4.10.** The supermodification `α_π : (X_π, x_π) ⇛ (Y_π, y_π)` induced by a
supermodification `α : (X, x) ⇛ (Y, y)`: `(α_π)_λ = (α_λ)_0^0`. -/
def mapPiSupermodification {θ θ' : TwoNatTrans F G} (α : θ ⟶ θ') :
    mapPiNatTrans θ ⟶ mapPiNatTrans θ' where
  app a := J2 (α.app a.as)
  naturality f := by
    have h := fun p => mapPi_supermodification_naturality_of_mem (TwoNatTrans.projHom p α).app
      (fun a => proj_mem (R := R) p (α.app a)) (TwoNatTrans.projHom p α).naturality f
    have e : ∀ a : B, α.app a = (TwoNatTrans.projHom 0 α).app a +
        (TwoNatTrans.projHom 1 α).app a :=
      fun a => (proj_add_proj (R := R) (α.app a)).symm
    have eJ : ∀ a : B, (J2 (α.app a) : Jm (R := R) (θ.X a) ⟶ Jm (θ'.X a)) =
        J2 ((TwoNatTrans.projHom 0 α).app a) + J2 ((TwoNatTrans.projHom 1 α).app a) :=
      fun a => hom_ext (e a)
    rw [eJ, eJ, TwoEnvelope.add_whiskerRight', TwoEnvelope.whiskerLeft_add', Preadditive.comp_add,
      Preadditive.add_comp, h 0, h 1]

end TwoEnvelope

end StringDiagrams

end
