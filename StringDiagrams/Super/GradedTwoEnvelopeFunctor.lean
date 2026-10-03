import StringDiagrams.Super.TwoEnvelopeFunctor
import StringDiagrams.Super.GradedTwoEnvelope
import StringDiagrams.Super.QPiTwoSCat

/-!
# Functoriality of the graded 2-envelope

The action on 2-superfunctors of Brundan–Ellis, *Monoidal supercategories*,
arXiv:1603.05928v3, (6.2). The `Q`-layer preserves the integer shift, and the
existing Π-envelope action preserves the parity label. Both transport the
underlying 2-morphism and coherence maps without changing them.

`QPiTwoEnvelope.mapQPi` preserves grading, identities and composition. These
laws are consumed by `GTwoSCat.envelope`, a functor of the **1-truncations**.
This does not construct the action on graded 2-natural transformations or
supermodifications, or assert the full 2-adjunction.

The ungraded case is (4.7): `-_π` preserves identities and composition on the nose
(`TwoEnvelope.mapPi_id`, `TwoEnvelope.mapPi_comp`) and the canonical 2-superfunctors
`𝕁 : 𝔄 → 𝔄_π` are strictly natural, `ℝ_π ∘ 𝕁 = 𝕁 ∘ ℝ` (`TwoEnvelope.twoJ_comp_mapPi`). This gives
the functor of 1-truncations `TwoSCat.envelope : 2-SCat ⥤ Π-2-SCat` and the natural
transformation `TwoSCat.envelopeUnit : 𝟭 ⟶ -_π ⋙ ν` with components `𝕁`.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory GradedSupercategory BicategoryStruct TwoSupercategory

universe w w₁ v₁ u₁ w₂ v₂ u₂ w₃ v₃ u₃

namespace TwoEnvelope

open Envelope

variable {R : Type w} [CommRing R]
  {B : Type u₁} [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]
  {C : Type u₂} [BicategoryStruct.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ a b : C, Supercategory R (a ⟶ b)] [TwoSupercategory R C]
  {D : Type u₃} [BicategoryStruct.{w₃, v₃} D]
  [∀ a b : D, Preadditive (a ⟶ b)] [∀ a b : D, Linear R (a ⟶ b)]
  [∀ a b : D, Supercategory R (a ⟶ b)] [TwoSupercategory R D]

variable (R B) in
/-- **(4.7), strictness.** `-_π` preserves identity 2-superfunctors: `𝕀_π = 𝕀`. -/
theorem mapPi_id : mapPi (TwoSuperfunctor.id R B) = TwoSuperfunctor.id R (TwoEnvelope R B) := by
  refine twoSuperfunctor_ext rfl HEq.rfl HEq.rfl (heq_of_eq ?_) (heq_of_eq ?_)
  · funext a b c f g
    exact Iso.ext rfl
  · funext a
    exact Iso.ext rfl

/-- **(4.7), strictness.** `-_π` preserves composition of 2-superfunctors:
`(𝕊ℝ)_π = 𝕊_π ℝ_π`. -/
theorem mapPi_comp (F : TwoSuperfunctor R B C) (G : TwoSuperfunctor R C D) :
    mapPi (F.comp G) = (mapPi F).comp (mapPi G) := by
  refine twoSuperfunctor_ext rfl HEq.rfl HEq.rfl (heq_of_eq ?_) (heq_of_eq ?_)
  · funext a b c f g
    exact Iso.ext rfl
  · funext a
    exact Iso.ext rfl

/-- `ℝ_π` is graded if `ℝ` is. -/
theorem mapPi_isGraded [∀ a b : B, GradedSupercategory R (a ⟶ b)]
    [∀ a b : C, GradedSupercategory R (a ⟶ b)] {F : TwoSuperfunctor R B C} (hF : F.IsGraded) :
    (mapPi F).IsGraded where
  map₂_mem_degree hη := hF.map₂_mem_degree hη
  mapComp_hom_mem_degree f g := hF.mapComp_hom_mem_degree f.obj g.obj
  mapId_hom_mem_degree a := hF.mapId_hom_mem_degree a.as

/-- **(4.7).** The canonical 2-superfunctors `𝕁 : 𝔄 → 𝔄_π` are strictly natural:
`ℝ_π ∘ 𝕁 = 𝕁 ∘ ℝ`. -/
theorem twoJ_comp_mapPi (F : TwoSuperfunctor R B C) :
    (twoJ R B).comp (mapPi F) = F.comp (twoJ R C) := by
  refine twoSuperfunctor_ext rfl HEq.rfl HEq.rfl (heq_of_eq ?_) (heq_of_eq ?_)
  · funext a b c f g
    apply Iso.ext
    apply hom_ext
    change (F.mapComp f g).hom ≫ F.map₂ (𝟙 (f ≫ g)) = 𝟙 _ ≫ (F.mapComp f g).hom
    rw [F.map₂_id, Category.comp_id, Category.id_comp]
  · funext a
    apply Iso.ext
    apply hom_ext
    change (F.mapId a).hom ≫ F.map₂ (𝟙 (𝟙 a)) = 𝟙 _ ≫ (F.mapId a).hom
    rw [F.map₂_id, Category.comp_id, Category.id_comp]

end TwoEnvelope

namespace QTwoEnvelope

open QEnvelope

variable {R : Type w} [CommRing R]
  {B : Type u₁} [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]
  {C : Type u₂} [BicategoryStruct.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ a b : C, Supercategory R (a ⟶ b)] [TwoSupercategory R C]
  {D : Type u₃} [BicategoryStruct.{w₃, v₃} D]
  [∀ a b : D, Preadditive (a ⟶ b)] [∀ a b : D, Linear R (a ⟶ b)]
  [∀ a b : D, Supercategory R (a ⟶ b)] [TwoSupercategory R D]

/-- The 2-superfunctor `ℝ_q : 𝔄_q → 𝔅_q` induced by a 2-superfunctor `ℝ : 𝔄 → 𝔅`:
`Q^mF ↦ Q^m(ℝF)`, `x^n_m ↦ (ℝx)^n_m`, with coherence maps `(c_{F,G})^{m+n}_{m+n}` and `i^0_0`.
All axioms are those of `ℝ`. -/
def mapQ (F : TwoSuperfunctor R B C) :
    TwoSuperfunctor R (QTwoEnvelope R B) (QTwoEnvelope R C) where
  obj a := ⟨F.obj a.as⟩
  map f := ⟨f.shift, F.map f.obj⟩
  map₂ η := QEnvelope.ofHom (F.map₂ (QEnvelope.toHom η))
  map₂_id f := F.map₂_id f.obj
  map₂_comp η θ := F.map₂_comp (QEnvelope.toHom η) (QEnvelope.toHom θ)
  map₂_add η θ := F.map₂_add (QEnvelope.toHom η) (QEnvelope.toHom θ)
  map₂_smul r η := F.map₂_smul r (QEnvelope.toHom η)
  map₂_mem hη := F.map₂_mem hη
  mapComp f g := QEnvelope.isoOfIso (F.mapComp f.obj g.obj)
  mapId a := QEnvelope.isoOfIso (F.mapId a.as)
  mapComp_hom_mem f g := F.mapComp_hom_mem f.obj g.obj
  mapId_hom_mem a := F.mapId_hom_mem a.as
  mapComp_naturality_left η g := F.mapComp_naturality_left (QEnvelope.toHom η) g.obj
  mapComp_naturality_right f _ _ η := F.mapComp_naturality_right f.obj (QEnvelope.toHom η)
  map₂_associator f g h := F.map₂_associator f.obj g.obj h.obj
  map₂_leftUnitor f := F.map₂_leftUnitor f.obj
  map₂_rightUnitor f := F.map₂_rightUnitor f.obj

omit [TwoSupercategory R B] [TwoSupercategory R C] in
@[simp] theorem mapQ_obj (F : TwoSuperfunctor R B C) (a : QTwoEnvelope R B) :
    (mapQ F).obj a = ⟨F.obj a.as⟩ := rfl

omit [TwoSupercategory R B] [TwoSupercategory R C] in
theorem mapQ_map (F : TwoSuperfunctor R B C) {a b : QTwoEnvelope R B} (f : a ⟶ b) :
    (mapQ F).map f = ⟨f.shift, F.map f.obj⟩ := rfl

omit [TwoSupercategory R B] [TwoSupercategory R C] in
theorem toHom_mapQ_map₂ (F : TwoSuperfunctor R B C) {a b : QTwoEnvelope R B} {f g : a ⟶ b}
    (η : f ⟶ g) : QEnvelope.toHom ((mapQ F).map₂ η) = F.map₂ (QEnvelope.toHom η) := rfl

omit [TwoSupercategory R B] [TwoSupercategory R C] in
theorem toHom_mapQ_mapComp (F : TwoSuperfunctor R B C) {a b c : QTwoEnvelope R B} (f : a ⟶ b)
    (g : b ⟶ c) :
    QEnvelope.toHom ((mapQ F).mapComp f g).hom = (F.mapComp f.obj g.obj).hom := rfl

omit [TwoSupercategory R B] [TwoSupercategory R C] in
theorem toHom_mapQ_mapId (F : TwoSuperfunctor R B C) (a : QTwoEnvelope R B) :
    QEnvelope.toHom ((mapQ F).mapId a).hom = (F.mapId a.as).hom := rfl

omit [TwoSupercategory R B] [TwoSupercategory R C] in
/-- `ℝ_q` is graded if `ℝ` is. -/
theorem mapQ_isGraded [∀ a b : B, GradedSupercategory R (a ⟶ b)]
    [∀ a b : C, GradedSupercategory R (a ⟶ b)] {F : TwoSuperfunctor R B C} (hF : F.IsGraded) :
    (mapQ F).IsGraded where
  map₂_mem_degree hη := hF.map₂_mem_degree hη
  mapComp_hom_mem_degree f g := by
    show (F.mapComp f.obj g.obj).hom ∈ degree (R := R) (F.map f.obj ≫ F.map g.obj) (F.map (f.obj ≫ g.obj))
      (0 + (f.shift + g.shift - (f.shift + g.shift)))
    rw [show (0 : ℤ) + (f.shift + g.shift - (f.shift + g.shift)) = 0 by ring]
    exact hF.mapComp_hom_mem_degree f.obj g.obj
  mapId_hom_mem_degree a := by
    show (F.mapId a.as).hom ∈ degree (R := R) (𝟙 (F.obj a.as)) (F.map (𝟙 a.as)) (0 + (0 - 0))
    rw [show (0 : ℤ) + (0 - 0) = 0 by ring]
    exact hF.mapId_hom_mem_degree a.as

variable (R B) in
/-- `-_q` preserves identity 2-superfunctors. -/
theorem mapQ_id : mapQ (TwoSuperfunctor.id R B) = TwoSuperfunctor.id R (QTwoEnvelope R B) := by
  refine TwoEnvelope.twoSuperfunctor_ext rfl HEq.rfl HEq.rfl (heq_of_eq ?_) (heq_of_eq ?_)
  · funext a b c f g
    exact Iso.ext rfl
  · funext a
    exact Iso.ext rfl

omit [TwoSupercategory R B] [TwoSupercategory R C] in
/-- `-_q` preserves composition of 2-superfunctors. -/
theorem mapQ_comp (F : TwoSuperfunctor R B C) (G : TwoSuperfunctor R C D) :
    mapQ (F.comp G) = (mapQ F).comp (mapQ G) := by
  refine TwoEnvelope.twoSuperfunctor_ext rfl HEq.rfl HEq.rfl (heq_of_eq ?_) (heq_of_eq ?_)
  · funext a b c f g
    exact Iso.ext rfl
  · funext a
    exact Iso.ext rfl

end QTwoEnvelope

namespace QPiTwoEnvelope

variable {R : Type w} [CommRing R]
  {B : Type u₁} [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]
  {C : Type u₂} [BicategoryStruct.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ a b : C, Supercategory R (a ⟶ b)] [TwoSupercategory R C]
  {D : Type u₃} [BicategoryStruct.{w₃, v₃} D]
  [∀ a b : D, Preadditive (a ⟶ b)] [∀ a b : D, Linear R (a ⟶ b)]
  [∀ a b : D, Supercategory R (a ⟶ b)] [TwoSupercategory R D]

/-- **§6, (6.2).** The 2-superfunctor `ℝ_{q,π} : 𝔄_{q,π} → 𝔅_{q,π}` induced by a 2-superfunctor
`ℝ : 𝔄 → 𝔅`: `Q^mΠ^aF ↦ Q^mΠ^a(ℝF)`, `x^{n,b}_{m,a} ↦ (ℝx)^{n,b}_{m,a}`, with coherence maps
`(c_{F,G})^{m+n,a+b}_{m+n,a+b}` and `i^{0,0}_{0,0}`. -/
def mapQPi (F : TwoSuperfunctor R B C) :
    TwoSuperfunctor R (QPiTwoEnvelope R B) (QPiTwoEnvelope R C) :=
  TwoEnvelope.mapPi (QTwoEnvelope.mapQ F)

@[simp] theorem mapQPi_obj (F : TwoSuperfunctor R B C) (a : QPiTwoEnvelope R B) :
    (mapQPi F).obj a = ⟨⟨F.obj a.as.as⟩⟩ := rfl

theorem mapQPi_map (F : TwoSuperfunctor R B C) {a b : QPiTwoEnvelope R B} (f : a ⟶ b) :
    (mapQPi F).map f = ⟨f.par, ⟨f.obj.shift, F.map f.obj.obj⟩⟩ := rfl

theorem toHom_mapQPi_map₂ (F : TwoSuperfunctor R B C) {a b : QPiTwoEnvelope R B} {f g : a ⟶ b}
    (η : f ⟶ g) : toHom ((mapQPi F).map₂ η) = F.map₂ (toHom η) := rfl

theorem toHom_mapQPi_mapComp (F : TwoSuperfunctor R B C) {a b c : QPiTwoEnvelope R B}
    (f : a ⟶ b) (g : b ⟶ c) :
    toHom ((mapQPi F).mapComp f g).hom = (F.mapComp f.obj.obj g.obj.obj).hom := rfl

theorem toHom_mapQPi_mapId (F : TwoSuperfunctor R B C) (a : QPiTwoEnvelope R B) :
    toHom ((mapQPi F).mapId a).hom = (F.mapId a.as.as).hom := rfl

/-- `ℝ_{q,π}` is graded if `ℝ` is. -/
theorem mapQPi_isGraded [∀ a b : B, GradedSupercategory R (a ⟶ b)]
    [∀ a b : C, GradedSupercategory R (a ⟶ b)] {F : TwoSuperfunctor R B C} (hF : F.IsGraded) :
    (mapQPi F).IsGraded :=
  TwoEnvelope.mapPi_isGraded (QTwoEnvelope.mapQ_isGraded hF)

variable (R B) in
/-- **(6.2), strictness.** `-_{q,π}` preserves identity 2-superfunctors. -/
theorem mapQPi_id :
    mapQPi (TwoSuperfunctor.id R B) = TwoSuperfunctor.id R (QPiTwoEnvelope R B) := by
  rw [mapQPi, QTwoEnvelope.mapQ_id, TwoEnvelope.mapPi_id]

/-- **(6.2), strictness.** `-_{q,π}` preserves composition of 2-superfunctors. -/
theorem mapQPi_comp (F : TwoSuperfunctor R B C) (G : TwoSuperfunctor R C D) :
    mapQPi (F.comp G) = (mapQPi F).comp (mapQPi G) := by
  rw [mapQPi, QTwoEnvelope.mapQ_comp, TwoEnvelope.mapPi_comp]
  rfl

end QPiTwoEnvelope

namespace GTwoSCat

variable {R : Type w} [CommRing R]

/-- **Brundan–Ellis, §6, (6.2).** The functor `-_{q,π} : 2-GSCat ⥤ (Q, Π)-2-GSCat`, sending a
graded 2-supercategory to its `(Q, Π)`-envelope (Definition 6.10) and a graded 2-superfunctor
`ℝ` to `ℝ_{q,π}` (`QPiTwoEnvelope.mapQPi`). -/
def envelope : GTwoSCat.{w, w₁, v₁, u₁} R ⥤ QPiTwoGSCat.{w, w₁, v₁, u₁} R where
  obj B := QPiTwoGSCat.of R (QPiTwoEnvelope R B)
  map F := ⟨QPiTwoEnvelope.mapQPi F.1, QPiTwoEnvelope.mapQPi_isGraded F.2⟩
  map_id B := Subtype.ext (QPiTwoEnvelope.mapQPi_id R B)
  map_comp F G := Subtype.ext (QPiTwoEnvelope.mapQPi_comp F.1 G.1)

@[simp] theorem envelope_obj (B : GTwoSCat.{w, w₁, v₁, u₁} R) :
    envelope.obj B = QPiTwoGSCat.of R (QPiTwoEnvelope R B) := rfl

@[simp] theorem envelope_map_val {B C : GTwoSCat.{w, w₁, v₁, u₁} R} (F : B ⟶ C) :
    (envelope.map F).1 = QPiTwoEnvelope.mapQPi F.1 := rfl

end GTwoSCat

namespace TwoSCat

variable {R : Type w} [CommRing R]

/-- **Brundan–Ellis, (4.7).** The functor `-_π : 2-SCat ⥤ Π-2-SCat` of 1-truncations, sending a
2-supercategory to its Π-envelope (Definition 4.4) and a 2-superfunctor `ℝ` to `ℝ_π`
(`TwoEnvelope.mapPi`). -/
def envelope : TwoSCat.{w, w₁, v₁, u₁} R ⥤ PiTwoSCat.{w, w₁, v₁, u₁} R where
  obj B := PiTwoSCat.of R (TwoEnvelope R B)
  map F := TwoEnvelope.mapPi F
  map_id B := TwoEnvelope.mapPi_id R B
  map_comp F G := TwoEnvelope.mapPi_comp F G

@[simp] theorem envelope_obj (B : TwoSCat.{w, w₁, v₁, u₁} R) :
    envelope.obj B = PiTwoSCat.of R (TwoEnvelope R B) := rfl

@[simp] theorem envelope_map {B C : TwoSCat.{w, w₁, v₁, u₁} R} (F : B ⟶ C) :
    envelope.map F = TwoEnvelope.mapPi F := rfl

/-- **Brundan–Ellis, (4.7).** The canonical 2-superfunctors `𝕁 : 𝔄 → 𝔄_π` form a natural
transformation `𝟭 ⟶ -_π ⋙ ν` of functors of 1-truncations (`TwoEnvelope.twoJ_comp_mapPi`).
This is not a claim of a global 2-adjunction. -/
def envelopeUnit : 𝟭 (TwoSCat.{w, w₁, v₁, u₁} R) ⟶ envelope ⋙ PiTwoSCat.forget where
  app B := TwoEnvelope.twoJ R B
  naturality _ _ F := (TwoEnvelope.twoJ_comp_mapPi F).symm

@[simp] theorem envelopeUnit_app (B : TwoSCat.{w, w₁, v₁, u₁} R) :
    envelopeUnit.app B = TwoEnvelope.twoJ R B := rfl

end TwoSCat

end StringDiagrams
