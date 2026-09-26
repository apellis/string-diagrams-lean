import StringDiagrams.Super.QAssociatedTwo
import StringDiagrams.Super.OrbitLift

/-!
# `𝔻 ∘ 𝔼 ≅ 𝕀` for graded (Q, Π)-2-supercategories

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §6, the
discussion after Definition 6.14: for a graded `(Q, Π)`-2-supercategory `𝔅`, the associated
graded `(Q, Π)`-2-supercategory `(𝔅̲)^ = QAssociated2 R (GUnderlying2 R 𝔅)` of its underlying
`(Q, Π)`-2-category is isomorphic to `𝔅`.

* `𝔅` carries the central invertible family `(q, q⁻¹, ii, jj, γ)` of Lemma 6.6
  (`QPiTwoSupercategory.centralShift`), so each morphism supercategory `ℋom_𝔅(λ, μ)` carries
  the shift datum `- q_μ`, trivialized by `σ_F := F σ_μ` (`QPiTwoSupercategory.homTriv`).
* `𝕋_𝔅 : (𝔅̲)^ → 𝔅` (`QAssociated2.T`) is the identity on objects and 1-morphisms, and on
  2-morphisms the lift (`Orbit.lift`) of the functor `𝕋` of Lemma 5.4 on the morphism
  categories: a family `(x_{i,j})` of degree `m` goes to `τ_{-m} ∘ 𝕋(x_{0,-m})`, where
  `τ_{-m} : F q_μ^{-m} ≅ F` is built from `σ`. It is a 2-superfunctor with identity coherence
  maps, graded (`QAssociated2.T_map₂_mem_degree`), bijective on 2-morphisms
  (`QAssociated2.T_map₂_bijective`), and carries `σ` to `σ` (`QAssociated2.T_map₂_σ`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory GradedSupercategory BicategoryStruct TwoSupercategory

universe w w₁ v₁ u₁

namespace QPiTwoSupercategory

variable {R : Type w} [CommRing R] {B : Type u₁} [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [∀ a b : B, GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R B] [GradedTwoSupercategory R B] [QPiTwoSupercategory R B]

variable (R B) in
/-- **Lemma 6.6.** A graded `(Q, Π)`-2-supercategory carries the central invertible family
`(q, q⁻¹, ii, jj, γ)`. -/
def centralShift : CentralShift R B where
  q a := q (R := R) a
  qinv a := qinv (R := R) a
  ii a := ii (R := R) a
  jj a := jj (R := R) a
  ii_hom_mem a := ii_hom_mem a
  jj_hom_mem a := jj_hom_mem a
  q_ii a := q_ii a
  γ f := γ (R := R) f
  γ_hom_mem f := γ_hom_mem f
  γ_naturality η := γ_naturality η
  γ_comp f g := γ_comp f g
  γ_id a := γ_id a
  γ_q a := γ_q a

attribute [local instance] centralShift

open CentralShift

theorem centralShift_q (a : B) : CentralShift.q (R := R) a = QPiTwoSupercategory.q (R := R) a := rfl

variable (R) in
/-- The trivialization `σ_F := F σ_μ` of the shift datum `- q_μ` on `ℋom_𝔅(λ, μ)`. -/
def homTriv (a b : B) : (homShift R a b).Trivialization where
  σ f := whiskerLeftIso (R := R) f (σ (R := R) b) ≪≫ rightUnitor f
  σ_mem f := by
    simpa using comp_mem (whiskerLeft_mem f (σ_hom_mem (R := R) b)) (rightUnitor_hom_mem (R := R) f)
  σ_mem_degree f := by
    simpa using comp_mem_degree (GradedTwoSupercategory.whiskerLeft_mem_degree f
      (σ_hom_mem_degree (R := R) b)) (GradedTwoSupercategory.rightUnitor_hom_mem_degree (R := R) f)
  σ_naturality {f g} η := by
    simp only [homShift_Q, postcomp_obj, postcomp_map, Iso.trans_hom, whiskerLeftIso_hom]
    have e := whisker_exchange_of_even_right (R := R) η (σ_hom_mem (R := R) b)
    erw [← Category.assoc, e, Category.assoc, rightUnitor_naturality R, Category.assoc]
  counit_mem_degree f := by
    change (CentralShift.counitIso (R := R) a b).hom.app f ∈ _
    rw [counitIso_hom_app]
    simpa using comp_mem_degree (comp_mem_degree
      (GradedTwoSupercategory.associator_hom_mem_degree (R := R) f _ _)
      (GradedTwoSupercategory.whiskerLeft_mem_degree f (jj_hom_mem_degree (R := R) b)))
      (GradedTwoSupercategory.rightUnitor_hom_mem_degree (R := R) f)

theorem homTriv_σ_hom {a b : B} (f : a ⟶ b) :
    ((homTriv R a b).σ f).hom = f ◁ (σ (R := R) b).hom ≫ (rightUnitor f).hom := rfl

/-- Horizontal composition with a 1-morphism on the left is compatible with the
trivializations `σ`. -/
theorem preShift_trivCompat {a b : B} (c : B) (f : a ⟶ b) :
    Orbit.IsTrivCompatible (homTriv R b c) (homTriv R a c) (preShift R c f) := fun X => by
  simp only [preShift_γ_inv_app, homTriv_σ_hom, preShift_F, precomp_obj, precomp_map,
    whiskerLeft_comp' R]
  change (associator f X (q (R := R) c)).inv ≫ (f ≫ X) ◁ (σ (R := R) c).hom ≫ _ = _
  rw [← associator_inv_naturality_right_assoc R, whiskerLeft_rightUnitor R]

/-- Horizontal composition with a 1-morphism on the right is compatible with the
trivializations `σ`. -/
theorem postShift_trivCompat (a : B) {b c : B} (h : b ⟶ c) :
    Orbit.IsTrivCompatible (homTriv R a b) (homTriv R a c) (postShift R a h) := fun X => by
  have key : (γ (R := R) h).inv ≫ h ◁ (σ (R := R) c).hom ≫ (rightUnitor h).hom =
      (σ (R := R) b).hom ▷ h ≫ (leftUnitor h).hom := by
    rw [Iso.inv_comp_eq, reassoc_of% (γ_hom_comp_σ (R := R) h)]
    simp
  simp only [postShift_γ_inv_app, homTriv_σ_hom, postShift_F, postcomp_obj, postcomp_map,
    γR_inv, Category.assoc]
  change _ ≫ X ◁ (γ (R := R) h).inv ≫ (associator X h (q (R := R) c)).inv ≫
    (X ≫ h) ◁ (σ (R := R) c).hom ≫ (rightUnitor (X ≫ h)).hom = _
  rw [← associator_inv_naturality_right_assoc R, ← whiskerLeft_rightUnitor R,
    ← whiskerLeft_comp' R, ← whiskerLeft_comp' R, key, whiskerLeft_comp' R,
    comp_whiskerRight' R, whisker_assoc (R := R), ← TwoSupercategory.triangle (R := R)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rfl

end QPiTwoSupercategory

namespace QAssociated2

variable {R : Type w} [CommRing R] {B : Type u₁} [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [∀ a b : B, GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R B] [GradedTwoSupercategory R B] [QPiTwoSupercategory R B]

attribute [local instance] QPiTwoSupercategory.centralShift

open CentralShift QPiTwoSupercategory Orbit

/-- The Π-2-supercategory `(𝔅̲)^` associated to the underlying `(Q, Π)`-2-category of `𝔅`. -/
local notation "𝔄" => Associated2 R (GUnderlying2 R B)

/-- The object of `𝔅` underlying an object of `(𝔅̲)^`. -/
abbrev bo (a : 𝔄) : B := a.obj.obj.as

variable (R B) in
/-- The functor `𝕋 : ℋom_{(𝔅̲)^}(λ, μ) ⥤ ℋom_𝔅(λ, μ)` of Lemma 5.4 (for the Π-2-supercategory
of 2-morphisms of degree zero of `𝔅`), followed by the inclusion of the 2-morphisms of degree
zero: `(x₀, x₁) ↦ x₀ + ζ_μ G ∘ x₁`. -/
def TF (a b : 𝔄) : (a ⟶ b) ⥤ (bo a ⟶ bo b) :=
  (Associated2.T R (DegreeZero2 R B)).mapFunctor a b ⋙ DegreeZero.ι R (bo a ⟶ bo b)

instance (a b : 𝔄) : (TF R B a b).Additive where
  map_add {_ _ x y} := congrArg Subtype.val ((Associated2.T R (DegreeZero2 R B)).map₂_add x y)

instance (a b : 𝔄) : (TF R B a b).Linear R where
  map_smul x r := congrArg Subtype.val ((Associated2.T R (DegreeZero2 R B)).map₂_smul r x)

instance (a b : 𝔄) : IsSuperfunctor R (TF R B a b) where
  map_mem hx := (Associated2.T R (DegreeZero2 R B)).map₂_mem hx

theorem TF_obj {a b : 𝔄} (f : a ⟶ b) : (TF R B a b).obj f = f.obj.obj.obj := rfl

theorem TF_map {a b : 𝔄} {f g : a ⟶ b} (x : f ⟶ g) :
    (TF R B a b).map x = ((Associated2.T R (DegreeZero2 R B)).map₂ x).1 := rfl

theorem TF_map_mem_degree {a b : 𝔄} {f g : a ⟶ b} (x : f ⟶ g) :
    (TF R B a b).map x ∈ degree (R := R) _ _ 0 :=
  ((Associated2.T R (DegreeZero2 R B)).map₂ x).2

theorem TF_map_injective {a b : 𝔄} {f g : a ⟶ b} {x y : f ⟶ g}
    (h : (TF R B a b).map x = (TF R B a b).map y) : x = y :=
  Associated2.T_map₂_injective (DegreeZero.hom_ext h)

instance (a b : 𝔄) : (TF R B a b).Faithful where
  map_injective h := TF_map_injective h

theorem TF_map_surjective {a b : 𝔄} {f g : a ⟶ b}
    (h : (TF R B a b).obj f ⟶ (TF R B a b).obj g) (hh : h ∈ degree (R := R) _ _ 0) :
    ∃ x : f ⟶ g, (TF R B a b).map x = h := by
  obtain ⟨x, hx⟩ := (Associated2.T_map₂_bijective (R := R) (A := DegreeZero2 R B) f g).2
    (⟨h, hh⟩ : (⟨(TF R B a b).obj f⟩ : DegreeZero R (bo a ⟶ bo b)) ⟶ ⟨(TF R B a b).obj g⟩)
  exact ⟨x, congrArg Subtype.val hx⟩

theorem TF_whiskerRight {a b c : 𝔄} {f g : a ⟶ b} (x : f ⟶ g) (h : b ⟶ c) :
    (TF R B a c).map (x ▷ h) = (TF R B a b).map x ▷ (TF R B b c).obj h := by
  have e := (Associated2.T R (DegreeZero2 R B)).mapComp_naturality_left x h
  simp only [Associated2.T_mapComp, Iso.refl_hom] at e
  erw [Category.id_comp, Category.comp_id] at e
  exact (congrArg Subtype.val e).symm

theorem TF_whiskerLeft {a b c : 𝔄} (f : a ⟶ b) {g h : b ⟶ c} (x : g ⟶ h) :
    (TF R B a c).map (f ◁ x) = (TF R B a b).obj f ◁ (TF R B b c).map x := by
  have e := (Associated2.T R (DegreeZero2 R B)).mapComp_naturality_right f x
  simp only [Associated2.T_mapComp, Iso.refl_hom] at e
  erw [Category.id_comp, Category.comp_id] at e
  exact (congrArg Subtype.val e).symm

theorem TF_associator_hom {a b c d : 𝔄} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (TF R B a d).map (associator f g h).hom =
      (associator ((TF R B a b).obj f) ((TF R B b c).obj g) ((TF R B c d).obj h)).hom := by
  simp [TF_map, Associated2.T_map₂]
  rfl

theorem TF_associator_inv {a b c d : 𝔄} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (TF R B a d).map (associator f g h).inv =
      (associator ((TF R B a b).obj f) ((TF R B b c).obj g) ((TF R B c d).obj h)).inv := by
  simp [TF_map, Associated2.T_map₂]
  rfl

theorem TF_leftUnitor_hom {a b : 𝔄} (f : a ⟶ b) :
    (TF R B a b).map (leftUnitor f).hom = (leftUnitor ((TF R B a b).obj f)).hom := by
  simp [TF_map, Associated2.T_map₂]
  rfl

theorem TF_rightUnitor_hom {a b : 𝔄} (f : a ⟶ b) :
    (TF R B a b).map (rightUnitor f).hom = (rightUnitor ((TF R B a b).obj f)).hom := by
  simp [TF_map, Associated2.T_map₂]
  rfl

theorem TF_γ {a b : 𝔄} (f : a ⟶ b) :
    (TF R B a b).map (CentralShift.γ (R := R) f).hom =
      (QPiTwoSupercategory.γ (R := R) ((TF R B a b).obj f)).hom := by
  simp [TF_map, Associated2.T_map₂, Associated2.centralShift_γ_eq]
  rfl

variable (R B) in
/-- `TF` as a morphism of shift data `(- q_μ) → (- q_μ)`, with `γ = 1`. -/
def TΦ (a b : 𝔄) : ShiftFunctor R (homShift R a b) (homShift R (bo a) (bo b)) where
  F := TF R B a b
  γ := NatIso.ofComponents (fun _ => Iso.refl _)
    (fun {f g} x => by
      simp only [Functor.comp_obj, Functor.comp_map, homShift_Q, postcomp_obj, postcomp_map,
        Iso.refl_hom, Category.comp_id, Category.id_comp]
      exact (TF_whiskerRight x (CentralShift.q (R := R) b)).symm)
  γ_mem _ := id_mem _

@[simp] theorem TΦ_F (a b : 𝔄) : (TΦ R B a b).F = TF R B a b := rfl

@[simp] theorem TΦ_γ_hom_app {a b : 𝔄} (f : a ⟶ b) : (TΦ R B a b).γ.hom.app f = 𝟙 _ := rfl

@[simp] theorem TΦ_γ_inv_app {a b : 𝔄} (f : a ⟶ b) : (TΦ R B a b).γ.inv.app f = 𝟙 _ := rfl

variable (R B) in
/-- `𝕋` on the morphism supercategories: the lift of `TΦ` along the trivialization
`σ_F = F σ_μ`. -/
def Thom (a b : 𝔄) : Orbit (homShift R a b) ⥤ (bo a ⟶ bo b) :=
  Orbit.lift (homTriv R (bo a) (bo b)) (TΦ R B a b)

/-! ### Compatibility of `𝕋` with horizontal composition -/

theorem TF_γR {a b c : 𝔄} (g : a ⟶ b) (h : b ⟶ c) :
    (TF R B a c).map (CentralShift.γR (R := R) g h).hom =
      (CentralShift.γR (R := R) ((TF R B a b).obj g) ((TF R B b c).obj h)).hom := by
  rw [γR_hom, γR_hom, Functor.map_comp, Functor.map_comp, TF_associator_hom, TF_whiskerLeft,
    TF_associator_inv, TF_γ]
  rfl

theorem map_post_comp {a : 𝔄} {b c : 𝔄} (h : b ⟶ c) :
    Orbit.map ((postShift R a h).comp (TΦ R B a c)) =
      Orbit.map ((TΦ R B a b).comp (postShift R (bo a) ((TF R B b c).obj h))) := by
  refine Orbit.map_congr' (fun _ => rfl) (fun y => ?_) fun X => ?_
  · simp only [ShiftFunctor.comp_F, Functor.comp_map, postShift_F, postcomp_map, TΦ_F,
      eqToHom_refl, Category.comp_id, Category.id_comp]
    exact TF_whiskerRight y h
  · simp only [ShiftFunctor.comp_γ_hom_app, TΦ_γ_hom_app, postShift_γ_hom_app, TΦ_F,
      postShift_F, eqToHom_refl, Category.comp_id, Category.id_comp]
    rw [TF_γR, postcomp_map]
    erw [id_whiskerRight (R := R), Category.comp_id]

theorem map_pre_comp {a b : 𝔄} (c : 𝔄) (f : a ⟶ b) :
    Orbit.map ((preShift R c f).comp (TΦ R B a c)) =
      Orbit.map ((TΦ R B b c).comp (preShift R (bo c) ((TF R B a b).obj f))) := by
  refine Orbit.map_congr' (fun _ => rfl) (fun y => ?_) fun X => ?_
  · simp only [ShiftFunctor.comp_F, Functor.comp_map, preShift_F, precomp_map, TΦ_F,
      eqToHom_refl, Category.comp_id, Category.id_comp]
    exact TF_whiskerLeft f y
  · simp only [ShiftFunctor.comp_γ_hom_app, TΦ_γ_hom_app, preShift_γ_hom_app, TΦ_F,
      preShift_F, eqToHom_refl, Category.comp_id, Category.id_comp]
    rw [TF_associator_hom, precomp_map]
    erw [whiskerLeft_id (R := R), Category.comp_id]
    rfl

variable {a b c : QAssociated2 R (GUnderlying2 R B)}

theorem Thom_whiskerRight {f g : a ⟶ b} (x : f ⟶ g) (h : b ⟶ c) :
    (Thom R B a.obj c.obj).map (x ▷ h) =
      (Thom R B a.obj b.obj).map x ▷ (TF R B b.obj c.obj).obj h.obj := by
  rw [Orbit2.whiskerRight_def]
  unfold Thom
  have e := CategoryTheory.Functor.congr_hom (map_post_comp (a := a.obj) h.obj) x
  erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id] at e
  rw [lift_map, lift_map, map_map_comp]
  erw [e]
  rw [← map_map_comp, eval_map_map (postShift_trivCompat (R := R) _ _)]
  rfl

theorem Thom_whiskerLeft (f : a ⟶ b) {g h : b ⟶ c} (x : g ⟶ h) :
    (Thom R B a.obj c.obj).map (f ◁ x) =
      (TF R B a.obj b.obj).obj f.obj ◁ (Thom R B b.obj c.obj).map x := by
  rw [Orbit2.whiskerLeft_def]
  unfold Thom
  have e := CategoryTheory.Functor.congr_hom (map_pre_comp c.obj f.obj) x
  erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id] at e
  rw [lift_map, lift_map, map_map_comp]
  erw [e]
  rw [← map_map_comp, eval_map_map (preShift_trivCompat (R := R) _ _)]
  rfl

end QAssociated2

end StringDiagrams

end
