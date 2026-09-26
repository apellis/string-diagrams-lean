import StringDiagrams.Super.OrbitTwo
import StringDiagrams.Super.QPiTwoCategory
import StringDiagrams.Super.AssociatedTwoNat

/-!
# The graded (Q, Π)-2-supercategory associated to a (Q, Π)-2-category

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §6, the
discussion after Definition 6.14: for a `(Q, Π)`-2-category `𝔄` there is an associated graded
`(Q, Π)`-2-supercategory `𝔄̂`, "which we leave to the reader", such that the constructions
`𝔄 ↦ 𝔄̲` (`GUnderlying2`) and `𝔄 ↦ 𝔄̂` are mutually inverse up to isomorphism.

* The Π-2-supercategory `Associated2 R 𝔄` of (5.5) carries the central invertible family
  `(q, q⁻¹, ii, jj, γ)` of `𝔄`, viewed in degree zero (`Associated2.instCentralShift`); that
  `γ` is natural with respect to the odd 2-morphisms of `Associated2 R 𝔄` uses the axiom
  `γ_{π_λ} = β_{q_λ}⁻¹` of Definition 6.14(ii).
* `QAssociated2 R 𝔄 := Orbit2 R (Associated2 R 𝔄)` is the associated graded
  `(Q, Π)`-2-supercategory (the 2-categorical orbit construction of
  `StringDiagrams.Super.OrbitTwo`): its 2-morphisms `F ⇒ G` of degree `m` and parity `a` are
  the 2-morphisms `F ⇒ G q_μ^{-m} π_μ^a` of `𝔄` (with the degree convention of the erratum to
  Theorem 6.13), in the form of `q_μ`-compatible families.
* **`𝔼 ∘ 𝔻 = 𝕀` on objects**: the identification `QAssociated2.unit : 𝔄 → (𝔄̂)̲` (the identity
  on objects and 1-morphisms, and `x ↦ (x, 0)` in degree zero on 2-morphisms) is a strict
  pseudofunctor, bijective on 2-morphisms (`QAssociated2.unit_map₂_bijective`), and carries
  `π`, `q`, `q⁻¹`, `β`, `ξ` and `γ` of `𝔄` to those of `(𝔄̂)̲` (`QAssociated2.unitPiTwoFunctor`,
  `QAssociated2.unit_γ`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Bicategory Supercategory

universe w w₁ v₁ u₁

namespace Associated2

variable {R : Type w} [CommRing R] {B : Type u₁} [Bicategory.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)] [PreadditiveBicategory B]
  [LinearBicategory R B] [QPiTwoCategory R B]

open PiTwoCategory QPiTwoCategory BicategoryStruct

local notation "𝛑" => PiTwoCategory.pi (R := R)
local notation "𝐪" => QPiTwoCategory.q (R := R)
local notation "𝐪⁻" => QPiTwoCategory.qinv (R := R)
local notation "𝛄" => QPiTwoCategory.γ (R := R)

variable {a b c : Associated2 R B}

/-- `γ_F` of `𝔄`, as an even 2-isomorphism `F q_μ ≅ q_λ F` of `𝔄̂`. -/
def γhat (f : a ⟶ b) : f ≫ (⟨𝐪 b.obj⟩ : b ⟶ b) ≅ (⟨𝐪 a.obj⟩ : a ⟶ a) ≫ f :=
  Associated.evenIso (𝛄 f.obj)

@[simp] theorem γhat_hom_fst (f : a ⟶ b) : (γhat (R := R) f).hom.1 = (𝛄 f.obj).hom := rfl

@[simp] theorem γhat_hom_snd (f : a ⟶ b) : (γhat (R := R) f).hom.2 = 0 := rfl

/-- **Definition 6.14(ii), `γ_{π_λ} = β_{q_λ}⁻¹`, at work.** `γ` is natural with respect to all
2-morphisms of `𝔄̂`, including the odd ones. -/
theorem γhat_naturality {f g : a ⟶ b} (η : f ⟶ g) :
    (γhat (R := R) f).hom ≫ (⟨𝐪 a.obj⟩ : a ⟶ a) ◁ η = η ▷ (⟨𝐪 b.obj⟩ : b ⟶ b) ≫ (γhat (R := R) g).hom := by
  apply hom₂_ext
  · simp only [comp₂_fst, whiskerLeft_fst, whiskerLeft_snd, whiskerRight_fst, whiskerRight_snd,
      γhat_hom_fst, γhat_hom_snd, PreadditiveBicategory.zero_whiskerRight, Limits.zero_comp,
      sub_zero, Limits.comp_zero]
    exact γ_naturality η.1
  · simp only [comp₂_snd, whiskerLeft_fst, whiskerLeft_snd, whiskerRight_fst, whiskerRight_snd,
      γhat_hom_fst, γhat_hom_snd, Limits.comp_zero, Limits.zero_comp, zero_add, add_zero, pi_map,
      pi_obj, Category.assoc]
    have n := γ_naturality (R := R) η.2
    rw [reassoc_of% n]
    erw [γ_comp]
    rw [γ_pi, βR_inv]
    simp

/-- **Brundan–Ellis, after Definition 6.14.** The Π-2-supercategory `𝔄̂` of a
`(Q, Π)`-2-category `𝔄` carries the central invertible family `(q, q⁻¹, ii, jj, γ)` of `𝔄`, in
degree zero. -/
instance instCentralShift : CentralShift R (Associated2 R B) where
  q a := ⟨𝐪 a.obj⟩
  qinv a := ⟨𝐪⁻ a.obj⟩
  ii a := Associated.evenIso (ii (R := R) a.obj)
  jj a := Associated.evenIso (jj (R := R) a.obj)
  ii_hom_mem _ := Associated.mem_parity_zero.2 rfl
  jj_hom_mem _ := Associated.mem_parity_zero.2 rfl
  q_ii a := by
    apply hom₂_ext
    · simpa using q_ii (R := R) a.obj
    · simp
  γ := γhat
  γ_hom_mem _ := Associated.mem_parity_zero.2 rfl
  γ_naturality := γhat_naturality
  γ_comp f g := by
    apply hom₂_ext
    · simpa using γ_comp (R := R) f.obj g.obj
    · simp
  γ_id a := by
    apply hom₂_ext
    · simpa using γ_id (R := R) a.obj
    · simp
  γ_q a := by
    apply hom₂_ext
    · simpa using γ_q (R := R) a.obj
    · simp

@[simp] theorem centralShift_q_obj (a : Associated2 R B) :
    (CentralShift.q (R := R) a).obj = 𝐪 a.obj := rfl

@[simp] theorem centralShift_qinv_obj (a : Associated2 R B) :
    (CentralShift.qinv (R := R) a).obj = 𝐪⁻ a.obj := rfl

theorem centralShift_γ_eq (f : a ⟶ b) : CentralShift.γ (R := R) f = γhat f := rfl

end Associated2

/-- **The graded `(Q, Π)`-2-supercategory associated to a `(Q, Π)`-2-category** (Brundan–Ellis,
after Definition 6.14): the orbit 2-supercategory of the Π-2-supercategory `𝔄̂` of (5.5) with
respect to `q`. -/
abbrev QAssociated2 (R : Type w) [CommRing R] (B : Type u₁) [Bicategory.{w₁, v₁} B]
    [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)] [PreadditiveBicategory B]
    [LinearBicategory R B] [QPiTwoCategory R B] :=
  Orbit2 R (Associated2 R B)

namespace QAssociated2

variable {R : Type w} [CommRing R] {B : Type u₁} [Bicategory.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)] [PreadditiveBicategory B]
  [LinearBicategory R B] [QPiTwoCategory R B]

example : QPiTwoSupercategory R (QAssociated2 R B) := inferInstance

open PiTwoCategory QPiTwoCategory CentralShift Orbit

/-- The 1-morphism of `𝔄̂` given by a 1-morphism of `𝔄`. -/
abbrev hom1 {a b : B} (f : a ⟶ b) : (⟨⟨a⟩⟩ : QAssociated2 R B) ⟶ ⟨⟨b⟩⟩ := ⟨⟨f⟩⟩

/-- The 2-morphism of `𝔄̂` (of degree zero, even) given by a 2-morphism of `𝔄`. -/
abbrev hom2 {a b : B} {f g : a ⟶ b} (η : f ⟶ g) : hom1 (R := R) f ⟶ hom1 g :=
  (Orbit.ι _).map (Associated.homMk (X := ⟨f⟩) (Y := ⟨g⟩) η 0)

theorem hom2_mem {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
    hom2 (R := R) η ∈ parity (R := R) (hom1 f) (hom1 g) 0 :=
  map_mem (Orbit.ι _) (Associated.mem_parity_zero.2 rfl)

theorem hom2_mem_degree {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
    hom2 (R := R) η ∈ GradedSupercategory.degree (R := R) (hom1 f) (hom1 g) 0 :=
  ι_map_mem_degree _

theorem hom2_id {a b : B} (f : a ⟶ b) : hom2 (R := R) (𝟙 f) = 𝟙 (hom1 f) :=
  (Orbit.ι _).map_id _

theorem hom2_comp {a b : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) :
    hom2 (R := R) (η ≫ θ) = hom2 η ≫ hom2 θ := by
  rw [← Functor.map_comp, Associated.homMk_comp_homMk_even]

theorem hom2_whiskerLeft {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    hom2 (R := R) (f ◁ η) = BicategoryStruct.whiskerLeft (hom1 (R := R) f) (hom2 η) := by
  rw [hom2, Orbit2.whiskerLeft_ι]
  congr 1
  apply Associated2.hom₂_ext <;> simp

theorem hom2_whiskerRight {a b c : B} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    hom2 (R := R) (η ▷ h) = BicategoryStruct.whiskerRight (hom2 (R := R) η) (hom1 h) := by
  rw [hom2, Orbit2.whiskerRight_ι]
  congr 1
  apply Associated2.hom₂_ext <;> simp

theorem hom2_associator_hom {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    hom2 (R := R) (α_ f g h).hom = (BicategoryStruct.associator (hom1 f) (hom1 g) (hom1 h)).hom := rfl

theorem hom2_associator_inv {a b c d : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    hom2 (R := R) (α_ f g h).inv = (BicategoryStruct.associator (hom1 f) (hom1 g) (hom1 h)).inv := rfl

theorem hom2_leftUnitor_hom {a b : B} (f : a ⟶ b) :
    hom2 (R := R) (λ_ f).hom = (BicategoryStruct.leftUnitor (hom1 f)).hom := rfl

theorem hom2_leftUnitor_inv {a b : B} (f : a ⟶ b) :
    hom2 (R := R) (λ_ f).inv = (BicategoryStruct.leftUnitor (hom1 f)).inv := rfl

theorem hom2_rightUnitor_hom {a b : B} (f : a ⟶ b) :
    hom2 (R := R) (ρ_ f).hom = (BicategoryStruct.rightUnitor (hom1 f)).hom := rfl

theorem hom2_rightUnitor_inv {a b : B} (f : a ⟶ b) :
    hom2 (R := R) (ρ_ f).inv = (BicategoryStruct.rightUnitor (hom1 f)).inv := rfl

/-- The 1-morphism of the underlying `(Q, Π)`-2-category of `𝔄̂` given by a 1-morphism of
`𝔄`. -/
abbrev hom1U {a b : B} (f : a ⟶ b) :
    (⟨⟨⟨⟨a⟩⟩⟩⟩ : GUnderlying2 R (QAssociated2 R B)) ⟶ ⟨⟨⟨⟨b⟩⟩⟩⟩ :=
  ⟨⟨hom1 f⟩⟩

/-- The 2-morphism of the underlying `(Q, Π)`-2-category of `𝔄̂` given by a 2-morphism of
`𝔄`. -/
abbrev hom2U {a b : B} {f g : a ⟶ b} (η : f ⟶ g) : hom1U (R := R) f ⟶ hom1U g :=
  ⟨⟨hom2 η, hom2_mem_degree η⟩, hom2_mem η⟩

variable (R B) in
/-- **`𝔼 ∘ 𝔻 = 𝕀` on objects.** The identification of a `(Q, Π)`-2-category `𝔄` with the
underlying `(Q, Π)`-2-category of `𝔄̂`: the identity on objects and 1-morphisms, and
`x ↦ (x, 0)` in degree zero on 2-morphisms, with identity coherence maps (a strict
pseudofunctor). -/
@[simps]
def unit : Pseudofunctor B (GUnderlying2 R (QAssociated2 R B)) where
  obj a := ⟨⟨⟨⟨a⟩⟩⟩⟩
  map f := hom1U f
  map₂ η := hom2U η
  map₂_id f := Subtype.ext (Subtype.ext (hom2_id f))
  map₂_comp η θ := Subtype.ext (Subtype.ext (hom2_comp η θ))
  mapId a := Iso.refl (𝟙 (⟨⟨⟨⟨a⟩⟩⟩⟩ : GUnderlying2 R (QAssociated2 R B)))
  mapComp f g := Iso.refl (hom1U f ≫ hom1U g)
  map₂_whisker_left f _ _ η := by
    simp only [Iso.refl_hom, Iso.refl_inv, Category.comp_id]
    refine Subtype.ext (Subtype.ext ?_)
    change hom2 (f ◁ η) = 𝟙 _ ≫ BicategoryStruct.whiskerLeft (hom1 f) (hom2 η)
    rw [Category.id_comp]
    exact hom2_whiskerLeft f η
  map₂_whisker_right η h := by
    simp only [Iso.refl_hom, Iso.refl_inv, Category.comp_id]
    refine Subtype.ext (Subtype.ext ?_)
    change hom2 (η ▷ h) = 𝟙 _ ≫ BicategoryStruct.whiskerRight (hom2 η) (hom1 h)
    rw [Category.id_comp]
    exact hom2_whiskerRight η h
  map₂_associator f g h := by
    simp only [Iso.refl_hom, Iso.refl_inv, Category.comp_id]
    refine Subtype.ext (Subtype.ext ?_)
    change hom2 (α_ f g h).hom = 𝟙 _ ≫ BicategoryStruct.whiskerRight (𝟙 (hom1 f ≫ hom1 g)) (hom1 h) ≫
      (BicategoryStruct.associator (hom1 f) (hom1 g) (hom1 h)).hom ≫
        BicategoryStruct.whiskerLeft (hom1 f) (𝟙 (hom1 g ≫ hom1 h))
    rw [Category.id_comp, TwoSupercategory.id_whiskerRight (R := R),
      TwoSupercategory.whiskerLeft_id (R := R), Category.id_comp, Category.comp_id]
    exact hom2_associator_hom f g h
  map₂_left_unitor f := by
    simp only [Iso.refl_hom, Iso.refl_inv, Category.comp_id]
    refine Subtype.ext (Subtype.ext ?_)
    change hom2 (λ_ f).hom = 𝟙 _ ≫ BicategoryStruct.whiskerRight (𝟙 (𝟙 _)) (hom1 f) ≫
      (BicategoryStruct.leftUnitor (hom1 f)).hom
    rw [Category.id_comp, TwoSupercategory.id_whiskerRight (R := R), Category.id_comp]
    exact hom2_leftUnitor_hom f
  map₂_right_unitor f := by
    simp only [Iso.refl_hom, Iso.refl_inv, Category.comp_id]
    refine Subtype.ext (Subtype.ext ?_)
    change hom2 (ρ_ f).hom = 𝟙 _ ≫ BicategoryStruct.whiskerLeft (hom1 f) (𝟙 (𝟙 _)) ≫
      (BicategoryStruct.rightUnitor (hom1 f)).hom
    rw [Category.id_comp, TwoSupercategory.whiskerLeft_id (R := R), Category.id_comp]
    exact hom2_rightUnitor_hom f

/-- The 2-morphism of `𝔄` underlying an even 2-morphism of degree zero of `𝔄̂` (the entry
`(0, 0)` of the family, and its even part). -/
def unitInv₂ {a b : B} {f g : a ⟶ b} (x : hom1U (R := R) f ⟶ hom1U g) : f ⟶ g :=
  ((π₀ (homShift R (⟨a⟩ : Associated2 R B) ⟨b⟩)).map
    (x.1 : (⟨hom1 f⟩ : GradedSupercategory.DegreeZero R
      (Orbit (homShift R (⟨a⟩ : Associated2 R B) ⟨b⟩))) ⟶ ⟨hom1 g⟩)).1

theorem unitInv₂_hom2U {a b : B} {f g : a ⟶ b} (η : f ⟶ g) : unitInv₂ (hom2U (R := R) η) = η := by
  show ((π₀ (homShift R (⟨a⟩ : Associated2 R B) ⟨b⟩)).map
    ((ιZ (homShift R (⟨a⟩ : Associated2 R B) ⟨b⟩)).map
      (Associated.homMk (X := ⟨f⟩) (Y := ⟨g⟩) η 0))).1 = η
  rw [ιZ_comp_π₀_map]
  rfl

theorem hom2U_unitInv₂ {a b : B} {f g : a ⟶ b} (x : hom1U (R := R) f ⟶ hom1U g) :
    hom2U (unitInv₂ x) = x := by
  refine Subtype.ext (Subtype.ext ?_)
  have hx1 : (x.1 : (⟨hom1 f⟩ : GradedSupercategory.DegreeZero R
      (Orbit (homShift R (⟨a⟩ : Associated2 R B) ⟨b⟩))) ⟶ ⟨hom1 g⟩) ∈
      parity (R := R) (⟨hom1 f⟩ : GradedSupercategory.DegreeZero R
        (Orbit (homShift R (⟨a⟩ : Associated2 R B) ⟨b⟩))) ⟨hom1 g⟩ 0 := x.2
  have hy0 := Associated.mem_parity_zero.1
    (map_mem (π₀ (homShift R (⟨a⟩ : Associated2 R B) ⟨b⟩)) hx1)
  have e := congrArg Subtype.val (π₀_comp_ιZ_map (d := homShift R (⟨a⟩ : Associated2 R B) ⟨b⟩)
    (x.1 : (⟨hom1 f⟩ : GradedSupercategory.DegreeZero R
      (Orbit (homShift R (⟨a⟩ : Associated2 R B) ⟨b⟩))) ⟶ ⟨hom1 g⟩))
  refine Eq.trans ?_ e
  show (Orbit.ι (homShift R (⟨a⟩ : Associated2 R B) ⟨b⟩)).map
    (Associated.homMk (X := (⟨f⟩ : (⟨a⟩ : Associated2 R B) ⟶ ⟨b⟩)) (Y := ⟨g⟩) (unitInv₂ x) 0) =
    (Orbit.ι (homShift R (⟨a⟩ : Associated2 R B) ⟨b⟩)).map _
  congr 1
  exact Associated.hom_ext rfl hy0.symm

/-- **`𝔼 ∘ 𝔻 = 𝕀` on objects.** The identification is bijective on 2-morphisms (and the
identity on objects and 1-morphisms): the even 2-morphisms of degree zero of `𝔄̂` are the
2-morphisms of `𝔄`. -/
theorem unit_map₂_bijective {a b : B} (f g : a ⟶ b) :
    Function.Bijective ((unit R B).map₂ : (f ⟶ g) → ((unit R B).map f ⟶ (unit R B).map g)) :=
  ⟨fun η θ h => by
    have h' : unitInv₂ (hom2U (R := R) η) = unitInv₂ (hom2U θ) := congrArg unitInv₂ h
    rwa [unitInv₂_hom2U, unitInv₂_hom2U] at h',
    fun x => ⟨unitInv₂ x, hom2U_unitInv₂ x⟩⟩

end QAssociated2

end StringDiagrams

end
