import StringDiagrams.Super.SVec
import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Superalgebras as supercategories, and the unit supercategory `I`

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Example 1.2(ii) and Example 1.17(ii).

* A *superalgebra* is a `k`-algebra `A` with a `ℤ/2`-grading `𝒜 : ZMod 2 → Submodule k A`
  making it a graded algebra (Mathlib's `GradedAlgebra 𝒜`): the multiplication is even.
* `SuperalgebraCat 𝒜`: the supercategory with one object whose endomorphism superalgebra is
  `A` (Example 1.2(ii)). Composition is multiplication, `g ∘ f = g f`, i.e. `f ≫ g = g * f`.
* `trivialGrading k`: the grading of `k` concentrated in even parity, and the supercategory
  `UnitSupercat k := SuperalgebraCat (trivialGrading k)`: the unit object `I` of the monoidal
  category of supercategories (§1.2). It is a strict monoidal supercategory
  (`UnitSupercat.instMonoidalSupercategory`, `UnitSupercat.instIsStrict`; Example 1.17(ii)),
  and this strict monoidal structure is unique (`UnitSupercat.monoidalStruct_eq`).
* `UnitSupercat.toSVec`: the canonical superfunctor `I → SVec` sending the object to `k`, a
  monoidal superfunctor (`UnitSupercat.toSVecMonoidal`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory MonoidalCategory Supercategory

universe u v

variable {k : Type u} [CommRing k] {A : Type v} [Ring A] [Algebra k A]

variable (𝒜 : ZMod 2 → Submodule k A)

/-- **Brundan–Ellis, Example 1.2(ii).** The supercategory with one object whose endomorphism
superalgebra is `A`. (The grading `𝒜` is part of the type.) -/
@[nolint unusedArguments]
def SuperalgebraCat (_𝒜 : ZMod 2 → Submodule k A) : Type := Unit

namespace SuperalgebraCat

/-- The only object. -/
def star : SuperalgebraCat 𝒜 := ()

instance : Category.{v} (SuperalgebraCat 𝒜) where
  Hom _ _ := A
  id _ := (1 : A)
  comp f g := (g : A) * f
  id_comp f := mul_one (f : A)
  comp_id f := one_mul (f : A)
  assoc f g h := (mul_assoc (h : A) g f).symm

variable {𝒜}

/-- The element of `A` underlying a morphism. -/
def toElem {X Y : SuperalgebraCat 𝒜} (f : X ⟶ Y) : A := f

/-- The morphism given by an element of `A`. -/
def ofElem {X Y : SuperalgebraCat 𝒜} (a : A) : X ⟶ Y := a

@[simp] theorem toElem_ofElem {X Y : SuperalgebraCat 𝒜} (a : A) : toElem (ofElem a : X ⟶ Y) = a :=
  rfl

@[simp] theorem toElem_comp {X Y Z : SuperalgebraCat 𝒜} (f : X ⟶ Y) (g : Y ⟶ Z) :
    toElem (f ≫ g) = toElem g * toElem f := rfl

@[simp] theorem toElem_id (X : SuperalgebraCat 𝒜) : toElem (𝟙 X) = 1 := rfl

theorem hom_ext {X Y : SuperalgebraCat 𝒜} {f g : X ⟶ Y} (h : toElem f = toElem g) : f = g := h

instance : Preadditive (SuperalgebraCat 𝒜) where
  homGroup _ _ := inferInstanceAs (AddCommGroup A)
  add_comp _ _ _ f f' g := mul_add (g : A) f f'
  comp_add _ _ _ f g g' := add_mul (g : A) g' f

instance : Linear k (SuperalgebraCat 𝒜) where
  homModule _ _ := inferInstanceAs (Module k A)
  smul_comp _ _ _ r f g := mul_smul_comm r (g : A) f
  comp_smul _ _ _ f r g := smul_mul_assoc r (g : A) f

@[simp] theorem toElem_add {X Y : SuperalgebraCat 𝒜} (f g : X ⟶ Y) :
    toElem (f + g) = toElem f + toElem g := rfl

@[simp] theorem toElem_smul {X Y : SuperalgebraCat 𝒜} (r : k) (f : X ⟶ Y) :
    toElem (r • f) = r • toElem f := rfl

variable (𝒜) [GradedAlgebra 𝒜]

/-- **Brundan–Ellis, Example 1.2(ii).** A superalgebra is a supercategory with one object. -/
instance instSupercategory : Supercategory k (SuperalgebraCat 𝒜) where
  parity _ _ p := 𝒜 p
  isInternal _ _ := DirectSum.Decomposition.isInternal 𝒜
  id_mem _ := SetLike.GradedOne.one_mem
  comp_mem {_ _ _ p q f g} hf hg := by
    rw [add_comm]; exact SetLike.GradedMul.mul_mem hg hf

theorem mem_parity_iff {X Y : SuperalgebraCat 𝒜} {p : ZMod 2} {f : X ⟶ Y} :
    f ∈ parity (R := k) X Y p ↔ toElem f ∈ 𝒜 p := Iff.rfl

end SuperalgebraCat

/-! ## The unit supercategory `I` -/

variable (k) in
/-- The grading of `k` concentrated in even parity. -/
def trivialGrading : ZMod 2 → Submodule k k := fun p => if p = 0 then ⊤ else ⊥

@[simp] theorem trivialGrading_zero : trivialGrading k 0 = ⊤ := if_pos rfl

@[simp] theorem trivialGrading_one : trivialGrading k 1 = ⊥ := if_neg (by decide)

instance : SetLike.GradedMonoid (trivialGrading k) where
  one_mem := by simp
  mul_mem p q a b ha hb := by
    rcases parity_eq_zero_or_one p with rfl | rfl
    · rcases parity_eq_zero_or_one q with rfl | rfl
      · simp
      · simp only [trivialGrading_one, Submodule.mem_bot] at hb; simp [hb]
    · simp only [trivialGrading_one, Submodule.mem_bot] at ha; simp [ha]

theorem isInternal_trivialGrading : DirectSum.IsInternal (trivialGrading k) := by
  rw [DirectSum.isInternal_submodule_iff_isCompl _ (i := 0) (j := 1) (by decide)
    (by ext p; rcases parity_eq_zero_or_one p with rfl | rfl <;> simp)]
  simpa using isCompl_top_bot

/-- `k`, concentrated in even parity, is a superalgebra. -/
instance : GradedAlgebra (trivialGrading k) :=
  { (inferInstance : SetLike.GradedMonoid (trivialGrading k)),
    isInternal_trivialGrading.chooseDecomposition with }

variable (k) in
/-- **Brundan–Ellis, §1.2 and Example 1.17(ii).** The supercategory `I`: one object, with
endomorphism superalgebra `k` concentrated in even parity. -/
abbrev UnitSupercat : Type := SuperalgebraCat (trivialGrading k)

namespace UnitSupercat

open SuperalgebraCat

theorem mem_parity_zero {X Y : UnitSupercat k} (f : X ⟶ Y) : f ∈ parity (R := k) X Y 0 := by
  rw [mem_parity_iff, trivialGrading_zero]; trivial

theorem eq_zero_of_mem_parity_one {X Y : UnitSupercat k} {f : X ⟶ Y}
    (hf : f ∈ parity (R := k) X Y 1) : f = 0 := by
  rwa [mem_parity_iff, trivialGrading_one, Submodule.mem_bot] at hf

instance instMonoidalCategoryStruct : MonoidalCategoryStruct (UnitSupercat k) where
  tensorObj _ _ := ()
  whiskerLeft _ _ _ f := f
  whiskerRight f _ := f
  tensorUnit := ()
  associator _ _ _ := Iso.refl _
  leftUnitor _ := Iso.refl _
  rightUnitor _ := Iso.refl _

theorem tensorHom_eq {X₁ Y₁ X₂ Y₂ : UnitSupercat k} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    toElem (f ⊗ g) = toElem f * toElem g := by
  change toElem g * toElem f = _
  exact mul_comm _ _

/-- **Brundan–Ellis, Example 1.17(ii).** `I` is a monoidal supercategory: the tensor product of
morphisms is multiplication in `k`. -/
instance instMonoidalSupercategory : MonoidalSupercategory k (UnitSupercat k) where
  tensorHom_def _ _ := rfl
  whiskerLeft_id _ _ := rfl
  id_whiskerRight _ _ := rfl
  whiskerLeft_comp _ _ _ _ _ _ := rfl
  comp_whiskerRight _ _ _ := rfl
  whiskerLeft_add _ _ _ _ _ := rfl
  add_whiskerRight _ _ _ := rfl
  whiskerLeft_smul _ _ _ _ _ := rfl
  smul_whiskerRight _ _ _ := rfl
  whiskerLeft_mem _ _ _ _ _ h := h
  whiskerRight_mem _ h := h
  super_interchange {X X' Y Y' p q f g} hf hg := by
    rcases koszulSign_eq_one_or p q with h | ⟨rfl, rfl⟩
    · rw [h, one_smul]; exact hom_ext (mul_comm (toElem g) (toElem f))
    · rw [eq_zero_of_mem_parity_one hf, koszulSign_one_one, neg_one_smul]
      exact hom_ext (by change toElem g * 0 = -(0 * toElem g); simp)
  associator_naturality f₁ f₂ f₃ := hom_ext (by
    change 1 * (toElem f₃ * (toElem f₂ * toElem f₁)) = (toElem f₃ * toElem f₂ * toElem f₁) * 1
    rw [one_mul, mul_one, mul_assoc])
  leftUnitor_naturality f := hom_ext (by
    change 1 * toElem f = toElem f * 1; rw [one_mul, mul_one])
  rightUnitor_naturality f := hom_ext (by
    change 1 * toElem f = toElem f * 1; rw [one_mul, mul_one])
  pentagon _ _ _ _ := hom_ext (by change (1 : k) * 1 * 1 = 1 * 1; simp)
  triangle _ _ := hom_ext (by change 1 * (1 : k) = 1; simp)
  associator_hom_mem _ _ _ := mem_parity_zero _
  leftUnitor_hom_mem _ := mem_parity_zero _
  rightUnitor_hom_mem _ := mem_parity_zero _

/-- **Brundan–Ellis, Example 1.17(ii).** `I` is a strict monoidal supercategory. -/
instance instIsStrict : MonoidalSupercategory.IsStrict (UnitSupercat k) where
  tensor_assoc _ _ _ := rfl
  unit_tensor _ := rfl
  tensor_unit _ := rfl
  associator_eq _ _ _ := rfl
  leftUnitor_eq _ := rfl
  rightUnitor_eq _ := rfl

/-- **Brundan–Ellis, Example 1.17(ii).** The strict monoidal supercategory structure on `I` is
unique: any strict monoidal supercategory structure on `I` (with its given supercategory
structure) is the one above. -/
theorem monoidalStruct_eq (S : MonoidalCategoryStruct (UnitSupercat k))
    (hS : @MonoidalSupercategory k _ (UnitSupercat k) _ _ _ _ S)
    (hS' : @MonoidalSupercategory.IsStrict (UnitSupercat k) _ S) :
    S = instMonoidalCategoryStruct := by
  have hL : ∀ (X : UnitSupercat k) {Y Z : UnitSupercat k} (f : Y ⟶ Z),
      @MonoidalCategoryStruct.whiskerLeft _ _ S X Y Z f = f := by
    intro X Y Z f
    have h1 := @MonoidalSupercategory.whiskerLeft_smul k _ _ _ _ _ _ S hS X Y Z (toElem f)
      (𝟙 Y)
    have h2 := @MonoidalSupercategory.whiskerLeft_id k _ _ _ _ _ _ S hS X Y
    rw [h2] at h1
    have : (toElem f • 𝟙 Y : Y ⟶ Y) = f := hom_ext (by change toElem f * 1 = toElem f; simp)
    rw [this] at h1
    rw [h1]; exact hom_ext (by change toElem f * 1 = toElem f; simp)
  have hR : ∀ {X Y : UnitSupercat k} (f : X ⟶ Y) (Z : UnitSupercat k),
      @MonoidalCategoryStruct.whiskerRight _ _ S X Y f Z = f := by
    intro X Y f Z
    have h1 := @MonoidalSupercategory.smul_whiskerRight k _ _ _ _ _ _ S hS X X (toElem f) (𝟙 X) Z
    have h2 := @MonoidalSupercategory.id_whiskerRight k _ _ _ _ _ _ S hS X Z
    rw [h2] at h1
    have : (toElem f • 𝟙 X : X ⟶ X) = f := hom_ext (by change toElem f * 1 = toElem f; simp)
    rw [this] at h1
    rw [h1]; exact hom_ext (by change toElem f * 1 = toElem f; simp)
  obtain ⟨tensorObj, whiskerLeft, whiskerRight, tensorHom, tensorUnit, associator, leftUnitor,
    rightUnitor⟩ := S
  obtain rfl : tensorObj = fun _ _ => () := rfl
  obtain rfl : tensorUnit = () := rfl
  have hα := hS'.associator_eq
  have hlu := hS'.leftUnitor_eq
  have hru := hS'.rightUnitor_eq
  have htH := @MonoidalSupercategory.tensorHom_def k _ _ _ _ _ _ _ hS
  simp only at hL hR hα hlu hru htH
  have e1 : whiskerLeft = fun _ _ _ f => f := by funext X Y Z f; exact hL X f
  have e2 : @whiskerRight = fun _ _ f _ => f := by
    funext X Y f Z; exact hR f Z
  subst e1 e2
  have e3 : @tensorHom = fun _ _ _ _ f g => f ≫ g := by
    funext X₁ Y₁ X₂ Y₂ f g; exact htH f g
  subst e3
  have e4 : associator = (instMonoidalCategoryStruct (k := k)).associator := by
    funext X Y Z; rw [hα X Y Z]; rfl
  have e5 : leftUnitor = (instMonoidalCategoryStruct (k := k)).leftUnitor := by
    funext X; rw [hlu X]; rfl
  have e6 : rightUnitor = (instMonoidalCategoryStruct (k := k)).rightUnitor := by
    funext X; rw [hru X]; rfl
  subst e4 e5 e6
  rfl

/-! ## The canonical superfunctor `I → SVec` -/

variable (k) in
/-- The canonical superfunctor `I → SVec` sending the only object to `k` and `r ∈ k` to
multiplication by `r`. -/
@[simps]
def toSVec : UnitSupercat k ⥤ SVec k where
  obj _ := SVec.unit
  map f := SVec.ofHom (toElem f • LinearMap.id)
  map_id _ := by
    change ((1 : k) • LinearMap.id : k →ₗ[k] k) = LinearMap.id
    rw [one_smul]
  map_comp f g := by
    change ((toElem g * toElem f) • LinearMap.id : k →ₗ[k] k) =
      (toElem g • LinearMap.id) ∘ₗ (toElem f • LinearMap.id)
    ext; simp [mul_smul]

instance : (toSVec k).Additive where
  map_add {_ _ f g} := by
    change ((toElem f + toElem g) • LinearMap.id : k →ₗ[k] k) =
      toElem f • LinearMap.id + toElem g • LinearMap.id
    rw [add_smul]

instance : (toSVec k).Linear k where
  map_smul f r := by
    change ((r • toElem f) • LinearMap.id : k →ₗ[k] k) = r • toElem f • LinearMap.id
    rw [smul_assoc]

instance : IsSuperfunctor k (toSVec k) where
  map_mem {X Y p f} hf := by
    rcases parity_eq_zero_or_one p with rfl | rfl
    · intro q
      rw [add_zero]
      exact LinearMap.ext fun v => (map_smul (SVec.unit.proj q) (toElem f) v).symm
    · rw [eq_zero_of_mem_parity_one hf, Functor.map_zero]; exact Submodule.zero_mem _

theorem toSVec_map_apply {X Y : UnitSupercat k} (f : X ⟶ Y) (r : k) :
    (toSVec k).map f r = toElem f * r := rfl

theorem toSVec_map_mem {X Y : UnitSupercat k} (f : X ⟶ Y) :
    (toSVec k).map f ∈ SVec.parityHom SVec.unit SVec.unit 0 :=
  IsSuperfunctor.map_mem (F := toSVec k) (mem_parity_zero f)

/-- The canonical superfunctor `I → SVec` is monoidal, with coherence maps
`k ⊗ k → k, a ⊗ b ↦ ab` and `1_k`. -/
def toSVecMonoidal : MonoidalSuperfunctor k (toSVec k) where
  μIso _ _ := SVec.leftUnitor SVec.unit
  εIso := Iso.refl _
  μ_mem _ _ := SVec.leftUnitor_mem _
  ε_mem := id_mem _
  μ_natural_left f _ := by
    refine TensorProduct.ext' fun (a : k) (b : k) => ?_
    change TensorProduct.lid k k ((toElem f * a) ⊗ₜ b) = toElem f * TensorProduct.lid k k (a ⊗ₜ b)
    simp [mul_assoc, mul_left_comm]
  μ_natural_right _ f := by
    change SVec.whiskerLeft _ _ ≫ _ = _
    erw [SVec.whiskerLeft_even _ (toSVec_map_mem f)]
    refine TensorProduct.ext' fun (a : k) (b : k) => ?_
    change TensorProduct.lid k k (a ⊗ₜ (toElem f * b)) = toElem f * TensorProduct.lid k k (a ⊗ₜ b)
    simp [mul_left_comm]
  associativity _ _ _ := by
    change SVec.whiskerRight _ _ ≫ _ ≫ _ = _ ≫ SVec.whiskerLeft _ _ ≫ _
    erw [SVec.whiskerLeft_even _ (SVec.leftUnitor_mem SVec.unit)]
    refine TensorProduct.ext_threefold fun (a : k) (b : k) (c : k) => ?_
    change 1 * TensorProduct.lid k k (TensorProduct.lid k k (a ⊗ₜ b) ⊗ₜ c) =
      TensorProduct.lid k k (a ⊗ₜ TensorProduct.lid k k (b ⊗ₜ c))
    simp [mul_assoc]
  left_unitality _ := by
    refine TensorProduct.ext' fun (a : k) (b : k) => ?_
    change TensorProduct.lid k k (a ⊗ₜ b) = 1 * TensorProduct.lid k k (a ⊗ₜ b)
    rw [one_mul]
  right_unitality _ := by
    change _ = SVec.whiskerLeft _ _ ≫ _ ≫ _
    erw [SVec.whiskerLeft_even _ (SVec.instSupercategory.id_mem SVec.unit)]
    refine TensorProduct.ext' fun (a : k) (b : k) => ?_
    change TensorProduct.rid k k (a ⊗ₜ b) = 1 * TensorProduct.lid k k (a ⊗ₜ b)
    simp [mul_comm]

end UnitSupercat

end StringDiagrams
