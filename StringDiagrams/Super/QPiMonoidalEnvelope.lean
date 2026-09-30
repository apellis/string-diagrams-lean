import StringDiagrams.Super.QEnvelope
import StringDiagrams.Super.MonoidalEnvelope
import StringDiagrams.Super.GradedMonoidal

/-!
# The (Q, Π)-envelope of a graded monoidal supercategory

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §6,
Definition 6.10 in the one-object case (a graded monoidal supercategory being a graded
2-supercategory with one object, `StringDiagrams.GradedMonoidalSupercategory`).

For a graded monoidal supercategory `A`, the `(Q, Π)`-envelope `A_{q,π}` of Definition 6.8 is a
graded monoidal supercategory with `(Q^n Π^b G) ⊗ (Q^m Π^a F) := Q^{n+m} Π^{b+a} (G ⊗ F)`, unit
`Q⁰ Π⁰ 1`, coherence maps induced from those of `A`, and tensor product of morphisms

  `y^{l,d}_{n,b} ⊗ x^{k,c}_{m,a} = (-1)^{b|x| + |y|c + bc + ab} (y ⊗ x)^{l+k,d+c}_{n+m,b+a}`

(Definition 6.10, with `yx` the horizontal composite of the one-object 2-supercategory, i.e.
`y ⊗ x`). As for Definition 6.8 (`StringDiagrams.Super.QEnvelope`) it is built in two steps:

* the `Q`-envelope `QEnvelope R A` is a monoidal supercategory with
  `Q^n G ⊗ Q^m F = Q^{n+m}(G ⊗ F)` and all structure (whiskerings, tensor product of morphisms,
  coherence maps) that of `A`, without signs (`QEnvelope.instMonoidalCategoryStruct`,
  `QEnvelope.monoidalSupercategory`), and a graded monoidal supercategory
  (`QEnvelope.gradedMonoidalSupercategory`);
* the Π-envelope of a monoidal supercategory is monoidal (Definition 1.16,
  `Envelope.monoidalSupercategory`), and it is graded monoidal when the monoidal supercategory is
  (`Envelope.gradedMonoidalSupercategory`).

Thus `QPiEnvelope R A = Envelope R (QEnvelope R A)` is a graded monoidal supercategory, and a
monoidal Π-supercategory (`Envelope.instMonoidalPiSupercategory`). The sign formula of
Definition 6.10 is `QPiEnvelope.ofHom_superTensorHom_ofHom` (for the paper's tensor product
`superTensorHom`). If `A` is strict, so are `QEnvelope R A`, `Envelope R A` and `A_{q,π}`
(`QEnvelope.instIsStrict`, `Envelope.instIsStrict`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory MonoidalCategory Supercategory GradedSupercategory

universe w w₁ w₂

/-! ## The monoidal `Q`-envelope -/

namespace QEnvelope

variable {R : Type w} {C : Type w₁} [Category.{w₂} C]

/-- `toHom` of an `eqToHom`. -/
theorem toHom_eqToHom {X Y : QEnvelope R C} (h : X = Y) :
    toHom (eqToHom h) = eqToHom (congrArg QEnvelope.obj h) := by
  subst h; rfl

variable [MonoidalCategoryStruct C]

/-- The monoidal structure on the `Q`-envelope: `Q^m λ ⊗ Q^n μ = Q^{m+n}(λ ⊗ μ)`, unit `Q⁰ 1`,
whiskerings, tensor product of morphisms and coherence maps those of `C` (no signs). -/
instance instMonoidalCategoryStruct : MonoidalCategoryStruct (QEnvelope R C) where
  tensorObj X Y := ⟨X.shift + Y.shift, X.obj ⊗ Y.obj⟩
  whiskerLeft X _ _ g := ofHom (X.obj ◁ toHom g)
  whiskerRight f Y := ofHom (toHom f ▷ Y.obj)
  tensorHom f g := ofHom (toHom f ⊗ₘ toHom g)
  tensorUnit := ⟨0, 𝟙_ C⟩
  associator X Y Z := isoOfIso (α_ X.obj Y.obj Z.obj)
  leftUnitor X := isoOfIso (λ_ X.obj)
  rightUnitor X := isoOfIso (ρ_ X.obj)

@[simp] theorem tensorObj_shift (X Y : QEnvelope R C) : (X ⊗ Y).shift = X.shift + Y.shift := rfl

@[simp] theorem tensorObj_obj (X Y : QEnvelope R C) : (X ⊗ Y).obj = X.obj ⊗ Y.obj := rfl

@[simp] theorem tensorUnit_shift : (𝟙_ (QEnvelope R C)).shift = 0 := rfl

@[simp] theorem tensorUnit_obj : (𝟙_ (QEnvelope R C)).obj = 𝟙_ C := rfl

theorem toHom_whiskerLeft (X : QEnvelope R C) {Y Y' : QEnvelope R C} (g : Y ⟶ Y') :
    toHom (X ◁ g) = X.obj ◁ toHom g := rfl

theorem toHom_whiskerRight {X X' : QEnvelope R C} (f : X ⟶ X') (Y : QEnvelope R C) :
    toHom (f ▷ Y) = toHom f ▷ Y.obj := rfl

theorem toHom_tensorHom {X₁ Y₁ X₂ Y₂ : QEnvelope R C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    toHom (f ⊗ₘ g) = toHom f ⊗ₘ toHom g := rfl

@[simp] theorem toHom_associator_hom (X Y Z : QEnvelope R C) :
    toHom (α_ X Y Z).hom = (α_ X.obj Y.obj Z.obj).hom := rfl

@[simp] theorem toHom_leftUnitor_hom (X : QEnvelope R C) :
    toHom (λ_ X).hom = (λ_ X.obj).hom := rfl

@[simp] theorem toHom_rightUnitor_hom (X : QEnvelope R C) :
    toHom (ρ_ X).hom = (ρ_ X.obj).hom := rfl

section Monoidal

variable [Preadditive C] [CommRing R] [Linear R C] [Supercategory R C]
  [MonoidalSupercategory R C]

/-- The `Q`-envelope of a monoidal supercategory is a monoidal supercategory: all axioms are
those of `C`. -/
instance monoidalSupercategory : MonoidalSupercategory R (QEnvelope R C) where
  tensorHom_def f g := MonoidalSupercategory.tensorHom_def (R := R) (toHom f) (toHom g)
  whiskerLeft_id X Y := MonoidalSupercategory.whiskerLeft_id (R := R) X.obj Y.obj
  id_whiskerRight X Y := MonoidalSupercategory.id_whiskerRight (R := R) X.obj Y.obj
  whiskerLeft_comp X _ _ _ f g :=
    MonoidalSupercategory.whiskerLeft_comp (R := R) X.obj (toHom f) (toHom g)
  comp_whiskerRight f g W :=
    MonoidalSupercategory.comp_whiskerRight (R := R) (toHom f) (toHom g) W.obj
  whiskerLeft_add X _ _ f g :=
    MonoidalSupercategory.whiskerLeft_add (R := R) X.obj (toHom f) (toHom g)
  add_whiskerRight f g Z :=
    MonoidalSupercategory.add_whiskerRight (R := R) (toHom f) (toHom g) Z.obj
  whiskerLeft_smul X _ _ r f := MonoidalSupercategory.whiskerLeft_smul X.obj r (toHom f)
  smul_whiskerRight r f Z := MonoidalSupercategory.smul_whiskerRight r (toHom f) Z.obj
  whiskerLeft_mem X _ _ _ _ hf := MonoidalSupercategory.whiskerLeft_mem (R := R) (C := C) X.obj hf
  whiskerRight_mem Z hf := MonoidalSupercategory.whiskerRight_mem (R := R) (C := C) Z.obj hf
  super_interchange hf hg := MonoidalSupercategory.super_interchange (R := R) (C := C) hf hg
  associator_naturality f₁ f₂ f₃ :=
    MonoidalSupercategory.associator_naturality (R := R) (toHom f₁) (toHom f₂) (toHom f₃)
  leftUnitor_naturality f := MonoidalSupercategory.leftUnitor_naturality (R := R) (toHom f)
  rightUnitor_naturality f := MonoidalSupercategory.rightUnitor_naturality (R := R) (toHom f)
  pentagon W X Y Z := MonoidalSupercategory.pentagon (R := R) W.obj X.obj Y.obj Z.obj
  triangle X Y := MonoidalSupercategory.triangle (R := R) X.obj Y.obj
  associator_hom_mem X Y Z := MonoidalSupercategory.associator_hom_mem (R := R) X.obj Y.obj Z.obj
  leftUnitor_hom_mem X := MonoidalSupercategory.leftUnitor_hom_mem (R := R) X.obj
  rightUnitor_hom_mem X := MonoidalSupercategory.rightUnitor_hom_mem (R := R) X.obj

omit [Preadditive C] [CommRing R] [Linear R C] [Supercategory R C] [MonoidalSupercategory R C] in
theorem toHom_superTensorHom {X₁ Y₁ X₂ Y₂ : QEnvelope R C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    toHom (MonoidalSupercategory.superTensorHom f g) =
      MonoidalSupercategory.superTensorHom (toHom f) (toHom g) := rfl

variable [GradedSupercategory R C] [GradedMonoidalSupercategory R C]

/-- The `Q`-envelope of a graded monoidal supercategory is a graded monoidal supercategory. -/
instance gradedMonoidalSupercategory : GradedMonoidalSupercategory R (QEnvelope R C) where
  whiskerLeft_mem_degree X {Y Z n f} hf := by
    rw [mem_degree_iff] at hf ⊢
    rw [toHom_whiskerLeft, tensorObj_shift, tensorObj_shift,
      show n + (X.shift + Y.shift - (X.shift + Z.shift)) = n + (Y.shift - Z.shift) by ring]
    exact GradedMonoidalSupercategory.whiskerLeft_mem_degree X.obj hf
  whiskerRight_mem_degree {X Y n f} Z hf := by
    rw [mem_degree_iff] at hf ⊢
    rw [toHom_whiskerRight, tensorObj_shift, tensorObj_shift,
      show n + (X.shift + Z.shift - (Y.shift + Z.shift)) = n + (X.shift - Y.shift) by ring]
    exact GradedMonoidalSupercategory.whiskerRight_mem_degree Z.obj hf
  associator_hom_mem_degree X Y Z := by
    rw [mem_degree_iff, toHom_associator_hom, tensorObj_shift, tensorObj_shift, tensorObj_shift,
      tensorObj_shift,
      show (0 : ℤ) + (X.shift + Y.shift + Z.shift - (X.shift + (Y.shift + Z.shift))) = 0 by ring]
    exact GradedMonoidalSupercategory.associator_hom_mem_degree X.obj Y.obj Z.obj
  leftUnitor_hom_mem_degree X := by
    rw [mem_degree_iff, toHom_leftUnitor_hom, tensorObj_shift, tensorUnit_shift,
      show (0 : ℤ) + (0 + X.shift - X.shift) = 0 by ring]
    exact GradedMonoidalSupercategory.leftUnitor_hom_mem_degree X.obj
  rightUnitor_hom_mem_degree X := by
    rw [mem_degree_iff, toHom_rightUnitor_hom, tensorObj_shift, tensorUnit_shift,
      show (0 : ℤ) + (X.shift + 0 - X.shift) = 0 by ring]
    exact GradedMonoidalSupercategory.rightUnitor_hom_mem_degree X.obj

end Monoidal

/-- The `Q`-envelope of a strict monoidal supercategory is strict. -/
instance instIsStrict [MonoidalSupercategory.IsStrict C] :
    MonoidalSupercategory.IsStrict (QEnvelope R C) where
  tensor_assoc X Y Z :=
    QEnvelope.ext (add_assoc _ _ _) (MonoidalSupercategory.IsStrict.tensor_assoc X.obj Y.obj Z.obj)
  unit_tensor X := QEnvelope.ext (zero_add _) (MonoidalSupercategory.IsStrict.unit_tensor X.obj)
  tensor_unit X := QEnvelope.ext (add_zero _) (MonoidalSupercategory.IsStrict.tensor_unit X.obj)
  associator_eq X Y Z := by
    ext; apply hom_ext
    rw [eqToIso.hom, toHom_eqToHom, toHom_associator_hom,
      MonoidalSupercategory.IsStrict.associator_eq, eqToIso.hom]
  leftUnitor_eq X := by
    ext; apply hom_ext
    rw [eqToIso.hom, toHom_eqToHom, toHom_leftUnitor_hom,
      MonoidalSupercategory.IsStrict.leftUnitor_eq, eqToIso.hom]
  rightUnitor_eq X := by
    ext; apply hom_ext
    rw [eqToIso.hom, toHom_eqToHom, toHom_rightUnitor_hom,
      MonoidalSupercategory.IsStrict.rightUnitor_eq, eqToIso.hom]

end QEnvelope

/-! ## The Π-envelope of a graded monoidal supercategory -/

namespace Envelope

variable {R : Type w} {C : Type w₁} [Category.{w₂} C]

/-- `toHom` of an `eqToHom`. -/
theorem toHom_eqToHom {X Y : Envelope R C} (h : X = Y) :
    toHom (eqToHom h) = eqToHom (congrArg Envelope.obj h) := by
  subst h; rfl

variable [Preadditive C] [CommRing R] [Linear R C] [Supercategory R C] [MonoidalCategoryStruct C]

/-- The Π-envelope of a graded monoidal supercategory is a graded monoidal supercategory, with
the degrees of `C`. -/
instance gradedMonoidalSupercategory [MonoidalSupercategory R C] [GradedSupercategory R C]
    [GradedMonoidalSupercategory R C] : GradedMonoidalSupercategory R (Envelope R C) where
  whiskerLeft_mem_degree X {Y Z _ _} hf := by
    have h := twist_mem_degree (R := R) (C := Envelope R C) (X := Y) (Y := Z) X.par hf
    rw [mem_degree_iff] at h ⊢
    rw [toHom_whiskerLeft]
    exact GradedMonoidalSupercategory.whiskerLeft_mem_degree (R := R) X.obj h
  whiskerRight_mem_degree {X Y _ _} Z hf := by
    rw [mem_degree_iff] at hf ⊢
    have h := twist_mem_degree (R := R) (C := C) Z.par hf
    rw [toHom_whiskerRight]
    exact GradedMonoidalSupercategory.whiskerRight_mem_degree (R := R) Z.obj h
  associator_hom_mem_degree X Y Z :=
    GradedMonoidalSupercategory.associator_hom_mem_degree (R := R) X.obj Y.obj Z.obj
  leftUnitor_hom_mem_degree X :=
    GradedMonoidalSupercategory.leftUnitor_hom_mem_degree (R := R) X.obj
  rightUnitor_hom_mem_degree X :=
    GradedMonoidalSupercategory.rightUnitor_hom_mem_degree (R := R) X.obj

/-- The Π-envelope of a strict monoidal supercategory is strict. -/
instance instIsStrict [MonoidalSupercategory.IsStrict C] :
    MonoidalSupercategory.IsStrict (Envelope R C) where
  tensor_assoc X Y Z :=
    Envelope.ext (add_assoc _ _ _) (MonoidalSupercategory.IsStrict.tensor_assoc X.obj Y.obj Z.obj)
  unit_tensor X := Envelope.ext (zero_add _) (MonoidalSupercategory.IsStrict.unit_tensor X.obj)
  tensor_unit X := Envelope.ext (add_zero _) (MonoidalSupercategory.IsStrict.tensor_unit X.obj)
  associator_eq X Y Z := by
    ext; apply hom_ext
    rw [eqToIso.hom, toHom_eqToHom, toHom_associator_hom,
      MonoidalSupercategory.IsStrict.associator_eq, eqToIso.hom]
  leftUnitor_eq X := by
    ext; apply hom_ext
    rw [eqToIso.hom, toHom_eqToHom, toHom_leftUnitor_hom,
      MonoidalSupercategory.IsStrict.leftUnitor_eq, eqToIso.hom]
  rightUnitor_eq X := by
    ext; apply hom_ext
    rw [eqToIso.hom, toHom_eqToHom, toHom_rightUnitor_hom,
      MonoidalSupercategory.IsStrict.rightUnitor_eq, eqToIso.hom]

end Envelope

/-! ## The `(Q, Π)`-envelope -/

namespace QPiEnvelope

variable {R : Type w} [CommRing R] {C : Type w₁} [Category.{w₂} C] [Preadditive C] [Linear R C]
  [Supercategory R C] [MonoidalCategoryStruct C] [MonoidalSupercategory R C]

omit [MonoidalSupercategory R C] in
/-- **Definition 6.10** (one-object case): `(Q^n Π^b G) ⊗ (Q^m Π^a F) = Q^{n+m} Π^{b+a}(G ⊗ F)`. -/
theorem tensorObj_mk (n : ℤ) (b : ZMod 2) (G : C) (m : ℤ) (a : ZMod 2) (F : C) :
    (mk n b G : QPiEnvelope R C) ⊗ mk m a F = mk (n + m) (b + a) (G ⊗ F) := rfl

omit [MonoidalSupercategory R C] in
/-- **Definition 6.10** (one-object case): the unit object is `Q⁰ Π⁰ 1`. -/
theorem tensorUnit_eq : 𝟙_ (QPiEnvelope R C) = mk 0 0 (𝟙_ C) := rfl

/-- **Definition 6.10** (one-object case), the sign formula for the tensor product of
morphisms: for `y : G ⟶ K` and `x : F ⟶ H` homogeneous in `A` of parities `|y|`, `|x|`,
`y^{l,d}_{n,b} ⊗ x^{k,c}_{m,a} = (-1)^{b|x| + |y|c + bc + ab} (y ⊗ x)^{l+k,d+c}_{n+m,b+a}`,
for the paper's tensor product `f ⊗ g = (f ⊗ 1) ∘ (1 ⊗ g)` (`superTensorHom`). Here
`X = Q^nΠ^bG`, `X' = Q^lΠ^dK`, `Y = Q^mΠ^aF`, `Y' = Q^kΠ^cH`. -/
theorem ofHom_superTensorHom_ofHom {X X' Y Y' : QPiEnvelope R C} {y : X.obj.obj ⟶ X'.obj.obj}
    {x : Y.obj.obj ⟶ Y'.obj.obj} {py px : ZMod 2}
    (hy : y ∈ parity (R := R) X.obj.obj X'.obj.obj py)
    (hx : x ∈ parity (R := R) Y.obj.obj Y'.obj.obj px) :
    MonoidalSupercategory.superTensorHom (ofHom y : X ⟶ X') (ofHom x : Y ⟶ Y') =
      sign R (X.par * px + py * Y'.par + X.par * Y'.par + Y.par * X.par) •
        (ofHom (MonoidalSupercategory.superTensorHom y x) : X ⊗ Y ⟶ X' ⊗ Y') := by
  apply Envelope.hom_ext
  rw [Envelope.toHom_superTensorHom (pf := py) (pg := px) hy hx, mul_comm Y.par X.par]
  rfl

end QPiEnvelope

end StringDiagrams

end
