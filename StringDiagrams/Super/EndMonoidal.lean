import StringDiagrams.Super.PiTwo
import StringDiagrams.Super.MonoidalPi

/-!
# The monoidal supercategory `End(A)`

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Examples 1.5(ii) and 1.13(ii).

For a supercategory `A`, the supercategory `End(A) = ℋom(A, A)` of superfunctors `A → A` and
supernatural transformations (Example 1.2(iv), `Supercategory.Superfunctor`) is a strict
monoidal supercategory with `F ⊗ G := F ∘ G` (in Lean, `G.comp F`) and
`(x ⊗ y)_λ := x_{Kλ} ∘ F y_λ` for `x : F ⇒ G`, `y : H ⇒ K`
(`SuperEnd.instMonoidalSupercategory`, `SuperEnd.instIsStrict`, `SuperEnd.superTensorHom_eq`).
If `(A, Π, ζ)` is a Π-supercategory, then `(End(A), Π, ζ)` is a strict monoidal
Π-supercategory (`SuperEnd.instMonoidalPiSupercategory`).

`SuperEnd R A` is a type synonym for `Superfunctor R A A`, so that the monoidal structure is not
an instance on all superfunctor supercategories.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory MonoidalCategory Supercategory

universe w v u

variable (R : Type w) [CommRing R] (A : Type u) [Category.{v} A] [Preadditive A] [Linear R A]
  [Supercategory R A]

/-- **Brundan–Ellis, Example 1.5(ii).** The supercategory `End(A)` of superfunctors `A → A`. -/
def SuperEnd : Type _ := Superfunctor R A A

namespace SuperEnd

instance : Category (SuperEnd R A) := inferInstanceAs (Category (Superfunctor R A A))

instance : Preadditive (SuperEnd R A) := inferInstanceAs (Preadditive (Superfunctor R A A))

instance : Linear R (SuperEnd R A) := inferInstanceAs (Linear R (Superfunctor R A A))

instance : Supercategory R (SuperEnd R A) :=
  inferInstanceAs (Supercategory R (Superfunctor R A A))

variable {R A}

/-- A superfunctor, as an object of `End(A)`. -/
def of (F : Superfunctor R A A) : SuperEnd R A := F

/-- The superfunctor underlying an object of `End(A)`. -/
def toSuperfunctor (F : SuperEnd R A) : Superfunctor R A A := F

instance instMonoidalCategoryStruct : MonoidalCategoryStruct (SuperEnd R A) where
  tensorObj F G := of ((toSuperfunctor G).comp (toSuperfunctor F))
  whiskerLeft F _ _ y := Superfunctor.whiskerRight y (toSuperfunctor F)
  whiskerRight x G := Superfunctor.whiskerLeft (toSuperfunctor G) x
  tensorUnit := of (Superfunctor.id R A)
  associator _ _ _ := Iso.refl _
  leftUnitor _ := Iso.refl _
  rightUnitor _ := Iso.refl _

/-- `F ⊗ G = F ∘ G`. -/
theorem tensorObj_def (F G : SuperEnd R A) :
    toSuperfunctor (F ⊗ G) = (toSuperfunctor G).comp (toSuperfunctor F) := rfl

/-- `(F y)_λ = F(y_λ)`. -/
theorem whiskerLeft_app (F : SuperEnd R A) {G K : SuperEnd R A} (y : G ⟶ K) (p : ZMod 2)
    (X : A) : (F ◁ y).app p X = (toSuperfunctor F).map (y.app p X) := rfl

/-- `(x G)_λ = x_{Gλ}`. -/
theorem whiskerRight_app {F H : SuperEnd R A} (x : F ⟶ H) (G : SuperEnd R A) (p : ZMod 2)
    (X : A) : (x ▷ G).app p X = x.app p ((toSuperfunctor G).obj X) := rfl

theorem whiskerLeft_whiskerLeft (F G : Superfunctor R A A) {H K : Superfunctor R A A}
    (y : H ⟶ K) :
    Superfunctor.whiskerLeft G (Superfunctor.whiskerLeft F y) =
      Superfunctor.whiskerLeft (G.comp F) y :=
  Superfunctor.hom_ext fun _ _ => rfl

theorem whiskerLeft_whiskerRight (F : Superfunctor R A A) {G K : Superfunctor R A A}
    (y : G ⟶ K) (H : Superfunctor R A A) :
    Superfunctor.whiskerLeft F (Superfunctor.whiskerRight y H) =
      Superfunctor.whiskerRight (Superfunctor.whiskerLeft F y) H :=
  Superfunctor.hom_ext fun _ _ => rfl

theorem whiskerRight_whiskerRight {F G : Superfunctor R A A} (x : F ⟶ G)
    (H K : Superfunctor R A A) :
    Superfunctor.whiskerRight x (H.comp K) =
      Superfunctor.whiskerRight (Superfunctor.whiskerRight x H) K :=
  Superfunctor.hom_ext fun _ _ => rfl

theorem whiskerLeft_id' {G H : Superfunctor R A A} (x : G ⟶ H) :
    Superfunctor.whiskerLeft (Superfunctor.id R A) x = x :=
  Superfunctor.hom_ext fun _ _ => rfl

theorem whiskerRight_id' {G H : Superfunctor R A A} (x : G ⟶ H) :
    Superfunctor.whiskerRight x (Superfunctor.id R A) = x :=
  Superfunctor.hom_ext fun _ _ => rfl

/-- **Brundan–Ellis, Example 1.5(ii).** `End(A)` is a monoidal supercategory. -/
instance instMonoidalSupercategory : MonoidalSupercategory R (SuperEnd R A) where
  tensorHom_def _ _ := rfl
  whiskerLeft_id X Y := Superfunctor.id_whiskerRight _ _
  id_whiskerRight X Y := Superfunctor.whiskerLeft_id _ _
  whiskerLeft_comp X _ _ _ f g := Superfunctor.comp_whiskerRight f g _
  comp_whiskerRight f g W := Superfunctor.whiskerLeft_comp _ f g
  whiskerLeft_add X _ _ f g := Superfunctor.add_whiskerRight f g _
  add_whiskerRight f g Z := Superfunctor.whiskerLeft_add _ f g
  whiskerLeft_smul X _ _ r f := Superfunctor.smul_whiskerRight r f _
  smul_whiskerRight r f Z := Superfunctor.whiskerLeft_smul _ r f
  whiskerLeft_mem X _ _ _ _ hf := Superfunctor.whiskerRight_mem hf _
  whiskerRight_mem Z hf := Superfunctor.whiskerLeft_mem _ hf
  super_interchange {X X' Y Y' p q f g} hf hg := by
    change Superfunctor.whiskerLeft _ f ≫ Superfunctor.whiskerRight g _ =
      koszulSign p q • (Superfunctor.whiskerRight g _ ≫ Superfunctor.whiskerLeft _ f)
    rw [Superfunctor.whisker_exchange hg hf, koszulSign_comm, koszulSign_smul_smul]
  associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} f₁ f₂ f₃ := by
    change (Superfunctor.whiskerLeft _ (Superfunctor.whiskerLeft _ f₁ ≫
        Superfunctor.whiskerRight f₂ _) ≫ Superfunctor.whiskerRight f₃ _) ≫ 𝟙 _ =
      𝟙 _ ≫ (Superfunctor.whiskerLeft _ f₁ ≫ Superfunctor.whiskerRight
        (Superfunctor.whiskerLeft _ f₂ ≫ Superfunctor.whiskerRight f₃ _) _)
    rw [Category.comp_id, Category.id_comp, Superfunctor.whiskerLeft_comp,
      Superfunctor.comp_whiskerRight, whiskerLeft_whiskerLeft, whiskerLeft_whiskerRight,
      whiskerRight_whiskerRight, Category.assoc]
  leftUnitor_naturality f := by
    change Superfunctor.whiskerRight f (Superfunctor.id R A) ≫ 𝟙 _ = 𝟙 _ ≫ f
    rw [whiskerRight_id', Category.comp_id, Category.id_comp]
  rightUnitor_naturality f := by
    change Superfunctor.whiskerLeft (Superfunctor.id R A) f ≫ 𝟙 _ = 𝟙 _ ≫ f
    rw [whiskerLeft_id', Category.comp_id, Category.id_comp]
  pentagon W X Y Z := by
    have e1 : (α_ W X Y).hom ▷ Z = 𝟙 _ := Superfunctor.whiskerLeft_id _ _
    have e2 : W ◁ (α_ X Y Z).hom = 𝟙 _ := Superfunctor.id_whiskerRight _ _
    rw [e1, e2]
    change 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _ ≫ 𝟙 _
    simp only [Category.comp_id]
  triangle X Y := by
    have e1 : (ρ_ X).hom ▷ Y = 𝟙 _ := Superfunctor.whiskerLeft_id _ _
    have e2 : X ◁ (λ_ Y).hom = 𝟙 _ := Superfunctor.id_whiskerRight _ _
    rw [e1, e2]
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    rw [Category.comp_id]
  associator_hom_mem _ _ _ := id_mem _
  leftUnitor_hom_mem _ := id_mem _
  rightUnitor_hom_mem _ := id_mem _

/-- **Brundan–Ellis, Example 1.5(ii).** `End(A)` is a strict monoidal supercategory. -/
instance instIsStrict : MonoidalSupercategory.IsStrict (SuperEnd R A) where
  tensor_assoc _ _ _ := rfl
  unit_tensor _ := rfl
  tensor_unit _ := rfl
  associator_eq _ _ _ := rfl
  leftUnitor_eq _ := rfl
  rightUnitor_eq _ := rfl

/-- **Brundan–Ellis, Example 1.5(ii).** The paper's tensor product of supernatural
transformations `x : F ⇒ G`, `y : H ⇒ K` is `(x ⊗ y)_λ = x_{Kλ} ∘ F y_λ`, i.e. the horizontal
composite `Superfunctor.hcomp y x`. -/
theorem superTensorHom_eq {F G H K : SuperEnd R A} (x : F ⟶ G) (y : H ⟶ K) :
    MonoidalSupercategory.superTensorHom x y = Superfunctor.hcomp y x := rfl

/-! ## Example 1.13(ii) -/

variable [PiSupercategory R A]

/-- **Brundan–Ellis, Example 1.13(ii).** For a Π-supercategory `(A, Π, ζ)`, `(End(A), Π, ζ)`
is a strict monoidal Π-supercategory. -/
instance instMonoidalPiSupercategory : MonoidalPiSupercategory R (SuperEnd R A) where
  pi := of (PiSCat.piHom (PiSCat.of R A))
  ζ := PiSCat.ζHom (PiSCat.of R A)
  ζ_hom_mem := (PiTwoSupercategory.ζ_hom_mem (R := R) (B := PiSCat R) (PiSCat.of R A))

end SuperEnd

end StringDiagrams
