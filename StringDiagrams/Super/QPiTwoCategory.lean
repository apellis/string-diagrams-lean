import StringDiagrams.Super.GradedTwo
import StringDiagrams.Super.PiTwoCategory

/-!
# (Q, Π)-2-categories

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §6,
Definition 6.14 and the discussion after it.

* `StringDiagrams.QPiTwoCategory` (**Definition 6.14**), stated (like Definition 5.2 in
  `StringDiagrams.Super.PiTwoCategory`) for not necessarily strict Mathlib bicategories with
  associators and unitors inserted, and with 1-morphisms composed in diagrammatic order: a
  Π-2-category (Definition 5.2) with 1-morphisms `q_λ, q_λ⁻¹`, natural isomorphisms
  `γ_F : F ≫ q_μ ≅ q_λ ≫ F` making `(q, γ)` an object of the Drinfeld center (`γ_naturality`,
  `γ_comp`, `γ_id`), with `γ_{q_λ} = 1` (`γ_q`) and `γ_{π_λ} = β_{q_λ}⁻¹` (`γ_pi`), and
  2-isomorphisms `ii_λ : q_λ ≫ q_λ⁻¹ ≅ 1_λ`, `jj_λ : q_λ⁻¹ ≫ q_λ ≅ 1_λ` with `q_λ ii_λ = jj_λ q_λ`
  and `ii_λ q_λ⁻¹ = q_λ⁻¹ jj_λ` (`q_ii`, `ii_qinv`). (Part (ii) of Definition 6.14 also lists
  `β_{π_λ} = -1`, which is part of Definition 5.2.)
* For a graded 2-supercategory `𝔄`, `DegreeZero2 R 𝔄` is the 2-supercategory of 2-morphisms of
  degree zero, and the *underlying 2-category* of `𝔄` (the same objects and 1-morphisms, and the
  even 2-morphisms of degree zero) is `GUnderlying2 R 𝔄 := Underlying2 R (DegreeZero2 R 𝔄)`.
  For a graded `(Q, Π)`-2-supercategory it is a `(Q, Π)`-2-category
  (`GUnderlying2.instQPiTwoCategory`), with `β`, `ξ` of Lemma 3.2 and `γ`, `ii`, `jj` of
  Lemma 6.6.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Bicategory

universe w w₁ v₁ u₁

section Defs

variable (R : Type w) [CommRing R] (B : Type u₁) [Bicategory.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]

/-- A `(Q, Π)`-2-category (Brundan–Ellis, Definition 6.14), with associators and unitors
inserted in the axioms; see the module documentation. -/
class QPiTwoCategory [PreadditiveBicategory B] [LinearBicategory R B] extends
    PiTwoCategory R B where
  /-- The 1-morphisms `q_λ`. -/
  q (a : B) : a ⟶ a
  /-- The 1-morphisms `q_λ⁻¹`. -/
  qinv (a : B) : a ⟶ a
  /-- The isomorphisms `γ_F : q_μ F ≅ F q_λ`. -/
  γ {a b : B} (f : a ⟶ b) : f ≫ q b ≅ q a ≫ f
  γ_naturality {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
    (γ f).hom ≫ q a ◁ η = η ▷ q b ≫ (γ g).hom
  /-- `γ_{GF} = G γ_F ∘ γ_G F`. -/
  γ_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    (γ (f ≫ g)).hom = (α_ f g (q c)).hom ≫ f ◁ (γ g).hom ≫ (α_ f (q b) g).inv ≫
      (γ f).hom ▷ g ≫ (α_ (q a) f g).hom
  /-- `γ_{1_λ} = 1_{q_λ}`. -/
  γ_id (a : B) : (γ (𝟙 a)).hom = (λ_ (q a)).hom ≫ (ρ_ (q a)).inv
  /-- `γ_{q_λ} = 1_{q_λ²}`. -/
  γ_q (a : B) : (γ (q a)).hom = 𝟙 _
  /-- `γ_{π_λ} = β_{q_λ}⁻¹`. -/
  γ_pi (a : B) : (γ (pi a)).hom = (β (q a)).inv
  /-- `ii_λ : q_λ⁻¹ q_λ ≅ 1_λ`. -/
  ii (a : B) : q a ≫ qinv a ≅ 𝟙 a
  /-- `jj_λ : q_λ q_λ⁻¹ ≅ 1_λ`. -/
  jj (a : B) : qinv a ≫ q a ≅ 𝟙 a
  /-- `q_λ ii_λ = jj_λ q_λ`. -/
  q_ii (a : B) : (ii a).hom ▷ q a ≫ (λ_ (q a)).hom = (α_ (q a) (qinv a) (q a)).hom ≫
    q a ◁ (jj a).hom ≫ (ρ_ (q a)).hom
  /-- `ii_λ q_λ⁻¹ = q_λ⁻¹ jj_λ`. -/
  ii_qinv (a : B) : qinv a ◁ (ii a).hom ≫ (ρ_ (qinv a)).hom = (α_ (qinv a) (q a) (qinv a)).inv ≫
    (jj a).hom ▷ qinv a ≫ (λ_ (qinv a)).hom

end Defs

/-! ## The 2-supercategory of 2-morphisms of degree zero -/

open Supercategory GradedSupercategory BicategoryStruct TwoSupercategory

/-- The objects of the 2-supercategory of 2-morphisms of degree zero of a graded
2-supercategory `B`: the objects of `B`. -/
@[ext]
structure DegreeZero2 (R : Type w) (B : Type u₁) where
  /-- The underlying object. -/
  as : B

namespace DegreeZero2

variable {R : Type w} [CommRing R] {B : Type u₁} [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [∀ a b : B, GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R B] [GradedTwoSupercategory R B]

open GradedTwoSupercategory

/-- The bicategory data: the 1-morphisms of `B` and its 2-morphisms of degree zero. -/
instance instBicategoryStruct : BicategoryStruct.{w₁, v₁} (DegreeZero2 R B) where
  Hom a b := DegreeZero R (a.as ⟶ b.as)
  id a := ⟨𝟙 a.as⟩
  comp f g := ⟨f.obj ≫ g.obj⟩
  homCategory a b := inferInstanceAs (Category (DegreeZero R (a.as ⟶ b.as)))
  whiskerLeft f _ _ η := ⟨f.obj ◁ η.1, whiskerLeft_mem_degree f.obj η.2⟩
  whiskerRight η h := ⟨η.1 ▷ h.obj, whiskerRight_mem_degree h.obj η.2⟩
  associator f g h := DegreeZero.isoMk (associator f.obj g.obj h.obj)
    (associator_hom_mem_degree (R := R) f.obj g.obj h.obj)
  leftUnitor f := DegreeZero.isoMk (leftUnitor f.obj) (leftUnitor_hom_mem_degree (R := R) f.obj)
  rightUnitor f := DegreeZero.isoMk (rightUnitor f.obj) (rightUnitor_hom_mem_degree (R := R) f.obj)

instance (a b : DegreeZero2 R B) : Preadditive (a ⟶ b) :=
  inferInstanceAs (Preadditive (DegreeZero R (a.as ⟶ b.as)))

instance (a b : DegreeZero2 R B) : Linear R (a ⟶ b) :=
  inferInstanceAs (Linear R (DegreeZero R (a.as ⟶ b.as)))

instance (a b : DegreeZero2 R B) : Supercategory R (a ⟶ b) :=
  inferInstanceAs (Supercategory R (DegreeZero R (a.as ⟶ b.as)))

/-- The 2-morphisms of degree zero of a graded 2-supercategory form a 2-supercategory. -/
instance twoSupercategory : TwoSupercategory R (DegreeZero2 R B) where
  whiskerLeft_id f g := DegreeZero.hom_ext (TwoSupercategory.whiskerLeft_id (R := R) f.obj g.obj)
  whiskerLeft_comp f _ _ _ η θ := DegreeZero.hom_ext
    (TwoSupercategory.whiskerLeft_comp (R := R) f.obj η.1 θ.1)
  id_whiskerLeft η := DegreeZero.hom_ext (TwoSupercategory.id_whiskerLeft (R := R) η.1)
  comp_whiskerLeft f g _ _ η := DegreeZero.hom_ext
    (TwoSupercategory.comp_whiskerLeft (R := R) f.obj g.obj η.1)
  id_whiskerRight f g := DegreeZero.hom_ext (TwoSupercategory.id_whiskerRight (R := R) f.obj g.obj)
  comp_whiskerRight η θ i := DegreeZero.hom_ext
    (TwoSupercategory.comp_whiskerRight (R := R) η.1 θ.1 i.obj)
  whiskerRight_id η := DegreeZero.hom_ext (TwoSupercategory.whiskerRight_id (R := R) η.1)
  whiskerRight_comp η g h := DegreeZero.hom_ext
    (TwoSupercategory.whiskerRight_comp (R := R) η.1 g.obj h.obj)
  whisker_assoc f _ _ η h := DegreeZero.hom_ext
    (TwoSupercategory.whisker_assoc (R := R) f.obj η.1 h.obj)
  pentagon f g h i := DegreeZero.hom_ext
    (TwoSupercategory.pentagon (R := R) f.obj g.obj h.obj i.obj)
  triangle f g := DegreeZero.hom_ext (TwoSupercategory.triangle (R := R) f.obj g.obj)
  whiskerLeft_add f _ _ η θ := DegreeZero.hom_ext
    (TwoSupercategory.whiskerLeft_add (R := R) f.obj η.1 θ.1)
  add_whiskerRight η θ h := DegreeZero.hom_ext
    (TwoSupercategory.add_whiskerRight (R := R) η.1 θ.1 h.obj)
  whiskerLeft_smul f _ _ r η := DegreeZero.hom_ext (TwoSupercategory.whiskerLeft_smul f.obj r η.1)
  smul_whiskerRight r η h := DegreeZero.hom_ext (TwoSupercategory.smul_whiskerRight r η.1 h.obj)
  whiskerLeft_mem f _ _ _ _ hη := TwoSupercategory.whiskerLeft_mem (R := R) (B := B) f.obj hη
  whiskerRight_mem h hη := TwoSupercategory.whiskerRight_mem (R := R) (B := B) h.obj hη
  super_interchange hη hθ := DegreeZero.hom_ext
    (TwoSupercategory.super_interchange (R := R) (B := B) hη hθ)
  associator_hom_mem f g h := TwoSupercategory.associator_hom_mem (R := R) f.obj g.obj h.obj
  leftUnitor_hom_mem f := TwoSupercategory.leftUnitor_hom_mem (R := R) f.obj
  rightUnitor_hom_mem f := TwoSupercategory.rightUnitor_hom_mem (R := R) f.obj

variable [QPiTwoSupercategory R B]

/-- The Π-structure of a graded `(Q, Π)`-2-supercategory restricts to degree zero. -/
instance instPiTwoSupercategory : PiTwoSupercategory R (DegreeZero2 R B) where
  pi a := ⟨PiTwoSupercategory.pi (R := R) a.as⟩
  ζ a := DegreeZero.isoMk (PiTwoSupercategory.ζ (R := R) a.as)
    (QPiTwoSupercategory.ζ_hom_mem_degree a.as)
  ζ_hom_mem a := PiTwoSupercategory.ζ_hom_mem (R := R) a.as

end DegreeZero2

/-- The underlying 2-category of a graded 2-supercategory: the same objects and 1-morphisms, and
the even 2-morphisms of degree zero. -/
abbrev GUnderlying2 (R : Type w) (B : Type u₁) := Underlying2 R (DegreeZero2 R B)

namespace GUnderlying2

variable {R : Type w} [CommRing R] {B : Type u₁} [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [∀ a b : B, GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R B] [GradedTwoSupercategory R B] [QPiTwoSupercategory R B]

open QPiTwoSupercategory

/-- An even 2-isomorphism of degree zero of `B`, as a 2-isomorphism of the underlying
2-category. -/
def isoU {a b : B} {f g : a ⟶ b} (e : f ≅ g) (h0 : e.hom ∈ parity (R := R) f g 0)
    (hd : e.hom ∈ degree (R := R) f g 0) :
    (⟨⟨f⟩⟩ : (⟨⟨a⟩⟩ : GUnderlying2 R B) ⟶ ⟨⟨b⟩⟩) ≅ ⟨⟨g⟩⟩ :=
  Underlying.isoMk (DegreeZero.isoMk e hd) h0

/-- **Brundan–Ellis, after Definition 6.14.** The underlying 2-category of a graded
`(Q, Π)`-2-supercategory is a `(Q, Π)`-2-category, with `β`, `ξ` of Lemma 3.2 and `γ`, `ii`,
`jj` of Lemma 6.6. -/
instance instQPiTwoCategory : QPiTwoCategory R (GUnderlying2 R B) where
  q a := ⟨⟨q (R := R) a.obj.as⟩⟩
  qinv a := ⟨⟨qinv (R := R) a.obj.as⟩⟩
  γ f := isoU (γ (R := R) f.obj.obj) (γ_hom_mem _) (γ_hom_mem_degree _)
  γ_naturality η := Subtype.ext (DegreeZero.hom_ext (γ_naturality η.1.1))
  γ_comp f g := Subtype.ext (DegreeZero.hom_ext (γ_comp f.obj.obj g.obj.obj))
  γ_id a := Subtype.ext (DegreeZero.hom_ext (γ_id a.obj.as))
  γ_q a := Subtype.ext (DegreeZero.hom_ext (γ_q a.obj.as))
  γ_pi a := Subtype.ext (DegreeZero.hom_ext (γ_pi a.obj.as))
  ii a := isoU (ii (R := R) a.obj.as) (ii_hom_mem _) (ii_hom_mem_degree _)
  jj a := isoU (jj (R := R) a.obj.as) (jj_hom_mem _) (jj_hom_mem_degree _)
  q_ii a := Subtype.ext (DegreeZero.hom_ext (q_ii a.obj.as))
  ii_qinv a := Subtype.ext (DegreeZero.hom_ext (ii_qinv a.obj.as))

end GUnderlying2

end StringDiagrams

end
