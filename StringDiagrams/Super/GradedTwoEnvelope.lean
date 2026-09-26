import StringDiagrams.Super.GradedTwo
import StringDiagrams.Super.QEnvelope
import StringDiagrams.Super.TwoEnvelopePi

/-!
# The (Q, Π)-envelope of a graded 2-supercategory

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §6,
Definition 6.10.

The `(Q, Π)`-envelope `𝔄_{q,π}` of a graded 2-supercategory `𝔄` has the objects of `𝔄`, and
its morphism supercategories are the `(Q, Π)`-envelopes of those of `𝔄`: the 1-morphisms
`λ → μ` are the `Q^m Π^a F`, and `Hom(Q^m Π^a F, Q^n Π^b G) := Q^{n-m} Π^{a+b} Hom_𝔄(F, G)`;
`(Q^n Π^b G)(Q^m Π^a F) := Q^{m+n} Π^{a+b}(GF)`, and horizontal composition of 2-morphisms is
`y^{l,d}_{n,b} x^{k,c}_{m,a} = (-1)^{b|x| + |y|c + bc + ab} (yx)^{k+l,c+d}_{m+n,a+b}`.

As for Definition 6.8 we build it in two steps: the *`Q`-envelope* `QTwoEnvelope R 𝔄`
(morphism supercategories `QEnvelope R (λ ⟶ μ)`, 1-morphisms `Q^m F`, horizontal composition
without signs), a graded 2-supercategory (`QTwoEnvelope.gradedTwoSupercategory`), and the
Π-envelope `TwoEnvelope` of Definition 4.4, which is a graded 2-supercategory for a graded
2-supercategory (`TwoEnvelope.gradedTwoSupercategory`). Thus
`QPiTwoEnvelope R 𝔄 := TwoEnvelope R (QTwoEnvelope R 𝔄)`, whose morphism supercategories are
literally the `(Q, Π)`-envelopes `QPiEnvelope R (λ ⟶ μ)` of Definition 6.8.

## Main statements

* `QPiTwoEnvelope R B` (**Definition 6.10**): a graded 2-supercategory, and a graded
  `(Q, Π)`-2-supercategory (`QPiTwoEnvelope.instQPiTwoSupercategory`) with
  `q_λ = Q¹Π⁰1_λ`, `q_λ⁻¹ = Q⁻¹Π⁰1_λ`, `π_λ = Q⁰Π¹1_λ` and `σ_λ`, `σ̄_λ`, `ζ_λ` induced by
  `1_{1_λ}`.
* `QPiTwoEnvelope.toHom_hcomp`: the sign formula for horizontal composition of Definition 6.10.
* `QPiTwoEnvelope.J_gradedSuperequivalence_iff`: the canonical `𝕁 : 𝔄 → 𝔄_{q,π}` is a graded
  superequivalence on all morphism supercategories if and only if they are all
  `(Q, Π)`-complete (the 2-categorical analogue of Lemma 4.1, stated after Definition 6.10).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory GradedSupercategory BicategoryStruct TwoSupercategory

universe w w₁ v u

/-! ## The `Q`-envelope of a graded 2-supercategory -/

/-- The objects of the `Q`-envelope of a 2-supercategory: the objects of `B`. -/
@[ext]
structure QTwoEnvelope (R : Type w₁) (B : Type u) where
  /-- The underlying object. -/
  as : B

namespace QTwoEnvelope

variable {R : Type w₁} [CommRing R] {B : Type u} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)]

open QEnvelope

/-- The bicategory data of the `Q`-envelope: 1-morphisms `Q^m F`, `(Q^n G)(Q^m F) = Q^{m+n}(GF)`,
whiskerings and coherence maps those of `B`. -/
instance instBicategoryStruct : BicategoryStruct.{w, v} (QTwoEnvelope R B) where
  Hom a b := QEnvelope R (a.as ⟶ b.as)
  id a := ⟨0, 𝟙 a.as⟩
  comp f g := ⟨f.shift + g.shift, f.obj ≫ g.obj⟩
  homCategory a b := inferInstanceAs (Category (QEnvelope R (a.as ⟶ b.as)))
  whiskerLeft f _ _ η := QEnvelope.ofHom (f.obj ◁ QEnvelope.toHom η)
  whiskerRight η h := QEnvelope.ofHom (QEnvelope.toHom η ▷ h.obj)
  associator f g h := QEnvelope.isoOfIso (associator f.obj g.obj h.obj)
  leftUnitor f := QEnvelope.isoOfIso (leftUnitor f.obj)
  rightUnitor f := QEnvelope.isoOfIso (rightUnitor f.obj)

instance (a b : QTwoEnvelope R B) : Preadditive (a ⟶ b) :=
  inferInstanceAs (Preadditive (QEnvelope R (a.as ⟶ b.as)))

instance (a b : QTwoEnvelope R B) : Linear R (a ⟶ b) :=
  inferInstanceAs (Linear R (QEnvelope R (a.as ⟶ b.as)))

instance (a b : QTwoEnvelope R B) : Supercategory R (a ⟶ b) :=
  inferInstanceAs (Supercategory R (QEnvelope R (a.as ⟶ b.as)))

/-- The `Q`-envelope of a 2-supercategory is a 2-supercategory: all axioms are those of
`B`. -/
instance twoSupercategory [TwoSupercategory R B] : TwoSupercategory R (QTwoEnvelope R B) where
  whiskerLeft_id f g := TwoSupercategory.whiskerLeft_id (R := R) f.obj g.obj
  whiskerLeft_comp f _ _ _ η θ := TwoSupercategory.whiskerLeft_comp (R := R) f.obj
    (QEnvelope.toHom η) (QEnvelope.toHom θ)
  id_whiskerLeft η := TwoSupercategory.id_whiskerLeft (R := R) (QEnvelope.toHom η)
  comp_whiskerLeft f g _ _ η := TwoSupercategory.comp_whiskerLeft (R := R) f.obj g.obj
    (QEnvelope.toHom η)
  id_whiskerRight f g := TwoSupercategory.id_whiskerRight (R := R) f.obj g.obj
  comp_whiskerRight η θ i := TwoSupercategory.comp_whiskerRight (R := R) (QEnvelope.toHom η)
    (QEnvelope.toHom θ) i.obj
  whiskerRight_id η := TwoSupercategory.whiskerRight_id (R := R) (QEnvelope.toHom η)
  whiskerRight_comp η g h := TwoSupercategory.whiskerRight_comp (R := R) (QEnvelope.toHom η)
    g.obj h.obj
  whisker_assoc f _ _ η h := TwoSupercategory.whisker_assoc (R := R) f.obj (QEnvelope.toHom η)
    h.obj
  pentagon f g h i := TwoSupercategory.pentagon (R := R) f.obj g.obj h.obj i.obj
  triangle f g := TwoSupercategory.triangle (R := R) f.obj g.obj
  whiskerLeft_add f _ _ η θ := TwoSupercategory.whiskerLeft_add (R := R) f.obj
    (QEnvelope.toHom η) (QEnvelope.toHom θ)
  add_whiskerRight η θ h := TwoSupercategory.add_whiskerRight (R := R) (QEnvelope.toHom η)
    (QEnvelope.toHom θ) h.obj
  whiskerLeft_smul f _ _ r η := TwoSupercategory.whiskerLeft_smul f.obj r (QEnvelope.toHom η)
  smul_whiskerRight r η h := TwoSupercategory.smul_whiskerRight r (QEnvelope.toHom η) h.obj
  whiskerLeft_mem f _ _ _ _ hη := TwoSupercategory.whiskerLeft_mem (R := R) (B := B) f.obj hη
  whiskerRight_mem h hη := TwoSupercategory.whiskerRight_mem (R := R) (B := B) h.obj hη
  super_interchange hη hθ := TwoSupercategory.super_interchange (R := R) (B := B) hη hθ
  associator_hom_mem f g h := TwoSupercategory.associator_hom_mem (R := R) f.obj g.obj h.obj
  leftUnitor_hom_mem f := TwoSupercategory.leftUnitor_hom_mem (R := R) f.obj
  rightUnitor_hom_mem f := TwoSupercategory.rightUnitor_hom_mem (R := R) f.obj

variable [∀ a b : B, GradedSupercategory R (a ⟶ b)]

instance (a b : QTwoEnvelope R B) : GradedSupercategory R (a ⟶ b) :=
  inferInstanceAs (GradedSupercategory R (QEnvelope R (a.as ⟶ b.as)))

/-- The `Q`-envelope of a graded 2-supercategory is a graded 2-supercategory. -/
instance gradedTwoSupercategory [TwoSupercategory R B] [GradedTwoSupercategory R B] :
    GradedTwoSupercategory R (QTwoEnvelope R B) where
  whiskerLeft_mem_degree {a b c} f {g h n η} hη := by
    show f.obj ◁ QEnvelope.toHom η ∈ degree (R := R) _ _ (n + ((f.shift + g.shift) - (f.shift + h.shift)))
    rw [show n + ((f.shift + g.shift) - (f.shift + h.shift)) = n + (g.shift - h.shift) by ring]
    exact GradedTwoSupercategory.whiskerLeft_mem_degree f.obj hη
  whiskerRight_mem_degree {a b c f g n η} h hη := by
    show QEnvelope.toHom η ▷ h.obj ∈ degree (R := R) _ _ (n + ((f.shift + h.shift) - (g.shift + h.shift)))
    rw [show n + ((f.shift + h.shift) - (g.shift + h.shift)) = n + (f.shift - g.shift) by ring]
    exact GradedTwoSupercategory.whiskerRight_mem_degree h.obj hη
  associator_hom_mem_degree f g h := by
    show (associator f.obj g.obj h.obj).hom ∈ degree (R := R) _ _
      (0 + (f.shift + g.shift + h.shift - (f.shift + (g.shift + h.shift))))
    rw [show (0 : ℤ) + (f.shift + g.shift + h.shift - (f.shift + (g.shift + h.shift))) = 0 by ring]
    exact GradedTwoSupercategory.associator_hom_mem_degree f.obj g.obj h.obj
  leftUnitor_hom_mem_degree f := by
    show (leftUnitor f.obj).hom ∈ degree (R := R) _ _ (0 + (0 + f.shift - f.shift))
    rw [show (0 : ℤ) + (0 + f.shift - f.shift) = 0 by ring]
    exact GradedTwoSupercategory.leftUnitor_hom_mem_degree f.obj
  rightUnitor_hom_mem_degree f := by
    show (rightUnitor f.obj).hom ∈ degree (R := R) _ _ (0 + (f.shift + 0 - f.shift))
    rw [show (0 : ℤ) + (f.shift + 0 - f.shift) = 0 by ring]
    exact GradedTwoSupercategory.rightUnitor_hom_mem_degree f.obj

end QTwoEnvelope

/-! ## The Π-envelope of a graded 2-supercategory is graded -/

namespace TwoEnvelope

variable {R : Type w₁} [CommRing R] {B : Type u} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [∀ a b : B, GradedSupercategory R (a ⟶ b)]

instance (a b : TwoEnvelope R B) : GradedSupercategory R (a ⟶ b) :=
  inferInstanceAs (GradedSupercategory R (Envelope R (a.as ⟶ b.as)))

/-- The Π-envelope of a graded 2-supercategory is a graded 2-supercategory. -/
instance gradedTwoSupercategory [TwoSupercategory R B] [GradedTwoSupercategory R B] :
    GradedTwoSupercategory R (TwoEnvelope R B) where
  whiskerLeft_mem_degree {_ _ _} f {_ _ _ _} hη :=
    GradedTwoSupercategory.whiskerLeft_mem_degree (R := R) f.obj (twist_mem_degree _ hη)
  whiskerRight_mem_degree {a _ _ f g _ _} h hη :=
    GradedTwoSupercategory.whiskerRight_mem_degree (R := R) h.obj
      (twist_mem_degree (R := R) (C := a ⟶ _) (X := f) (Y := g) h.par hη)
  associator_hom_mem_degree f g h :=
    GradedTwoSupercategory.associator_hom_mem_degree (R := R) f.obj g.obj h.obj
  leftUnitor_hom_mem_degree f := GradedTwoSupercategory.leftUnitor_hom_mem_degree (R := R) f.obj
  rightUnitor_hom_mem_degree f := GradedTwoSupercategory.rightUnitor_hom_mem_degree (R := R) f.obj

end TwoEnvelope

end StringDiagrams

end
