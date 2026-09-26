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
* `QPiTwoEnvelope.QPiComplete2`, `QPiTwoEnvelope.qpiComplete2_iff`,
  `QPiTwoEnvelope.J_gradedEvenlyDense_iff`: the canonical `𝕁 : 𝔄 → 𝔄_{q,π}` is graded evenly
  dense (hence, being full and faithful, a graded superequivalence) on all morphism
  supercategories if and only if `𝔄` is `(Q, Π)`-complete in the sense stated after
  Definition 6.10, if and only if all its morphism supercategories are `(Q, Π)`-complete.
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

/-! ## The `(Q, Π)`-envelope -/

/-- **Definition 6.10.** The `(Q, Π)`-envelope `𝔄_{q,π}` of a graded 2-supercategory: the
Π-envelope (Definition 4.4) of the `Q`-envelope. Its morphism supercategories are the
`(Q, Π)`-envelopes `QPiEnvelope R (λ ⟶ μ)` of Definition 6.8. -/
abbrev QPiTwoEnvelope (R : Type w₁) (B : Type u) := TwoEnvelope R (QTwoEnvelope R B)

namespace QPiTwoEnvelope

variable {R : Type w₁} [CommRing R] {B : Type u} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [∀ a b : B, GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R B] [GradedTwoSupercategory R B]

example : TwoSupercategory R (QPiTwoEnvelope R B) := inferInstance
example : GradedTwoSupercategory R (QPiTwoEnvelope R B) := inferInstance

omit [(a b : B) → GradedSupercategory R (a ⟶ b)] [TwoSupercategory R B]
  [GradedTwoSupercategory R B] in
/-- The morphism supercategories of `𝔄_{q,π}` are the `(Q, Π)`-envelopes of those of `𝔄`. -/
theorem hom_eq (a b : QPiTwoEnvelope R B) : (a ⟶ b) = QPiEnvelope R (a.as.as ⟶ b.as.as) := rfl

/-- The 1-morphism `q_λ = Q¹Π⁰1_λ`. -/
def q (a : QPiTwoEnvelope R B) : a ⟶ a := ⟨0, ⟨1, 𝟙 a.as.as⟩⟩

/-- The 1-morphism `q_λ⁻¹ = Q⁻¹Π⁰1_λ`. -/
def qinv (a : QPiTwoEnvelope R B) : a ⟶ a := ⟨0, ⟨-1, 𝟙 a.as.as⟩⟩

/-- `σ_λ : q_λ ⇒ 1_λ`, induced by `1_{1_λ}`. -/
def σ (a : QPiTwoEnvelope R B) : q a ≅ 𝟙 a :=
  Envelope.isoOfIso (QEnvelope.isoOfIso (Iso.refl (𝟙 a.as.as)))

/-- `σ̄_λ : q_λ⁻¹ ⇒ 1_λ`, induced by `1_{1_λ}`. -/
def σbar (a : QPiTwoEnvelope R B) : qinv a ≅ 𝟙 a :=
  Envelope.isoOfIso (QEnvelope.isoOfIso (Iso.refl (𝟙 a.as.as)))

omit [(a b : B) → GradedSupercategory R (a ⟶ b)] [TwoSupercategory R B]
  [GradedTwoSupercategory R B] in
theorem idIso_hom_mem {a : QPiTwoEnvelope R B} {f : a ⟶ a} (hf : f.par = 0) (hobj : f.obj.obj = 𝟙 a.as.as)
    (e : f.obj.obj ≅ 𝟙 a.as.as) (he : e = eqToIso hobj) :
    (Envelope.isoOfIso (QEnvelope.isoOfIso e) : f ≅ 𝟙 a).hom ∈ parity (R := R) f (𝟙 a) 0 := by
  obtain ⟨p, ⟨m, x⟩⟩ := f
  simp only at hf hobj
  subst hf hobj he
  show 𝟙 _ ∈ parity (R := R) (C := a.as.as ⟶ a.as.as) _ _ (0 + (0 + 0))
  simpa using id_mem (R := R) (𝟙 a.as.as)

/-- **Definition 6.10.** The `(Q, Π)`-envelope is a graded `(Q, Π)`-2-supercategory:
`π_λ = Q⁰Π¹1_λ` (Definition 4.4), `q_λ = Q¹Π⁰1_λ`, `q_λ⁻¹ = Q⁻¹Π⁰1_λ`, and `ζ_λ`, `σ_λ`, `σ̄_λ`
induced by `1_{1_λ}`, which are odd, even and even of degrees `0`, `-1` and `1`. -/
instance instQPiTwoSupercategory : QPiTwoSupercategory R (QPiTwoEnvelope R B) where
  ζ_hom_mem_degree a := by
    show 𝟙 (𝟙 a.as.as) ∈ degree (R := R) _ _ (0 + (0 - 0))
    simpa using id_mem_degree (R := R) (𝟙 a.as.as)
  q := q
  qinv := qinv
  σ := σ
  σbar := σbar
  σ_hom_mem a := idIso_hom_mem rfl rfl _ rfl
  σ_hom_mem_degree a := by
    show 𝟙 (𝟙 a.as.as) ∈ degree (R := R) _ _ (-1 + (1 - 0))
    simpa using id_mem_degree (R := R) (𝟙 a.as.as)
  σbar_hom_mem a := idIso_hom_mem rfl rfl _ rfl
  σbar_hom_mem_degree a := by
    show 𝟙 (𝟙 a.as.as) ∈ degree (R := R) _ _ (1 + (-1 - 0))
    simpa using id_mem_degree (R := R) (𝟙 a.as.as)

/-- The morphism of `𝔄` underlying a 2-morphism `x^{n,b}_{m,a}` of `𝔄_{q,π}`. -/
abbrev toHom {a b : QPiTwoEnvelope R B} {f g : a ⟶ b} (x : f ⟶ g) : f.obj.obj ⟶ g.obj.obj :=
  QEnvelope.toHom (Envelope.toHom x)

omit [(a b : B) → GradedSupercategory R (a ⟶ b)] [GradedTwoSupercategory R B] in
/-- **Definition 6.10**, horizontal composition:
`y^{l,d}_{n,b} x^{k,c}_{m,a} = (-1)^{b|x| + |y|c + bc + ab} (yx)^{k+l,c+d}_{m+n,a+b}`
(with 1-morphisms composed in diagrammatic order, `x : Q^mΠ^aF ⇒ Q^kΠ^cH`,
`y : Q^nΠ^bG ⇒ Q^lΠ^dK`, and `|x|`, `|y|` the parities in `𝔄`). The degrees add
(`GradedTwoSupercategory.hcomp_mem_degree`). -/
theorem toHom_hcomp {a b c : QPiTwoEnvelope R B} {f h : a ⟶ b} {g k : b ⟶ c} {x : f ⟶ h}
    {y : g ⟶ k} {px py : ZMod 2} (hx : toHom x ∈ parity (R := R) f.obj.obj h.obj.obj px)
    (hy : toHom y ∈ parity (R := R) g.obj.obj k.obj.obj py) :
    toHom (hcomp x y) =
      sign R (g.par * px + py * h.par + g.par * h.par + f.par * g.par) • hcomp (toHom x) (toHom y) :=
  congrArg QEnvelope.toHom (TwoEnvelope.toHom_hcomp (R := R) (B := QTwoEnvelope R B) hx hy)

omit [TwoSupercategory R B] [GradedTwoSupercategory R B] in
/-- The 2-morphism `x^{n,b}_{m,a}` has degree `deg x + n - m`. -/
theorem ofHom_mem_degree {a b : QPiTwoEnvelope R B} {f g : a ⟶ b} {x : f.obj.obj ⟶ g.obj.obj}
    {d : ℤ} (hx : x ∈ degree (R := R) _ _ d) :
    (Envelope.ofHom (QEnvelope.ofHom x) : f ⟶ g) ∈ degree (R := R) f g (d + g.obj.shift - f.obj.shift) :=
  QPiEnvelope.ofHom_mem_degree (R := R) (X := f) (Y := g) hx

/-! ### `(Q, Π)`-completeness -/

/-- The condition after Definition 6.10: every object `λ` has 1-morphisms `q^±_λ, π_λ` with
homogeneous 2-isomorphisms `q^±_λ ⇒ 1_λ` even of degrees `∓1` and `π_λ ⇒ 1_λ` odd of degree
`0`. -/
def QPiComplete2 : Prop :=
  ∀ a : B, (∃ (f : a ⟶ a) (e : f ≅ 𝟙 a), e.hom ∈ parity (R := R) f (𝟙 a) 0 ∧
      e.hom ∈ degree (R := R) f (𝟙 a) 1) ∧
    (∃ (f : a ⟶ a) (e : f ≅ 𝟙 a), e.hom ∈ parity (R := R) f (𝟙 a) 0 ∧
      e.hom ∈ degree (R := R) f (𝟙 a) (-1)) ∧
    (∃ (f : a ⟶ a) (e : f ≅ 𝟙 a), e.hom ∈ parity (R := R) f (𝟙 a) 1 ∧
      e.hom ∈ degree (R := R) f (𝟙 a) 0)

/-- `𝔄` is `(Q, Π)`-complete if and only if all its morphism supercategories are. -/
theorem qpiComplete2_iff : QPiComplete2 (R := R) (B := B) ↔
    ∀ a b : B, QPiEnvelope.QPiComplete R (a ⟶ b) := by
  constructor
  · intro h a b F
    have key : ∀ (p : ZMod 2) (n : ℤ), (∃ (f : a ⟶ a) (e : f ≅ 𝟙 a),
        e.hom ∈ parity (R := R) f (𝟙 a) p ∧ e.hom ∈ degree (R := R) f (𝟙 a) n) →
        ∃ (Y : a ⟶ b) (e : Y ≅ F), e.hom ∈ parity (R := R) Y F p ∧
          e.hom ∈ degree (R := R) Y F n := by
      rintro p n ⟨f, e, he, he'⟩
      refine ⟨f ≫ F, whiskerRightIso (R := R) e F ≪≫ leftUnitor F, ?_, ?_⟩
      · simpa using comp_mem (whiskerRight_mem F he) (leftUnitor_hom_mem (R := R) F)
      · simpa using comp_mem_degree (GradedTwoSupercategory.whiskerRight_mem_degree F he')
          (GradedTwoSupercategory.leftUnitor_hom_mem_degree (R := R) F)
    exact ⟨key 0 1 (h a).1, key 0 (-1) (h a).2.1, key 1 0 (h a).2.2⟩
  · intro h a
    exact ⟨(h a a (𝟙 a)).1, (h a a (𝟙 a)).2.1, (h a a (𝟙 a)).2.2⟩

/-- The components `QPiEnvelope.J : (λ ⟶ μ) → (λ ⟶ μ)_{q,π}` of `𝕁 : 𝔄 → 𝔄_{q,π}` are graded
superequivalences if and only if `𝔄` is `(Q, Π)`-complete. -/
theorem J_gradedEvenlyDense_iff :
    (∀ a b : B, GradedEvenlyDense R (QPiEnvelope.J R (a ⟶ b))) ↔ QPiComplete2 (R := R) (B := B) := by
  rw [qpiComplete2_iff]
  exact forall_congr' fun a => forall_congr' fun b => QPiEnvelope.J_gradedEvenlyDense_iff

end QPiTwoEnvelope

end StringDiagrams

end
