import StringDiagrams.Super.Bicategory
import StringDiagrams.Super.MonoidalEnvelope

/-!
# The Π-envelope of a 2-supercategory

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Definition 4.4 and Lemmas 4.5–4.6.

The Π-envelope `𝔄_π` of a 2-supercategory `𝔄` (`StringDiagrams.TwoEnvelope R B`) has the same
objects as `𝔄`, and its morphism supercategories are the Π-envelopes of those of `𝔄`: the
1-morphisms `λ → μ` are the `Πᵃ F` for `F : λ → μ` in `𝔄` and `a ∈ ℤ/2`, and
`Hom(Πᵃ F, Πᵇ G) := Π^{a+b} Hom_𝔄(F, G)`, the 2-morphism `x_a^b : Πᵃ F ⇒ Πᵇ G` coming from a
homogeneous `x : F ⇒ G` having parity `|x| + a + b`; vertical composition is (4.3),
`y_b^c ∘ x_a^b = (y ∘ x)_a^c`. In Lean the hom categories are literally
`Envelope R (a ⟶ b)`.

Horizontal composition of 1-morphisms is `(Πᵇ G)(Πᵃ F) := Π^{a+b}(GF)`, and of 2-morphisms is
(4.4): for `x : Πᵃ F ⇒ Πᶜ H` and `y : Πᵇ G ⇒ Πᵈ K`,

  `y_b^d x_a^c := (-1)^{b|x| + |y|c + bc + ab} (yx)_{a+b}^{c+d}`.

With 1-morphisms composed in diagrammatic order (`F ≫ G` is the paper's `GF`) and the
whiskering presentation of `StringDiagrams.TwoSupercategory`, (4.4) amounts to

* `Πᵃ F ◁ y = (-1)^{a|y|} (F ◁ y)` (the paper's `y (1_F)_a^a`), and
* `x ▷ Πᵇ G = (-1)^{b(|x| + a + c)} (x ▷ G)` (the paper's `(1_G)_b^b x`),

(`toHom_whiskerLeft_of_mem`, `toHom_whiskerRight_of_mem`), and the paper's formula (4.4) for
the horizontal composite is `TwoEnvelope.toHom_hcomp`. The coherence maps are those of `𝔄`.

The units are `𝟙_λ = Π⁰ 𝟙_λ`, and the Π-structure is `π_λ := Π¹ 𝟙_λ` with the odd 2-isomorphism
`ζ_λ := (1_{𝟙_λ})_1^0 : π_λ ⇒ 𝟙_λ`; `ξ_λ := ζ_λ ζ_λ` is minus the identity (`toHom_ξ`).

## Main statements

* `TwoEnvelope R B`, with its `BicategoryStruct` and hom-category instances, and
  `TwoEnvelope.twoSupercategory`: **Definition 4.4** and **Lemma 4.5** (the compositions (4.3)
  and (4.4) satisfy the super interchange law, in the paper's formulation
  `TwoEnvelope.toHom_super_interchange`).
* `TwoEnvelope.toHom_hcomp`: the sign formula (4.4).
* `TwoEnvelope.π`, `TwoEnvelope.ζ`, `TwoEnvelope.ζ_hom_mem`, `TwoEnvelope.toHom_ξ`: the
  Π-structure of Definition 4.4.
* `TwoEnvelope.associator_sign_eq`: the two expressions for `(z_c^f y_b^e) x_a^d` and
  `z_c^f (y_b^e x_a^d)` displayed in Definition 4.4 carry the same sign.
* `TwoEnvelope.PiComplete`, `TwoEnvelope.superequivalenceJ_iff` (**Lemma 4.6**): the canonical
  `𝕁 : 𝔄 → 𝔄_π` (identity on objects, `Envelope.J` on each morphism supercategory) induces
  superequivalences on all morphism supercategories if and only if `𝔄` is Π-complete, i.e.
  each `𝟙_λ` is the target of an odd 2-isomorphism.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory BicategoryStruct

universe w w₁ v u

/-- The objects of the Π-envelope of a 2-supercategory `B` (Brundan–Ellis, Definition 4.4):
the objects of `B`. -/
@[ext]
structure TwoEnvelope (R : Type w₁) (B : Type u) where
  /-- The underlying object. -/
  as : B

namespace TwoEnvelope

variable {R : Type w₁} {B : Type u} [BicategoryStruct.{w, v} B]

section Struct

variable [CommRing R] [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)]

/-- **Definition 4.4.** The bicategory data of the Π-envelope: 1-morphisms `a ⟶ b` are the
objects `Πᵃ F` of `Envelope R (a ⟶ b)`, `(Πᵃ F) ≫ (Πᵇ G) := Π^{a+b}(F ≫ G)`, units `Π⁰ 𝟙`,
whiskerings given by (4.4) and coherence maps those of `B`. -/
instance instBicategoryStruct : BicategoryStruct.{w, v} (TwoEnvelope R B) where
  Hom a b := Envelope R (a.as ⟶ b.as)
  id a := ⟨0, 𝟙 a.as⟩
  comp f g := ⟨f.par + g.par, f.obj ≫ g.obj⟩
  homCategory a b := inferInstanceAs (Category (Envelope R (a.as ⟶ b.as)))
  whiskerLeft f _ _ η := Envelope.ofHom (f.obj ◁ twist R f.par (Envelope.toHom η))
  whiskerRight {_ _ _ _ _} η h := Envelope.ofHom (Envelope.toHom (twist R h.par η) ▷ h.obj)
  associator f g h := Envelope.isoOfIso (associator f.obj g.obj h.obj)
  leftUnitor f := Envelope.isoOfIso (leftUnitor f.obj)
  rightUnitor f := Envelope.isoOfIso (rightUnitor f.obj)

instance (a b : TwoEnvelope R B) : Preadditive (a ⟶ b) :=
  inferInstanceAs (Preadditive (Envelope R (a.as ⟶ b.as)))

instance (a b : TwoEnvelope R B) : Linear R (a ⟶ b) :=
  inferInstanceAs (Linear R (Envelope R (a.as ⟶ b.as)))

instance (a b : TwoEnvelope R B) : Supercategory R (a ⟶ b) :=
  inferInstanceAs (Supercategory R (Envelope R (a.as ⟶ b.as)))

instance (a b : TwoEnvelope R B) : PiSupercategory R (a ⟶ b) :=
  inferInstanceAs (PiSupercategory R (Envelope R (a.as ⟶ b.as)))

open Envelope

variable {a b c d : TwoEnvelope R B}

@[simp] theorem comp_par (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).par = f.par + g.par := rfl

@[simp] theorem comp_obj (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).obj = f.obj ≫ g.obj := rfl

@[simp] theorem id_par (a : TwoEnvelope R B) : (𝟙 a : a ⟶ a).par = 0 := rfl

@[simp] theorem id_obj (a : TwoEnvelope R B) : (𝟙 a : a ⟶ a).obj = 𝟙 a.as := rfl

theorem toHom_whiskerLeft (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    toHom (f ◁ η) = f.obj ◁ twist R f.par (toHom η) := rfl

theorem toHom_whiskerRight {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    toHom (η ▷ h) = toHom (twist R h.par η) ▷ h.obj := rfl

@[simp] theorem toHom_associator_hom (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    toHom (associator f g h).hom = (associator f.obj g.obj h.obj).hom := rfl

@[simp] theorem toHom_associator_inv (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    toHom (associator f g h).inv = (associator f.obj g.obj h.obj).inv := rfl

@[simp] theorem toHom_leftUnitor_hom (f : a ⟶ b) :
    toHom (leftUnitor f).hom = (leftUnitor f.obj).hom := rfl

@[simp] theorem toHom_leftUnitor_inv (f : a ⟶ b) :
    toHom (leftUnitor f).inv = (leftUnitor f.obj).inv := rfl

@[simp] theorem toHom_rightUnitor_hom (f : a ⟶ b) :
    toHom (rightUnitor f).hom = (rightUnitor f.obj).hom := rfl

@[simp] theorem toHom_rightUnitor_inv (f : a ⟶ b) :
    toHom (rightUnitor f).inv = (rightUnitor f.obj).inv := rfl

end Struct

/-! ## Lemma 4.5: the Π-envelope is a 2-supercategory -/

section Axioms

variable [CommRing R] [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]

open Envelope TwoSupercategory

variable {a b c d e : TwoEnvelope R B}

/-- `Πᵃ F ◁ y = (-1)^{a|y|} (F ◁ y)` for `y` of parity `r` in `B`. -/
theorem toHom_whiskerLeft_of_mem (f : a ⟶ b) {g h : b ⟶ c} {η : g ⟶ h} {r : ZMod 2}
    (hη : toHom η ∈ parity (R := R) g.obj h.obj r) :
    toHom (f ◁ η) = sign R (f.par * r) • (f.obj ◁ toHom η) := by
  rw [toHom_whiskerLeft, twist_of_mem _ hη, TwoSupercategory.whiskerLeft_smul]

/-- `x ▷ Πᵇ G = (-1)^{b(|x| + a + c)} (x ▷ G)` for `x : Πᵃ F ⇒ Πᶜ H` of parity `r` in `B`. -/
theorem toHom_whiskerRight_of_mem {f g : a ⟶ b} {η : f ⟶ g} {r : ZMod 2}
    (hη : toHom η ∈ parity (R := R) f.obj g.obj r) (h : b ⟶ c) :
    toHom (η ▷ h) = sign R (h.par * (r + (f.par + g.par))) • (toHom η ▷ h.obj) := by
  rw [toHom_whiskerRight, toHom_twist, twist_of_mem _ hη, smul_smul, ← sign_add,
    TwoSupercategory.smul_whiskerRight]
  congr 2
  ring

theorem toHom_whiskerLeft_mem (f : a ⟶ b) {g h : b ⟶ c} {η : g ⟶ h} {r : ZMod 2}
    (hη : toHom η ∈ parity (R := R) g.obj h.obj r) :
    toHom (f ◁ η) ∈ parity (R := R) (f.obj ≫ g.obj) (f.obj ≫ h.obj) r := by
  rw [toHom_whiskerLeft_of_mem f hη]
  exact Submodule.smul_mem _ _ (TwoSupercategory.whiskerLeft_mem _ hη)

theorem toHom_whiskerRight_mem {f g : a ⟶ b} {η : f ⟶ g} {r : ZMod 2}
    (hη : toHom η ∈ parity (R := R) f.obj g.obj r) (h : b ⟶ c) :
    toHom (η ▷ h) ∈ parity (R := R) (f.obj ≫ h.obj) (g.obj ≫ h.obj) r := by
  rw [toHom_whiskerRight_of_mem hη]
  exact Submodule.smul_mem _ _ (TwoSupercategory.whiskerRight_mem _ hη)

omit [TwoSupercategory R B] in
theorem toHom_whiskerLeft_of_par_zero (f : a ⟶ b) (hf : f.par = 0) {g h : b ⟶ c}
    (η : g ⟶ h) : toHom (f ◁ η) = f.obj ◁ toHom η := by
  rw [toHom_whiskerLeft, hf, twist_zero]

omit [TwoSupercategory R B] in
theorem toHom_whiskerRight_of_par_zero {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) (hh : h.par = 0) :
    toHom (η ▷ h) = toHom η ▷ h.obj := by
  rw [toHom_whiskerRight, hh, twist_zero]

theorem toHom_whiskerLeft_of_even (f : a ⟶ b) {g h : b ⟶ c} {η : g ⟶ h}
    (hη : toHom η ∈ parity (R := R) g.obj h.obj 0) : toHom (f ◁ η) = f.obj ◁ toHom η := by
  rw [toHom_whiskerLeft_of_mem f hη, mul_zero, sign_zero, one_smul]

theorem toHom_whiskerRight_of_even {f g : a ⟶ b} {η : f ⟶ g}
    (hη : toHom η ∈ parity (R := R) f.obj g.obj 0) (h : b ⟶ c) (hfg : f.par = g.par) :
    toHom (η ▷ h) = toHom η ▷ h.obj := by
  rw [toHom_whiskerRight_of_mem hη, hfg, zmod2_add_self, add_zero, mul_zero, sign_zero,
    one_smul]

theorem whiskerLeft_add' (f : a ⟶ b) {g h : b ⟶ c} (η θ : g ⟶ h) :
    f ◁ (η + θ) = f ◁ η + f ◁ θ := by
  apply hom_ext
  rw [toHom_add, toHom_whiskerLeft, toHom_whiskerLeft, toHom_whiskerLeft, toHom_add, map_add,
    TwoSupercategory.whiskerLeft_add (R := R)]

theorem add_whiskerRight' {f g : a ⟶ b} (η θ : f ⟶ g) (h : b ⟶ c) :
    (η + θ) ▷ h = η ▷ h + θ ▷ h := by
  apply hom_ext
  rw [toHom_add, toHom_whiskerRight, toHom_whiskerRight, toHom_whiskerRight, map_add, toHom_add,
    TwoSupercategory.add_whiskerRight (R := R)]

theorem whiskerLeft_zero' (f : a ⟶ b) {g h : b ⟶ c} : f ◁ (0 : g ⟶ h) = 0 := by
  have := whiskerLeft_add' f (0 : g ⟶ h) 0
  rw [add_zero] at this
  exact (add_eq_left.1 this.symm)

theorem zero_whiskerRight' {f g : a ⟶ b} (h : b ⟶ c) : (0 : f ⟶ g) ▷ h = 0 := by
  have := add_whiskerRight' (0 : f ⟶ g) 0 h
  rw [add_zero] at this
  exact (add_eq_left.1 this.symm)

/-- Parity bookkeeping in `ZMod 2`. -/
private theorem zmod2_cases (P : ZMod 2 → Prop) (h0 : P 0) (h1 : P 1) (p : ZMod 2) : P p := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;> assumption

/-- **Definition 4.4 / Lemma 4.5.** The Π-envelope of a 2-supercategory is a
2-supercategory. -/
instance twoSupercategory : TwoSupercategory R (TwoEnvelope R B) where
  whiskerLeft_id f g := by
    apply hom_ext
    rw [toHom_whiskerLeft, toHom_id, twist_id]
    exact TwoSupercategory.whiskerLeft_id (R := R) _ _
  whiskerLeft_comp f _ _ _ η θ := by
    apply hom_ext
    rw [toHom_comp, toHom_whiskerLeft, toHom_whiskerLeft, toHom_whiskerLeft, toHom_comp,
      twist_comp, TwoSupercategory.whiskerLeft_comp (R := R)]
  id_whiskerLeft {_ _ f g} η := by
    apply hom_ext
    rw [toHom_whiskerLeft_of_par_zero _ rfl, toHom_comp, toHom_comp, toHom_leftUnitor_hom,
      toHom_leftUnitor_inv]
    exact TwoSupercategory.id_whiskerLeft (R := R) _
  comp_whiskerLeft {_ _ _ _} f g {h h'} η := by
    refine induction_on' (R := R) η ?_ (fun r η hη => ?_) (fun η θ hη hθ => ?_)
    · rw [whiskerLeft_zero', whiskerLeft_zero', whiskerLeft_zero', Limits.zero_comp,
        Limits.comp_zero]
    · apply hom_ext
      rw [toHom_comp, toHom_comp, toHom_whiskerLeft_of_mem _ hη,
        toHom_whiskerLeft_of_mem f (toHom_whiskerLeft_mem g hη), toHom_whiskerLeft_of_mem g hη,
        TwoSupercategory.whiskerLeft_smul, smul_smul, Linear.smul_comp, Linear.comp_smul,
        toHom_associator_hom, toHom_associator_inv, ← sign_add]
      erw [TwoSupercategory.comp_whiskerLeft (R := R)]
      congr 2
      simp only [comp_par]; ring
    · rw [whiskerLeft_add', whiskerLeft_add', whiskerLeft_add',
        Preadditive.add_comp, Preadditive.comp_add, hη, hθ]
  id_whiskerRight f g := by
    apply hom_ext
    rw [toHom_whiskerRight, twist_id, toHom_id, toHom_id]
    exact TwoSupercategory.id_whiskerRight (R := R) _ _
  comp_whiskerRight η θ i := by
    apply hom_ext
    rw [toHom_comp, toHom_whiskerRight, toHom_whiskerRight, toHom_whiskerRight, twist_comp,
      toHom_comp, TwoSupercategory.comp_whiskerRight (R := R)]
  whiskerRight_id η := by
    apply hom_ext
    rw [toHom_whiskerRight_of_par_zero _ _ rfl, toHom_comp, toHom_comp, toHom_rightUnitor_hom,
      toHom_rightUnitor_inv]
    exact TwoSupercategory.whiskerRight_id (R := R) _
  whiskerRight_comp {_ _ _ _ f f'} η g h := by
    refine induction_on' (R := R) η ?_ (fun r η hη => ?_) (fun η θ hη hθ => ?_)
    · rw [zero_whiskerRight', zero_whiskerRight', zero_whiskerRight', Limits.zero_comp,
        Limits.comp_zero]
    · apply hom_ext
      rw [toHom_comp, toHom_comp, toHom_whiskerRight_of_mem hη,
        toHom_whiskerRight_of_mem (toHom_whiskerRight_mem hη g) h,
        toHom_whiskerRight_of_mem hη, TwoSupercategory.smul_whiskerRight, smul_smul,
        Linear.smul_comp, Linear.comp_smul, toHom_associator_hom, toHom_associator_inv,
        ← sign_add]
      erw [TwoSupercategory.whiskerRight_comp (R := R)]
      congr 2
      simp only [comp_par]
      generalize f.par = x; generalize f'.par = y; generalize g.par = z; generalize h.par = t
      clear hη; revert x y z t r; decide
    · rw [add_whiskerRight', add_whiskerRight', add_whiskerRight',
        Preadditive.add_comp, Preadditive.comp_add, hη, hθ]
  whisker_assoc {_ _ _ _} f {g g'} η h := by
    refine induction_on' (R := R) η ?_ (fun r η hη => ?_) (fun η θ hη hθ => ?_)
    · rw [whiskerLeft_zero', zero_whiskerRight', zero_whiskerRight', whiskerLeft_zero',
        Limits.zero_comp, Limits.comp_zero]
    · apply hom_ext
      rw [toHom_comp, toHom_comp, toHom_whiskerRight_of_mem (toHom_whiskerLeft_mem f hη),
        toHom_whiskerLeft_of_mem f hη, toHom_whiskerLeft_of_mem f (toHom_whiskerRight_mem hη h),
        toHom_whiskerRight_of_mem hη, TwoSupercategory.smul_whiskerRight,
        TwoSupercategory.whiskerLeft_smul, smul_smul, smul_smul, Linear.smul_comp,
        Linear.comp_smul, toHom_associator_hom, toHom_associator_inv, ← sign_add, ← sign_add,
        TwoSupercategory.whisker_assoc (R := R)]
      congr 2
      simp only [comp_par]
      generalize f.par = x; generalize g.par = y; generalize g'.par = z; generalize h.par = t
      clear hη; revert x y z t r; decide
    · rw [whiskerLeft_add', add_whiskerRight', add_whiskerRight', whiskerLeft_add',
        Preadditive.add_comp, Preadditive.comp_add, hη, hθ]
  pentagon f g h i := by
    apply hom_ext
    rw [toHom_comp, toHom_comp, toHom_comp, toHom_associator_hom, toHom_associator_hom,
      toHom_associator_hom]
    rw [toHom_whiskerRight_of_even (TwoSupercategory.associator_hom_mem _ _ _) _
        (by simp only [comp_par, add_assoc]),
      toHom_whiskerLeft_of_even _ (TwoSupercategory.associator_hom_mem _ _ _),
      toHom_associator_hom, toHom_associator_hom]
    exact TwoSupercategory.pentagon (R := R) _ _ _ _
  triangle f g := by
    apply hom_ext
    rw [toHom_comp, toHom_associator_hom]
    rw [toHom_whiskerRight_of_even (TwoSupercategory.rightUnitor_hom_mem _) _
        (by simp only [comp_par, id_par, add_zero]),
      toHom_whiskerLeft_of_even _ (TwoSupercategory.leftUnitor_hom_mem _), toHom_leftUnitor_hom,
      toHom_rightUnitor_hom]
    exact TwoSupercategory.triangle (R := R) _ _
  whiskerLeft_add f _ _ η θ := whiskerLeft_add' f η θ
  add_whiskerRight η θ h := add_whiskerRight' η θ h
  whiskerLeft_smul f _ _ r η := by
    apply hom_ext
    rw [toHom_smul, toHom_whiskerLeft, toHom_whiskerLeft, toHom_smul, map_smul,
      TwoSupercategory.whiskerLeft_smul]
  smul_whiskerRight r η h := by
    apply hom_ext
    rw [toHom_smul, toHom_whiskerRight, toHom_whiskerRight, map_smul, toHom_smul,
      TwoSupercategory.smul_whiskerRight]
  whiskerLeft_mem {_ _ _} f {g h p η} hη := by
    rw [mem_parity_iff] at hη ⊢
    have := toHom_whiskerLeft_mem f hη
    convert this using 2
    simp only [comp_par]
    generalize f.par = x; generalize g.par = y; generalize h.par = z
    clear hη this; revert x y z p; decide
  whiskerRight_mem {_ _ _ f g p η} h hη := by
    rw [mem_parity_iff] at hη ⊢
    have := toHom_whiskerRight_mem hη h
    convert this using 2
    simp only [comp_par]
    generalize f.par = x; generalize g.par = y; generalize h.par = z
    clear hη this; revert x y z p; decide
  super_interchange {_ _ _ f g h i p q η θ} hη hθ := by
    rw [mem_parity_iff] at hη hθ
    rw [koszulSign_smul (R := R)]
    apply hom_ext
    rw [toHom_comp, toHom_smul, toHom_comp, toHom_whiskerRight_of_mem hη,
      toHom_whiskerLeft_of_mem _ hθ, toHom_whiskerLeft_of_mem _ hθ,
      toHom_whiskerRight_of_mem hη, Linear.smul_comp, Linear.comp_smul, Linear.smul_comp,
      Linear.comp_smul, TwoSupercategory.super_interchange hη hθ,
      koszulSign_smul (R := R), smul_smul, smul_smul, smul_smul, smul_smul, ← sign_add,
      ← sign_add, ← sign_add, ← sign_add]
    congr 2
    clear hη hθ
    generalize f.par = x; generalize g.par = y; generalize h.par = z; generalize i.par = t
    revert x y z t p q; decide
  associator_hom_mem f g h := by
    rw [mem_parity_iff, toHom_associator_hom]
    convert TwoSupercategory.associator_hom_mem (R := R) f.obj g.obj h.obj using 2
    simp only [comp_par]
    generalize f.par = x; generalize g.par = y; generalize h.par = z
    revert x y z; decide
  leftUnitor_hom_mem f := by
    rw [mem_parity_iff, toHom_leftUnitor_hom]
    convert TwoSupercategory.leftUnitor_hom_mem (R := R) f.obj using 2
    simp only [comp_par, id_par, zero_add, zmod2_add_self]
  rightUnitor_hom_mem f := by
    rw [mem_parity_iff, toHom_rightUnitor_hom]
    convert TwoSupercategory.rightUnitor_hom_mem (R := R) f.obj using 2
    simp only [comp_par, id_par, add_zero, zmod2_add_self]

/-- **Definition 4.4**, formula (4.4): for `x : Πᵃ F ⇒ Πᶜ H` and `y : Πᵇ G ⇒ Πᵈ K` homogeneous
in `B`, the horizontal composite in `𝔄_π` is
`y_b^d x_a^c = (-1)^{b|x| + |y|c + bc + ab} (yx)_{a+b}^{c+d}`. -/
theorem toHom_hcomp {f h : a ⟶ b} {g k : b ⟶ c} {x : f ⟶ h} {y : g ⟶ k} {px py : ZMod 2}
    (hx : toHom x ∈ parity (R := R) f.obj h.obj px)
    (hy : toHom y ∈ parity (R := R) g.obj k.obj py) :
    toHom (hcomp x y) =
      sign R (g.par * px + py * h.par + g.par * h.par + f.par * g.par) •
        hcomp (toHom x) (toHom y) := by
  rw [hcomp, hcomp, toHom_comp, toHom_whiskerRight_of_mem hx, toHom_whiskerLeft_of_mem _ hy,
    Linear.smul_comp, Linear.comp_smul, smul_smul, ← sign_add]
  congr 2
  ring

/-- **Lemma 4.5**, in the paper's formulation: for `x_a^c, u_c^e` and `y_b^d, v_d^f` (with
`u`, `y` homogeneous in `B`), `(v_d^f u_c^e) ∘ (y_b^d x_a^c) =
(-1)^{(c+e+|u|)(b+d+|y|)} (v_d^f ∘ y_b^d)(u_c^e ∘ x_a^c)`. -/
theorem toHom_super_interchange {f g k : a ⟶ b} {h i l : b ⟶ c} {pu py : ZMod 2}
    (x : f ⟶ g) (u : g ⟶ k) (y : h ⟶ i) (v : i ⟶ l)
    (hu : toHom u ∈ parity (R := R) g.obj k.obj pu)
    (hy : toHom y ∈ parity (R := R) h.obj i.obj py) :
    hcomp x y ≫ hcomp u v =
      koszulSign (pu + (g.par + k.par)) (py + (h.par + i.par)) • hcomp (x ≫ u) (y ≫ v) :=
  hcomp_comp_hcomp (R := R) x u y v (ofHom_mem hu) (ofHom_mem hy)

/-- The sign check displayed in Definition 4.4 for the associator: for
`x : Πᵃ F ⇒ Πᵈ F'`, `y : Πᵇ G ⇒ Πᵉ G'`, `z : Πᶜ H ⇒ Πᶠ H'`, the signs in
`(z_c^f y_b^e) x_a^d = (-1)^{c|y|+|z|e+ce+bc+(b+c)|x|+(|y|+|z|)d+(b+c)d+a(b+c)} ((zy)x)` and
`z_c^f (y_b^e x_a^d) = (-1)^{b|x|+|y|d+bd+ab+c(|x|+|y|)+|z|(d+e)+c(d+e)+(a+b)c} (z(yx))`
agree. -/
theorem associator_sign_eq (a b c d e x y z : ZMod 2) :
    c * y + z * e + c * e + b * c + (b + c) * x + (y + z) * d + (b + c) * d + a * (b + c) =
      b * x + y * d + b * d + a * b + c * (x + y) + z * (d + e) + c * (d + e) + (a + b) * c := by
  ring

/-! ## The Π-structure -/

variable (R) in
/-- `π_λ := Π¹ 𝟙_λ` (Definition 4.4). -/
def π (a : TwoEnvelope R B) : a ⟶ a := ⟨1, 𝟙 a.as⟩

omit [TwoSupercategory R B] in
variable (R) in
/-- `ζ_λ := (1_{𝟙_λ})_1^0 : π_λ ≅ 𝟙_λ` (Definition 4.4). -/
def ζ (a : TwoEnvelope R B) : π R a ≅ 𝟙 a := isoOfIso (Iso.refl (𝟙 a.as))

omit [TwoSupercategory R B] in
theorem ζ_hom_mem (a : TwoEnvelope R B) : (ζ R a).hom ∈ parity (R := R) (π R a) (𝟙 a) 1 := by
  rw [mem_parity_iff]
  show 𝟙 (𝟙 a.as) ∈ parity (R := R) (𝟙 a.as) (𝟙 a.as) (1 + (1 + 0))
  exact id_mem _

omit [TwoSupercategory R B] in
@[simp] theorem toHom_ζ_hom (a : TwoEnvelope R B) : toHom (ζ R a).hom = 𝟙 (𝟙 a.as) := rfl

/-- **Definition 4.4.** `ξ_λ := ζ_λ ζ_λ : π_λ π_λ ⇒ 𝟙_λ 𝟙_λ` is minus the identity. -/
theorem toHom_ξ (a : TwoEnvelope R B) :
    toHom (hcomp (ζ R a).hom (ζ R a).hom) = -𝟙 (𝟙 a.as ≫ 𝟙 a.as) := by
  rw [toHom_hcomp (x := (ζ R a).hom) (y := (ζ R a).hom) (px := 0) (py := 0) (id_mem (𝟙 a.as))
    (id_mem (𝟙 a.as)), hcomp, toHom_ζ_hom]
  show sign R ((1 : ZMod 2) * 0 + 0 * 0 + 1 * 0 + 1 * 1) •
    (𝟙 (𝟙 a.as) ▷ 𝟙 a.as ≫ 𝟙 a.as ◁ 𝟙 (𝟙 a.as)) = _
  rw [TwoSupercategory.id_whiskerRight (R := R), TwoSupercategory.whiskerLeft_id (R := R),
    Category.comp_id]
  simp

/-! ## The canonical `𝕁` and Lemma 4.6 -/

variable (R B) in
/-- A 2-supercategory is Π-complete (Lemma 4.6) if each unit `𝟙_λ` is the target of an odd
2-isomorphism `π_λ ≅ 𝟙_λ`. -/
def PiComplete : Prop :=
  ∀ a : B, ∃ (p : a ⟶ a) (e : p ≅ 𝟙 a), e.hom ∈ parity (R := R) p (𝟙 a) 1

/-- In a Π-complete 2-supercategory every morphism supercategory is Π-complete: `F : λ → μ` is
the target of the odd 2-isomorphism `π_λ F ≅ 𝟙_λ F ≅ F`. -/
theorem piComplete_hom (h : PiComplete R B) (x y : B) : Envelope.PiComplete R (x ⟶ y) := by
  intro f
  obtain ⟨p, e, he⟩ := h x
  let w : p ≫ f ≅ 𝟙 x ≫ f :=
    { hom := e.hom ▷ f
      inv := e.inv ▷ f
      hom_inv_id := by
        rw [← TwoSupercategory.comp_whiskerRight (R := R), e.hom_inv_id,
          TwoSupercategory.id_whiskerRight (R := R)]
      inv_hom_id := by
        rw [← TwoSupercategory.comp_whiskerRight (R := R), e.inv_hom_id,
          TwoSupercategory.id_whiskerRight (R := R)] }
  refine ⟨p ≫ f, w.trans (leftUnitor f), ?_⟩
  have := comp_mem (TwoSupercategory.whiskerRight_mem (R := R) f he)
    (TwoSupercategory.leftUnitor_hom_mem (R := R) f)
  simpa using this

/-- **Lemma 4.6.** The canonical 2-superfunctor `𝕁 : 𝔄 → 𝔄_π` (the identity on objects, so
that it is a 2-superequivalence exactly when it induces superequivalences on all morphism
supercategories) is a 2-superequivalence if and only if `𝔄` is Π-complete. -/
theorem superequivalenceJ_iff :
    (∀ x y : B, Nonempty (Superequivalence R (Envelope.J R (x ⟶ y)))) ↔ PiComplete R B := by
  constructor
  · intro h x
    exact Envelope.piComplete_of_superequivalence (h x x).some (𝟙 x)
  · intro h x y
    exact ⟨Envelope.superequivalenceJ (piComplete_hom h x y)⟩

end Axioms

end TwoEnvelope

end StringDiagrams

end
