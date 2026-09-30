import StringDiagrams.Super.QEnvelope
import StringDiagrams.Super.EnvelopeAdjunction
import StringDiagrams.Super.GSCatMonoidal

/-!
# Theorem 6.9 as a graded superequivalence, and the 1-categorical shadow of `-_{q,π} ⊣ ν`

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §6,
Theorem 6.9: for a graded supercategory `A` and a graded `(Q, Π)`-supercategory `B`, the
extension `F ↦ F̃`, `x ↦ x̃` is a graded superequivalence

  `ℋom(A, νB) → ℋom(A_{q,π}, B)`

of graded supercategories of graded superfunctors and graded supernatural transformations
(`GradedHom`, the last example after Definition 6.1), "hence the functor `-_{q,π}` is left
2-adjoint to the forgetful functor `ν`".

## Main definitions and statements

* `QPiEnvelope.extendHom R A B : GradedHom R A B ⥤ GradedHom R (QPiEnvelope R A) B`, the
  superfunctor `F ↦ F̃`, `x ↦ x̃` (on a graded supernatural transformation `x`, the extension of
  `QPiEnvelope.extendNat` applied to each parity component), a graded superfunctor.
* **Theorem 6.9.** `QPiEnvelope.extendHomGradedSuperequivalence`: `extendHom R A B` is full,
  faithful and evenly dense in degree zero, hence a graded superequivalence.
* `QPiGSCat.instCategory`: the category of graded `(Q, Π)`-supercategories and graded
  superfunctors (the underlying category of `(Q, Π)-𝔊𝔖ℭ𝔞𝔱`); `QPiGSCat.forget R` is the
  forgetful functor `ν` to `GSCat R`, and `QPiGSCat.envelope R : GSCat R ⥤ QPiGSCat R` is the
  functor `A ↦ A_{q,π}`, `F ↦ F_{q,π}` (`QPiEnvelope.map`), strictly functorial.
* `QPiGSCat.not_exists_adjunction_unit_J`: **the strict universal property fails.** For every
  nonempty graded supercategory `A` there is no adjunction `-_{q,π} ⊣ ν` of 1-categories whose
  unit at `A` is `J : A → A_{q,π}`. Indeed restriction along `J` is not injective on graded
  superfunctors out of `A_{q,π}` (`QPiEnvelope.exists_ne_of_J_comp_eq`): the graded superfunctor
  `J : A_{q,π} → (A_{q,π})_{q,π}` and the extension of its restriction `(J ∘ J)~` agree after
  restriction along `J` but differ on the object `Π λ`.

## Literal versus formalized

The paper's "left 2-adjoint" is a statement about 2-categories; at the level of the underlying
1-categories the universal property of `J` holds only up to isomorphism (a graded superfunctor
`H : A_{q,π} → B` is isomorphic to `(H J)~`, not equal to it, since the morphisms of
`(Q, Π)-GSCat` need not commute with `Q` and `Π`). So there is no strict 1-adjunction with unit
`J`, and the precise content formalized here is the printed Theorem 6.9: the graded
superequivalence of Hom-categories `ℋom(A, νB) ≃ ℋom(A_{q,π}, B)`. Its naturality in `A` and
`B` (the "functorial" of Theorem 6.9) is in `StringDiagrams.Super.QEnvelopeNaturality`.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory GradedSupercategory

universe w w₁ w₂ w₃ w₄

/-! ## Supernaturality of the extension along the `Q`-envelope -/

namespace QEnvelope

variable {R : Type w} [CommRing R] {C : Type w₁} [Category.{w₂} C] [Preadditive C] [Linear R C]
  [Supercategory R C]
  {B : Type w₃} [Category.{w₄} B] [Preadditive B] [Linear R B] [Supercategory R B]
  [GradedSupercategory R B] [QPiSupercategory R B]
  {F G : C ⥤ B}

open QPiSupercategory

set_option backward.isDefEq.respectTransparency false in
/-- The extension along the `Q`-envelope of a supernatural transformation homogeneous of parity
`p` is supernatural of parity `p` (no grading assumption on `x`). -/
theorem isSupernatural_extendNat [G.Linear R] {p : ZMod 2} {x : ∀ X, F.obj X ⟶ G.obj X}
    (hx : IsSupernatural R p x) :
    IsSupernatural R p (F := extend R F) (G := extend R G) (extendNat R F G x) where
  mem X := by
    have := comp_mem (comp_mem (σPow_hom_mem (R := R) X.shift (F.obj X.obj)) (hx.mem X.obj))
      (σPow_inv_mem (R := R) X.shift (G.obj X.obj))
    simpa [extendNat] using! this
  naturality {X Y q f} hf := by
    simp only [extend_map, extendNat, Category.assoc, Iso.inv_hom_id_assoc]
    rw [reassoc_of% (hx.naturality (f := toHom f) hf), Linear.smul_comp, Linear.comp_smul]
    simp only [Category.assoc]

omit [Preadditive C] [Linear R C] [Supercategory R C] in
set_option backward.isDefEq.respectTransparency false in
theorem extendNat_add (x y : ∀ X, F.obj X ⟶ G.obj X) :
    extendNat R F G (x + y) = extendNat R F G x + extendNat R F G y := by
  funext X
  simp only [extendNat, Pi.add_apply, Preadditive.add_comp, Preadditive.comp_add]

omit [Preadditive C] [Linear R C] [Supercategory R C] in
set_option backward.isDefEq.respectTransparency false in
theorem extendNat_smul (r : R) (x : ∀ X, F.obj X ⟶ G.obj X) :
    extendNat R F G (r • x) = r • extendNat R F G x := by
  funext X
  simp only [extendNat, Pi.smul_apply, Linear.smul_comp, Linear.comp_smul]

omit [Preadditive C] [Linear R C] [Supercategory R C] in
set_option backward.isDefEq.respectTransparency false in
theorem extendNat_zero : extendNat R F G (0 : ∀ X, F.obj X ⟶ G.obj X) = 0 := by
  funext X
  simp only [extendNat, Pi.zero_apply, Limits.zero_comp, Limits.comp_zero]

end QEnvelope

namespace QPiEnvelope

variable {R : Type w} [CommRing R]
  {A : Type w₁} [Category.{w₂} A] [Preadditive A] [Linear R A] [Supercategory R A]
  [GradedSupercategory R A]
  {B : Type w₃} [Category.{w₄} B] [Preadditive B] [Linear R B] [Supercategory R B]
  [GradedSupercategory R B] [QPiSupercategory R B]

/-! ## The extension on supernatural transformations -/

section Nat

variable {F G : A ⥤ B} [F.Additive] [F.Linear R] [IsGradedSuperfunctor R F]
  [G.Additive] [G.Linear R] [IsGradedSuperfunctor R G]

omit [GradedSupercategory R A] [F.Additive] [F.Linear R] [IsGradedSuperfunctor R F] [G.Additive]
  [IsGradedSuperfunctor R G] in
/-- The extension of a supernatural transformation homogeneous of parity `p` is supernatural of
parity `p`. -/
theorem isSupernatural_extendNat {p : ZMod 2} {x : ∀ X, F.obj X ⟶ G.obj X}
    (hx : IsSupernatural R p x) :
    IsSupernatural R p (F := extend R F) (G := extend R G) (extendNat R F G p x) :=
  Envelope.isSupernatural_extendNat (QEnvelope.isSupernatural_extendNat hx)

omit [Preadditive A] [Linear R A] [Supercategory R A] [GradedSupercategory R A] [F.Additive]
  [F.Linear R] [IsGradedSuperfunctor R F] [G.Additive] [G.Linear R] [IsGradedSuperfunctor R G] in
theorem extendNat_add (p : ZMod 2) (x y : ∀ X, F.obj X ⟶ G.obj X) :
    extendNat R F G p (x + y) = extendNat R F G p x + extendNat R F G p y := by
  simp only [extendNat, QEnvelope.extendNat_add, Envelope.extendNat_add]

omit [Preadditive A] [Linear R A] [Supercategory R A] [GradedSupercategory R A] [F.Additive]
  [F.Linear R] [IsGradedSuperfunctor R F] [G.Additive] [G.Linear R] [IsGradedSuperfunctor R G] in
theorem extendNat_smul (p : ZMod 2) (r : R) (x : ∀ X, F.obj X ⟶ G.obj X) :
    extendNat R F G p (r • x) = r • extendNat R F G p x := by
  simp only [extendNat, QEnvelope.extendNat_smul, Envelope.extendNat_smul]

omit [Preadditive A] [Linear R A] [Supercategory R A] [GradedSupercategory R A] [F.Additive]
  [F.Linear R] [IsGradedSuperfunctor R F] [G.Additive] [G.Linear R] [IsGradedSuperfunctor R G] in
theorem extendNat_zero (p : ZMod 2) :
    extendNat R F G p (0 : ∀ X, F.obj X ⟶ G.obj X) = 0 := by
  funext X
  simp only [extendNat, QEnvelope.extendNat_zero, Envelope.extendNat, Pi.zero_apply,
    Limits.zero_comp, Limits.comp_zero, smul_zero]
  rfl

omit [Preadditive A] [Linear R A] [Supercategory R A] [F.Additive] [F.Linear R]
  [IsGradedSuperfunctor R F] [GradedSupercategory R A] in
set_option backward.isDefEq.respectTransparency false in
/-- `F̃ (J f) = F f`. -/
theorem extend_map_J_map {X Y : A} (f : X ⟶ Y) :
    (extend R F).map ((J R A).map f) = F.map f := by
  change (Envelope.extend R (QEnvelope.extend R F)).map
    ((Envelope.J R (QEnvelope R A)).map ((QEnvelope.J R A).map f)) = F.map f
  rw [Envelope.extend_map_J_map]
  change (QPiSupercategory.σPow R 0 (F.obj X)).hom ≫ F.map f ≫
    (QPiSupercategory.σPow R 0 (F.obj Y)).inv = F.map f
  simp

end Nat

/-! ## The superfunctor `ℋom(A, νB) → ℋom(A_{q,π}, B)` -/

open GradedSuperfunctor

variable (R) in
/-- The extension `F̃ : A_{q,π} → B` of a graded superfunctor, bundled. -/
abbrev extendGS (F : GradedSuperfunctor R A B) : GradedSuperfunctor R (QPiEnvelope R A) B :=
  ⟨⟨extend R F.toFunctor⟩⟩

/-- The extension `x̃ = x̃₀ + x̃₁` of a supernatural transformation `x : F ⇒ G` between graded
superfunctors, given on each parity component by `QPiEnvelope.extendNat`. -/
def extendSuperNatTrans {F G : GradedSuperfunctor R A B}
    (x : F.toSuperfunctor ⟶ G.toSuperfunctor) :
    (extendGS R F).toSuperfunctor ⟶ (extendGS R G).toSuperfunctor :=
  Envelope.superNatTransOf (fun p => extendNat R F.toFunctor G.toFunctor p (x.app p))
    (fun p => isSupernatural_extendNat (x.isSupernatural p))

@[simp] theorem extendSuperNatTrans_app {F G : GradedSuperfunctor R A B}
    (x : F.toSuperfunctor ⟶ G.toSuperfunctor) (p : ZMod 2) (X : QPiEnvelope R A) :
    (extendSuperNatTrans x).app p X = extendNat R F.toFunctor G.toFunctor p (x.app p) X := rfl

theorem extendSuperNatTrans_add {F G : GradedSuperfunctor R A B}
    (x y : F.toSuperfunctor ⟶ G.toSuperfunctor) :
    extendSuperNatTrans (x + y) = extendSuperNatTrans x + extendSuperNatTrans y :=
  Superfunctor.hom_ext fun p X => congrFun (extendNat_add p (x.app p) (y.app p)) X

theorem extendSuperNatTrans_smul {F G : GradedSuperfunctor R A B} (r : R)
    (x : F.toSuperfunctor ⟶ G.toSuperfunctor) :
    extendSuperNatTrans (r • x) = r • extendSuperNatTrans x :=
  Superfunctor.hom_ext fun p X => congrFun (extendNat_smul p r (x.app p)) X

theorem extendSuperNatTrans_zero {F G : GradedSuperfunctor R A B} :
    extendSuperNatTrans (0 : F.toSuperfunctor ⟶ G.toSuperfunctor) = 0 :=
  Superfunctor.hom_ext fun p X => congrFun (extendNat_zero p) X

/-- The extension preserves supernatural transformations homogeneous of degree `n`. -/
theorem extendSuperNatTrans_mem_degNat {F G : GradedSuperfunctor R A B} {n : ℤ}
    {x : F.toSuperfunctor ⟶ G.toSuperfunctor} (hx : x ∈ degNat F G n) :
    extendSuperNatTrans x ∈ degNat (extendGS R F) (extendGS R G) n := fun p X =>
  (isGradedSupernatural_extendNat (F := F.toFunctor) (G := G.toFunctor)
    ⟨x.isSupernatural p, hx p⟩).mem_degree X

set_option backward.isDefEq.respectTransparency false in
theorem extendSuperNatTrans_mem_hom {F G : GradedSuperfunctor R A B}
    {x : F.toSuperfunctor ⟶ G.toSuperfunctor} (hx : x ∈ (family R A B).hom F G) :
    extendSuperNatTrans x ∈ (family R (QPiEnvelope R A) B).hom (extendGS R F) (extendGS R G) := by
  refine (family R A B).hom_induction hx
    (fun n y hy => (family R _ B).mem_hom_of_mem (extendSuperNatTrans_mem_degNat hy)) ?_ ?_
  · rw [extendSuperNatTrans_zero]; exact Submodule.zero_mem _
  · intro y z hy hz
    rw [extendSuperNatTrans_add]; exact Submodule.add_mem _ hy hz

theorem extendSuperNatTrans_id (F : GradedSuperfunctor R A B) :
    extendSuperNatTrans (𝟙 F.toSuperfunctor) = 𝟙 (extendGS R F).toSuperfunctor :=
  Superfunctor.hom_ext fun p X => by
    refine congrFun (eq_of_restrict_eq (R := R) (p := p)
      (isSupernatural_extendNat (SuperNatTrans.isSupernatural (𝟙 F.toSuperfunctor) p))
      (SuperNatTrans.isSupernatural (𝟙 (extendGS R F).toSuperfunctor) p) fun Y => ?_) X
    rw [J_obj, extendNat_J]
    rcases parity_eq_zero_or_one p with rfl | rfl <;> rfl

theorem extendSuperNatTrans_comp {F G H : GradedSuperfunctor R A B}
    (x : F.toSuperfunctor ⟶ G.toSuperfunctor) (y : G.toSuperfunctor ⟶ H.toSuperfunctor) :
    extendSuperNatTrans (x ≫ y) = extendSuperNatTrans x ≫ extendSuperNatTrans y :=
  Superfunctor.hom_ext fun p X => by
    refine congrFun (eq_of_restrict_eq (R := R) (p := p)
      (isSupernatural_extendNat (SuperNatTrans.isSupernatural (x ≫ y) p))
      (SuperNatTrans.isSupernatural (extendSuperNatTrans x ≫ extendSuperNatTrans y) p)
      fun Y => ?_) X
    rw [J_obj, extendNat_J, Superfunctor.comp_app, Superfunctor.comp_app]
    simp only [extendSuperNatTrans_app, extendNat_J]
    rfl

variable (R A B) in
/-- **Theorem 6.9.** The superfunctor `ℋom(A, νB) → ℋom(A_{q,π}, B)`, `F ↦ F̃`, `x ↦ x̃`. -/
def extendHom : GradedHom R A B ⥤ GradedHom R (QPiEnvelope R A) B where
  obj F := ⟨extendGS R F.as⟩
  map x := ⟨extendSuperNatTrans x.1, extendSuperNatTrans_mem_hom x.2⟩
  map_id F := GradedSubcategory.hom_ext (extendSuperNatTrans_id F.as)
  map_comp x y := GradedSubcategory.hom_ext (extendSuperNatTrans_comp x.1 y.1)

@[simp] theorem extendHom_obj (F : GradedHom R A B) :
    (extendHom R A B).obj F = ⟨extendGS R F.as⟩ := rfl

@[simp] theorem extendHom_map_val {F G : GradedHom R A B} (x : F ⟶ G) :
    ((extendHom R A B).map x).1 = extendSuperNatTrans x.1 := rfl

instance : (extendHom R A B).Additive where
  map_add {_ _ x y} := GradedSubcategory.hom_ext (extendSuperNatTrans_add x.1 y.1)

instance : (extendHom R A B).Linear R where
  map_smul {_ _} x r := GradedSubcategory.hom_ext (extendSuperNatTrans_smul r x.1)

set_option backward.isDefEq.respectTransparency false in
instance : IsGradedSuperfunctor R (extendHom R A B) where
  map_mem {F G p x} hx := by
    rw [GradedSubcategory.mem_parity_iff, Superfunctor.mem_parity_iff] at hx ⊢
    show extendNat R F.as.toFunctor G.as.toFunctor (p + 1) (x.1.app (p + 1)) = 0
    rw [hx]
    exact extendNat_zero (p + 1)
  map_mem_degree {_ _ _ x} hx := extendSuperNatTrans_mem_degNat (x := x.1) hx

set_option backward.isDefEq.respectTransparency false in
instance : (extendHom R A B).Faithful where
  map_injective {F G x y} h := GradedSubcategory.hom_ext <| Superfunctor.hom_ext fun p X => by
    have key : ∀ z : F ⟶ G, ((extendHom R A B).map z).1.app p (mk 0 0 X) = z.1.app p X :=
      fun z => extendNat_J p _ X
    rw [← key x, ← key y, h]

/-! ### Fullness -/

set_option backward.isDefEq.respectTransparency false in
/-- The restriction `y J : F ⇒ G` of a supernatural transformation `y : F̃ ⇒ G̃`. -/
def restrictSuperNatTrans {F G : GradedSuperfunctor R A B}
    (y : (extendGS R F).toSuperfunctor ⟶ (extendGS R G).toSuperfunctor) :
    F.toSuperfunctor ⟶ G.toSuperfunctor :=
  Envelope.superNatTransOf (fun p X => y.app p ((J R A).obj X)) fun p =>
    { mem := fun X => y.app_mem p ((J R A).obj X)
      naturality := fun {X Y q f} hf => by
        have := (SuperNatTrans.isSupernatural y p).naturality (map_mem (J R A) hf)
        have e1 : (extendGS R F).toFunctor.map ((J R A).map f) = F.toFunctor.map f :=
          extend_map_J_map (R := R) (F := F.toFunctor) f
        have e2 : (extendGS R G).toFunctor.map ((J R A).map f) = G.toFunctor.map f :=
          extend_map_J_map (R := R) (F := G.toFunctor) f
        rw [e1, e2] at this
        exact this }

@[simp] theorem restrictSuperNatTrans_app {F G : GradedSuperfunctor R A B}
    (y : (extendGS R F).toSuperfunctor ⟶ (extendGS R G).toSuperfunctor) (p : ZMod 2) (X : A) :
    (restrictSuperNatTrans y).app p X = y.app p ((J R A).obj X) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem restrictSuperNatTrans_mem_hom {F G : GradedSuperfunctor R A B}
    {y : (extendGS R F).toSuperfunctor ⟶ (extendGS R G).toSuperfunctor}
    (hy : y ∈ (family R (QPiEnvelope R A) B).hom (extendGS R F) (extendGS R G)) :
    restrictSuperNatTrans y ∈ (family R A B).hom F G := by
  refine (family R (QPiEnvelope R A) B).hom_induction hy
    (fun n z hz => (family R A B).mem_hom_of_mem (n := n) fun p X => hz p ((J R A).obj X)) ?_ ?_
  · rw [show restrictSuperNatTrans (0 : (extendGS R F).toSuperfunctor ⟶
      (extendGS R G).toSuperfunctor) = 0 from Superfunctor.hom_ext fun _ _ => rfl]
    exact Submodule.zero_mem _
  · intro z z' hz hz'
    rw [show restrictSuperNatTrans (z + z') = restrictSuperNatTrans z + restrictSuperNatTrans z'
      from Superfunctor.hom_ext fun _ _ => rfl]
    exact Submodule.add_mem _ hz hz'

theorem extendSuperNatTrans_restrictSuperNatTrans {F G : GradedSuperfunctor R A B}
    (y : (extendGS R F).toSuperfunctor ⟶ (extendGS R G).toSuperfunctor) :
    extendSuperNatTrans (restrictSuperNatTrans y) = y :=
  Superfunctor.hom_ext fun p X => congrFun (eq_of_restrict_eq (R := R) (p := p)
    (isSupernatural_extendNat (SuperNatTrans.isSupernatural (restrictSuperNatTrans y) p))
    (SuperNatTrans.isSupernatural y p) fun Y => by
      rw [J_obj, extendNat_J]; rfl) X

instance : (extendHom R A B).Full where
  map_surjective {_ _} y := ⟨⟨restrictSuperNatTrans y.1, restrictSuperNatTrans_mem_hom y.2⟩,
    GradedSubcategory.hom_ext (extendSuperNatTrans_restrictSuperNatTrans y.1)⟩

/-! ### Even density in degree zero -/

variable (R A) in
/-- The canonical graded superfunctor `J : A → A_{q,π}`, bundled. -/
abbrev JGS : GradedSuperfunctor R A (QPiEnvelope R A) := ⟨⟨J R A⟩⟩

theorem isGradedSupernatural_extendRestrictIso_hom (H : QPiEnvelope R A ⥤ B) [H.Additive]
    [H.Linear R] [IsGradedSuperfunctor R H] :
    IsGradedSupernatural R 0 0 fun X => ((extendRestrictIso H).app X).hom :=
  ⟨isSupernatural_of_natTrans (extendRestrictIso H).hom (extendRestrictIso_hom_mem H),
    extendRestrictIso_hom_mem_degree H⟩

theorem isGradedSupernatural_extendRestrictIso_inv (H : QPiEnvelope R A ⥤ B) [H.Additive]
    [H.Linear R] [IsGradedSuperfunctor R H] :
    IsGradedSupernatural R 0 (-0) fun X => ((extendRestrictIso H).app X).inv :=
  ⟨isSupernatural_of_natTrans (extendRestrictIso H).inv
      (fun X => inv_mem ((extendRestrictIso H).app X) (extendRestrictIso_hom_mem H X)),
    fun X => inv_mem_degree ((extendRestrictIso H).app X) (extendRestrictIso_hom_mem_degree H X)⟩

/-- The even isomorphism `(H J)~ ≅ H` of degree zero of Theorem 6.9, in `ℋom(A_{q,π}, B)`. -/
def extendRestrictGradedIso (H : GradedHom R (QPiEnvelope R A) B) :
    (extendHom R A B).obj ⟨(JGS R A).comp H.as⟩ ≅ H :=
  GradedHom.isoOfHomogeneous (x := fun X => (extendRestrictIso H.as.toFunctor).app X)
    (isGradedSupernatural_extendRestrictIso_hom H.as.toFunctor)
    (isGradedSupernatural_extendRestrictIso_inv H.as.toFunctor)

theorem extendHom_gradedEvenlyDense : GradedEvenlyDense R (extendHom R A B) := fun H =>
  ⟨⟨(JGS R A).comp H.as⟩, extendRestrictGradedIso H,
    GradedHom.ofHomogeneous_mem (isGradedSupernatural_extendRestrictIso_hom H.as.toFunctor),
    GradedHom.ofHomogeneous_mem_degree
      (isGradedSupernatural_extendRestrictIso_hom H.as.toFunctor)⟩

variable (R A B) in
/-- **Theorem 6.9.** For a graded supercategory `A` and a graded `(Q, Π)`-supercategory `B`,
`F ↦ F̃`, `x ↦ x̃` is a graded superequivalence `ℋom(A, νB) → ℋom(A_{q,π}, B)`. -/
def extendHomGradedSuperequivalence : GradedSuperequivalence R (extendHom R A B) :=
  GradedSuperequivalence.ofFullyFaithful _ extendHom_gradedEvenlyDense

/-! ## Failure of the strict universal property -/

omit [QPiSupercategory R B] in
/-- Restriction along `J` is not injective on graded superfunctors out of `A_{q,π}`: for every
object `λ` of `A`, the graded superfunctor `J : A_{q,π} → (A_{q,π})_{q,π}` and the extension
`(J ∘ J)~` of its restriction agree after restriction along `J` but differ on `Π λ`. So the
universal property of `J` does not hold on the nose. -/
theorem exists_ne_of_J_comp_eq (X : A) :
    ∃ H H' : QPiEnvelope R A ⥤ QPiEnvelope R (QPiEnvelope R A),
      J R A ⋙ H = J R A ⋙ H' ∧ H ≠ H' := by
  refine ⟨J R (QPiEnvelope R A), extend R (J R A ⋙ J R (QPiEnvelope R A)),
    (J_comp_extend R _).symm, fun h => ?_⟩
  have := congrArg (fun K : QPiEnvelope R A ⥤ QPiEnvelope R (QPiEnvelope R A) =>
    (K.obj (mk 0 1 X)).par) h
  change (0 : ZMod 2) = 0 + 1 at this
  exact absurd this (by decide)

end QPiEnvelope

/-! ## The category `(Q, Π)-GSCat` and the functors `-_{q,π}` and `ν` -/

/-- Graded superfunctors with the same underlying functor are equal. -/
theorem GradedSuperfunctor.ext_toFunctor {R : Type w} [CommRing R] {C : Type w₁} [Category.{w₂} C]
    [Preadditive C] [Linear R C] [Supercategory R C] [GradedSupercategory R C] {D : Type w₃}
    [Category.{w₄} D] [Preadditive D] [Linear R D] [Supercategory R D] [GradedSupercategory R D]
    {F G : GradedSuperfunctor R C D} (h : F.toFunctor = G.toFunctor) : F = G := by
  obtain ⟨⟨F, _, _, _⟩, _⟩ := F
  obtain ⟨⟨G, _, _, _⟩, _⟩ := G
  change F = G at h
  subst h
  rfl

namespace QPiGSCat

variable {R : Type w} [CommRing R]

universe v u

/-- The category of graded `(Q, Π)`-supercategories and graded superfunctors: the underlying
category of the strict graded 2-supercategory `(Q, Π)-𝔊𝔖ℭ𝔞𝔱`. -/
instance instCategory : Category (QPiGSCat.{w, v, u} R) where
  toCategoryStruct := (inferInstance : BicategoryStruct (QPiGSCat.{w, v, u} R)).toCategoryStruct
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

variable (R) in
/-- The forgetful functor `ν : (Q, Π)-GSCat → GSCat`. -/
@[simps]
def forget : QPiGSCat.{w, v, u} R ⥤ GSCat.{w, v, u} R where
  obj A := A.toGSCat
  map F := F

variable (R) in
/-- The functor `-_{q,π} : GSCat → (Q, Π)-GSCat`, `A ↦ A_{q,π}` (Definition 6.8),
`F ↦ F_{q,π}` (`QPiEnvelope.map`). -/
@[simps]
def envelope : GSCat.{w, v, u} R ⥤ QPiGSCat.{w, v, u} R where
  obj A := QPiGSCat.of R (QPiEnvelope R A)
  map F := ⟨⟨⟨QPiEnvelope.map R F.as.toFunctor⟩⟩⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The canonical graded superfunctor `J : A → ν(A_{q,π})`, as a morphism of `GSCat`. -/
def unitJ (A : GSCat.{w, v, u} R) : A ⟶ (forget R).obj ((envelope R).obj A) :=
  ⟨QPiEnvelope.JGS R A⟩

/-- `J` is natural: `J ∘ F = F_{q,π} ∘ J` (`QPiEnvelope.J_comp_map`). -/
theorem unitJ_naturality {A A' : GSCat.{w, v, u} R} (F : A ⟶ A') :
    F ≫ unitJ A' = unitJ A ≫ (forget R).map ((envelope R).map F) := rfl

/-- **The strict form of `-_{q,π} ⊣ ν` fails.** For a nonempty graded supercategory `A`, there is
no adjunction `-_{q,π} ⊣ ν` of 1-categories whose unit at `A` is `J : A → A_{q,π}`: the
associated bijection `Hom(A_{q,π}, B) ≃ Hom(A, νB)` would be restriction along `J`, which is
not injective for `B = (A_{q,π})_{q,π}` (`QPiEnvelope.exists_ne_of_J_comp_eq`). The correct
statement is Theorem 6.9, the graded superequivalence
`QPiEnvelope.extendHomGradedSuperequivalence`. -/
theorem not_exists_adjunction_unit_J (A : GSCat.{w, v, u} R) [Nonempty A] :
    ¬ ∃ adj : envelope R ⊣ forget R, adj.unit.app A = unitJ A := by
  rintro ⟨adj, h⟩
  obtain ⟨X⟩ := ‹Nonempty A›
  let B := (envelope R).obj ((forget R).obj ((envelope R).obj A))
  let H : (envelope R).obj A ⟶ B := ⟨QPiEnvelope.JGS R (QPiEnvelope R A)⟩
  let H' : (envelope R).obj A ⟶ B :=
    ⟨QPiEnvelope.extendGS R ((QPiEnvelope.JGS R A).comp (QPiEnvelope.JGS R (QPiEnvelope R A)))⟩
  have e : adj.homEquiv _ _ H = adj.homEquiv _ _ H' := by
    rw [adj.homEquiv_unit, adj.homEquiv_unit, h]
    change (⟨(QPiEnvelope.JGS R A).comp (QPiEnvelope.JGS R (QPiEnvelope R A))⟩ :
        GradedHom R A (QPiEnvelope R (QPiEnvelope R A))) =
      ⟨(QPiEnvelope.JGS R A).comp (QPiEnvelope.extendGS R
        ((QPiEnvelope.JGS R A).comp (QPiEnvelope.JGS R (QPiEnvelope R A))))⟩
    congr 1
    exact GradedSuperfunctor.ext_toFunctor (QPiEnvelope.J_comp_extend R _).symm
  have e' := congrArg (fun K : (envelope R).obj A ⟶ B =>
    Envelope.par (K.as.toFunctor.obj (QPiEnvelope.mk 0 1 X))) ((adj.homEquiv _ _).injective e)
  change (0 : ZMod 2) = 0 + 1 at e'
  exact absurd e' (by decide)

end QPiGSCat

end StringDiagrams

end
