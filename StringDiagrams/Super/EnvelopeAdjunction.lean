import StringDiagrams.Super.Envelope
import StringDiagrams.Super.FunctorCategory

/-!
# Theorem 4.3 as a superequivalence of Hom-supercategories

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Theorem 4.3, i.e. the first half of Theorem 1.9.

For a supercategory `A` and a Π-supercategory `B`, the extension of Lemma 4.2 is a superfunctor
between the supercategories of superfunctors of Example 1.2(iv)
(`Supercategory.Superfunctor`, with supernatural transformations as morphisms),

  `ℋom(A, νB) → ℋom(A_π, B)`, `F ↦ F̃`, `x ↦ x̃`

(`Envelope.extendHom`), where on a supernatural transformation `x = x₀ + x₁` the extension is
formula (4.2) applied to each homogeneous component. It is full, faithful and evenly dense, so
it is a superequivalence (`Envelope.extendHomSuperequivalence`). This is Theorem 4.3, and the
first statement of Theorem 1.9 ("the functor (1) is left 2-adjoint to the forgetful functor
`ν` in the sense that there is a superequivalence `ℋom(A, νB) → ℋom(A_π, B)`").

The strict 2-superfunctor `-_π` and the 2-adjunction language of Theorem 4.3 are not packaged
beyond this superequivalence.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory

universe w w₁ w₂ w₃ w₄

namespace Envelope

variable {R : Type w} [CommRing R]
  {A : Type w₁} [Category.{w₂} A] [Preadditive A] [Linear R A] [Supercategory R A]
  {B : Type w₃} [Category.{w₄} B] [Preadditive B] [Linear R B] [Supercategory R B]
  [PiSupercategory R B]

/-- A supernatural transformation from homogeneous supernatural families of each parity. -/
def superNatTransOf {C D : Type*} [Category C] [Preadditive C] [Linear R C] [Supercategory R C]
    [Category D] [Preadditive D] [Linear R D] [Supercategory R D] {F G : C ⥤ D}
    (x : ZMod 2 → ∀ X, F.obj X ⟶ G.obj X) (hx : ∀ p, IsSupernatural R p (x p)) : SuperNatTrans R F G where
  app := x
  app_mem p := (hx p).mem
  naturality q _ _ _ _ hf := by rw [(hx q).naturality hf, koszulSign_smul (R := R)]

/-- The extension `x̃ = x̃₀ + x̃₁` of a supernatural transformation `x : F ⇒ G`, given by (4.2)
on each homogeneous component. -/
def extendSuperNatTrans {F G : Superfunctor R A B} (x : F ⟶ G) :
    (⟨extend R F.toFunctor⟩ : Superfunctor R (Envelope R A) B) ⟶ ⟨extend R G.toFunctor⟩ :=
  superNatTransOf (fun p => extendNat R F.toFunctor G.toFunctor p (x.app p))
    (fun p => isSupernatural_extendNat (x.isSupernatural p))

@[simp] theorem extendSuperNatTrans_app {F G : Superfunctor R A B} (x : F ⟶ G) (p : ZMod 2)
    (X : Envelope R A) :
    (extendSuperNatTrans x).app p X = extendNat R F.toFunctor G.toFunctor p (x.app p) X := rfl

variable (R A B) in
/-- **Theorem 4.3 / Theorem 1.9.** The superfunctor `ℋom(A, νB) → ℋom(A_π, B)`,
`F ↦ F̃`, `x ↦ x̃`. -/
@[simps]
def extendHom : Superfunctor R A B ⥤ Superfunctor R (Envelope R A) B where
  obj F := ⟨extend R F.toFunctor⟩
  map x := extendSuperNatTrans x
  map_id F := Superfunctor.hom_ext fun p X => by
    refine congrFun (eq_of_restrict_eq (R := R) (p := p)
      (isSupernatural_extendNat (SuperNatTrans.isSupernatural (𝟙 F : F ⟶ F) p))
      (SuperNatTrans.isSupernatural
        (𝟙 (⟨extend R F.toFunctor⟩ : Superfunctor R (Envelope R A) B)) p)
      fun Y => ?_) X
    rw [extendNat_zero_par]
    rcases parity_eq_zero_or_one p with rfl | rfl <;> rfl
  map_comp {F G H} x y := Superfunctor.hom_ext fun p X => by
    refine congrFun (eq_of_restrict_eq (R := R) (p := p)
      (isSupernatural_extendNat (SuperNatTrans.isSupernatural (x ≫ y) p))
      (SuperNatTrans.isSupernatural (extendSuperNatTrans x ≫ extendSuperNatTrans y) p)
      fun Y => ?_) X
    rw [extendNat_zero_par, Superfunctor.comp_app, Superfunctor.comp_app]
    simp only [extendSuperNatTrans_app, extendNat_zero_par]

instance : (extendHom R A B).Additive where
  map_add {F G x y} := Superfunctor.hom_ext fun p X => by
    show extendNat R F.toFunctor G.toFunctor p (x.app p + y.app p) X = _
    rw [extendNat_add]
    rfl

instance : (extendHom R A B).Linear R where
  map_smul {F G} x r := Superfunctor.hom_ext fun p X => by
    simp only [extendHom_map, extendSuperNatTrans_app, Superfunctor.smul_app]
    exact congrFun (extendNat_smul r (x.app p)) X

instance : IsSuperfunctor R (extendHom R A B) where
  map_mem {F G p x} hx := by
    rw [Superfunctor.mem_parity_iff] at hx ⊢
    funext X
    simp only [extendHom_map, extendSuperNatTrans_app, hx]
    simp [extendNat]

instance : (extendHom R A B).Faithful where
  map_injective {F G x y} h := Superfunctor.hom_ext fun p X => by
    have := congrArg (fun t : (extendHom R A B).obj F ⟶ (extendHom R A B).obj G =>
      t.app p ((J R A).obj X)) h
    simpa using this

/-- The restriction `y J : F ⇒ G` of a supernatural transformation `y : F̃ ⇒ G̃`. -/
def restrictSuperNatTrans {F G : Superfunctor R A B}
    (y : (extendHom R A B).obj F ⟶ (extendHom R A B).obj G) : F ⟶ G :=
  superNatTransOf (fun p X => y.app p ((J R A).obj X)) fun p =>
    { mem := fun X => y.app_mem p ((J R A).obj X)
      naturality := fun {X Y q f} hf => by
        have := (SuperNatTrans.isSupernatural y p).naturality (map_mem (J R A) hf)
        simpa using this }

instance : (extendHom R A B).Full where
  map_surjective {F G} y := ⟨restrictSuperNatTrans y, Superfunctor.hom_ext fun p X =>
    congrFun (eq_of_restrict_eq (R := R) (p := p)
      (isSupernatural_extendNat (SuperNatTrans.isSupernatural (restrictSuperNatTrans y) p))
      (SuperNatTrans.isSupernatural y p) fun Y => by
        rw [extendNat_zero_par]; rfl) X⟩

/-- The even isomorphism `(H J)~ ≅ H` of Theorem 4.3, in the supercategory `ℋom(A_π, B)`. -/
def extendRestrictSuperIso (H : Superfunctor R (Envelope R A) B) :
    (extendHom R A B).obj ⟨J R A ⋙ H.toFunctor⟩ ≅ H where
  hom := SuperNatTrans.ofNatTrans (extendRestrictIso H.toFunctor).hom
    (extendRestrictIso_hom_mem H.toFunctor)
  inv := SuperNatTrans.ofNatTrans (extendRestrictIso H.toFunctor).inv
    (fun X => inv_mem ((extendRestrictIso H.toFunctor).app X)
      (extendRestrictIso_hom_mem H.toFunctor X))
  hom_inv_id := Superfunctor.hom_ext_parity (fun X => by
      simp [SuperNatTrans.ofNatTrans]; rfl)
    (fun X => by simp [SuperNatTrans.ofNatTrans])
  inv_hom_id := Superfunctor.hom_ext_parity (fun X => by
      simp [SuperNatTrans.ofNatTrans])
    (fun X => by simp [SuperNatTrans.ofNatTrans])

theorem extendHom_evenlyDense : EvenlyDense R (extendHom R A B) := fun H =>
  ⟨⟨J R A ⋙ H.toFunctor⟩, extendRestrictSuperIso H, by
    rw [Superfunctor.mem_parity_iff]
    rfl⟩

variable (R A B) in
/-- **Theorem 4.3 (the first half of Theorem 1.9).** For a supercategory `A` and a
Π-supercategory `B`, `F ↦ F̃`, `x ↦ x̃` is a superequivalence
`ℋom(A, νB) → ℋom(A_π, B)`. -/
def extendHomSuperequivalence : Superequivalence R (extendHom R A B) :=
  Superequivalence.ofFullyFaithful _ extendHom_evenlyDense

end Envelope

end StringDiagrams

end
