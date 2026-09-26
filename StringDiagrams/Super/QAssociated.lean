import StringDiagrams.Super.Orbit
import StringDiagrams.Super.QPiCategory
import StringDiagrams.Super.Associated

/-!
# The graded (Q, Π)-supercategory associated to a (Q, Π)-category

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §6, the
construction `𝔻` in the proof of Theorem 6.13.

For a `(Q, Π)`-category `A`, the paper's associated graded `(Q, Π)`-supercategory `Â` has the
objects of `A` and `Hom_Â(λ, μ)_{m,a} := Hom_A(λ, Q^m Π^a μ)`, with composition using
`β_{Qⁿ}`, `ξ` and the coherence isomorphisms `c_{m,n} : QᵐQⁿ ≅ Qᵐ⁺ⁿ`. We build it in two steps:

1. the associated Π-supercategory `Associated R A` of (5.2) (Lemma 5.1), with the sign
   correction of `StringDiagrams.Super.Associated`; `Q` induces a superfunctor `Q̂` of it
   (`Associated.map` of the Π-functor `(Q, β_Q)`), which is full, faithful and evenly dense;
2. the orbit supercategory `Orbit` of `Q̂` (`StringDiagrams.Super.Orbit`), in which a morphism of
   degree `m` is a family `(f_{i,j} : Q̂ⁱ λ → Q̂ʲ μ)_{i-j=m}` compatible with `Q̂`, determined by
   `f_{0,-m} : λ → Q̂⁻ᵐ μ`.

Thus `QAssociated R A := Orbit (QAssociated.shiftData R A)`, a graded `(Q, Π)`-supercategory.

## A convention correction

With the degree conventions of Definition 6.4 (`σ : Q ⇒ I` has degree `-1`, as for the grading
shift `(QV)ₙ = Vₙ₋₁`), the morphisms `λ → μ` of degree `m` must correspond to
`Hom_A(λ, Q⁻ᵐ Π^a μ)`, not to `Hom_A(λ, Q^m Π^a μ)` as printed: the isomorphism
`σ_λ : Qλ → λ` of the associated supercategory comes from `1_{Qλ} ∈ Hom_A(Qλ, Q¹ λ)`, which
must have degree `-1`. (With the printed convention there is no degree `-1` isomorphism
`Qλ → λ` in general.) Our orbit supercategory uses the corrected convention.

## Main definitions and statements

* `QAssociated.shiftData`, `QAssociated R A` (the object part of `𝔻`), a graded
  `(Q, Π)`-supercategory (instances from `StringDiagrams.Super.Orbit`).
* `QAssociated.unit`, `QAssociated.counit`: mutually inverse functors between `A` and the
  underlying category of `QAssociated R A` (`unit_comp_counit`, `counit_comp_unit`), which
  commute strictly with `Π`, `Q` and `ξ`; `QAssociated.unitQPiFunctor` is the resulting
  `(Q, Π)`-functor with `β = 1` and `γ = 1` (`𝔼 ∘ 𝔻 = I` on objects).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory GradedSupercategory

universe w w₁ w₂ w₃ w₄

namespace QAssociated

variable (R : Type w) [CommRing R] (A : Type w₁) [Category.{w₂} A] [Preadditive A] [Linear R A]
  [QPiCategory R A]

open Associated

/-- The superfunctor `Q̂` of the associated Π-supercategory. -/
abbrev Qhat : Associated R A ⥤ Associated R A :=
  Associated.map (QPiCategory.Q_pi (R := R) (C := A))

instance : (QPiCategory.Q (R := R) (C := A)).Full :=
  inferInstanceAs (QPiCategory.qEquivalence R A).functor.Full

instance : (QPiCategory.Q (R := R) (C := A)).Faithful :=
  inferInstanceAs (QPiCategory.qEquivalence R A).functor.Faithful

instance : (Qhat R A).Faithful where
  map_injective {X Y f g} h := by
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [Associated.map_map, homMk_fst, homMk_snd] at h1 h2
    exact hom_ext ((QPiCategory.Q (R := R)).map_injective h1)
      ((QPiCategory.Q (R := R)).map_injective ((cancel_mono _).1 h2))

instance : (Qhat R A).Full where
  map_surjective {X Y} f :=
    ⟨homMk ((QPiCategory.Q (R := R)).preimage f.1)
      ((QPiCategory.Q (R := R)).preimage
        (f.2 ≫ (QPiCategory.Q_pi (R := R) (C := A)).β.hom.app Y.obj)), by
      apply hom_ext
      · simp
      · simp⟩

/-- `Q̂` is evenly dense: `jj_λ : Q Q⁻¹ λ ≅ λ` is even. -/
theorem Qhat_evenlyDense : EvenlyDense R (Qhat R A) := fun Y =>
  ⟨⟨(QPiCategory.Qinv (R := R)).obj Y.obj⟩,
    (Underlying.ι R (Associated R A)).mapIso ((Associated.unit R A).mapIso
      ((QPiCategory.jj (R := R) (C := A)).app Y.obj)),
    ((Associated.unit R A).map ((QPiCategory.jj (R := R) (C := A)).hom.app Y.obj)).2⟩

/-- The superequivalence `Q̂`. -/
def Qhat_superequivalence : Superequivalence R (Qhat R A) :=
  Superequivalence.ofFullyFaithful (Qhat R A) (Qhat_evenlyDense R A)

omit [Preadditive A] [Linear R A] [QPiCategory R A] in
theorem equivalence_mk_unit_app {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (G : D ⥤ C)
    (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D) (X : C) :
    (CategoryTheory.Equivalence.mk F G η ε).unitIso.hom.app X =
      η.hom.app X ≫ G.map (ε.inv.app (F.obj X)) ≫ G.map (F.map (η.inv.app X)) := by
  simp [CategoryTheory.Equivalence.mk, CategoryTheory.Equivalence.adjointifyη]

/-- The shift data of the associated Π-supercategory: the adjoint equivalence obtained from
the superequivalence `Q̂`. -/
def shiftData : ShiftData R (Associated R A) where
  e := CategoryTheory.Equivalence.mk (Qhat R A) (Qhat_superequivalence R A).inverse
    (Qhat_superequivalence R A).unitIso (Qhat_superequivalence R A).counitIso
  functor_additive := inferInstanceAs (Qhat R A).Additive
  functor_linear := inferInstanceAs ((Qhat R A).Linear R)
  functor_isSuperfunctor := inferInstanceAs (IsSuperfunctor R (Qhat R A))
  inverse_additive := inferInstanceAs (Qhat_superequivalence R A).inverse.Additive
  inverse_linear := inferInstanceAs ((Qhat_superequivalence R A).inverse.Linear R)
  inverse_isSuperfunctor := inferInstanceAs (IsSuperfunctor R (Qhat_superequivalence R A).inverse)
  unit_mem X := by
    rw [equivalence_mk_unit_app]
    have h1 := (Qhat_superequivalence R A).unitIso_mem X
    have h2 := inv_mem _ ((Qhat_superequivalence R A).counitIso_mem ((Qhat R A).obj X))
    have h3 := inv_mem _ ((Qhat_superequivalence R A).unitIso_mem X)
    have := comp_mem h1 (comp_mem (map_mem (Qhat_superequivalence R A).inverse h2)
      (map_mem (Qhat_superequivalence R A).inverse (map_mem (Qhat R A) h3)))
    simpa using this
  counit_mem X := Superequivalence.counitIso_mem (Qhat_superequivalence R A) X

end QAssociated

/-- **The graded `(Q, Π)`-supercategory associated to a `(Q, Π)`-category** (the object part of
the 2-functor `𝔻` in the proof of Theorem 6.13): the orbit supercategory of `Q̂` on the
associated Π-supercategory. -/
abbrev QAssociated (R : Type w) [CommRing R] (A : Type w₁) [Category.{w₂} A] [Preadditive A]
    [Linear R A] [QPiCategory R A] :=
  Orbit (QAssociated.shiftData R A)

namespace QAssociated

variable {R : Type w} [CommRing R] {A : Type w₁} [Category.{w₂} A] [Preadditive A] [Linear R A]
  [QPiCategory R A]

open Associated Orbit

example : QPiSupercategory R (QAssociated R A) := inferInstance

variable (R A) in
/-- The identification of `A` with the underlying category of `QAssociated R A`
(`𝔼 ∘ 𝔻 = I` on objects): `f ↦ ι(f, 0)`. -/
def unit : A ⥤ GUnderlying R (QAssociated R A) :=
  Associated.unit R A ⋙ Underlying.map (R := R) (ιZ (shiftData R A))

variable (R A) in
/-- The inverse identification: a morphism of degree zero is determined by its entry `(0, 0)`,
whose even part is a morphism of `A`. -/
def counit : GUnderlying R (QAssociated R A) ⥤ A :=
  Underlying.map (R := R) (π₀ (shiftData R A)) ⋙ Associated.counit R A

@[simp] theorem unit_obj (X : A) : (unit R A).obj X = ⟨⟨⟨⟨X⟩⟩⟩⟩ := rfl

theorem unit_map_val {X Y : A} (f : X ⟶ Y) :
    ((unit R A).map f).1.1 = (ι (shiftData R A)).map (homMk (X := ⟨X⟩) (Y := ⟨Y⟩) f 0) := rfl

theorem unit_comp_counit : unit R A ⋙ counit R A = 𝟭 A :=
  CategoryTheory.Functor.ext (fun _ => rfl) fun X Y f => by
    simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map, eqToHom_refl,
      Category.comp_id, Category.id_comp]
    show ((π₀ (shiftData R A)).map ((ιZ (shiftData R A)).map (homMk (X := ⟨X⟩) (Y := ⟨Y⟩) f 0))).1 = f
    rw [ιZ_comp_π₀_map]; rfl

theorem counit_comp_unit : counit R A ⋙ unit R A = 𝟭 _ :=
  CategoryTheory.Functor.ext (fun _ => rfl) fun X Y x => by
    simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map, eqToHom_refl,
      Category.comp_id, Category.id_comp]
    apply Underlying.hom_ext
    show (ιZ (shiftData R A)).map (homMk ((π₀ (shiftData R A)).map x.1).1 0) = x.1
    have h0 : ((π₀ (shiftData R A)).map x.1).2 = 0 :=
      Associated.mem_parity_zero.1 (map_mem (π₀ (shiftData R A)) x.2)
    rw [show homMk ((π₀ (shiftData R A)).map x.1).1 0 = (π₀ (shiftData R A)).map x.1 from
      hom_ext rfl h0.symm, π₀_comp_ιZ_map]

theorem unit_map_pi {X Y : A} (f : X ⟶ Y) :
    (PiCategory.pi (R := R)).map ((unit R A).map f) = (unit R A).map ((PiCategory.pi (R := R)).map f) := by
  apply Underlying.hom_ext; apply DegreeZero.hom_ext
  show (PiSupercategory.pi (R := R)).map ((ι (shiftData R A)).map (homMk f 0)) =
    (ι (shiftData R A)).map (homMk ((PiCategory.pi (R := R)).map f) 0)
  rw [pi_map_ι]
  congr 1
  exact congrArg Subtype.val (Associated.unit_map_pi (R := R) (C := A) f)

theorem unit_map_Q {X Y : A} (f : X ⟶ Y) :
    (QPiCategory.Q (R := R)).map ((unit R A).map f) = (unit R A).map ((QPiCategory.Q (R := R)).map f) := by
  apply Underlying.hom_ext; apply DegreeZero.hom_ext
  show (QPiSupercategory.Q (R := R)).map ((ι (shiftData R A)).map (homMk f 0)) =
    (ι (shiftData R A)).map (homMk ((QPiCategory.Q (R := R)).map f) 0)
  rw [Q_map_ι]
  congr 1
  refine hom_ext rfl ?_
  show ((Qhat R A).map (homMk f 0)).2 = 0
  simp

theorem ξ_unit (X : A) :
    (PiCategory.ξApp (R := R) ((unit R A).obj X)).hom = (unit R A).map (PiCategory.ξApp (R := R) X).hom := by
  apply Underlying.hom_ext
  rw [Underlying.ξApp_hom_val]
  apply DegreeZero.hom_ext
  rw [DegreeZero.ξ_hom_val]
  exact (ξ_hom_eq (d := shiftData R A) (⟨X⟩ : Associated R A)).trans
    (congrArg (ι (shiftData R A)).map (Associated.ξ_hom (R := R) (C := A) ⟨X⟩))

variable (R A) in
/-- **`𝔼 ∘ 𝔻 = I`**: the identification `unit` is a `(Q, Π)`-functor with `β = 1` and
`γ = 1`. -/
def unitQPiFunctor : QPiFunctor R (unit R A) where
  β := NatIso.ofComponents (fun X => Iso.refl _) fun f => by
    simp only [Functor.comp_obj, Functor.comp_map, Iso.refl_hom, Category.comp_id,
      Category.id_comp]
    exact unit_map_pi f
  comm X := by
    simp only [NatIso.ofComponents_hom_app, Iso.refl_hom, CategoryTheory.Functor.map_id,
      Category.id_comp]
    have h := ξ_unit (R := R) (A := A) X
    rw [PiCategory.ξApp_hom, PiCategory.ξApp_hom] at h
    rw [h, ← Functor.map_comp, Iso.hom_inv_id_app]
    exact (unit R A).map_id _
  γ := NatIso.ofComponents (fun X => Iso.refl _) fun f => by
    simp only [Functor.comp_obj, Functor.comp_map, Iso.refl_hom, Category.comp_id,
      Category.id_comp]
    exact unit_map_Q f

@[simp] theorem unitQPiFunctor_β_hom_app (X : A) :
    (unitQPiFunctor R A).β.hom.app X = 𝟙 _ := rfl

@[simp] theorem unitQPiFunctor_γ_hom_app (X : A) :
    (unitQPiFunctor R A).γ.hom.app X = 𝟙 _ := rfl

end QAssociated

/-! ## `𝔻 ∘ 𝔼 ≅ I`: the isomorphism `T_B : (B̲)^ ≅ B` -/

namespace QAssociated

section T

variable {R : Type w} [CommRing R] {B : Type w₁} [Category.{w₂} B] [Preadditive B] [Linear R B]
  [Supercategory R B] [GradedSupercategory R B] [QPiSupercategory R B]

open ShiftData Orbit QPiSupercategory

variable (R B) in
/-- The shift data of the associated Π-supercategory of the underlying `(Q, Π)`-category. -/
abbrev dB : ShiftData R (Associated R (GUnderlying R B)) := shiftData R (GUnderlying R B)

variable (R B) in
/-- `T_{B̲} : (B̲)^ ⥤ B̲` of Lemma 5.1 followed by the inclusion into `B`. -/
abbrev TbF : Associated R (GUnderlying R B) ⥤ B :=
  Associated.T R (DegreeZero R B) ⋙ DegreeZero.ι R B

theorem TbF_map_mem_degree {X Y : Associated R (GUnderlying R B)} (f : X ⟶ Y) :
    (TbF R B).map f ∈ degree (R := R) ((TbF R B).obj X) ((TbF R B).obj Y) 0 :=
  ((Associated.T R (DegreeZero R B)).map f).2

theorem TbF_map_injective {X Y : Associated R (GUnderlying R B)} {f g : X ⟶ Y}
    (h : (TbF R B).map f = (TbF R B).map g) : f = g :=
  Associated.T_map_injective (DegreeZero.hom_ext h)

/-- `T` intertwines `Q̂` and `Q` (Lemma 5.1, naturality of `T`). -/
theorem TbF_map_Qhat {X Y : Associated R (GUnderlying R B)} (f : X ⟶ Y) :
    (TbF R B).map ((Qhat R (GUnderlying R B)).map f) =
      (QPiSupercategory.Q (R := R)).map ((TbF R B).map f) := by
  have h := CategoryTheory.Functor.congr_hom (Associated.T_naturality (R := R)
    (A := DegreeZero R B) (B := DegreeZero R B) (DegreeZero.map (R := R)
      (QPiSupercategory.Q (R := R) (C := B)))) f
  simp only [Functor.comp_map, eqToHom_refl, Category.comp_id, Category.id_comp] at h
  exact congrArg Subtype.val h

/-- The object of `B` underlying an object of the associated Π-supercategory. -/
abbrev bobj (X : Associated R (GUnderlying R B)) : B := (TbF R B).obj X

variable (R B) in
/-- `τ_n : Qⁿ X ≅ X` in `B` for the powers of `Q̂`, `n ∈ ℕ`: iterated `σ`. -/
def τNat : ∀ (n : ℕ) (X : Associated R (GUnderlying R B)), bobj (((dB R B).powNat n).obj X) ≅ bobj X
  | 0, _ => Iso.refl _
  | n + 1, X => σ (R := R) (bobj (((dB R B).powNat n).obj X)) ≪≫ τNat n X

variable (R B) in
/-- `τ_{-n-1} : Q⁻ⁿ⁻¹ X ≅ X` in `B`: `σ⁻¹` followed by the counit. -/
def τNeg : ∀ (n : ℕ) (X : Associated R (GUnderlying R B)), bobj (((dB R B).powNeg (n + 1)).obj X) ≅ bobj X
  | 0, X => (σ (R := R) (bobj ((dB R B).Qi.obj X))).symm ≪≫ (TbF R B).mapIso ((dB R B).e.counitIso.app X)
  | n + 1, X => (σ (R := R) (bobj ((dB R B).Qi.obj (((dB R B).powNeg (n + 1)).obj X)))).symm ≪≫
      (TbF R B).mapIso ((dB R B).e.counitIso.app (((dB R B).powNeg (n + 1)).obj X)) ≪≫ τNeg n X

variable (R B) in
/-- `τ_i : Qⁱ X ≅ X` in `B`, even of degree `-i`. -/
def τ : ∀ (i : ℤ) (X : Associated R (GUnderlying R B)), bobj (((dB R B).pow i).obj X) ≅ bobj X
  | Int.ofNat n, X => τNat R B n X
  | Int.negSucc n, X => τNeg R B n X

theorem τ_zero (X : Associated R (GUnderlying R B)) : τ R B 0 X = Iso.refl _ := rfl

/-- The recursion of `τ`: `τ_{i+1} = τ_i ∘ σ ∘ T(Q Qⁱ ≅ Qⁱ⁺¹)⁻¹`. -/
theorem τ_succ (i : ℤ) (X : Associated R (GUnderlying R B)) :
    (τ R B (i + 1) X).hom = (TbF R B).map (((dB R B).succ i).inv.app X) ≫
      (σ (R := R) (bobj (((dB R B).pow i).obj X))).hom ≫ (τ R B i X).hom := by
  rcases i with n | (_ | n)
  · show (τNat R B (n + 1) X).hom = (TbF R B).map (𝟙 _) ≫ _ ≫ _
    rw [CategoryTheory.Functor.map_id, Category.id_comp]; rfl
  · show 𝟙 _ = (TbF R B).map ((dB R B).e.counitIso.inv.app X) ≫ _ ≫
      ((σ (R := R) (bobj ((dB R B).Qi.obj X))).inv ≫ (TbF R B).map ((dB R B).e.counitIso.hom.app X))
    erw [Iso.hom_inv_id_assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
    exact ((TbF R B).map_id _).symm
  · show (τ R B (Int.negSucc n) X).hom = (TbF R B).map (((dB R B).succ (Int.negSucc (n + 1))).inv.app X) ≫
      _ ≫ ((σ (R := R) _).inv ≫ (TbF R B).map ((dB R B).e.counitIso.hom.app _) ≫ (τNeg R B n X).hom)
    rw [succ_negSucc_succ_inv_app]
    erw [Iso.hom_inv_id_assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
    rcases n with _ | n <;> rfl

theorem τNat_hom_mem (n : ℕ) (X : Associated R (GUnderlying R B)) :
    (τNat R B n X).hom ∈ parity (R := R) _ _ 0 ∧ (τNat R B n X).hom ∈ degree (R := R) _ _ (-n) := by
  induction n with
  | zero => exact ⟨id_mem _, id_mem_degree _⟩
  | succ n ih =>
    refine ⟨by simpa using comp_mem (σ_hom_mem (R := R) _) ih.1, ?_⟩
    have := comp_mem_degree (σ_hom_mem_degree (R := R) _) ih.2
    rwa [show (-1 + -(n : ℤ)) = -((n + 1 : ℕ) : ℤ) by push_cast; ring] at this

theorem τNeg_hom_mem (n : ℕ) (X : Associated R (GUnderlying R B)) :
    (τNeg R B n X).hom ∈ parity (R := R) _ _ 0 ∧
      (τNeg R B n X).hom ∈ degree (R := R) _ _ ((n : ℤ) + 1) := by
  induction n with
  | zero =>
    show (σ (R := R) _).inv ≫ (TbF R B).map ((dB R B).e.counitIso.hom.app X) ∈ _ ∧
      (σ (R := R) _).inv ≫ (TbF R B).map ((dB R B).e.counitIso.hom.app X) ∈ _
    refine ⟨?_, ?_⟩
    · have := comp_mem (σ_inv_mem (R := R) (bobj ((dB R B).Qi.obj X)))
        (map_mem (TbF R B) ((dB R B).counit_mem X))
      simpa using this
    · have := comp_mem_degree (σ_inv_mem_degree (R := R) (bobj ((dB R B).Qi.obj X)))
        (TbF_map_mem_degree (R := R) (B := B) ((dB R B).e.counitIso.hom.app X))
      simpa using this
  | succ n ih =>
    show (σ (R := R) _).inv ≫ (TbF R B).map ((dB R B).e.counitIso.hom.app _) ≫ (τNeg R B n X).hom ∈ _ ∧
      (σ (R := R) _).inv ≫ (TbF R B).map ((dB R B).e.counitIso.hom.app _) ≫ (τNeg R B n X).hom ∈ _
    refine ⟨?_, ?_⟩
    · have := comp_mem (σ_inv_mem (R := R) (bobj ((dB R B).Qi.obj (((dB R B).powNeg (n + 1)).obj X))))
        (comp_mem (map_mem (TbF R B) ((dB R B).counit_mem (((dB R B).powNeg (n + 1)).obj X))) ih.1)
      simpa using this
    · have := comp_mem_degree
        (σ_inv_mem_degree (R := R) (bobj ((dB R B).Qi.obj (((dB R B).powNeg (n + 1)).obj X))))
        (comp_mem_degree (TbF_map_mem_degree (R := R) (B := B)
          ((dB R B).e.counitIso.hom.app (((dB R B).powNeg (n + 1)).obj X))) ih.2)
      rwa [show (1 + (0 + ((n : ℤ) + 1))) = ((n + 1 : ℕ) : ℤ) + 1 by push_cast; ring] at this

/-- `τ_i` is even of degree `-i`. -/
theorem τ_hom_mem (i : ℤ) (X : Associated R (GUnderlying R B)) :
    (τ R B i X).hom ∈ parity (R := R) _ _ 0 ∧ (τ R B i X).hom ∈ degree (R := R) _ _ (-i) := by
  rcases i with n | n
  · exact τNat_hom_mem n X
  · refine ⟨(τNeg_hom_mem n X).1, ?_⟩
    have := (τNeg_hom_mem n X).2
    rwa [show ((n : ℤ) + 1) = -Int.negSucc n by rw [Int.neg_negSucc]; push_cast; ring] at this

theorem τ_inv_mem (i : ℤ) (X : Associated R (GUnderlying R B)) :
    (τ R B i X).inv ∈ parity (R := R) _ _ 0 ∧ (τ R B i X).inv ∈ degree (R := R) _ _ i := by
  refine ⟨inv_mem _ (τ_hom_mem i X).1, ?_⟩
  simpa using inv_mem_degree _ (τ_hom_mem i X).2

theorem τ_succ_inv (i : ℤ) (X : Associated R (GUnderlying R B)) :
    (τ R B (i + 1) X).inv = (τ R B i X).inv ≫ (σ (R := R) (bobj (((dB R B).pow i).obj X))).inv ≫
      (TbF R B).map (((dB R B).succ i).hom.app X) := by
  rw [← cancel_epi (τ R B (i + 1) X).hom, Iso.hom_inv_id, τ_succ]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp, Iso.inv_hom_id_app]
  exact ((TbF R B).map_id _).symm

variable {X Y : Associated R (GUnderlying R B)}

/-- The morphism `τ_j ∘ T(f_{i,j}) ∘ τ_i⁻¹ : X → Y` of `B` given by an entry of a family. -/
def val (f : (dB R B).FamAll X Y) (i j : ℤ) : bobj X ⟶ bobj Y :=
  (τ R B i X).inv ≫ (TbF R B).map (f i j) ≫ (τ R B j Y).hom

/-- All entries of a compatible family give the same morphism of `B`. -/
theorem val_succ {m : ℤ} {f : (dB R B).FamAll X Y} (hf : f ∈ (dB R B).Fam R m X Y) (i j : ℤ) :
    val f (i + 1) (j + 1) = val f i j := by
  rw [val, val, τ_succ_inv, τ_succ, Fam.compat hf]
  simp only [Category.assoc, Functor.map_comp]
  rw [← Functor.map_comp_assoc (TbF R B) (((dB R B).succ i).hom.app X), Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← Functor.map_comp_assoc (TbF R B) (((dB R B).succ j).hom.app Y), Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  erw [TbF_map_Qhat]
  rw [QPiSupercategory.Q_map_eq]
  simp

theorem val_eq {m : ℤ} {f : (dB R B).FamAll X Y} (hf : f ∈ (dB R B).Fam R m X Y) {i j : ℤ}
    (h : i - j = m) : val f i j = val f 0 (-m) := by
  have key : ∀ k : ℤ, val f (0 + k) (-m + k) = val f 0 (-m) := by
    intro k
    induction k using Int.induction_on with
    | hz => simp
    | hp k ih => rw [← ih, ← add_assoc, ← add_assoc, val_succ hf]
    | hn k ih =>
      rw [← ih, show (0 : ℤ) + -(k : ℤ) = 0 + (-(k : ℤ) - 1) + 1 by ring,
        show -m + -(k : ℤ) = -m + (-(k : ℤ) - 1) + 1 by ring, val_succ hf]
  rw [← key i, show 0 + i = i by ring, show -m + i = j by omega]

theorem val_zero {m : ℤ} (f : (dB R B).FamAll X Y) :
    val f 0 (-m) = (TbF R B).map (f 0 (-m)) ≫ (τ R B (-m) Y).hom := by
  rw [val, τ_zero]; simp

theorem val_famComp (m : ℤ) {Z : Associated R (GUnderlying R B)} (f : (dB R B).FamAll X Y)
    (g : (dB R B).FamAll Y Z) (i k : ℤ) :
    val ((dB R B).famComp m f g) i k = val f i (i - m) ≫ val g (i - m) k := by
  rw [val, val, val, famComp, Functor.map_comp]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

end T

end QAssociated

end StringDiagrams

end
