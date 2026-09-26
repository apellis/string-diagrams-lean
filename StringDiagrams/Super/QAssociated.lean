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

## A missing axiom in Definition 6.12(ii)

The construction of `𝔻` on 1-morphisms needs the isomorphism `γ_F : Q'F ≅ FQ` of a
`(Q, Π)`-functor to be compatible with `β`:
`γ_F Π ∘ Q' β_F ∘ β_{Q'} F = F β_Q ∘ β_F Q ∘ Π' γ_F` in `Hom(Π'Q'F, FQΠ)`, i.e. `γ_F` must be a
Π-natural transformation between the Π-functors `Q'F` and `FQ`
(`QPiFunctor.IsCompatible`). Otherwise `F̂` does not commute with the odd morphisms, which
involve `β_{Qⁿ}`. This condition is not among the axioms of Definition 6.12(ii), but it holds
for all `(Q, Π)`-functors in the image of `𝔼` (`GradedSupercategory.GUnderlying.qpiFunctor_isCompatible`,
from `QPiSupercategory.β_γ_compat`) and it is invariant under `(Q, Π)`-natural isomorphism. So
with Definition 6.12(ii) as printed, `𝔼` is not essentially surjective on 1-morphisms as soon
as some `(Q, Π)`-category admits a natural automorphism `α` of `Q` with `αΠ ∘ β_Q ≠ β_Q ∘ Πα`
(then `(I, β = 1, γ = α)` is a `(Q, Π)`-functor which is not compatible). Theorem 6.13 holds
after adding the compatibility to Definition 6.12(ii); we formalize `𝔻` on compatible
`(Q, Π)`-functors.

## Main definitions and statements

* `QAssociated.shiftData`, `QAssociated R A` (the object part of `𝔻`), a graded
  `(Q, Π)`-supercategory (instances from `StringDiagrams.Super.Orbit`).
* `QAssociated.unit`, `QAssociated.counit`: mutually inverse functors between `A` and the
  underlying category of `QAssociated R A` (`unit_comp_counit`, `counit_comp_unit`), which
  commute strictly with `Π`, `Q` and `ξ`; `QAssociated.unitQPiFunctor` is the resulting
  `(Q, Π)`-functor with `β = 1` and `γ = 1` (`𝔼 ∘ 𝔻 = I` on objects).
* `QAssociated.map hF hc` (`𝔻` on a compatible `(Q, Π)`-functor): a graded superfunctor,
  with `unit ⋙ 𝔼(𝔻 F) = F ⋙ unit` (`unit_comp_map`, `𝔼 ∘ 𝔻 = I` on 1-morphisms).
* `QAssociated.T` (`𝔻 ∘ 𝔼 ≅ I`): for a graded `(Q, Π)`-supercategory `B`, the graded
  superfunctor `T_B : 𝔻(𝔼 B) ⥤ B`, an isomorphism of categories with inverse `Tinv`
  (`T_comp_Tinv`, `Tinv_comp_T`) which preserves `Π`, `Q` on objects and carries `ζ` to `ζ`
  and `σ` to `σ` (`T_map_ζ`, `T_map_σ`), natural in `B`: `𝔻(𝔼 F) ⋙ T_{B'} = T_B ⋙ F`
  (`T_naturality`).
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

/-! ## `𝔻` on compatible `(Q, Π)`-functors -/

section Map

variable {A' : Type w₃} [Category.{w₄} A'] [Preadditive A'] [Linear R A'] [QPiCategory R A']

theorem compat_inv {F : A ⥤ A'} [F.Additive] (hF : QPiFunctor R F) (hc : hF.IsCompatible R)
    (Y : A) :
    (QPiCategory.Q (R := R)).map (hF.β.inv.app Y) ≫
        (QPiCategory.Q_pi (R := R) (C := A')).β.inv.app (F.obj Y) ≫
          (PiCategory.pi (R := R)).map (hF.γ.hom.app Y) =
      hF.γ.hom.app ((PiCategory.pi (R := R)).obj Y) ≫
        F.map ((QPiCategory.Q_pi (R := R) (C := A)).β.inv.app Y) ≫
          hF.β.inv.app ((QPiCategory.Q (R := R)).obj Y) := by
  have h := (QPiFunctor.IsCompatible.iff hF).1 hc Y
  rw [← cancel_epi ((QPiCategory.Q_pi (R := R) (C := A')).β.hom.app (F.obj Y) ≫
    (QPiCategory.Q (R := R)).map (hF.β.hom.app Y))]
  simp only [Category.assoc]
  rw [reassoc_of% h]
  simp only [Functor.comp_obj, ← Functor.map_comp_assoc, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc]
  simp

/-- The even isomorphism `γ̂_F : Q̂' F̂ ≅ F̂ Q̂` of the associated Π-supercategories, for a
compatible `(Q, Π)`-functor. -/
def γhat {F : A ⥤ A'} [F.Additive] (hF : QPiFunctor R F) (hc : hF.IsCompatible R) :
    Associated.map hF.toPiFunctor ⋙ Qhat R A' ≅ Qhat R A ⋙ Associated.map hF.toPiFunctor :=
  NatIso.ofComponents (fun X =>
    { hom := homMk (X := ⟨(QPiCategory.Q (R := R)).obj (F.obj X.obj)⟩)
        (Y := ⟨F.obj ((QPiCategory.Q (R := R)).obj X.obj)⟩) (hF.γ.hom.app X.obj) 0
      inv := homMk (X := ⟨F.obj ((QPiCategory.Q (R := R)).obj X.obj)⟩)
        (Y := ⟨(QPiCategory.Q (R := R)).obj (F.obj X.obj)⟩) (hF.γ.inv.app X.obj) 0
      hom_inv_id := hom_ext (by simp) (by simp)
      inv_hom_id := hom_ext (by simp) (by simp) })
    (fun {_ Y} f => by
      apply hom_ext
      · simp only [Functor.comp_obj, Functor.comp_map, Associated.map_map, comp_fst, homMk_fst,
          homMk_snd, Limits.comp_zero, Limits.zero_comp, sub_zero, Functor.map_zero]
        exact hF.γ.hom.naturality f.1
      · simp only [Functor.comp_obj, Functor.comp_map, Associated.map_map, comp_snd, homMk_fst,
          homMk_snd, Limits.comp_zero, zero_add, add_zero, Functor.map_comp, Category.assoc]
        have n := hF.γ.hom.naturality f.2
        simp only [Functor.comp_obj, Functor.comp_map] at n
        rw [Limits.zero_comp, add_zero]
        erw [compat_inv hF hc Y.obj]
        rw [reassoc_of% n]
        rfl)

variable (R) in
/-- The morphism of shift data induced by a compatible `(Q, Π)`-functor. -/
def shiftFunctor {F : A ⥤ A'} [F.Additive] [F.Linear R] (hF : QPiFunctor R F)
    (hc : hF.IsCompatible R) : ShiftFunctor R (shiftData R A) (shiftData R A') where
  F := Associated.map hF.toPiFunctor
  γ := γhat hF hc
  γ_mem _ := Associated.mem_parity_zero.2 rfl

/-- **`𝔻` on 1-morphisms.** The graded superfunctor `F̂ : Â → Â'` induced by a compatible
`(Q, Π)`-functor. -/
abbrev map {F : A ⥤ A'} [F.Additive] [F.Linear R] (hF : QPiFunctor R F) (hc : hF.IsCompatible R) :
    QAssociated R A ⥤ QAssociated R A' :=
  Orbit.map (shiftFunctor R hF hc)

example {F : A ⥤ A'} [F.Additive] [F.Linear R] (hF : QPiFunctor R F) (hc : hF.IsCompatible R) :
    IsGradedSuperfunctor R (map hF hc) := inferInstance

/-- **`𝔼 ∘ 𝔻 = I` on 1-morphisms**: under the identifications `unit`, `𝔼(𝔻 F) = F`. -/
theorem unit_comp_map {F : A ⥤ A'} [F.Additive] [F.Linear R] (hF : QPiFunctor R F)
    (hc : hF.IsCompatible R) : unit R A ⋙ GUnderlying.map R (map hF hc) = F ⋙ unit R A' :=
  CategoryTheory.Functor.ext (fun _ => rfl) fun X Y f => by
    simp only [Functor.comp_map, eqToHom_refl, Category.comp_id, Category.id_comp]
    apply Underlying.hom_ext; apply DegreeZero.hom_ext
    show (Orbit.map (shiftFunctor R hF hc)).map ((ι (shiftData R A)).map (homMk f 0)) =
      (ι (shiftData R A')).map (homMk (F.map f) 0)
    have := CategoryTheory.Functor.congr_hom (Orbit.ι_comp_map (shiftFunctor R hF hc))
      (homMk (X := ⟨X⟩) (Y := ⟨Y⟩) f 0)
    simp only [Functor.comp_map, eqToHom_refl, Category.comp_id, Category.id_comp] at this
    rw [this]
    congr 1
    exact hom_ext rfl (by simp [shiftFunctor])

end Map

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

theorem TbF_map_dQ {X Y : Associated R (GUnderlying R B)} (f : X ⟶ Y) :
    (TbF R B).map ((shiftData R (GUnderlying R B)).Q.map f) =
      (QPiSupercategory.Q (R := R)).map ((TbF R B).map f) :=
  TbF_map_Qhat f

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

variable (R B) in
/-- `T` on families of degree `m`: `f ↦ τ_{-m} ∘ T(f_{0,-m})`. -/
def Tfam (m : ℤ) (X Y : Associated R (GUnderlying R B)) :
    (dB R B).Fam R m X Y →ₗ[R] (bobj X ⟶ bobj Y) where
  toFun f := val f.1 0 (-m)
  map_add' f g := by
    simp only [val, Submodule.coe_add, FamAll.add_apply, Functor.map_add, Preadditive.add_comp,
      Preadditive.comp_add]
  map_smul' r f := by
    simp only [val, Submodule.coe_smul, FamAll.smul_apply, Functor.map_smul, Linear.smul_comp,
      Linear.comp_smul, RingHom.id_apply]

variable (R B) in
/-- `T` on morphisms, as a linear map. -/
def TL (X Y : Associated R (GUnderlying R B)) : (dB R B).Hom X Y →ₗ[R] (bobj X ⟶ bobj Y) :=
  DirectSum.toModule R ℤ (bobj X ⟶ bobj Y) fun m => Tfam R B m X Y

theorem TL_lof {m : ℤ} (f : (dB R B).Fam R m X Y) :
    TL R B X Y ((dB R B).lof m X Y f) = val f.1 0 (-m) := by
  rw [TL, ShiftData.lof]
  erw [DirectSum.toModule_lof]
  rfl

variable (R B) in
/-- **`𝔻 ∘ 𝔼 ≅ I`.** The graded superfunctor `T_B : (B̲)^ ⥤ B`: a family of degree `m` goes to
`τ_{-m} ∘ T(f_{0,-m})`, where `T` is the functor of Lemma 5.1 and `τ_{-m} : Q⁻ᵐ μ ≅ μ` is built
from `σ`. -/
def T : QAssociated R (GUnderlying R B) ⥤ B where
  obj X := bobj X.obj
  map {X Y} x := TL R B X.obj Y.obj x
  map_id X := by
    show TL R B _ _ ((dB R B).lof 0 _ _ _) = _
    rw [TL_lof]
    show val ((dB R B).idFam X.obj) 0 (-0) = 𝟙 _
    rw [neg_zero, val, (dB R B).idFam_self, τ_zero]
    simp
  map_comp {X Y Z} x y := by
    show TL R B _ _ ((dB R B).compL _ _ _ x y) = TL R B _ _ x ≫ TL R B _ _ y
    induction x using Hom.induction_on with
    | zero => simp
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx', Preadditive.add_comp]
    | lof m f =>
      induction y using Hom.induction_on with
      | zero => simp
      | add y y' hy hy' => simp only [map_add, hy, hy', Preadditive.comp_add]
      | lof n g =>
        rw [compL_lof_lof, TL_lof, TL_lof, TL_lof, famCompₗ_apply, val_famComp,
          val_eq g.2 (show 0 - m - -(m + n) = n by ring), zero_sub]

theorem T_map_lof {X Y : QAssociated R (GUnderlying R B)} {m : ℤ} (f : (dB R B).Fam R m X.obj Y.obj) :
    (T R B).map ((dB R B).lof m X.obj Y.obj f : X ⟶ Y) = val f.1 0 (-m) :=
  TL_lof f

instance : (T R B).Additive where
  map_add {X Y x y} := LinearMap.map_add (TL R B X.obj Y.obj) x y

instance : (T R B).Linear R where
  map_smul {X Y} x r := LinearMap.map_smul (TL R B X.obj Y.obj) r x

theorem val_mem {p : ZMod 2} {f : (dB R B).FamAll X Y} (i j : ℤ)
    (hf : f i j ∈ parity (R := R) _ _ p) : val f i j ∈ parity (R := R) _ _ p := by
  have := comp_mem (comp_mem (τ_inv_mem i X).1 (map_mem (TbF R B) hf)) (τ_hom_mem j Y).1
  rw [zero_add, add_zero, Category.assoc] at this
  exact this

theorem val_mem_degree {f : (dB R B).FamAll X Y} (i j : ℤ) :
    val f i j ∈ degree (R := R) (bobj X) (bobj Y) (i - j) := by
  have := comp_mem_degree (comp_mem_degree (τ_inv_mem i X).2 (TbF_map_mem_degree (f i j)))
    (τ_hom_mem j Y).2
  rw [show i + 0 + -j = i - j by ring, Category.assoc] at this
  exact this

instance : IsGradedSuperfunctor R (T R B) where
  map_mem {X Y p x} hx := by
    rw [← (dB R B).projHom_of_mem hx]
    clear hx
    induction x using Hom.induction_on with
    | zero => simp only [map_zero]; exact Submodule.zero_mem _
    | add x x' hx hx' =>
      rw [map_add, Functor.map_add]; exact Submodule.add_mem _ hx hx'
    | lof m f =>
      rw [projHom_lof, T_map_lof]
      exact val_mem 0 (-m) (proj_mem _ _)
  map_mem_degree {X Y n x} hx := by
    obtain ⟨f, rfl⟩ := hx
    rw [T_map_lof]
    simpa using val_mem_degree (f := f.1) 0 (-n)

/-! ### `T_B` is an isomorphism -/

theorem dproj_TL (n : ℤ) (x : (dB R B).Hom X Y) :
    dproj R n (TL R B X Y x) = val ((dB R B).component n X Y x).1 0 (-n) := by
  induction x using Hom.induction_on with
  | zero => simp [val]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add]
    simp only [val, Submodule.coe_add, FamAll.add_apply, Functor.map_add, Preadditive.add_comp,
      Preadditive.comp_add]
  | lof m f =>
    rw [TL_lof]
    by_cases h : m = n
    · subst h
      rw [component_lof_self, dproj_of_mem]
      simpa using val_mem_degree (f := f.1) 0 (-m)
    · rw [(dB R B).component_lof_of_ne _ h, dproj_of_mem_ne (by simpa using val_mem_degree (f := f.1) 0 (-m)) h]
      simp [val]

theorem TL_injective : Function.Injective (TL R B X Y) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  refine Hom.ext fun n => ?_
  rw [map_zero]
  have h0 : val ((dB R B).component n X Y x).1 0 (-n) = 0 := by
    rw [← dproj_TL, LinearMap.mem_ker.1 hx, map_zero]
  rw [val_zero] at h0
  have h1 : (TbF R B).map (((dB R B).component n X Y x).1 0 (-n)) = (TbF R B).map 0 := by
    rw [Functor.map_zero]
    exact (cancel_mono (τ R B (-n) Y).hom).1 (by rw [h0, Limits.zero_comp])
  exact Subtype.ext (Fam.eq_of_entry ((dB R B).component n X Y x).2 (Submodule.zero_mem _)
    (i₀ := 0) (j₀ := -n) (by ring) (TbF_map_injective h1))

/-- The preimage under `T` of a morphism of `B` of degree `0`. -/
def TbPre {Z W : Associated R (GUnderlying R B)} (h : bobj Z ⟶ bobj W)
    (hh : h ∈ degree (R := R) (bobj Z) (bobj W) 0) : Z ⟶ W :=
  (Associated.Tinv R (DegreeZero R B)).map (⟨h, hh⟩ : (⟨bobj Z⟩ : DegreeZero R B) ⟶ ⟨bobj W⟩)

theorem TbF_map_TbPre {Z W : Associated R (GUnderlying R B)} (h : bobj Z ⟶ bobj W)
    (hh : h ∈ degree (R := R) (bobj Z) (bobj W) 0) : (TbF R B).map (TbPre h hh) = h :=
  congrArg Subtype.val (Associated.T_map_Tinv_map (R := R) (A := DegreeZero R B)
    (⟨h, hh⟩ : (⟨bobj Z⟩ : DegreeZero R B) ⟶ ⟨bobj W⟩))

theorem conj_mem_degree {n : ℤ} {g : bobj X ⟶ bobj Y} (hg : g ∈ degree (R := R) _ _ n) {i j : ℤ}
    (h : i - j = n) :
    (τ R B i X).hom ≫ g ≫ (τ R B j Y).inv ∈ degree (R := R) (bobj (((dB R B).pow i).obj X))
      (bobj (((dB R B).pow j).obj Y)) 0 := by
  have := comp_mem_degree (comp_mem_degree (τ_hom_mem i X).2 hg) (τ_inv_mem j Y).2
  rw [show -i + n + j = 0 by omega, Category.assoc] at this
  exact this

/-- The family of a morphism of `B` of degree `n`: `f_{i,j} = T⁻¹(τ_j⁻¹ ∘ g ∘ τ_i)`. -/
def famOf {n : ℤ} (g : bobj X ⟶ bobj Y) (hg : g ∈ degree (R := R) _ _ n) : (dB R B).FamAll X Y :=
  fun i j => if h : i - j = n then TbPre _ (conj_mem_degree hg h) else 0

theorem TbF_famOf {n : ℤ} (g : bobj X ⟶ bobj Y) (hg : g ∈ degree (R := R) _ _ n) {i j : ℤ}
    (h : i - j = n) : (TbF R B).map (famOf g hg i j) = (τ R B i X).hom ≫ g ≫ (τ R B j Y).inv := by
  rw [famOf, dif_pos h, TbF_map_TbPre]

theorem famOf_mem {n : ℤ} (g : bobj X ⟶ bobj Y) (hg : g ∈ degree (R := R) _ _ n) :
    famOf g hg ∈ (dB R B).Fam R n X Y := by
  refine ⟨fun i j h => by rw [famOf, dif_neg h], fun i j => ?_⟩
  by_cases h : i - j = n
  · apply TbF_map_injective
    rw [TbF_famOf g hg (by omega), Functor.map_comp, Functor.map_comp]
    erw [TbF_map_Qhat]
    rw [TbF_famOf g hg h, τ_succ, τ_succ_inv, QPiSupercategory.Q_map_eq]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  · rw [famOf, famOf, dif_neg (by omega), dif_neg h]; simp

theorem TL_famOf {n : ℤ} (g : bobj X ⟶ bobj Y) (hg : g ∈ degree (R := R) _ _ n) :
    TL R B X Y ((dB R B).lof n X Y ⟨famOf g hg, famOf_mem g hg⟩) = g := by
  rw [TL_lof, val, TbF_famOf g hg (by ring), τ_zero]
  simp

theorem TL_surjective : Function.Surjective (TL R B X Y) := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  rintro g -
  refine induction_on_degree (R := R) g (Submodule.zero_mem _) (fun n g hg => ⟨_, TL_famOf g hg⟩)
    (fun g h hg hh => Submodule.add_mem _ hg hh)

instance : (T R B).Faithful where
  map_injective h := TL_injective h

instance : (T R B).Full where
  map_surjective g := TL_surjective g

variable (R B) in
/-- The inverse of `T_B`. -/
@[simps obj]
def Tinv : B ⥤ QAssociated R (GUnderlying R B) where
  obj b := ⟨⟨⟨⟨b⟩⟩⟩⟩
  map {b b'} g := (T R B).preimage
    (show (T R B).obj ⟨⟨⟨⟨b⟩⟩⟩⟩ ⟶ (T R B).obj ⟨⟨⟨⟨b'⟩⟩⟩⟩ from g)
  map_id b := (T R B).map_injective (by simp; rfl)
  map_comp f g := (T R B).map_injective (by simp)

theorem T_map_Tinv_map {b b' : B} (g : b ⟶ b') : (T R B).map ((Tinv R B).map g) = g :=
  (T R B).map_preimage (show (T R B).obj ⟨⟨⟨⟨b⟩⟩⟩⟩ ⟶ (T R B).obj ⟨⟨⟨⟨b'⟩⟩⟩⟩ from g)

/-- **`𝔻 ∘ 𝔼 ≅ I`.** `T_B` is an isomorphism of categories. -/
theorem Tinv_comp_T : Tinv R B ⋙ T R B = 𝟭 B :=
  CategoryTheory.Functor.ext (fun _ => rfl) fun b b' g => by simpa using T_map_Tinv_map g

theorem T_comp_Tinv : T R B ⋙ Tinv R B = 𝟭 _ :=
  CategoryTheory.Functor.ext (fun _ => rfl) fun X Y x =>
    (T R B).map_injective (by simpa using T_map_Tinv_map ((T R B).map x))

instance : (Tinv R B).Additive where
  map_add := (T R B).map_injective (by simp [T_map_Tinv_map])

instance : (Tinv R B).Linear R where
  map_smul _ _ := (T R B).map_injective (by simp [T_map_Tinv_map])

instance : IsGradedSuperfunctor R (Tinv R B) where
  map_mem hg := mem_of_map_mem (T R B) (by rw [T_map_Tinv_map]; exact hg)
  map_mem_degree hg := mem_degree_of_map_mem (T R B) (by rw [T_map_Tinv_map]; exact hg)

/-! ### `T_B` preserves `Π`, `ζ`, `Q` and `σ` -/

theorem T_obj (X : QAssociated R (GUnderlying R B)) : (T R B).obj X = X.obj.obj.obj.obj := rfl

theorem T_obj_pi (X : QAssociated R (GUnderlying R B)) :
    (T R B).obj ((PiSupercategory.pi (R := R)).obj X) =
      (PiSupercategory.pi (R := R)).obj ((T R B).obj X) := rfl

theorem T_obj_Q (X : QAssociated R (GUnderlying R B)) :
    (T R B).obj ((QPiSupercategory.Q (R := R)).obj X) =
      (QPiSupercategory.Q (R := R)).obj ((T R B).obj X) := rfl

theorem T_map_ι {Z W : Associated R (GUnderlying R B)} (f : Z ⟶ W) :
    (T R B).map ((ι (dB R B)).map f) = (TbF R B).map f := by
  rw [ι_map]
  refine (T_map_lof (X := (⟨Z⟩ : QAssociated R _)) (Y := ⟨W⟩) _).trans ?_
  rw [neg_zero, val, τ_zero, τ_zero]
  simp [mapFam, diagFam_self]

/-- `T_B` carries `ζ` to `ζ`. -/
theorem T_map_ζ (X : QAssociated R (GUnderlying R B)) :
    (T R B).map (PiSupercategory.ζ (R := R) X).hom = (PiSupercategory.ζ (R := R) ((T R B).obj X)).hom := by
  rw [ζ_eq, ζIso, Functor.mapIso_hom]
  erw [T_map_ι]
  exact congrArg Subtype.val (Associated.T_map_ζ (R := R) (A := DegreeZero R B) X.obj)

/-- `T_B` carries `σ` to `σ`. -/
theorem T_map_σ (X : QAssociated R (GUnderlying R B)) :
    (T R B).map (QPiSupercategory.σ (R := R) X).hom = (σ (R := R) ((T R B).obj X)).hom := by
  rw [σ_eq]
  show (T R B).map ((dB R B).lof (-1) _ _ _) = _
  rw [T_map_lof, neg_neg, val, τ_zero]
  show 𝟙 _ ≫ (TbF R B).map ((dB R B).famσ X.obj 0 (0 + 1)) ≫ (τ R B 1 X.obj).hom = _
  rw [famσ_succ, comm_zero_hom_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]
  show (σ (R := R) _).hom ≫ 𝟙 _ = _
  rw [Category.comp_id]; rfl

/-! ### Naturality of `T` -/

section Naturality

variable {B' : Type w₃} [Category.{w₄} B'] [Preadditive B'] [Linear R B'] [Supercategory R B']
  [GradedSupercategory R B'] [QPiSupercategory R B']
  (F : B ⥤ B') [F.Additive] [F.Linear R] [IsGradedSuperfunctor R F]

/-- `𝔻(𝔼 F)`. -/
abbrev DEmap : QAssociated R (GUnderlying R B) ⥤ QAssociated R (GUnderlying R B') :=
  map (GUnderlying.qpiFunctor (R := R) F) (GUnderlying.qpiFunctor_isCompatible F)

/-- The morphism of shift data underlying `𝔻(𝔼 F)`. -/
abbrev DEΦ : ShiftFunctor R (dB R B) (dB R B') :=
  shiftFunctor R (GUnderlying.qpiFunctor (R := R) F) (GUnderlying.qpiFunctor_isCompatible F)

theorem TbF_map_F {Z W : Associated R (GUnderlying R B)} (f : Z ⟶ W) :
    (TbF R B').map ((DEΦ F).F.map f) = F.map ((TbF R B).map f) := by
  have h := CategoryTheory.Functor.congr_hom (Associated.T_naturality (R := R)
    (A := DegreeZero R B) (B := DegreeZero R B') (DegreeZero.map (R := R) F)) f
  simp only [Functor.comp_map, eqToHom_refl, Category.comp_id, Category.id_comp] at h
  exact congrArg Subtype.val h

theorem TbF_γhat_inv (Z : Associated R (GUnderlying R B)) :
    (TbF R B').map ((DEΦ F).γ.inv.app Z) = (γ R F (bobj Z)).inv := by
  show ((Associated.T R (DegreeZero R B')).map (Associated.homMk _ 0)).1 = _
  rw [Associated.T_map]
  simp only [Associated.homMk_fst, Associated.homMk_snd, Underlying.zero_val, Limits.zero_comp,
    add_zero]
  rfl

theorem TbF_Γ_zero (Z : Associated R (GUnderlying R B)) :
    (TbF R B').map (((DEΦ F).Γ 0).hom.app Z) = 𝟙 _ := by
  show (TbF R B').map (𝟙 _ ≫ 𝟙 _) = _
  simp

/-- The step of the comparison between `Γ` and `τ`. -/
theorem TbF_Γ_inv_τ_succ (i : ℤ) (Z : Associated R (GUnderlying R B)) :
    (TbF R B').map (((DEΦ F).Γ (i + 1)).inv.app Z) ≫ (τ R B' (i + 1) ((DEΦ F).F.obj Z)).hom =
      F.map ((TbF R B).map (((dB R B).succ i).inv.app Z) ≫ (σ (R := R) (bobj (((dB R B).pow i).obj Z))).hom) ≫
        (TbF R B').map (((DEΦ F).Γ i).inv.app Z) ≫ (τ R B' i ((DEΦ F).F.obj Z)).hom := by
  rw [ShiftFunctor.Γ_succ_inv_app]
  rw [τ_succ]
  rw [(TbF R B').map_comp, (TbF R B').map_comp, (TbF R B').map_comp]
  simp only [Category.assoc]
  rw [← (TbF R B').map_comp_assoc (((dB R B').succ i).hom.app _), Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [TbF_map_dQ, TbF_map_F, TbF_γhat_inv]
  erw [QPiSupercategory.σ_naturality_assoc (R := R) (C := B')
    ((TbF R B').map (((DEΦ F).Γ i).inv.app Z))]
  rw [γ_inv, F.map_comp]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_assoc]

theorem TbF_Γ_inv_τ (i : ℤ) (Z : Associated R (GUnderlying R B)) :
    (TbF R B').map (((DEΦ F).Γ i).inv.app Z) ≫ (τ R B' i ((DEΦ F).F.obj Z)).hom =
      F.map (τ R B i Z).hom := by
  have step : ∀ i : ℤ, ((TbF R B').map (((DEΦ F).Γ (i + 1)).inv.app Z) ≫
      (τ R B' (i + 1) ((DEΦ F).F.obj Z)).hom = F.map (τ R B (i + 1) Z).hom) ↔
      ((TbF R B').map (((DEΦ F).Γ i).inv.app Z) ≫ (τ R B' i ((DEΦ F).F.obj Z)).hom =
        F.map (τ R B i Z).hom) := by
    intro i
    let K := F.mapIso (((TbF R B).mapIso (((dB R B).succ i).app Z)).symm ≪≫
      σ (R := R) (bobj (((dB R B).pow i).obj Z)))
    have h1 := TbF_Γ_inv_τ_succ F i Z
    have h2 : F.map (τ R B (i + 1) Z).hom = K.hom ≫ F.map (τ R B i Z).hom := by
      rw [τ_succ]; simp [K]
    rw [h1, h2]
    exact ⟨fun h => (cancel_epi K.hom).1 h, fun h => by rw [h]; rfl⟩
  induction i using Int.induction_on with
  | hz =>
    rw [τ_zero, τ_zero]
    simp only [Iso.refl_hom, CategoryTheory.Functor.map_id]
    erw [Category.comp_id]
    show (TbF R B').map (𝟙 _ ≫ 𝟙 _) = 𝟙 _
    simp
  | hp k ih => exact (step k).2 ih
  | hn k ih =>
    have := (step (-(k : ℤ) - 1)).1
    rw [show -(k : ℤ) - 1 + 1 = -(k : ℤ) by ring] at this
    exact this ih

/-- **Naturality of `T`**: `F ∘ T_B = T_{B'} ∘ 𝔻(𝔼 F)` for a graded superfunctor `F`. -/
theorem T_naturality : DEmap F ⋙ T R B' = T R B ⋙ F :=
  CategoryTheory.Functor.ext (fun _ => rfl) fun X Y x => by
    simp only [Functor.comp_map, eqToHom_refl, Category.comp_id, Category.id_comp]
    induction x using Hom.induction_on with
    | zero => simp
    | add x y hx hy =>
      rw [(DEmap F).map_add, (T R B').map_add, hx, hy, (T R B).map_add, F.map_add]
    | lof m f =>
      have e1 : (DEmap F).map ((dB R B).lof m X.obj Y.obj f : X ⟶ Y) =
          (dB R B').lof m _ _ ((DEΦ F).famMapₗ m X.obj Y.obj f) :=
        Orbit.map_map_lof (DEΦ F) f
      rw [e1]
      refine (T_map_lof (X := (DEmap F).obj X) (Y := (DEmap F).obj Y)
        ((DEΦ F).famMapₗ m X.obj Y.obj f)).trans ?_
      rw [T_map_lof, val, val, τ_zero, τ_zero]
      simp only [Iso.refl_inv, F.map_comp]
      erw [Category.id_comp, CategoryTheory.Functor.map_id, Category.id_comp]
      show (TbF R B').map (((DEΦ F).Γ 0).hom.app _ ≫ (DEΦ F).F.map (f.1 0 (-m)) ≫
          ((DEΦ F).Γ (-m)).inv.app _) ≫ _ = _
      rw [(TbF R B').map_comp, (TbF R B').map_comp, TbF_Γ_zero, Category.id_comp, TbF_map_F,
        Category.assoc]
      congr 1
      exact TbF_Γ_inv_τ F (-m) Y.obj

end Naturality

end T

end QAssociated

end StringDiagrams

end
