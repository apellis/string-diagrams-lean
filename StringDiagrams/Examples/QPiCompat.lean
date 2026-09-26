import StringDiagrams.Super.QPiCategory
import StringDiagrams.Super.QEnvelope
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# The data of a `(Q, Π)`-functor which is not compatible

Brundan–Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, Definition 6.12(ii) and
Theorem 6.13: an example showing that the compatibility of `γ_F` with `β`
(`QPiFunctorData.IsCompatible`) does not follow from the axioms of Definition 6.12(ii) as
printed (`StringDiagrams.QPiFunctorData`: a Π-functor `(F, β_F)` with a natural isomorphism
`γ_F : Q'F ≅ FQ`), and hence that the 2-functor `𝔼` of (6.3) is not essentially surjective on
1-morphisms for the printed definition. This is why the definition of a `(Q, Π)`-functor
adopted in `StringDiagrams.QPiFunctor` includes the compatibility as an axiom.

Let `B` be the `(Q, Π)`-envelope (Definition 6.8) of the category of `R`-modules, graded
trivially (all morphisms even of degree zero), and `A = 𝔼(B)` its underlying
`(Q, Π)`-category. The natural automorphism `α` of `Q` acting on `Q^m Π^a M` by `(-1)^a` makes
`(I, β = 1, γ = α)` a `(Q, Π)`-functor `A → A` in the sense of the printed Definition 6.12(ii)
(`QPiCompat.twisted`). If `2 ≠ 0` in `R`, it is not compatible
(`QPiCompat.twisted_not_isCompatible`), so it is not isomorphic, by a `(Q, Π)`-natural
isomorphism, to `𝔼(F)` for any graded superfunctor `F : B → B`
(`QPiCompat.twisted_not_iso_image`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory GradedSupercategory

universe w

namespace QPiCompat

variable (R : Type w) [CommRing R]

/-- The category of `R`-modules, with all morphisms even of degree zero. -/
def Triv : Type (w + 1) := ModuleCat.{w} R

instance : Category (Triv R) := inferInstanceAs (Category (ModuleCat.{w} R))
instance : Preadditive (Triv R) := inferInstanceAs (Preadditive (ModuleCat.{w} R))
instance : Linear R (Triv R) := inferInstanceAs (Linear R (ModuleCat.{w} R))

/-- All morphisms are even. -/
instance : Supercategory R (Triv R) where
  parity _ _ p := if p = 0 then ⊤ else ⊥
  isInternal X Y := by
    rw [DirectSum.isInternal_submodule_iff_isCompl _ (i := 0) (j := 1) (by decide)
      (by ext p; rcases parity_eq_zero_or_one p with rfl | rfl <;> simp)]
    simpa using isCompl_top_bot
  id_mem _ := by simp
  comp_mem {X Y Z p q f g} hf hg := by
    by_cases hp : p = 0
    · by_cases hq : q = 0
      · subst hp hq; simp
      · simp only [hq, if_false, Submodule.mem_bot] at hg; subst hg; simp
    · simp only [hp, if_false, Submodule.mem_bot] at hf; subst hf; simp

theorem mem_parity_one {X Y : Triv R} {f : X ⟶ Y} (hf : f ∈ parity (R := R) X Y 1) : f = 0 := by
  have : f ∈ (⊥ : Submodule R (X ⟶ Y)) := by
    simpa [show ¬((1 : ZMod 2) = 0) by decide] using hf
  simpa using this

/-- All morphisms have degree zero. -/
instance : GradedSupercategory R (Triv R) where
  degree _ _ n := if n = 0 then ⊤ else ⊥
  isInternal_degree X Y := by
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    refine ⟨fun n => ?_, ?_⟩
    · by_cases hn : n = 0
      · subst hn
        simp only [if_true]
        rw [disjoint_iff, eq_bot_iff]
        intro x hx
        have : x ∈ ⨆ (j : ℤ) (_ : j ≠ 0), (if j = 0 then ⊤ else ⊥ : Submodule R (X ⟶ Y)) :=
          (Submodule.mem_inf.1 hx).2
        rw [show (⨆ (j : ℤ) (_ : j ≠ 0), (if j = 0 then ⊤ else ⊥ : Submodule R (X ⟶ Y))) = ⊥ by
          refine le_bot_iff.1 (iSup_le fun j => iSup_le fun hj => ?_); simp [hj]] at this
        exact this
      · simp [hn]
    · rw [eq_top_iff]
      exact le_iSup_of_le 0 (by simp)
  proj_mem_degree {X Y n f} p hf := by
    by_cases hn : n = 0
    · simp [hn]
    · simp only [hn, if_false, Submodule.mem_bot] at hf ⊢; subst hf; simp
  id_mem_degree _ := by simp
  comp_mem_degree {X Y Z m n f g} hf hg := by
    by_cases hm : m = 0
    · by_cases hn : n = 0
      · subst hm hn; simp
      · simp only [hn, if_false, Submodule.mem_bot] at hg; subst hg; simp
    · simp only [hm, if_false, Submodule.mem_bot] at hf; subst hf; simp

/-- The graded `(Q, Π)`-supercategory `B`: the `(Q, Π)`-envelope of `Triv R`. -/
abbrev B := QPiEnvelope R (Triv R)

/-- The `(Q, Π)`-category `A = 𝔼(B)`. -/
abbrev A := GUnderlying R (B R)

variable {R}

theorem map_eq_zero_of_par_ne {X Y : A R} (f : X ⟶ Y) (h : X.obj.obj.par ≠ Y.obj.obj.par) :
    f = 0 := by
  apply Underlying.hom_ext; apply DegreeZero.hom_ext
  have hf : Envelope.toHom f.1.1 ∈ parity (R := R) X.obj.obj.obj Y.obj.obj.obj
      (0 + (X.obj.obj.par + Y.obj.obj.par)) := f.2
  have h1 : (0 : ZMod 2) + (X.obj.obj.par + Y.obj.obj.par) = 1 := by
    generalize X.obj.obj.par = a at h ⊢; generalize Y.obj.obj.par = b at h ⊢
    revert a b; decide
  rw [h1] at hf
  exact mem_parity_one R hf

/-- The automorphism `α` of `Q`: `(-1)^a` on `Q^m Π^a M`. -/
def α : QPiCategory.Q (R := R) (C := A R) ≅ QPiCategory.Q (R := R) :=
  NatIso.ofComponents (fun X =>
    { hom := sign R X.obj.obj.par • 𝟙 _
      inv := sign R X.obj.obj.par • 𝟙 _
      hom_inv_id := by simp
      inv_hom_id := by simp })
    (fun {X Y} f => by
      by_cases h : X.obj.obj.par = Y.obj.obj.par
      · simp [h]
      · rw [map_eq_zero_of_par_ne f h]; simp)

variable (R) in
/-- The data `(I, β = 1, γ = α)` of a `(Q, Π)`-functor in the sense of the printed
Definition 6.12(ii). -/
def twisted : QPiFunctorData R (𝟭 (A R)) where
  toPiFunctor := PiFunctor.id R (A R)
  γ := Functor.leftUnitor _ ≪≫ α ≪≫ (Functor.rightUnitor _).symm

/-- The object `Q⁰Π⁰R` of `A`. -/
def X₀ : A R := ⟨⟨⟨0, ⟨0, ModuleCat.of R R⟩⟩⟩⟩

theorem two_smul_id_ne_zero (h2 : (2 : R) ≠ 0) (a : ZMod 2) (m : ℤ) :
    (2 : R) • 𝟙 (⟨⟨⟨a, ⟨m, ModuleCat.of R R⟩⟩⟩⟩ : A R) ≠ 0 := by
  intro h
  have h' := congrArg (fun g : (⟨⟨⟨a, ⟨m, ModuleCat.of R R⟩⟩⟩⟩ : A R) ⟶ _ =>
    QEnvelope.toHom (Envelope.toHom g.1.1)) h
  simp only [Underlying.smul_val, DegreeZero.smul_val, Underlying.id_val, DegreeZero.id_val,
    Underlying.zero_val, DegreeZero.zero_val, Envelope.toHom_smul, Envelope.toHom_id,
    QEnvelope.toHom_smul, QEnvelope.toHom_id, Envelope.toHom_zero, QEnvelope.toHom_zero] at h'
  have h'' := congrArg (fun g : ModuleCat.of R R ⟶ ModuleCat.of R R => g.hom (1 : R)) h'
  change (2 : R) • (1 : R) = 0 at h''
  exact h2 (by simpa using h'')

/-- **The compatibility is not automatic**: if `2 ≠ 0` in `R`, the data `(I, 1, α)` is not
compatible, so it is not the data of a `(Q, Π)`-functor in the adopted sense
(`StringDiagrams.QPiFunctor`). -/
theorem twisted_not_isCompatible (h2 : (2 : R) ≠ 0) : ¬ (twisted R).IsCompatible R := by
  intro hc
  rw [QPiFunctorData.IsCompatible.iff] at hc
  have h := hc X₀
  simp only [twisted, PiFunctor.id_β, Iso.refl_hom, NatTrans.id_app, Iso.trans_hom,
    NatTrans.comp_app, Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id, Iso.symm_hom,
    Functor.id_map, α, NatIso.ofComponents_hom_app, Functor.comp_obj, Functor.id_obj] at h
  have e1 : sign R (X₀ (R := R)).obj.obj.par = 1 := by show sign R 0 = 1; simp
  have e2 : sign R ((PiCategory.pi R).obj (X₀ (R := R))).obj.obj.par = -1 := by show sign R (0 + 1) = -1; simp
  rw [e1, e2, one_smul, CategoryTheory.Functor.map_id, Category.id_comp,
    neg_smul, one_smul, Preadditive.comp_neg, Category.comp_id] at h
  have h3 : (2 : R) • (QPiCategory.Q_pi (R := R) (C := A R)).β.hom.app X₀ = 0 := by
    rw [two_smul]; nth_rw 1 [← h]; simp
  have h4 : (2 : R) • 𝟙 ((PiCategory.pi R).obj ((QPiCategory.Q R).obj (X₀ (R := R)))) = 0 := by
    have := congrArg (· ≫ (QPiCategory.Q_pi (R := R) (C := A R)).β.inv.app X₀) h3
    simpa using this
  exact two_smul_id_ne_zero h2 _ _ h4

/-- **Theorem 6.13 fails for the printed Definition 6.12(ii)**: if `2 ≠ 0` in `R`, the data
`(I, 1, α)` of `A = 𝔼(B)` is not isomorphic, by a `(Q, Π)`-natural isomorphism, to `𝔼(F)` for
any graded superfunctor `F : B → B`. -/
theorem twisted_not_iso_image (h2 : (2 : R) ≠ 0) (F : B R ⥤ B R) [F.Additive] [F.Linear R]
    [IsGradedSuperfunctor R F] (x : 𝟭 (A R) ≅ GUnderlying.map R F) :
    ¬ QPiFunctorData.IsQPiNatural R (twisted R)
      (GUnderlying.qpiFunctor (R := R) F).toQPiFunctorData x.hom :=
  fun hx => twisted_not_isCompatible h2
    (QPiFunctorData.IsCompatible.of_iso x hx (GUnderlying.qpiFunctor (R := R) F).isCompatible)

end QPiCompat

end StringDiagrams

end
