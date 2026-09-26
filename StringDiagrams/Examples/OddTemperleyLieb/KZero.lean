import StringDiagrams.Examples.OddTemperleyLieb.SKar
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# The Grothendieck group of `SKar(STL(δ))`

J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, Theorem A.3
(`K₀` part).

* `multiplicity n b : K₀(SKar(STL(δ))) →+ ℤ`: the multiplicity of `P n b = (f_n)^b_b`, induced
  by `Z ↦ dim_k Hom(P n b, Z)`;
* `basisK₀`: the classes `[P n b]` (`n ∈ ℕ`, `b ∈ ℤ/2`) form a `ℤ`-basis of `K₀`.
-/

noncomputable section

namespace StringDiagrams.OddTemperleyLieb

open CategoryTheory Limits Idempotents
open Rep (delta)

variable {k : Type*} [Field k] (q : kˣ)

local notation "δq" => delta q

variable (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1)
include hq

/-! ## Hom spaces from `P n b` -/

omit hq in
/-- Morphisms into a biproduct. -/
def homBiprodEquiv (P Y₁ Y₂ : SKar k (STL k δq)) :
    (P ⟶ Y₁ ⊞ Y₂) ≃ₗ[k] (P ⟶ Y₁) × (P ⟶ Y₂) where
  toFun f := (f ≫ biprod.fst, f ≫ biprod.snd)
  invFun g := biprod.lift g.1 g.2
  map_add' f g := by simp
  map_smul' c f := by simp
  left_inv f := by apply biprod.hom_ext <;> simp
  right_inv g := by simp

omit hq in
theorem finrank_hom_zero (P : SKar k (STL k δq)) :
    Module.finrank k (P ⟶ bsum ([] : List (SKar k (STL k δq)))) = 0 := by
  haveI : Subsingleton (P ⟶ bsum ([] : List (SKar k (STL k δq)))) :=
    ⟨fun f g => (isZero_zero _).eq_of_tgt f g⟩
  exact Module.finrank_zero_of_subsingleton

/-- `Hom(P n b, P m a)` is `k` if `(n, b) = (m, a)` and `0` otherwise. -/
theorem finrank_hom_jwObj (n m : ℕ) (b a : ZMod 2) :
    FiniteDimensional k (jwObj q hq n b ⟶ jwObj q hq m a) ∧
      Module.finrank k (jwObj q hq n b ⟶ jwObj q hq m a) = if n = m ∧ b = a then 1 else 0 := by
  by_cases h : n = m ∧ b = a
  · obtain ⟨rfl, rfl⟩ := h
    rw [if_pos ⟨rfl, rfl⟩]
    -- `c ↦ c • 1` is a linear isomorphism `k ≃ End(P n b)`
    let e : k ≃ₗ[k] (jwObj q hq n b ⟶ jwObj q hq n b) :=
      LinearEquiv.ofBijective (LinearMap.toSpanSingleton k _ (𝟙 _))
        ⟨fun c d hcd => by
          simp only [LinearMap.toSpanSingleton_apply] at hcd
          by_contra hne
          have : (c - d) • 𝟙 (jwObj q hq n b) = 0 := by rw [sub_smul, hcd, sub_self]
          exact id_jwObj_ne_zero q hq n b ((smul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)),
         fun f => by
          obtain ⟨c, hc⟩ := jwObj_isSchur q hq n b f
          exact ⟨c, by simp [hc]⟩⟩
    exact ⟨LinearEquiv.finiteDimensional e, by rw [← e.finrank_eq, Module.finrank_self]⟩
  · rw [if_neg h]
    haveI : Subsingleton (jwObj q hq n b ⟶ jwObj q hq m a) :=
      ⟨fun f g => by
        rw [hom_jwObj_eq_zero q hq (by tauto) f, hom_jwObj_eq_zero q hq (by tauto) g]⟩
    exact ⟨inferInstance, Module.finrank_zero_of_subsingleton⟩

/-- Hom spaces from `P n b` are finite-dimensional. -/
theorem finiteDimensional_hom (n : ℕ) (b : ZMod 2) (Z : SKar k (STL k δq)) :
    FiniteDimensional k (jwObj q hq n b ⟶ Z) := by
  obtain ⟨L, hL, ⟨e⟩⟩ := exists_iso_bsum_jwObj q hq Z
  suffices FiniteDimensional k (jwObj q hq n b ⟶ bsum L) from
    LinearEquiv.finiteDimensional (Linear.homCongr k (Iso.refl _) e.symm)
  clear e
  induction L with
  | nil =>
    haveI : Subsingleton (jwObj q hq n b ⟶ bsum ([] : List (SKar k (STL k δq)))) :=
      ⟨fun f g => (isZero_zero _).eq_of_tgt f g⟩
    infer_instance
  | cons P L ih =>
    obtain ⟨m, a, rfl⟩ := hL P (by simp)
    haveI := (finrank_hom_jwObj q hq n m b a).1
    haveI := ih fun Q hQ => hL Q (by simp [hQ])
    exact LinearEquiv.finiteDimensional (homBiprodEquiv q _ _ _).symm

/-- The multiplicity of `P n b`: `Z ↦ dim_k Hom(P n b, Z)`. -/
def multiplicity (n : ℕ) (b : ZMod 2) : K₀ (SKar k (STL k δq)) →+ ℤ :=
  K₀.lift (fun Z => (Module.finrank k (jwObj q hq n b ⟶ Z) : ℤ))
    (fun Z Y e => by dsimp only; rw [(Linear.homCongr k (Iso.refl _) e).finrank_eq])
    (fun Z Y => by
      dsimp only
      haveI := finiteDimensional_hom q hq n b Z
      haveI := finiteDimensional_hom q hq n b Y
      rw [(homBiprodEquiv q _ _ _).finrank_eq, Module.finrank_prod]
      push_cast; rfl)

theorem multiplicity_jwObj (n m : ℕ) (b a : ZMod 2) :
    multiplicity q hq n b (K₀.mk (jwObj q hq m a)) = if n = m ∧ b = a then 1 else 0 := by
  rw [multiplicity, K₀.lift_mk, (finrank_hom_jwObj q hq n m b a).2]
  split_ifs <;> rfl

omit hq in
theorem mk_bsum (L : List (SKar k (STL k δq))) :
    K₀.mk (bsum L) = (L.map K₀.mk).sum := by
  induction L with
  | nil => exact K₀.mk_zero
  | cons P L ih => simp [K₀.mk_biprod, ih]

/-! ## The basis of `K₀` -/

/-- The classes `[P n b]`. -/
def classJw (x : ℕ × ZMod 2) : K₀ (SKar k (STL k δq)) := K₀.mk (jwObj q hq x.1 x.2)

theorem linearIndependent_classJw : LinearIndependent ℤ (classJw q hq) := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum i hi
  have := congrArg (multiplicity q hq i.1 i.2) hsum
  rw [map_sum, map_zero] at this
  rw [Finset.sum_eq_single_of_mem i hi] at this
  · rwa [map_zsmul, classJw, multiplicity_jwObj, if_pos ⟨rfl, rfl⟩, smul_eq_mul, mul_one] at this
  · intro j _ hji
    rw [map_zsmul, classJw, multiplicity_jwObj, if_neg, smul_zero]
    intro h
    exact hji (Prod.ext h.1.symm h.2.symm)

theorem span_classJw :
    Submodule.span ℤ (Set.range (classJw q hq)) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  induction x using K₀.induction_on with
  | mk Z =>
    obtain ⟨L, hL, ⟨e⟩⟩ := exists_iso_bsum_jwObj q hq Z
    rw [K₀.mk_eq_mk_of_iso e, mk_bsum]
    refine list_sum_mem ?_
    intro y hy
    obtain ⟨P, hP, rfl⟩ := List.mem_map.mp hy
    obtain ⟨n, a, rfl⟩ := hL P hP
    exact Submodule.subset_span ⟨(n, a), rfl⟩
  | zero => exact Submodule.zero_mem _
  | add x y hx hy => exact Submodule.add_mem _ hx hy
  | neg x hx => exact Submodule.neg_mem _ hx

/-- **The classes of the objects `P n b = (f_n)^b_b` form a `ℤ`-basis of `K₀(SKar(STL(δ)))`.** -/
def basisK₀ : Basis (ℕ × ZMod 2) ℤ (K₀ (SKar k (STL k δq))) :=
  Basis.mk (linearIndependent_classJw q hq) (span_classJw q hq).ge

@[simp] theorem basisK₀_apply (x : ℕ × ZMod 2) :
    basisK₀ q hq x = K₀.mk (jwObj q hq x.1 x.2) := Basis.mk_apply _ _ _

end StringDiagrams.OddTemperleyLieb

end
