import StringDiagrams.Examples.OddTemperleyLieb.KZero

/-!
# The ring `K₀(SKar(STL(δ)))`

J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, Theorem A.3 (last
paragraph).

* `unitIso`: the unit object of `SKar(STL(δ))` is `P 0 0 = (f_0)^0_0`;
* `piIso`: `Π (P n 0) ≅ P n 1`, so `[P n 1] = π [P n 0]` (`classJw_one`);
* `tensorIso`: `P (N+1) 0 ⊗ P 1 0 ≅ P (N+2) 0 ⊞ P N 1`, from `f_{N+1} ⊗ 1 = f_{N+2} + g_{N+2}` with
  `g_{N+2} ≅ Π f_N` (`Decomposition`); so
  `[P (N+1) 0] [P 1 0] = [P (N+2) 0] + π [P N 0]` (`classJw_mul_one`).
-/

noncomputable section

namespace StringDiagrams.OddTemperleyLieb

open CategoryTheory Limits Idempotents MonoidalCategory Supercategory
open Rep (delta)

variable {k : Type*} [Field k] (q : kˣ)

local notation "δq" => delta q

variable (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1)
include hq

omit hq in
theorem mat_comp_unique {D : Type*} [Category D] [Preadditive D] {M N K : Mat_ D} [Unique N.ι]
    (f : M ⟶ N) (g : N ⟶ K) (i : M.ι) (l : K.ι) : (f ≫ g) i l = f i default ≫ g default l := by
  rw [Mat_.comp_apply, Fintype.sum_unique]

/-! ## The unit -/

omit hq in
theorem homD_one (a : ZMod 2) (n : ℕ) (h) : homD (q := q) (a := a) (b := a) (𝟙 (X k δq n)) h =
    𝟙 (genD q a n) := Underlying.hom_ext rfl

theorem jwObj_zero_p (a : ZMod 2) :
    (jwObj q hq 0 a).p = 𝟙 ((Mat_.embedding (DD q)).obj (genD q a 0)) := by
  show (Mat_.embedding (DD q)).map _ = _
  rw [← CategoryTheory.Functor.map_id]
  congr 1

/-- The unit object of `SKar(STL(δ))` is `P 0 0`. -/
theorem unit_eq : 𝟙_ (SKar k (STL k δq)) = jwObj q hq 0 0 := by
  refine Karoubi.ext rfl ?_
  rw [jwObj_zero_p, eqToHom_refl, Category.comp_id, Category.id_comp]
  rfl

theorem one_eq_classJw : (1 : K₀ (SKar k (STL k δq))) = classJw q hq (0, 0) := by
  rw [K₀.one_def, classJw, unit_eq q hq]

/-! ## The parity shift -/

/-- `Π (P n 0) = P n 1`. -/
theorem pi_jwObj (n : ℕ) : (PiCategory.pi (R := k)).obj (jwObj q hq n 0) = jwObj q hq n 1 := by
  refine Karoubi.ext rfl ?_
  rw [eqToHom_refl, Category.comp_id, Category.id_comp]
  apply Mat_.hom_ext
  rintro ⟨⟩ ⟨⟩
  apply Underlying.hom_ext
  apply Envelope.hom_ext
  erw [Envelope.toHom_pi_map, twist_of_mem (R := k) 1 (jw_mem_parity q n 0)]
  rw [zmod2_add_self, sign_zero, one_smul, show (1 : ZMod 2) * (0 + 0) = 0 from rfl, sign_zero,
    one_smul]
  rfl

theorem classJw_one (n : ℕ) : classJw q hq (n, 1) = Zπ.π • classJw q hq (n, 0) := by
  rw [classJw, classJw, SKar.π_smul_mk_algebra, pi_jwObj]

end StringDiagrams.OddTemperleyLieb

end
