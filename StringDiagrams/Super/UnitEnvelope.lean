import StringDiagrams.Super.MonoidalUniversal
import StringDiagrams.Super.Superalgebra

/-!
# The Π-envelope of the unit supercategory `I`

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Example 4.8.

The monoidal supercategory `I` (one object, endomorphisms `k` in even parity;
`UnitSupercat k`) has Π-envelope `I_π` with two objects `Π⁰` and `Π¹`
(`UnitEnvelope.objEquiv`); each `Hom_{I_π}(Πᵃ, Πᵇ)` is free of rank one with basis
`1_a^b` (`UnitEnvelope.one`, `UnitEnvelope.homEquiv`), of parity `a + b`
(`UnitEnvelope.one_mem`). The tensor product satisfies `Πᵇ ⊗ Πᵃ = Π^{a+b}`
(`UnitEnvelope.tensorObj_eq`) and `1_b^d ⊗ 1_a^c = (-1)^{(a+c)b} 1_{a+b}^{c+d}`
(`UnitEnvelope.toHom_one_tensor_one`, for the paper's tensor product `superTensorHom`).

By the universal property (Lemma 4.7(i), monoidal case: `Envelope.extendMonoidal`), the
monoidal superfunctor `I → SVec` sending the object to `k` (`UnitSupercat.toSVecMonoidal`)
extends to a monoidal superfunctor `F̃ : I_π → SVec` (`UnitEnvelope.extendSVec`), for the
Π-supercategory structure `Π V` = `V` with the opposite grading, `ζ_V` the identity function,
of `SVec` (Example 1.8). It sends `Πᵃ ↦ Πᵃ k` (`extendSVec_obj_zero`, `extendSVec_obj_one`) and
`1_a^b` to the identity function `id_a^b : Πᵃ k → Πᵇ k` (`extendSVec_map_one`); its coherence
maps `Πᵇ k ⊗ Πᵃ k → Π^{a+b} k` send `1 ⊗ 1 ↦ 1` (`extendSVec_μ_one_tmul_one`). The signs are
consistent because `id_b^d ⊗ id_a^c` sends `1 ⊗ 1 ↦ (-1)^{(a+c)b} 1 ⊗ 1`
(`superTensorHom_extendSVec_one`).

The paper assumes that `k` is a field; the statements here hold over any commutative ring.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory MonoidalCategory Supercategory TensorProduct

universe u

namespace UnitEnvelope

variable (k : Type u) [CommRing k]

/-- The Π-envelope `I_π` of the unit supercategory. -/
abbrev Iπ : Type := Envelope k (UnitSupercat k)

/-- The object `Πᵃ` of `I_π`. -/
def P (a : ZMod 2) : Iπ k := ⟨a, ()⟩

/-- **Example 4.8.** `I_π` has exactly two objects, `Π⁰` and `Π¹`. -/
def objEquiv : Iπ k ≃ ZMod 2 where
  toFun X := X.par
  invFun a := P k a
  left_inv _ := rfl
  right_inv _ := rfl

variable {k}

/-- The basis morphism `1_a^b : Πᵃ ⟶ Πᵇ`. -/
def one (a b : ZMod 2) : P k a ⟶ P k b := Envelope.ofHom (SuperalgebraCat.ofElem (1 : k))

/-- **Example 4.8.** `1_a^b` has parity `a + b`. -/
theorem one_mem (a b : ZMod 2) : one (k := k) a b ∈ parity (R := k) (P k a) (P k b) (a + b) := by
  rw [Envelope.mem_parity_iff]
  show (1 : k) ∈ trivialGrading k (a + b + (a + b))
  rw [zmod2_add_self, trivialGrading_zero]; trivial

/-- **Example 4.8.** `Hom_{I_π}(Πᵃ, Πᵇ)` is free of rank one with basis `1_a^b`. -/
def homEquiv (a b : ZMod 2) : (P k a ⟶ P k b) ≃ₗ[k] k where
  toFun f := SuperalgebraCat.toElem (Envelope.toHom f)
  invFun r := r • one a b
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f := by
    show SuperalgebraCat.toElem (Envelope.toHom f) • (Envelope.ofHom (SuperalgebraCat.ofElem 1) :
      P k a ⟶ P k b) = f
    exact Envelope.hom_ext (SuperalgebraCat.hom_ext (by
      show SuperalgebraCat.toElem (Envelope.toHom f) * 1 = _; rw [mul_one]))
  right_inv r := by
    show r * 1 = r
    rw [mul_one]

@[simp] theorem homEquiv_symm_apply (a b : ZMod 2) (r : k) :
    (homEquiv (k := k) a b).symm r = r • one a b := rfl

/-- **Example 4.8.** `Πᵇ ⊗ Πᵃ = Π^{a+b}`. -/
theorem tensorObj_eq (a b : ZMod 2) : P k b ⊗ P k a = P k (a + b) :=
  Envelope.ext (add_comm b a) rfl

/-- **Example 4.8.** `1_b^d ⊗ 1_a^c = (-1)^{(a+c)b} 1_{a+b}^{c+d}`, for the paper's tensor
product `f ⊗ g = (f ⊗ 1) ∘ (1 ⊗ g)` (`superTensorHom`): on the underlying scalars. -/
theorem toHom_one_tensor_one (a b c d : ZMod 2) :
    SuperalgebraCat.toElem (Envelope.toHom
      (MonoidalSupercategory.superTensorHom (one (k := k) b d) (one a c))) =
      sign k ((a + c) * b) := by
  rw [Envelope.toHom_superTensorHom (pf := 0) (pg := 0) (UnitSupercat.mem_parity_zero _)
    (UnitSupercat.mem_parity_zero _)]
  show sign k (b * 0 + 0 * c + b * c + b * a) * (1 * 1) = _
  rw [mul_one, mul_one]
  congr 1
  ring

/-! ## The extension `F̃ : I_π → SVec` -/

variable (k) in
/-- **Example 4.8.** The monoidal superfunctor `F̃ : I_π → SVec` extending the monoidal
superfunctor `I → SVec` sending the object to `k` (Lemma 4.7(i), monoidal case). -/
def extendSVec : MonoidalSuperfunctor k (Envelope.extend k (UnitSupercat.toSVec k)) :=
  Envelope.extendMonoidal (UnitSupercat.toSVecMonoidal (k := k))

local notation "F̃" => Envelope.extend k (UnitSupercat.toSVec k)

theorem extendSVec_obj_zero : (F̃).obj (P k 0) = SVec.unit := rfl

theorem extendSVec_obj_one : (F̃).obj (P k 1) = SVec.piObj SVec.unit := rfl

variable (k) in
/-- The element `1 ∈ Πᵃ k`. -/
def oneElt : ∀ a : ZMod 2, ((F̃).obj (P k a)).carrier
  | ⟨0, _⟩ => (1 : k)
  | ⟨1, _⟩ => (1 : k)
  | ⟨_ + 2, h⟩ => absurd h (by simp)

theorem oneElt_mem (a : ZMod 2) : oneElt k a ∈ ((F̃).obj (P k a)).part a := by
  rcases parity_eq_zero_or_one a with rfl | rfl
  · rw [SVec.mem_part_zero_iff]; rfl
  · show (1 : k) ∈ (SVec.piObj SVec.unit).part 1
    rw [SVec.piObj_part, SVec.zmod2_one_add_one, SVec.mem_part_zero_iff]; rfl

/-- **Example 4.8.** `F̃(1_a^b)` is the identity function `id_a^b : Πᵃ k → Πᵇ k`. -/
theorem extendSVec_map_one (a b : ZMod 2) : (F̃).map (one a b) (oneElt k a) = oneElt k b := by
  rcases parity_eq_zero_or_one a with rfl | rfl <;>
  rcases parity_eq_zero_or_one b with rfl | rfl <;>
  · show (1 : k) • (1 : k) = 1
    exact one_smul k _

omit [CommRing k] in
theorem unit_whiskerLeft_one_tmul [CommRing k] {W W' : SVec k} {q : ZMod 2} {g : W ⟶ W'}
    (hg : g ∈ parity (R := k) W W' q) (w : W) :
    ((SVec.unit : SVec k) ◁ g) ((1 : k) ⊗ₜ w) = (1 : k) ⊗ₜ g w := by
  rw [SVec.whiskerLeft_tmul' (p := 0) hg (by rw [SVec.mem_part_zero_iff]; rfl), zero_mul,
    sign_zero, one_smul]

/-- **Example 4.8.** The coherence maps `Πᵇ k ⊗ Πᵃ k → Π^{a+b} k` of `F̃` send `1 ⊗ 1 ↦ 1`. -/
theorem extendSVec_μ_one_tmul_one (a b : ZMod 2) :
    ((extendSVec k).μIso (P k b) (P k a)).hom (oneElt k b ⊗ₜ oneElt k a) = oneElt k (b + a) := by
  have h := unit_whiskerLeft_one_tmul (Envelope.ζPow_hom_mem (R := k) a (SVec.unit : SVec k))
  rcases parity_eq_zero_or_one a with rfl | rfl <;>
  rcases parity_eq_zero_or_one b with rfl | rfl <;>
  · simp only [extendSVec, Envelope.extendMonoidal_μIso_hom, Envelope.extendμ, SVec.comp_apply]
    erw [SVec.whiskerRight_tmul', h]
    show (1 : k) * 1 = 1
    rw [mul_one]

/-- **Example 4.8.** The signs are consistent: `id_b^d ⊗ id_a^c` sends
`1 ⊗ 1 ↦ (-1)^{(a+c)b} 1 ⊗ 1` (the paper's tensor product of linear maps). -/
theorem superTensorHom_extendSVec_one (a b c d : ZMod 2) :
    MonoidalSupercategory.superTensorHom ((F̃).map (one b d)) ((F̃).map (one a c))
        (oneElt k b ⊗ₜ oneElt k a) = sign k ((a + c) * b) • (oneElt k d ⊗ₜ oneElt k c) := by
  rw [SVec.superTensorHom_tmul _ (map_mem (F̃) (one_mem a c)) (oneElt_mem b),
    extendSVec_map_one, extendSVec_map_one]

end UnitEnvelope

end StringDiagrams

end
