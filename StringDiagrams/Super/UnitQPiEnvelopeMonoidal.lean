import StringDiagrams.Super.UnitQPiEnvelope
import StringDiagrams.Super.QPiMonoidalEnvelope
import StringDiagrams.Super.MonoidalPi

/-!
# The monoidal structure of the (Q, Π)-envelope of the unit graded supercategory

The `(Q, Π)`-analogue of J. Brundan, A. P. Ellis, *Monoidal supercategories*,
arXiv:1603.05928v3, Example 4.8, for the `(Q, Π)`-envelope of Definition 6.8 with the
horizontal composition of Definition 6.10 (one-object case,
`StringDiagrams.Super.QPiMonoidalEnvelope`).

The unit supercategory `I` (`UnitSupercat k`), graded in degree `0`
(`UnitSupercat.instGradedSupercategory`), is a strict graded monoidal supercategory
(`UnitSupercat.instGradedMonoidalSupercategory`). Hence `I_{q,π}` is a strict graded monoidal
supercategory (`UnitQPiEnvelope.monoidalSupercategory`,
`UnitQPiEnvelope.gradedMonoidalSupercategory`, `UnitQPiEnvelope.isStrict`) and a monoidal
Π-supercategory (`Envelope.instMonoidalPiSupercategory`, with `π = Q⁰Π¹`). Its tensor product
satisfies `Q^nΠ^b ⊗ Q^mΠ^a = Q^{m+n}Π^{a+b}` (`UnitQPiEnvelope.tensorObj_P`,
`UnitQPiEnvelope.tensorObj_eq`), unit `Q⁰Π⁰` (`UnitQPiEnvelope.tensorUnit_eq`), and

  `1^{l,d}_{n,b} ⊗ 1^{j,c}_{m,a} = (-1)^{(a+c)b} 1^{l+j,d+c}_{n+m,b+a}`

for the paper's tensor product `f ⊗ g = (f ⊗ 1) ∘ (1 ⊗ g)`
(`UnitQPiEnvelope.one_superTensorHom_one`; this is the sign `(-1)^{b|x| + |y|c + bc + ab}` of Definition 6.10 with `|x| = |y| = 0`, and
reduces to Example 4.8's `1_b^d ⊗ 1_a^c = (-1)^{(a+c)b} 1_{a+b}^{c+d}` when `m = n = j = l = 0`).
For Mathlib's `f ⊗ₘ g = (1 ⊗ g) ∘ (f ⊗ 1)` the sign is `(-1)^{(a+c)d}`
(`UnitQPiEnvelope.one_tensorHom_one`). The degree shifts enter without signs.

The paper assumes that `k` is a field; the statements here hold over any commutative ring.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory MonoidalCategory Supercategory GradedSupercategory

universe u

namespace UnitSupercat

variable {k : Type u} [CommRing k]

/-- The unit supercategory `I`, graded in degree `0`, is a graded monoidal supercategory. -/
instance instGradedMonoidalSupercategory : GradedMonoidalSupercategory k (UnitSupercat k) where
  whiskerLeft_mem_degree _ _ _ _ _ h := h
  whiskerRight_mem_degree _ h := h
  associator_hom_mem_degree _ _ _ := id_mem_degree (R := k) _
  leftUnitor_hom_mem_degree _ := id_mem_degree (R := k) _
  rightUnitor_hom_mem_degree _ := id_mem_degree (R := k) _

end UnitSupercat

namespace UnitQPiEnvelope

open SuperalgebraCat

variable (k : Type u) [CommRing k]

/-- `I_{q,π}` is a monoidal supercategory (Definition 6.10, one-object case). -/
theorem monoidalSupercategory : MonoidalSupercategory k (Iqπ k) := inferInstance

/-- `I_{q,π}` is a graded monoidal supercategory. -/
theorem gradedMonoidalSupercategory : GradedMonoidalSupercategory k (Iqπ k) := inferInstance

/-- `I_{q,π}` is a strict monoidal supercategory. -/
theorem isStrict : MonoidalSupercategory.IsStrict (Iqπ k) := inferInstance

variable {k}

/-- `Q^nΠ^b ⊗ Q^mΠ^a = Q^{n+m}Π^{b+a}`. -/
theorem tensorObj_P (n : ℤ) (b : ZMod 2) (m : ℤ) (a : ZMod 2) :
    P k n b ⊗ P k m a = P k (n + m) (b + a) := rfl

/-- `Q^nΠ^b ⊗ Q^mΠ^a = Q^{m+n}Π^{a+b}`, as printed in Definition 6.10. -/
theorem tensorObj_eq (n : ℤ) (b : ZMod 2) (m : ℤ) (a : ZMod 2) :
    P k n b ⊗ P k m a = P k (m + n) (a + b) := by
  rw [tensorObj_P, add_comm n, add_comm b]

/-- The unit object of `I_{q,π}` is `Q⁰Π⁰`. -/
theorem tensorUnit_eq : 𝟙_ (Iqπ k) = P k 0 0 := rfl

/-- **Definition 6.10** for `I_{q,π}`:
`1^{l,d}_{n,b} ⊗ 1^{j,c}_{m,a} = (-1)^{(a+c)b} 1^{l+j,d+c}_{n+m,b+a}`, for the paper's tensor
product `f ⊗ g = (f ⊗ 1) ∘ (1 ⊗ g)` (`superTensorHom`). -/
theorem one_superTensorHom_one (n : ℤ) (b : ZMod 2) (l : ℤ) (d : ZMod 2) (m : ℤ) (a : ZMod 2)
    (j : ℤ) (c : ZMod 2) :
    MonoidalSupercategory.superTensorHom (one (k := k) n b l d) (one m a j c) =
      sign k ((a + c) * b) • one (n + m) (b + a) (l + j) (d + c) := by
  refine (QPiEnvelope.ofHom_superTensorHom_ofHom (R := k) (X := P k n b) (X' := P k l d)
    (Y := P k m a) (Y' := P k j c) (y := ofElem (1 : k)) (x := ofElem (1 : k))
    (UnitSupercat.mem_parity_zero _) (UnitSupercat.mem_parity_zero _)).trans ?_
  show sign k (b * 0 + 0 * c + b * c + a * b) • _ = _
  congr 1
  · congr 1; ring
  · exact Envelope.hom_ext (QEnvelope.hom_ext (SuperalgebraCat.hom_ext (𝒜 := trivialGrading k)
      (mul_one (1 : k))))

/-- Mathlib's tensor product `f ⊗ₘ g = (1 ⊗ g) ∘ (f ⊗ 1)` of basis morphisms of `I_{q,π}`:
`1^{l,d}_{n,b} ⊗ₘ 1^{j,c}_{m,a} = (-1)^{(a+c)d} 1^{l+j,d+c}_{n+m,b+a}`. -/
theorem one_tensorHom_one (n : ℤ) (b : ZMod 2) (l : ℤ) (d : ZMod 2) (m : ℤ) (a : ZMod 2)
    (j : ℤ) (c : ZMod 2) :
    one (k := k) n b l d ⊗ₘ one m a j c =
      sign k ((a + c) * d) • one (n + m) (b + a) (l + j) (d + c) := by
  rw [MonoidalSupercategory.tensorHom_eq_superTensorHom (R := k) (one_mem n b l d)
    (one_mem m a j c), koszulSign_smul (R := k), one_superTensorHom_one, smul_smul,
    ← sign_add]
  congr 2
  revert a b c d; decide

end UnitQPiEnvelope

end StringDiagrams

end
