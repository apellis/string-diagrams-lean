import StringDiagrams.Super.BalancedTensor

/-!
# The super-opposite superalgebra

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Remark 1.3: for a superalgebra `B`, the supercategory `B^{sop}` has the same object as `B`
(Example 1.2(ii)) and the new composition law `a • b := (-1)^{|a||b|} b ∘ a`.

`SuperOpposite ℬ` is the superalgebra with the same underlying superspace as `B` and the
product `a • b := (-1)^{|a||b|} b a` for homogeneous `a`, `b` (`SuperOpposite.mul_of_mem`),
extended bilinearly (`SuperOpposite.instRing`, `SuperOpposite.instAlgebra`); its grading is that
of `B` (`SuperOpposite.grading`, `SuperOpposite.instGradedAlgebra`). The supercategory `B^{sop}`
is `SuperalgebraCat (SuperOpposite.grading ℬ)` (`SuperOppositeCat`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory SuperBimodule

universe u v

variable {k : Type u} [CommRing k] {B : Type v} [Ring B] [Algebra k B]

/-- The super-opposite superalgebra of `B` (Brundan–Ellis, Remark 1.3): the same superspace
with the product `a • b := (-1)^{|a||b|} b a`. (The grading `ℬ` is part of the type.) -/
@[nolint unusedArguments]
def SuperOpposite (_ℬ : ZMod 2 → Submodule k B) : Type v := B

namespace SuperOpposite

variable (ℬ : ZMod 2 → Submodule k B) [GradedAlgebra ℬ]

instance : AddCommGroup (SuperOpposite ℬ) := inferInstanceAs (AddCommGroup B)

instance : Module k (SuperOpposite ℬ) := inferInstanceAs (Module k B)

/-- The product `a • b := Σ_{p, q} (-1)^{pq} b_q a_p`, as a bilinear map on `B`. -/
def mulBilin : B →ₗ[k] B →ₗ[k] B :=
  LinearMap.mk₂ k (fun a b => b * algProj ℬ 0 a + (algProj ℬ 0 b - algProj ℬ 1 b) * algProj ℬ 1 a)
    (fun a a' b => by simp only [map_add, mul_add]; abel)
    (fun r a b => by simp only [map_smul, mul_smul_comm, smul_add])
    (fun a b b' => by simp only [map_add, add_mul, add_sub_add_comm]; abel)
    (fun r b b' => by simp only [map_smul, smul_mul_assoc, ← smul_sub, smul_add])

theorem mulBilin_apply (a b : B) :
    mulBilin ℬ a b = b * algProj ℬ 0 a + (algProj ℬ 0 b - algProj ℬ 1 b) * algProj ℬ 1 a := rfl

/-- The product of homogeneous elements: `a • b = (-1)^{|a||b|} b a`. -/
theorem mulBilin_of_mem {p q : ZMod 2} {a b : B} (ha : a ∈ ℬ p) (hb : b ∈ ℬ q) :
    mulBilin ℬ a b = sign k (p * q) • (b * a) := by
  rw [mulBilin_apply]
  rcases parity_eq_zero_or_one p with rfl | rfl <;> rcases parity_eq_zero_or_one q with rfl | rfl <;>
    simp [algProj_of_mem ℬ ha, algProj_of_mem ℬ hb, algProj_of_mem_ne ℬ ha, algProj_of_mem_ne ℬ hb,
      sub_mul, add_mul]

theorem mulBilin_mem {p q : ZMod 2} {a b : B} (ha : a ∈ ℬ p) (hb : b ∈ ℬ q) :
    mulBilin ℬ a b ∈ ℬ (p + q) := by
  rw [mulBilin_of_mem ℬ ha hb, add_comm]
  exact Submodule.smul_mem _ _ (SetLike.GradedMul.mul_mem hb ha)

theorem mulBilin_assoc (a b c : B) :
    mulBilin ℬ (mulBilin ℬ a b) c = mulBilin ℬ a (mulBilin ℬ b c) := by
  induction a using alg_induction_on ℬ with
  | zero => simp
  | add a a' ha ha' => simp only [map_add, LinearMap.add_apply, ha, ha']
  | hom p a ha =>
    induction b using alg_induction_on ℬ with
    | zero => simp
    | add b b' hb hb' => simp only [map_add, LinearMap.add_apply, hb, hb']
    | hom q b hb =>
      induction c using alg_induction_on ℬ with
      | zero => simp
      | add c c' hc hc' => simp only [map_add, hc, hc']
      | hom r c hc =>
        rw [mulBilin_of_mem ℬ ha hb, mulBilin_of_mem ℬ hb hc, map_smul, LinearMap.smul_apply,
          map_smul, mulBilin_of_mem ℬ (SetLike.GradedMul.mul_mem hb ha) hc,
          mulBilin_of_mem ℬ ha (SetLike.GradedMul.mul_mem hc hb), smul_smul, smul_smul,
          ← sign_add, ← sign_add, mul_assoc]
        congr 2
        ring

instance instRing : Ring (SuperOpposite ℬ) :=
  { (inferInstance : AddCommGroup (SuperOpposite ℬ)) with
    mul := fun a b => mulBilin ℬ a b
    one := (1 : B)
    mul_assoc := mulBilin_assoc ℬ
    one_mul := fun b => by
      change mulBilin ℬ 1 b = b
      rw [mulBilin_apply, algProj_of_mem ℬ SetLike.GradedOne.one_mem,
        algProj_of_mem_ne ℬ SetLike.GradedOne.one_mem (by decide), mul_one, mul_zero, add_zero]
    mul_one := fun a => by
      change mulBilin ℬ a 1 = a
      rw [mulBilin_apply, algProj_of_mem ℬ SetLike.GradedOne.one_mem,
        algProj_of_mem_ne ℬ SetLike.GradedOne.one_mem (by decide), sub_zero, one_mul, one_mul,
        algProj_add_algProj]
    left_distrib := fun a b c => map_add (mulBilin ℬ a) b c
    right_distrib := fun a b c => by
      change mulBilin ℬ (a + b) c = mulBilin ℬ a c + mulBilin ℬ b c
      rw [map_add, LinearMap.add_apply]
    zero_mul := fun a => by
      change mulBilin ℬ 0 a = 0
      rw [map_zero, LinearMap.zero_apply]
    mul_zero := fun a => map_zero (mulBilin ℬ a) }

theorem mul_def (a b : SuperOpposite ℬ) : a * b = mulBilin ℬ a b := rfl

theorem one_def : (1 : SuperOpposite ℬ) = (1 : B) := rfl

/-- An element of `B`, viewed in `B^{sop}`. -/
def op (b : B) : SuperOpposite ℬ := b

/-- An element of `B^{sop}`, viewed in `B`. -/
def unop (b : SuperOpposite ℬ) : B := b

/-- `a • b = (-1)^{|a||b|} b a` for homogeneous `a`, `b`. -/
theorem mul_of_mem {p q : ZMod 2} {a b : B} (ha : a ∈ ℬ p) (hb : b ∈ ℬ q) :
    op ℬ a * op ℬ b = op ℬ (sign k (p * q) • (b * a)) :=
  (mul_def ℬ a b).trans (mulBilin_of_mem ℬ ha hb)

instance instAlgebra : Algebra k (SuperOpposite ℬ) :=
  Algebra.ofModule
    (fun r a b => by
      change mulBilin ℬ (r • a) b = r • mulBilin ℬ a b
      rw [map_smul, LinearMap.smul_apply])
    (fun r a b => by
      change mulBilin ℬ a (r • b) = r • mulBilin ℬ a b
      rw [map_smul])

/-- The grading of `B^{sop}`: that of `B`. -/
def grading : ZMod 2 → Submodule k (SuperOpposite ℬ) := ℬ

theorem mem_grading_iff {p : ZMod 2} {b : B} : (b : SuperOpposite ℬ) ∈ grading ℬ p ↔ b ∈ ℬ p :=
  Iff.rfl

instance : SetLike.GradedMonoid (grading ℬ) where
  one_mem := show (1 : B) ∈ ℬ 0 from SetLike.GradedOne.one_mem
  mul_mem _ _ _ _ ha hb := mulBilin_mem ℬ ha hb

/-- `B^{sop}` is a superalgebra. -/
instance instGradedAlgebra : GradedAlgebra (grading ℬ) :=
  { (inferInstance : SetLike.GradedMonoid (grading ℬ)),
    (inferInstance : DirectSum.Decomposition ℬ) with }

end SuperOpposite

/-- **Brundan–Ellis, Remark 1.3.** The supercategory `B^{sop}`: one object, with composition
`a • b := (-1)^{|a||b|} b ∘ a`. -/
abbrev SuperOppositeCat (ℬ : ZMod 2 → Submodule k B) [GradedAlgebra ℬ] : Type :=
  SuperalgebraCat (SuperOpposite.grading ℬ)

/-- Composition in `B^{sop}`: `f ≫ g = g • f = (-1)^{|f||g|} f g` for homogeneous `f`, `g`
(product in `B`). -/
theorem SuperOppositeCat.comp_of_mem (ℬ : ZMod 2 → Submodule k B) [GradedAlgebra ℬ]
    {X Y Z : SuperOppositeCat ℬ} {p q : ZMod 2} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : f ∈ parity (R := k) X Y p) (hg : g ∈ parity (R := k) Y Z q) :
    SuperOpposite.unop ℬ (SuperalgebraCat.toElem (f ≫ g)) =
      sign k (p * q) • (SuperOpposite.unop ℬ (SuperalgebraCat.toElem f) *
        SuperOpposite.unop ℬ (SuperalgebraCat.toElem g)) := by
  have hf' : SuperOpposite.unop ℬ (SuperalgebraCat.toElem f) ∈ ℬ p := hf
  have hg' : SuperOpposite.unop ℬ (SuperalgebraCat.toElem g) ∈ ℬ q := hg
  change SuperOpposite.mulBilin ℬ (SuperOpposite.unop ℬ (SuperalgebraCat.toElem g))
    (SuperOpposite.unop ℬ (SuperalgebraCat.toElem f)) = _
  rw [SuperOpposite.mulBilin_of_mem ℬ hg' hf', mul_comm q p]

end StringDiagrams

end
