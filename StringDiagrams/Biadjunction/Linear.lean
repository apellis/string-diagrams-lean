import StringDiagrams.Biadjunction.Cyclic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Mates and cyclicity in locally linear bicategories

Mathlib (at the pinned version) has no notion of a bicategory enriched in abelian groups or
modules. We introduce two `Prop`-valued classes on a bicategory whose hom categories are
preadditive (resp. `R`-linear), in the style of Mathlib's `MonoidalPreadditive` and
`MonoidalLinear`:

* `LocallyPreadditive B`: whiskering is additive;
* `LocallyLinear R B`: whiskering is `R`-linear.

Under these hypotheses the mates are additive (resp. `R`-linear) equivalences
(`Biadjunction.rightMateAddEquiv`, `Biadjunction.rightMateLinearEquiv`, and the left
versions), the cyclic 2-morphisms form a submodule (`Biadjunction.cyclicSubmodule`,
`IsCyclic.add`, `IsCyclic.smul`, ...), and the traces are additive and linear
(`rightTrace_add`, `rightTrace_smul`, ...).
-/

namespace StringDiagrams

open CategoryTheory Bicategory

universe w v u u'

variable {B : Type u} [Bicategory.{w, v} B]

/-- A bicategory with preadditive hom categories in which whiskering is additive. -/
class LocallyPreadditive (B : Type u) [Bicategory.{w, v} B]
    [∀ a b : B, Preadditive (a ⟶ b)] : Prop where
  whiskerLeft_add : ∀ {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η θ : g ⟶ h),
    f ◁ (η + θ) = f ◁ η + f ◁ θ
  add_whiskerRight : ∀ {a b c : B} {f g : a ⟶ b} (η θ : f ⟶ g) (h : b ⟶ c),
    (η + θ) ▷ h = η ▷ h + θ ▷ h

/-- A bicategory with `R`-linear hom categories in which whiskering is `R`-linear. -/
class LocallyLinear (R : Type u') [Semiring R] (B : Type u) [Bicategory.{w, v} B]
    [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)] : Prop where
  whiskerLeft_smul : ∀ {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (r : R) (η : g ⟶ h),
    f ◁ (r • η) = r • (f ◁ η)
  smul_whiskerRight : ∀ {a b c : B} {f g : a ⟶ b} (r : R) (η : f ⟶ g) (h : b ⟶ c),
    (r • η) ▷ h = r • (η ▷ h)

attribute [simp] LocallyPreadditive.whiskerLeft_add LocallyPreadditive.add_whiskerRight
attribute [simp] LocallyLinear.whiskerLeft_smul LocallyLinear.smul_whiskerRight

section Preadditive

variable [∀ a b : B, Preadditive (a ⟶ b)] [LocallyPreadditive B]

/-- Left whiskering as an additive map. -/
@[simps!]
def whiskerLeftAddHom {a b c : B} (f : a ⟶ b) (g h : b ⟶ c) : (g ⟶ h) →+ (f ≫ g ⟶ f ≫ h) :=
  AddMonoidHom.mk' (f ◁ ·) (LocallyPreadditive.whiskerLeft_add f)

/-- Right whiskering as an additive map. -/
@[simps!]
def whiskerRightAddHom {a b c : B} (f g : a ⟶ b) (h : b ⟶ c) : (f ⟶ g) →+ (f ≫ h ⟶ g ≫ h) :=
  AddMonoidHom.mk' (· ▷ h) (fun η θ => LocallyPreadditive.add_whiskerRight η θ h)

@[simp]
theorem whiskerLeft_zero' {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} : f ◁ (0 : g ⟶ h) = 0 :=
  (whiskerLeftAddHom f g h).map_zero

@[simp]
theorem zero_whiskerRight' {a b c : B} {f g : a ⟶ b} (h : b ⟶ c) : (0 : f ⟶ g) ▷ h = 0 :=
  (whiskerRightAddHom f g h).map_zero

@[simp]
theorem whiskerLeft_neg' {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    f ◁ (-η) = -(f ◁ η) :=
  (whiskerLeftAddHom f g h).map_neg η

@[simp]
theorem neg_whiskerRight' {a b c : B} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    (-η) ▷ h = -(η ▷ h) :=
  (whiskerRightAddHom f g h).map_neg η

namespace Biadjunction

variable {a b : B} {f f' : a ⟶ b} {g g' : b ⟶ a}

theorem rightMate_add (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (α β : f ⟶ f') :
    rightMate P P' (α + β) = rightMate P P' α + rightMate P P' β := by
  simp only [rightMate_apply, LocallyPreadditive.whiskerLeft_add,
    LocallyPreadditive.add_whiskerRight, Preadditive.add_comp, Preadditive.comp_add]

theorem leftMate_add (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (α β : f ⟶ f') :
    leftMate P P' (α + β) = leftMate P P' α + leftMate P P' β := by
  simp only [leftMate_apply, LocallyPreadditive.whiskerLeft_add,
    LocallyPreadditive.add_whiskerRight, Preadditive.add_comp, Preadditive.comp_add]

/-- The right mate as an additive equivalence. -/
def rightMateAddEquiv (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') : (f ⟶ f') ≃+ (g' ⟶ g) :=
  { rightMate P P' with map_add' := rightMate_add P P' }

/-- The left mate as an additive equivalence. -/
def leftMateAddEquiv (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') : (f ⟶ f') ≃+ (g' ⟶ g) :=
  { leftMate P P' with map_add' := leftMate_add P P' }

@[simp]
theorem rightMateAddEquiv_apply (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (α : f ⟶ f') :
    rightMateAddEquiv P P' α = rightMate P P' α := rfl

@[simp]
theorem leftMateAddEquiv_apply (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (α : f ⟶ f') :
    leftMateAddEquiv P P' α = leftMate P P' α := rfl

@[simp]
theorem rightMate_zero (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') : rightMate P P' 0 = 0 :=
  (rightMateAddEquiv P P').map_zero

@[simp]
theorem leftMate_zero (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') : leftMate P P' 0 = 0 :=
  (leftMateAddEquiv P P').map_zero

theorem rightMate_neg (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (α : f ⟶ f') :
    rightMate P P' (-α) = -rightMate P P' α :=
  (rightMateAddEquiv P P').map_neg α

theorem leftMate_neg (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (α : f ⟶ f') :
    leftMate P P' (-α) = -leftMate P P' α :=
  (leftMateAddEquiv P P').map_neg α

theorem rightMate_sub (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (α β : f ⟶ f') :
    rightMate P P' (α - β) = rightMate P P' α - rightMate P P' β :=
  (rightMateAddEquiv P P').map_sub α β

theorem leftMate_sub (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (α β : f ⟶ f') :
    leftMate P P' (α - β) = leftMate P P' α - leftMate P P' β :=
  (leftMateAddEquiv P P').map_sub α β

theorem rightMate_sum {ι : Type*} (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (s : Finset ι)
    (α : ι → (f ⟶ f')) : rightMate P P' (∑ i ∈ s, α i) = ∑ i ∈ s, rightMate P P' (α i) :=
  map_sum (rightMateAddEquiv P P') α s

theorem leftMate_sum {ι : Type*} (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (s : Finset ι)
    (α : ι → (f ⟶ f')) : leftMate P P' (∑ i ∈ s, α i) = ∑ i ∈ s, leftMate P P' (α i) :=
  map_sum (leftMateAddEquiv P P') α s

theorem isCyclic_zero (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') : IsCyclic P P' 0 := by
  rw [IsCyclic, rightMate_zero, leftMate_zero]

theorem IsCyclic.add {P : f ⊣⊢ g} {P' : f' ⊣⊢ g'} {α β : f ⟶ f'} (hα : IsCyclic P P' α)
    (hβ : IsCyclic P P' β) : IsCyclic P P' (α + β) := by
  rw [IsCyclic, rightMate_add, leftMate_add, hα.eq, hβ.eq]

theorem IsCyclic.neg {P : f ⊣⊢ g} {P' : f' ⊣⊢ g'} {α : f ⟶ f'} (hα : IsCyclic P P' α) :
    IsCyclic P P' (-α) := by
  rw [IsCyclic, rightMate_neg, leftMate_neg, hα.eq]

theorem IsCyclic.sub {P : f ⊣⊢ g} {P' : f' ⊣⊢ g'} {α β : f ⟶ f'} (hα : IsCyclic P P' α)
    (hβ : IsCyclic P P' β) : IsCyclic P P' (α - β) := by
  rw [IsCyclic, rightMate_sub, leftMate_sub, hα.eq, hβ.eq]

theorem IsCyclic.sum {ι : Type*} {P : f ⊣⊢ g} {P' : f' ⊣⊢ g'} (s : Finset ι)
    {α : ι → (f ⟶ f')} (h : ∀ i ∈ s, IsCyclic P P' (α i)) :
    IsCyclic P P' (∑ i ∈ s, α i) := by
  rw [IsCyclic, rightMate_sum, leftMate_sum]
  exact Finset.sum_congr rfl fun i hi => (h i hi).eq

/-- The cyclic 2-morphisms form an additive subgroup. -/
def cyclicAddSubgroup (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') : AddSubgroup (f ⟶ f') where
  carrier := {α | IsCyclic P P' α}
  add_mem' := IsCyclic.add
  zero_mem' := isCyclic_zero P P'
  neg_mem' := IsCyclic.neg

@[simp]
theorem mem_cyclicAddSubgroup (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (α : f ⟶ f') :
    α ∈ cyclicAddSubgroup P P' ↔ IsCyclic P P' α := Iff.rfl

theorem rightTrace_add (P : f ⊣⊢ g) (α β : f ⟶ f) :
    rightTrace P (α + β) = rightTrace P α + rightTrace P β := by
  simp only [rightTrace, LocallyPreadditive.add_whiskerRight, Preadditive.add_comp,
    Preadditive.comp_add]

theorem leftTrace_add (P : f ⊣⊢ g) (α β : f ⟶ f) :
    leftTrace P (α + β) = leftTrace P α + leftTrace P β := by
  simp only [leftTrace, LocallyPreadditive.whiskerLeft_add, Preadditive.add_comp,
    Preadditive.comp_add]

/-- The right trace as an additive map. -/
@[simps!]
def rightTraceAddHom (P : f ⊣⊢ g) : (f ⟶ f) →+ (𝟙 a ⟶ 𝟙 a) :=
  AddMonoidHom.mk' (rightTrace P) (rightTrace_add P)

/-- The left trace as an additive map. -/
@[simps!]
def leftTraceAddHom (P : f ⊣⊢ g) : (f ⟶ f) →+ (𝟙 b ⟶ 𝟙 b) :=
  AddMonoidHom.mk' (leftTrace P) (leftTrace_add P)

end Biadjunction

end Preadditive

section Linear

variable (R : Type u') [Semiring R] [∀ a b : B, Preadditive (a ⟶ b)]
  [∀ a b : B, Linear R (a ⟶ b)] [LocallyPreadditive B] [LocallyLinear R B]

namespace Biadjunction

variable {R} {a b : B} {f f' : a ⟶ b} {g g' : b ⟶ a}

omit [LocallyPreadditive B] in
theorem rightMate_smul (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (r : R) (α : f ⟶ f') :
    rightMate P P' (r • α) = r • rightMate P P' α := by
  simp only [rightMate_apply, LocallyLinear.whiskerLeft_smul, LocallyLinear.smul_whiskerRight,
    Linear.smul_comp, Linear.comp_smul]

omit [LocallyPreadditive B] in
theorem leftMate_smul (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (r : R) (α : f ⟶ f') :
    leftMate P P' (r • α) = r • leftMate P P' α := by
  simp only [leftMate_apply, LocallyLinear.whiskerLeft_smul, LocallyLinear.smul_whiskerRight,
    Linear.smul_comp, Linear.comp_smul]

variable (R)

/-- The right mate as an `R`-linear equivalence. -/
def rightMateLinearEquiv (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') : (f ⟶ f') ≃ₗ[R] (g' ⟶ g) :=
  { rightMate P P' with
    map_add' := rightMate_add P P'
    map_smul' := rightMate_smul P P' }

/-- The left mate as an `R`-linear equivalence. -/
def leftMateLinearEquiv (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') : (f ⟶ f') ≃ₗ[R] (g' ⟶ g) :=
  { leftMate P P' with
    map_add' := leftMate_add P P'
    map_smul' := leftMate_smul P P' }

@[simp]
theorem rightMateLinearEquiv_apply (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (α : f ⟶ f') :
    rightMateLinearEquiv R P P' α = rightMate P P' α := rfl

@[simp]
theorem leftMateLinearEquiv_apply (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (α : f ⟶ f') :
    leftMateLinearEquiv R P P' α = leftMate P P' α := rfl

variable {R}

omit [LocallyPreadditive B] in
theorem IsCyclic.smul {P : f ⊣⊢ g} {P' : f' ⊣⊢ g'} {α : f ⟶ f'} (hα : IsCyclic P P' α)
    (r : R) : IsCyclic P P' (r • α) := by
  rw [IsCyclic, rightMate_smul, leftMate_smul, hα.eq]

variable (R) in
/-- The cyclic 2-morphisms form an `R`-submodule. -/
def cyclicSubmodule (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') : Submodule R (f ⟶ f') where
  carrier := {α | IsCyclic P P' α}
  add_mem' := IsCyclic.add
  zero_mem' := isCyclic_zero P P'
  smul_mem' r _ h := IsCyclic.smul h r

@[simp]
theorem mem_cyclicSubmodule (P : f ⊣⊢ g) (P' : f' ⊣⊢ g') (α : f ⟶ f') :
    α ∈ cyclicSubmodule R P P' ↔ IsCyclic P P' α := Iff.rfl

omit [LocallyPreadditive B] in
theorem rightTrace_smul (P : f ⊣⊢ g) (r : R) (α : f ⟶ f) :
    rightTrace P (r • α) = r • rightTrace P α := by
  simp only [rightTrace, LocallyLinear.smul_whiskerRight, Linear.smul_comp, Linear.comp_smul]

omit [LocallyPreadditive B] in
theorem leftTrace_smul (P : f ⊣⊢ g) (r : R) (α : f ⟶ f) :
    leftTrace P (r • α) = r • leftTrace P α := by
  simp only [leftTrace, LocallyLinear.whiskerLeft_smul, Linear.smul_comp, Linear.comp_smul]

variable (R)

/-- The right trace as an `R`-linear map. -/
def rightTraceLinearMap (P : f ⊣⊢ g) : (f ⟶ f) →ₗ[R] (𝟙 a ⟶ 𝟙 a) where
  toFun := rightTrace P
  map_add' := rightTrace_add P
  map_smul' := rightTrace_smul P

/-- The left trace as an `R`-linear map. -/
def leftTraceLinearMap (P : f ⊣⊢ g) : (f ⟶ f) →ₗ[R] (𝟙 b ⟶ 𝟙 b) where
  toFun := leftTrace P
  map_add' := leftTrace_add P
  map_smul' := leftTrace_smul P

end Biadjunction

end Linear

end StringDiagrams
