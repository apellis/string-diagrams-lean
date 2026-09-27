import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Data.Fintype.BigOperators

/-!
# Endomorphism algebras of finite direct sums, as matrices of morphisms

For a finite family of objects `X : ι → C` of an `R`-linear category, `MatEnd X` is the
`R`-algebra `⨁_{i, j} Hom(X i, X j)` of matrices of morphisms, with multiplication given by
composition,

`(f * g) i l = ∑ j, g i j ≫ f j l`,

so that `f * g` is "`g` first, then `f`", as in `CategoryTheory.End`. It is the endomorphism
algebra of the direct sum `⨁ i, X i` (`MatEnd.biproductAlgEquiv`), but it is defined without
requiring the direct sum to exist in `C`: it is the category algebra of the full subcategory on
the family `X`, and algebra homomorphisms into it are the natural targets of actions of
algebras with a complete set of orthogonal idempotents (`MatEnd.single i i (𝟙 _)`).

## Main definitions and results

* `MatEnd X` with its `Ring` and `Algebra R` structures; the matrix units `MatEnd.single i j f`
  (`single_mul_single`, `single_mul_single_of_ne`, `one_eq_sum_single`, `eq_sum_single`); the
  diagonal idempotents `MatEnd.idem i` (`idem_mul_idem`, `sum_idem`, `idem_mul_mul_idem`).
* `MatEnd.map F X : MatEnd X →ₐ[R] MatEnd (F.obj ∘ X)` for an `R`-linear functor `F`.
* `MatEnd.entry R i j : MatEnd X →ₗ[R] (X i ⟶ X j)`.
* `MatEnd.biproductAlgEquiv : End (⨁ X) ≃ₐ[R] MatEnd X`, sending `π i ≫ ι i` to `idem i`.
* `MatEnd.blockMap`: block-diagonal assembly of algebra homomorphisms `A →ₐ[R] MatEnd (X t)`,
  along a functorial linear transport of the blocks (`MatEnd.BlockTransport`), into
  `MatEnd Z` for a family `Z` indexed by `κ × ι`.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Preadditive

universe w v v' u u' u₁ u₂ u₃ u₄

/-- Matrices of morphisms between the members of a family of objects. -/
@[nolint unusedArguments]
def MatEnd {C : Type u} [Category.{v} C] {ι : Type u₁} (_X : ι → C) : Type (max u₁ v) :=
  ∀ i j : ι, _X i ⟶ _X j

namespace MatEnd

variable {R : Type w} [CommRing R] {C : Type u} [Category.{v} C] [Preadditive C]
  {ι : Type u₁} {X : ι → C}

instance : AddCommGroup (MatEnd X) := inferInstanceAs (AddCommGroup (∀ i j : ι, X i ⟶ X j))

instance [CategoryTheory.Linear R C] : Module R (MatEnd X) :=
  inferInstanceAs (Module R (∀ i j : ι, X i ⟶ X j))

instance : CoeFun (MatEnd X) (fun _ => ∀ i j : ι, X i ⟶ X j) := ⟨id⟩

omit [Preadditive C] in
@[ext] theorem ext {f g : MatEnd X} (h : ∀ i j, f i j = g i j) : f = g :=
  funext fun i => funext fun j => h i j

@[simp] theorem add_apply (f g : MatEnd X) (i j : ι) : (f + g) i j = f i j + g i j := rfl
@[simp] theorem sub_apply (f g : MatEnd X) (i j : ι) : (f - g) i j = f i j - g i j := rfl
@[simp] theorem neg_apply (f : MatEnd X) (i j : ι) : (-f) i j = -f i j := rfl
@[simp] theorem zero_apply (i j : ι) : (0 : MatEnd X) i j = 0 := rfl
@[simp] theorem smul_apply [CategoryTheory.Linear R C] (r : R) (f : MatEnd X) (i j : ι) :
    (r • f) i j = r • f i j := rfl

theorem sum_apply {α : Type*} (s : Finset α) (f : α → MatEnd X) (i j : ι) :
    (∑ a ∈ s, f a) i j = ∑ a ∈ s, f a i j := by
  induction s using Finset.cons_induction with
  | empty => rfl
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, add_apply, ih]

/-! ## Entries -/

variable (R) in
/-- The entry at `(i, j)`, as a linear map. -/
def entry [CategoryTheory.Linear R C] (i j : ι) : MatEnd X →ₗ[R] (X i ⟶ X j) where
  toFun f := f i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem entry_apply [CategoryTheory.Linear R C] (i j : ι) (f : MatEnd X) :
    entry R i j f = f i j := rfl

variable [DecidableEq ι]

/-! ## Matrix units -/

/-- The matrix whose only nonzero entry is `f : X i ⟶ X j`, at `(i, j)`. -/
def single (i j : ι) (f : X i ⟶ X j) : MatEnd X := fun i' j' =>
  if h : i' = i ∧ j' = j then eqToHom (congrArg X h.1) ≫ f ≫ eqToHom (congrArg X h.2.symm)
  else 0

@[simp] theorem single_apply_self (i j : ι) (f : X i ⟶ X j) : single i j f i j = f := by
  simp [single]

theorem single_apply_of_ne {i j i' j' : ι} (f : X i ⟶ X j) (h : ¬ (i' = i ∧ j' = j)) :
    single i j f i' j' = 0 := by
  simp [single, h]

theorem single_apply (i j : ι) (f : X i ⟶ X j) (i' j' : ι) :
    single i j f i' j' = if h : i' = i ∧ j' = j then
      eqToHom (congrArg X h.1) ≫ f ≫ eqToHom (congrArg X h.2.symm) else 0 := rfl

@[simp] theorem single_zero (i j : ι) : single i j (0 : X i ⟶ X j) = 0 := by
  ext i' j'; simp [single_apply]

theorem single_add (i j : ι) (f g : X i ⟶ X j) :
    single i j (f + g) = single i j f + single i j g := by
  ext i' j'; simp only [single_apply, add_apply]; split_ifs <;> simp

theorem single_sub (i j : ι) (f g : X i ⟶ X j) :
    single i j (f - g) = single i j f - single i j g := by
  ext i' j'; simp only [single_apply, sub_apply]; split_ifs <;> simp

theorem single_neg (i j : ι) (f : X i ⟶ X j) : single i j (-f) = -single i j f := by
  ext i' j'; simp only [single_apply, neg_apply]; split_ifs <;> simp

theorem single_smul [CategoryTheory.Linear R C] (i j : ι) (r : R) (f : X i ⟶ X j) :
    single i j (r • f) = r • single i j f := by
  ext i' j'; simp only [single_apply, smul_apply]; split_ifs <;> simp

theorem single_sum {α : Type*} (s : Finset α) (i j : ι) (f : α → (X i ⟶ X j)) :
    single i j (∑ a ∈ s, f a) = ∑ a ∈ s, single i j (f a) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, single_add, ih]

variable (R) in
/-- The matrix unit `single i j` as a linear map. -/
def singleₗ [CategoryTheory.Linear R C] (i j : ι) : (X i ⟶ X j) →ₗ[R] MatEnd X where
  toFun := single i j
  map_add' := single_add i j
  map_smul' r f := single_smul i j r f

@[simp] theorem singleₗ_apply [CategoryTheory.Linear R C] (i j : ι) (f : X i ⟶ X j) :
    singleₗ R i j f = single i j f := rfl

theorem single_eqToHom {i j j' : ι} (f : X i ⟶ X j) (h : j = j') :
    single i j' (f ≫ eqToHom (congrArg X h)) = single i j f := by
  subst h; simp

theorem single_eqToHom_left {i i' j : ι} (f : X i ⟶ X j) (h : i' = i) :
    single i' j (eqToHom (congrArg X h) ≫ f) = single i j f := by
  subst h; simp

/-! ## The ring structure -/

instance : One (MatEnd X) := ⟨fun i j => if h : i = j then eqToHom (congrArg X h) else 0⟩

theorem one_apply (i j : ι) :
    (1 : MatEnd X) i j = if h : i = j then eqToHom (congrArg X h) else 0 := rfl

@[simp] theorem one_apply_self (i : ι) : (1 : MatEnd X) i i = 𝟙 _ := by simp [one_apply]

theorem one_apply_of_ne {i j : ι} (h : i ≠ j) : (1 : MatEnd X) i j = 0 := by
  simp [one_apply, h]

variable [Fintype ι]

instance : Mul (MatEnd X) := ⟨fun f g i l => ∑ j, g i j ≫ f j l⟩

omit [DecidableEq ι] in
theorem mul_apply (f g : MatEnd X) (i l : ι) : (f * g) i l = ∑ j, g i j ≫ f j l := rfl

omit [DecidableEq ι] in
private theorem mul_assoc' (f g h : MatEnd X) : f * g * h = f * (g * h) := by
  ext i l
  simp only [mul_apply, comp_sum, sum_comp, Category.assoc]
  exact Finset.sum_comm

private theorem one_mul' (f : MatEnd X) : 1 * f = f := by
  ext i l
  simp only [mul_apply, one_apply, comp_dite, Limits.comp_zero]
  rw [Finset.sum_dite_eq' Finset.univ l]
  simp

private theorem mul_one' (f : MatEnd X) : f * 1 = f := by
  ext i l
  simp only [mul_apply, one_apply, dite_comp, Limits.zero_comp]
  rw [Finset.sum_dite_eq Finset.univ i]
  simp

instance : Ring (MatEnd X) :=
  { (inferInstance : AddCommGroup (MatEnd X)) with
    mul := (· * ·)
    one := 1
    mul_assoc := mul_assoc'
    one_mul := one_mul'
    mul_one := mul_one'
    left_distrib := fun f g h => by
      ext i l; simp only [mul_apply, add_apply, add_comp, Finset.sum_add_distrib]
    right_distrib := fun f g h => by
      ext i l; simp only [mul_apply, add_apply, comp_add, Finset.sum_add_distrib]
    zero_mul := fun f => by ext i l; simp [mul_apply]
    mul_zero := fun f => by ext i l; simp [mul_apply] }

instance [CategoryTheory.Linear R C] : Algebra R (MatEnd X) :=
  Algebra.ofModule
    (fun r f g => by
      ext i l; simp only [mul_apply, smul_apply, Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => Linear.comp_smul _ _ _ _ _ _)
    (fun r f g => by
      ext i l; simp only [mul_apply, smul_apply, Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => Linear.smul_comp _ _ _ _ _ _)

theorem single_mul_single (i j l : ι) (f : X i ⟶ X j) (g : X j ⟶ X l) :
    single j l g * single i j f = single i l (f ≫ g) := by
  ext i' l'
  rw [mul_apply]
  by_cases hi : i' = i
  · subst hi
    by_cases hl : l' = l
    · subst hl
      rw [Finset.sum_eq_single j]
      · simp
      · intro j' _ hj'; rw [single_apply_of_ne _ (fun h => hj' h.2), Limits.zero_comp]
      · simp
    · rw [single_apply_of_ne _ (fun h => hl h.2)]
      exact Finset.sum_eq_zero fun j' _ => by
        rw [single_apply_of_ne (i' := j') (j' := l') g (fun h => hl h.2), Limits.comp_zero]
  · rw [single_apply_of_ne _ (fun h => hi h.1)]
    exact Finset.sum_eq_zero fun j' _ => by
      rw [single_apply_of_ne (i' := i') f (fun h => hi h.1), Limits.zero_comp]

theorem single_mul_single_of_ne {i j j' l : ι} (f : X i ⟶ X j) (g : X j' ⟶ X l) (h : j ≠ j') :
    single j' l g * single i j f = 0 := by
  ext i' l'
  rw [mul_apply, zero_apply]
  refine Finset.sum_eq_zero fun m _ => ?_
  by_cases hm : m = j
  · subst hm; rw [single_apply_of_ne (i' := m) g (fun h' => h h'.1), Limits.comp_zero]
  · rw [single_apply_of_ne (j' := m) f (fun h' => hm h'.2), Limits.zero_comp]

theorem one_eq_sum_single : (1 : MatEnd X) = ∑ i, single i i (𝟙 (X i)) := by
  ext i j
  rw [sum_apply, Finset.sum_eq_single i]
  · by_cases h : i = j
    · subst h; simp
    · rw [one_apply_of_ne h, single_apply_of_ne _ (fun h' => h h'.2.symm)]
  · intro b _ hb; exact single_apply_of_ne _ (fun h => hb h.1.symm)
  · simp

theorem eq_sum_single (f : MatEnd X) : f = ∑ i, ∑ j, single i j (f i j) := by
  ext i' j'
  rw [sum_apply, Finset.sum_eq_single i', sum_apply, Finset.sum_eq_single j']
  · simp
  · intro b _ hb; exact single_apply_of_ne _ (fun h => hb h.2.symm)
  · simp
  · intro b _ hb
    rw [sum_apply]
    exact Finset.sum_eq_zero fun c _ => single_apply_of_ne _ (fun h => hb h.1.symm)
  · simp

/-! ## Diagonal idempotents -/

/-- The diagonal idempotent `single i i (𝟙 (X i))`: the projection onto the summand `X i`. -/
abbrev idem (i : ι) : MatEnd X := single i i (𝟙 (X i))

theorem idem_mul_idem (i : ι) : (idem i : MatEnd X) * idem i = idem i := by
  rw [single_mul_single, Category.comp_id]

theorem isIdempotentElem_idem (i : ι) : IsIdempotentElem (idem i : MatEnd X) :=
  idem_mul_idem i

theorem idem_mul_idem_of_ne {i j : ι} (h : i ≠ j) : (idem i : MatEnd X) * idem j = 0 :=
  single_mul_single_of_ne _ _ (Ne.symm h)

/-- The diagonal idempotents form a complete set of orthogonal idempotents. -/
theorem sum_idem : ∑ i, (idem i : MatEnd X) = 1 := one_eq_sum_single.symm

/-- The corners of `MatEnd X`: `idem j * f * idem i` is the entry `f i j`, as a matrix unit. -/
theorem idem_mul_mul_idem (f : MatEnd X) (i j : ι) :
    idem j * f * idem i = single i j (f i j) := by
  ext i' j'
  simp only [mul_apply, single_apply]
  by_cases hi : i' = i
  · subst hi
    by_cases hj : j' = j
    · subst hj
      rw [Finset.sum_eq_single i', Finset.sum_eq_single j'] <;>
        simp +contextual [Ne.symm]
    · simp [hj]
  · simp [hi]

theorem single_mul {i j : ι} (f : X i ⟶ X j) (g : MatEnd X) (i' l : ι) :
    (g * single i j f) i' l = if h : i' = i then eqToHom (congrArg X h) ≫ f ≫ g j l else 0 := by
  rw [mul_apply, Finset.sum_eq_single j]
  · by_cases h : i' = i
    · subst h; simp
    · simp [single_apply, h]
  · intro b _ hb; rw [single_apply_of_ne _ (fun h => hb h.2), Limits.zero_comp]
  · simp

theorem mul_single {j l : ι} (f : X j ⟶ X l) (g : MatEnd X) (i l' : ι) :
    (single j l f * g) i l' = if h : l' = l then g i j ≫ f ≫ eqToHom (congrArg X h.symm) else 0 := by
  rw [mul_apply, Finset.sum_eq_single j]
  · by_cases h : l' = l
    · subst h; simp
    · simp [single_apply, h]
  · intro b _ hb; rw [single_apply_of_ne _ (fun h => hb h.1), Limits.comp_zero]
  · simp

/-! ## Functoriality -/

section Map

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [CategoryTheory.Linear R C]
  [CategoryTheory.Linear R D]

variable (R) in
/-- An `R`-linear functor induces an algebra homomorphism of matrix algebras, entrywise. -/
def map (F : C ⥤ D) [F.Additive] [F.Linear R] (X : ι → C) :
    MatEnd X →ₐ[R] MatEnd (fun i => F.obj (X i)) where
  toFun f i j := F.map (f i j)
  map_one' := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [one_apply_of_ne h]
  map_mul' f g := by
    ext i l
    change F.map (∑ j, g i j ≫ f j l) = ∑ j, F.map (g i j) ≫ F.map (f j l)
    simp [Functor.map_sum]
  map_zero' := by ext; simp
  map_add' f g := by
    ext i j
    change F.map (f i j + g i j) = F.map (f i j) + F.map (g i j)
    simp
  commutes' r := by
    ext i j
    simp only [Algebra.algebraMap_eq_smul_one, smul_apply, Functor.map_smul]
    by_cases h : i = j
    · subst h; simp
    · simp [one_apply_of_ne h]

@[simp] theorem map_apply (F : C ⥤ D) [F.Additive] [F.Linear R] (f : MatEnd X) (i j : ι) :
    map R F X f i j = F.map (f i j) := rfl

theorem map_single (F : C ⥤ D) [F.Additive] [F.Linear R] (i j : ι) (f : X i ⟶ X j) :
    map R F X (single i j f) = single i j (F.map f) := by
  ext i' j'
  rw [map_apply]
  by_cases h : i' = i ∧ j' = j
  · obtain ⟨rfl, rfl⟩ := h; simp
  · rw [single_apply_of_ne _ h, single_apply_of_ne _ h, F.map_zero]

end Map

/-! ## The endomorphism algebra of a direct sum -/

section Biproduct

variable [CategoryTheory.Linear R C] {J : Type} [Fintype J] [DecidableEq J] {Y : J → C}
  [Limits.HasBiproduct Y]

open Limits

variable (R Y) in
/-- **The endomorphism algebra of a finite direct sum is the matrix algebra of morphisms**:
`f ↦ (ι i ≫ f ≫ π j)_{i, j}`. -/
def biproductAlgEquiv : End (⨁ Y) ≃ₐ[R] MatEnd Y where
  toFun f i j := biproduct.ι Y i ≫ f ≫ biproduct.π Y j
  invFun m := ∑ i, ∑ j, biproduct.π Y i ≫ m i j ≫ biproduct.ι Y j
  left_inv f := by
    change ∑ i, ∑ j, biproduct.π Y i ≫ (biproduct.ι Y i ≫ f ≫ biproduct.π Y j) ≫
      biproduct.ι Y j = f
    conv_rhs => rw [← Category.id_comp f, ← Category.comp_id f, ← biproduct.total]
    simp only [sum_comp, comp_sum, Category.assoc]
    exact Finset.sum_comm
  right_inv m := by
    ext i j
    change biproduct.ι Y i ≫ (∑ i', ∑ j', biproduct.π Y i' ≫ m i' j' ≫ biproduct.ι Y j') ≫
      biproduct.π Y j = m i j
    simp only [sum_comp, comp_sum, Category.assoc]
    rw [Finset.sum_eq_single i (fun a _ ha => Finset.sum_eq_zero fun b _ => by
      rw [biproduct.ι_π_ne_assoc Y (Ne.symm ha), Limits.zero_comp]) (by simp)]
    rw [Finset.sum_eq_single j (fun b _ hb => by
      rw [biproduct.ι_π_ne _ hb, Limits.comp_zero, Limits.comp_zero, Limits.comp_zero]) (by simp)]
    rw [biproduct.ι_π_self_assoc, biproduct.ι_π_self, Category.comp_id]
  map_mul' f g := by
    ext i l
    change biproduct.ι Y i ≫ (g ≫ f) ≫ biproduct.π Y l =
      ∑ j, (biproduct.ι Y i ≫ g ≫ biproduct.π Y j) ≫ biproduct.ι Y j ≫ f ≫ biproduct.π Y l
    conv_lhs => rw [← Category.comp_id g, ← biproduct.total]
    simp only [sum_comp, comp_sum, Category.assoc]
  map_add' f g := by
    ext i j
    change biproduct.ι Y i ≫ ((f : ⨁ Y ⟶ ⨁ Y) + g) ≫ biproduct.π Y j =
      biproduct.ι Y i ≫ f ≫ biproduct.π Y j + biproduct.ι Y i ≫ g ≫ biproduct.π Y j
    rw [add_comp, comp_add]
  commutes' r := by
    ext i j
    change biproduct.ι Y i ≫ (r • 𝟙 (⨁ Y)) ≫ biproduct.π Y j = r • (1 : MatEnd Y) i j
    rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, biproduct.ι_π, one_apply]

@[simp] theorem biproductAlgEquiv_apply (f : End (⨁ Y)) (i j : J) :
    biproductAlgEquiv R Y f i j = biproduct.ι Y i ≫ f ≫ biproduct.π Y j := rfl

theorem biproductAlgEquiv_symm_apply (m : MatEnd Y) :
    (biproductAlgEquiv R Y).symm m = ∑ i, ∑ j, biproduct.π Y i ≫ m i j ≫ biproduct.ι Y j :=
  rfl

/-- The projection `π i ≫ ι i` onto the summand `Y i` corresponds to the diagonal idempotent. -/
theorem biproductAlgEquiv_π_ι (i : J) :
    biproductAlgEquiv R Y (biproduct.π Y i ≫ biproduct.ι Y i) = idem i := by
  ext i' j'
  rw [biproductAlgEquiv_apply, idem, single_apply]
  simp only [Category.assoc]
  by_cases h : i' = i ∧ j' = i
  · obtain ⟨rfl, rfl⟩ := h; simp
  · rw [dite_eq_right h]
    by_cases hi : i' = i
    · subst hi
      rw [biproduct.ι_π_self_assoc, biproduct.ι_π_ne _ (fun e => h ⟨rfl, e.symm⟩)]
    · rw [biproduct.ι_π_ne_assoc Y hi, Limits.zero_comp]

end Biproduct

/-! ## Block-diagonal assembly -/

section Block

variable [CategoryTheory.Linear R C] {C' : Type u'} [Category.{v'} C'] [Preadditive C']
  [CategoryTheory.Linear R C'] {Idx : Type u₂} {κ : Type u₃} {ι' : Type u₄} [Fintype Idx]
  [DecidableEq Idx] [Fintype κ] [Fintype ι'] [DecidableEq ι'] {Z : Idx → C}

variable (R) in
/-- A functorial `R`-linear transport of morphisms `X t i ⟶ X t j` of the block `t` to
morphisms `Z (e (t, i)) ⟶ Z (e (t, j))`, compatible with composition and identities (for
instance, the placement of 2-morphisms between fixed 1-morphisms). -/
structure BlockTransport (e : κ × ι' ≃ Idx) (Y : κ → ι' → C') (Z : Idx → C) where
  /-- The transport maps. -/
  F : ∀ t i j, (Y t i ⟶ Y t j) →ₗ[R] (Z (e (t, i)) ⟶ Z (e (t, j)))
  map_comp : ∀ t i j l (f : Y t i ⟶ Y t j) (g : Y t j ⟶ Y t l),
    F t i l (f ≫ g) = F t i j f ≫ F t j l g
  map_id : ∀ t i, F t i i (𝟙 _) = 𝟙 _

variable {e : κ × ι' ≃ Idx} {Y : κ → ι' → C'} {A : Type*} [Ring A] [Algebra R A]

/-- The underlying linear map of `blockMap`. -/
def blockMapₗ (T : BlockTransport R e Y Z) (φ : ∀ t, A →ₐ[R] MatEnd (Y t)) :
    A →ₗ[R] MatEnd Z where
  toFun r := ∑ t, ∑ i, ∑ j, single (e (t, i)) (e (t, j)) (T.F t i j (φ t r i j))
  map_add' r r' := by
    simp only [map_add, add_apply, single_add, ← Finset.sum_add_distrib]
  map_smul' c r := by
    simp only [map_smul, smul_apply, single_smul, Finset.smul_sum, RingHom.id_apply]

theorem blockMapₗ_apply (T : BlockTransport R e Y Z) (φ : ∀ t, A →ₐ[R] MatEnd (Y t)) (r : A) :
    blockMapₗ T φ r = ∑ t, ∑ i, ∑ j, single (e (t, i)) (e (t, j)) (T.F t i j (φ t r i j)) :=
  rfl

theorem blockMapₗ_one (T : BlockTransport R e Y Z) (φ : ∀ t, A →ₐ[R] MatEnd (Y t)) :
    blockMapₗ T φ 1 = 1 := by
  rw [blockMapₗ_apply, one_eq_sum_single]
  have h1 : ∀ t i j, single (e (t, i)) (e (t, j)) (T.F t i j ((φ t 1) i j)) =
      if i = j then single (e (t, i)) (e (t, i)) (𝟙 _) else 0 := by
    intro t i j
    rw [map_one]
    split_ifs with h
    · subst h; rw [one_apply_self, T.map_id]
    · rw [one_apply_of_ne h, map_zero, single_zero]
  simp only [h1, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← Fintype.sum_prod_type', ← e.sum_comp]

theorem blockMapₗ_mul (T : BlockTransport R e Y Z) (φ : ∀ t, A →ₐ[R] MatEnd (Y t))
    (r r' : A) : blockMapₗ T φ (r * r') = blockMapₗ T φ r * blockMapₗ T φ r' := by
  simp only [blockMapₗ_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hcol : ∀ i m, ∑ t', ∑ i', ∑ j', single (e (t', i')) (e (t', j'))
      (T.F t' i' j' (φ t' r i' j')) * single (e (t, i)) (e (t, m)) (T.F t i m (φ t r' i m)) =
      ∑ j, single (e (t, i)) (e (t, j)) (T.F t i m (φ t r' i m) ≫ T.F t m j (φ t r m j)) := by
    intro i m
    rw [Finset.sum_eq_single t]
    · rw [Finset.sum_eq_single m]
      · exact Finset.sum_congr rfl fun j _ => single_mul_single _ _ _ _ _
      · intro i' _ hi'
        exact Finset.sum_eq_zero fun j' _ => single_mul_single_of_ne _ _
          (fun h => hi' (Prod.ext_iff.1 (e.injective h)).2.symm)
      · simp
    · intro t' _ ht'
      refine Finset.sum_eq_zero fun i' _ => Finset.sum_eq_zero fun j' _ => ?_
      exact single_mul_single_of_ne _ _ (fun h => ht' (Prod.ext_iff.1 (e.injective h)).1.symm)
    · simp
  simp only [hcol]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, mul_apply, map_sum, single_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [T.map_comp]

/-- **Block-diagonal assembly** of algebra homomorphisms `φ t : A →ₐ[R] MatEnd (Y t)` along
functorial transports: `r ↦ ∑_t ∑_{i, j} single (e (t, i)) (e (t, j)) (F t i j (φ t r i j))`. -/
def blockMap (T : BlockTransport R e Y Z) (φ : ∀ t, A →ₐ[R] MatEnd (Y t)) :
    A →ₐ[R] MatEnd Z :=
  AlgHom.ofLinearMap (blockMapₗ T φ) (blockMapₗ_one T φ) (blockMapₗ_mul T φ)

theorem blockMap_apply (T : BlockTransport R e Y Z) (φ : ∀ t, A →ₐ[R] MatEnd (Y t)) (r : A) :
    blockMap T φ r = ∑ t, ∑ i, ∑ j, single (e (t, i)) (e (t, j)) (T.F t i j (φ t r i j)) :=
  rfl

/-- The entries of `blockMap` within a block are the transported entries. -/
theorem blockMap_apply_block (T : BlockTransport R e Y Z) (φ : ∀ t, A →ₐ[R] MatEnd (Y t))
    (r : A) (t : κ) (i j : ι') :
    blockMap T φ r (e (t, i)) (e (t, j)) = T.F t i j (φ t r i j) := by
  rw [blockMap_apply, sum_apply, Finset.sum_eq_single t]
  · rw [sum_apply, Finset.sum_eq_single i]
    · rw [sum_apply, Finset.sum_eq_single j]
      · exact single_apply_self _ _ _
      · intro j' _ hj'
        exact single_apply_of_ne _ (fun h => hj' (Prod.ext_iff.1 (e.injective h.2.symm)).2)
      · simp
    · intro i' _ hi'
      rw [sum_apply]
      exact Finset.sum_eq_zero fun j' _ =>
        single_apply_of_ne _ (fun h => hi' (Prod.ext_iff.1 (e.injective h.1.symm)).2)
    · simp
  · intro t' _ ht'
    rw [sum_apply]
    refine Finset.sum_eq_zero fun i' _ => ?_
    rw [sum_apply]
    exact Finset.sum_eq_zero fun j' _ =>
      single_apply_of_ne _ (fun h => ht' (Prod.ext_iff.1 (e.injective h.1.symm)).1)
  · simp

/-- The entries of `blockMap` between different blocks vanish. -/
theorem blockMap_apply_ne (T : BlockTransport R e Y Z) (φ : ∀ t, A →ₐ[R] MatEnd (Y t))
    (r : A) {t t' : κ} (i j : ι') (h : t ≠ t') :
    blockMap T φ r (e (t, i)) (e (t', j)) = 0 := by
  rw [blockMap_apply, sum_apply]
  refine Finset.sum_eq_zero fun t'' _ => ?_
  rw [sum_apply]
  refine Finset.sum_eq_zero fun i' _ => ?_
  rw [sum_apply]
  refine Finset.sum_eq_zero fun j' _ => single_apply_of_ne _ fun hh => h ?_
  have h1 := (Prod.ext_iff.1 (e.injective hh.1)).1
  have h2 := (Prod.ext_iff.1 (e.injective hh.2)).1
  exact h1.trans h2.symm

/-- If every `φ t` sends `r` to the diagonal idempotent at `i`, then `blockMap` sends `r` to
the sum of the diagonal idempotents at the `e (t, i)`. -/
theorem blockMap_eq_of_idem (T : BlockTransport R e Y Z) (φ : ∀ t, A →ₐ[R] MatEnd (Y t))
    (r : A) (i : ι') (h : ∀ t, φ t r = idem i) :
    blockMap T φ r = ∑ t, idem (e (t, i)) := by
  rw [blockMap_apply]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [h t, idem, Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single i]
    · rw [single_apply_self, T.map_id]
    · intro j _ hj
      rw [single_apply_of_ne _ (fun h' => hj h'.2), map_zero, single_zero]
    · simp
  · intro i' _ hi'
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [single_apply_of_ne _ (fun h' => hi' h'.1), map_zero, single_zero]
  · simp

end Block

end MatEnd

end StringDiagrams

end
