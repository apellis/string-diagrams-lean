import StringDiagrams.Super.QEnvelope
import StringDiagrams.Super.Superalgebra

/-!
# The (Q, Π)-envelope of the unit graded supercategory

The `(Q, Π)`-analogue of J. Brundan, A. P. Ellis, *Monoidal supercategories*,
arXiv:1603.05928v3, Example 4.8, for the `(Q, Π)`-envelope of Definition 6.8.

The unit supercategory `I` (one object, endomorphisms `k` in even parity; `UnitSupercat k`)
is a graded supercategory concentrated in degree `0` (`UnitSupercat.instGradedSupercategory`).
Its `(Q, Π)`-envelope `I_{q,π}` has objects `Q^mΠ^a`, `m ∈ ℤ`, `a ∈ ℤ/2`
(`UnitQPiEnvelope.objEquiv`); each `Hom_{I_{q,π}}(Q^mΠ^a, Q^nΠ^b)` is free of rank one with
basis `1^{n,b}_{m,a}` (`UnitQPiEnvelope.one`, `UnitQPiEnvelope.homEquiv`), of parity `a + b`
and degree `n - m` (`UnitQPiEnvelope.one_mem`, `UnitQPiEnvelope.one_mem_degree`), and
`1^{l,c}_{n,b} ∘ 1^{n,b}_{m,a} = 1^{l,c}_{m,a}` (`UnitQPiEnvelope.one_comp_one`). The functors
`Q`, `Q⁻¹` and `Π` shift the labels (`UnitQPiEnvelope.Q_obj`, `UnitQPiEnvelope.Qinv_obj`,
`UnitQPiEnvelope.pi_obj`), and `σ`, `σ̄`, `ζ` are the basis morphisms
(`UnitQPiEnvelope.σ_hom`, `UnitQPiEnvelope.σbar_hom`, `UnitQPiEnvelope.ζ_hom`).

The paper assumes that `k` is a field; the statements here hold over any commutative ring.
The horizontal (monoidal) composition of `I_{q,π}` is not formalized: the `(Q, Π)`-envelope
of Definition 6.8 is a graded `(Q, Π)`-supercategory, not a monoidal one.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory GradedSupercategory

universe u

/-! ## The trivial grading of the unit supercategory -/

namespace UnitSupercat

variable (k : Type u) [CommRing k]

/-- The grading of `k` concentrated in degree `0`. -/
def trivialDegree : ℤ → Submodule k k := fun n => if n = 0 then ⊤ else ⊥

@[simp] theorem trivialDegree_zero : trivialDegree k 0 = ⊤ := if_pos rfl

theorem trivialDegree_of_ne {n : ℤ} (h : n ≠ 0) : trivialDegree k n = ⊥ := if_neg h

theorem isInternal_trivialDegree : DirectSum.IsInternal (trivialDegree k) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨?_, ?_⟩
  · rw [iSupIndep_def]
    intro n
    by_cases h : n = 0
    · subst h
      refine Disjoint.mono_right ?_ disjoint_bot_right
      refine iSup_le fun m => iSup_le fun hm => ?_
      rw [trivialDegree_of_ne k hm]
    · rw [trivialDegree_of_ne k h]
      exact disjoint_bot_left
  · exact eq_top_iff.2 ((trivialDegree_zero k).symm.le.trans (le_iSup (trivialDegree k) 0))

variable {k}

theorem mem_trivialDegree_iff {n : ℤ} {r : k} : r ∈ trivialDegree k n ↔ n = 0 ∨ r = 0 := by
  by_cases h : n = 0
  · simp [h]
  · simp [trivialDegree_of_ne k h, h]

/-- The unit supercategory `I` is a graded supercategory concentrated in degree `0`. -/
instance instGradedSupercategory : GradedSupercategory k (UnitSupercat k) where
  degree _ _ := trivialDegree k
  isInternal_degree _ _ := isInternal_trivialDegree k
  proj_mem_degree {_ _ n f} p hf := by
    rcases (mem_trivialDegree_iff (r := f)).1 hf with h | h
    · exact (mem_trivialDegree_iff (r := proj k p f)).2 (Or.inl h)
    · refine (mem_trivialDegree_iff (r := proj k p f)).2 (Or.inr ?_)
      show proj k p f = 0
      rw [show f = 0 from h, map_zero]
  id_mem_degree _ := (mem_trivialDegree_iff (r := 1)).2 (Or.inl rfl)
  comp_mem_degree {_ _ _ m n f g} hf hg := by
    rcases (mem_trivialDegree_iff (r := f)).1 hf with h | h
    · rcases (mem_trivialDegree_iff (r := g)).1 hg with h' | h'
      · exact (mem_trivialDegree_iff (r := f ≫ g)).2 (Or.inl (by rw [h, h', add_zero]))
      · refine (mem_trivialDegree_iff (r := f ≫ g)).2 (Or.inr ?_)
        show SuperalgebraCat.toElem g * SuperalgebraCat.toElem f = 0
        rw [show SuperalgebraCat.toElem g = 0 from h', zero_mul]
    · refine (mem_trivialDegree_iff (r := f ≫ g)).2 (Or.inr ?_)
      show SuperalgebraCat.toElem g * SuperalgebraCat.toElem f = 0
      rw [show SuperalgebraCat.toElem f = 0 from h, mul_zero]

theorem mem_degree_iff {X Y : UnitSupercat k} {n : ℤ} {f : X ⟶ Y} :
    f ∈ degree (R := k) X Y n ↔ n = 0 ∨ f = 0 :=
  mem_trivialDegree_iff

end UnitSupercat

/-! ## The `(Q, Π)`-envelope `I_{q,π}` -/

namespace UnitQPiEnvelope

open SuperalgebraCat

variable (k : Type u) [CommRing k]

/-- The `(Q, Π)`-envelope `I_{q,π}` of the unit graded supercategory. -/
abbrev Iqπ : Type := QPiEnvelope k (UnitSupercat k)

/-- The object `Q^mΠ^a` of `I_{q,π}`. -/
def P (m : ℤ) (a : ZMod 2) : Iqπ k := ⟨a, ⟨m, ()⟩⟩

/-- `I_{q,π}` has objects `Q^mΠ^a`, `m ∈ ℤ`, `a ∈ ℤ/2`. -/
def objEquiv : Iqπ k ≃ ℤ × ZMod 2 where
  toFun X := (X.obj.shift, X.par)
  invFun p := P k p.1 p.2
  left_inv _ := rfl
  right_inv _ := rfl

variable {k}

/-- The basis morphism `1^{n,b}_{m,a} : Q^mΠ^a ⟶ Q^nΠ^b`. -/
def one (m : ℤ) (a : ZMod 2) (n : ℤ) (b : ZMod 2) : P k m a ⟶ P k n b :=
  QPiEnvelope.ofHom (SuperalgebraCat.ofElem (1 : k))

/-- `1^{n,b}_{m,a}` has parity `a + b`. -/
theorem one_mem (m : ℤ) (a : ZMod 2) (n : ℤ) (b : ZMod 2) :
    one (k := k) m a n b ∈ parity (R := k) (P k m a) (P k n b) (a + b) := by
  have := QPiEnvelope.ofHom_mem (R := k) (X := P k m a) (Y := P k n b)
    (UnitSupercat.mem_parity_zero (SuperalgebraCat.ofElem (1 : k)))
  rwa [zero_add] at this

/-- `1^{n,b}_{m,a}` has degree `n - m`. -/
theorem one_mem_degree (m : ℤ) (a : ZMod 2) (n : ℤ) (b : ZMod 2) :
    one (k := k) m a n b ∈ degree (R := k) (P k m a) (P k n b) (n - m) := by
  have := QPiEnvelope.ofHom_mem_degree (R := k) (X := P k m a) (Y := P k n b)
    (f := SuperalgebraCat.ofElem (1 : k)) (UnitSupercat.mem_degree_iff.2 (Or.inl rfl))
  rwa [zero_add] at this

/-- `1^{l,c}_{n,b} ∘ 1^{n,b}_{m,a} = 1^{l,c}_{m,a}`. -/
theorem one_comp_one (m : ℤ) (a : ZMod 2) (n : ℤ) (b : ZMod 2) (l : ℤ) (c : ZMod 2) :
    one (k := k) m a n b ≫ one n b l c = one m a l c :=
  Envelope.hom_ext (QEnvelope.hom_ext (SuperalgebraCat.hom_ext (𝒜 := trivialGrading k)
    (mul_one (1 : k))))

/-- `Hom_{I_{q,π}}(Q^mΠ^a, Q^nΠ^b)` is free of rank one with basis `1^{n,b}_{m,a}`. -/
def homEquiv (m : ℤ) (a : ZMod 2) (n : ℤ) (b : ZMod 2) : (P k m a ⟶ P k n b) ≃ₗ[k] k where
  toFun f := SuperalgebraCat.toElem (QPiEnvelope.toHom f)
  invFun r := r • one m a n b
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv f :=
    Envelope.hom_ext (QEnvelope.hom_ext (SuperalgebraCat.hom_ext (𝒜 := trivialGrading k) (by
      show SuperalgebraCat.toElem (QPiEnvelope.toHom f) * 1 =
        SuperalgebraCat.toElem (QPiEnvelope.toHom f)
      exact mul_one _)))
  right_inv r := by
    show r * 1 = r
    exact mul_one r

@[simp] theorem homEquiv_symm_apply (m : ℤ) (a : ZMod 2) (n : ℤ) (b : ZMod 2) (r : k) :
    (homEquiv (k := k) m a n b).symm r = r • one m a n b := rfl

/-- `Q(Q^mΠ^a) = Q^{m+1}Π^a`. -/
theorem Q_obj (m : ℤ) (a : ZMod 2) : (QPiSupercategory.Q (R := k)).obj (P k m a) = P k (m + 1) a :=
  rfl

/-- `Q⁻¹(Q^mΠ^a) = Q^{m-1}Π^a`. -/
theorem Qinv_obj (m : ℤ) (a : ZMod 2) :
    (QPiSupercategory.Qinv (R := k)).obj (P k m a) = P k (m - 1) a := rfl

/-- `Π(Q^mΠ^a) = Q^mΠ^{a+1}`. -/
theorem pi_obj (m : ℤ) (a : ZMod 2) :
    (PiSupercategory.pi (R := k)).obj (P k m a) = P k m (a + 1) := rfl

/-- `σ_{Q^mΠ^a} = 1^{m,a}_{m+1,a}`. -/
theorem σ_hom (m : ℤ) (a : ZMod 2) :
    (QPiSupercategory.σ (R := k) (P k m a)).hom = one (m + 1) a m a := rfl

/-- `σ̄_{Q^mΠ^a} = 1^{m,a}_{m-1,a}`. -/
theorem σbar_hom (m : ℤ) (a : ZMod 2) :
    (QPiSupercategory.σbar (R := k) (P k m a)).hom = one (m - 1) a m a := rfl

/-- `ζ_{Q^mΠ^a} = 1^{m,a}_{m,a+1}`. -/
theorem ζ_hom (m : ℤ) (a : ZMod 2) :
    (PiSupercategory.ζ (R := k) (P k m a)).hom = one m (a + 1) m a := rfl

end UnitQPiEnvelope

end StringDiagrams

end
