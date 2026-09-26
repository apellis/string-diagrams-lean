import StringDiagrams.Examples.OddTemperleyLieb.Independence
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.NormNum
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# The basis theorem for the odd Temperley–Lieb supercategory (Theorem A.2)

J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, Theorem A.2:
*any set of representatives for the isotopy classes of crossingless matchings from `m` points
to `n` points defines a basis for `Hom_{STL(δ)}(m, n)`.*

## Crossingless matchings of a diagram

A crossingless matching from `m` points (bottom) to `n` points (top) is encoded, after bending
the bottom points up to the left (so that they are read from right to left, followed by the top
points from left to right), by the Dyck sequence of a crossingless matching of `m + n` points:
`CrossinglessMatching m n := DyckSeq (m + n)`. The identity diagram of `m` strands is the
nested matching `nestD m = +1^m -1^m`.

A diagram `d : m → n` (a composite of layers, each a cup or a cap) determines its crossingless
matching `matchingOf d` and its number of closed loops `loopsOf d`, obtained by following the
arcs of `nestD m` through the layers of `d` (`trackW`). Two diagrams are isotopic (as planar
diagrams with no closed loops) exactly when they have the same crossingless matching and no
loops; a *set of representatives* is a family `r` of diagrams with
`matchingOf (r M) = M` and `loopsOf (r M) = 0` (`IsRepresentatives`). Representatives exist
(`exists_representatives`).

## Main results

* `bend`, `unbend`: the linear maps `Hom(m, n) → Hom(0, m + n)`, `f ↦ nested cups ≫ (1_m ⊗ f)`,
  and back, `g ↦ (1_m ⊗ g) ≫ nested caps`; `unbend (bend f) = ± f` and `bend (unbend g) = ± g` on
  diagrams (`unbend_bend_evW`, `bend_unbend_evW`), by the snake identities.
* `bend_diag`: `bend d = ± δ^{loopsOf d} canon (matchingOf d)`: isotopic crossingless matchings
  give the same morphism up to sign, and every diagram is `±δ^ℓ` times the representative of
  its crossingless matching (`diag_pmEq_representative`).
* **`basisOfRepresentatives`** (Theorem A.2): for a commutative ring `R`, a unit `q`, and
  `δ = -(q - q⁻¹)`, any set of representatives is a basis of `Hom(m, n)`. The appendix assumes
  that `R` is a field of characteristic `≠ 2` and that `q` is not a root of unity
  (`theoremA2`); neither is needed.
* `finrank_hom_three_three`: `Hom(3, 3)` has dimension `5` (the third Catalan number).
-/

noncomputable section

namespace StringDiagrams.OddTemperleyLieb

open CategoryTheory
open TemperleyLieb.Rep (ins del)
open Rep (delta)

variable {R : Type*} [CommRing R] {δ : R}

/-! ## Bending -/

variable (R δ) in
/-- Bending the bottom boundary up: `f ↦ (nested cups) ≫ (1_m ⊗ f)`. -/
def bend (m n : ℕ) : (X R δ m ⟶ X R δ n) →ₗ[R] (X R δ 0 ⟶ X R δ (m + n)) where
  toFun f := evW R δ 0 (nestW m) (m + m) ≫ wLs R δ m f
  map_add' f g := by rw [wLs_add, Preadditive.comp_add]
  map_smul' r f := by rw [wLs_smul, Linear.comp_smul]; rfl

variable (R δ) in
/-- Bending back: `g ↦ (1_m ⊗ g) ≫ (nested caps)`. -/
def unbend (m n : ℕ) : (X R δ 0 ⟶ X R δ (m + n)) →ₗ[R] (X R δ m ⟶ X R δ n) where
  toFun g := wLs R δ m g ≫ evW R δ (m + (m + n)) (capsW m) n
  map_add' f g := by rw [wLs_add, Preadditive.add_comp]
  map_smul' r f := by rw [wLs_smul, Linear.smul_comp]; rfl

theorem ht_shift_nestW (m : ℕ) : ht m (shiftW m (nestW m)) = m + (m + m) := by
  have := ht_shiftW m 0 (valid_nestW m 0)
  rw [add_zero] at this
  rw [this, ht_nestW]; omega

/-- `unbend (bend f) = ± f` on words: the snake identity. -/
theorem unbend_bend_evW {m n : ℕ} {u : List Step} (hu : Valid m u) (hn : ht m u = n) :
    PmEq (unbend R δ m n (bend R δ m n (evW R δ m u n))) (evW R δ m u n) := by
  simp only [bend, unbend, LinearMap.coe_mk, AddHom.coe_mk]
  rw [wLs_comp, wLs_evW m (valid_nestW m 0), wLs_evW m hu, wLs_evW m (valid_shiftW m m hu),
    shiftW_shiftW]
  dsimp only [Nat.add_zero]
  rw [Category.assoc, ← evW_append (m + (m + m)) _ _ (b := m + (m + n))
    (by rw [show m + (m + m) = (m + m) + m by omega, ht_shiftW _ _ hu, hn]; omega),
    ← evW_append m _ _ (ht_shift_nestW m)]
  -- slide the caps under the word, then undo the zigzags
  have h1 := evW_farCaps (R := R) (δ := δ) m u hu (W := m + (m + m)) (by omega) [] n
  simp only [List.append_nil] at h1
  refine (PmEq.evW_prefix _ (ht_shift_nestW m) h1).trans ?_
  have h2 := evW_snake (R := R) (δ := δ) m (r := 0) (W := m) (by omega) u n
  simpa only [List.append_assoc] using h2

/-- `bend (unbend g) = ± g` on words: the mirror snake identity. -/
theorem bend_unbend_evW {m n : ℕ} {v : List Step} (hv : Valid 0 v) (hn : ht 0 v = m + n) :
    PmEq (bend R δ m n (unbend R δ m n (evW R δ 0 v (m + n)))) (evW R δ 0 v (m + n)) := by
  simp only [bend, unbend, LinearMap.coe_mk, AddHom.coe_mk]
  have hv' : Valid m (shiftW m v) := by simpa using valid_shiftW m 0 hv
  have hvh : ht m (shiftW m v) = m + (m + n) := by
    have := ht_shiftW m 0 hv; rw [add_zero] at this; rw [this, hn]
  rw [wLs_evW m hv]
  dsimp only [Nat.add_zero]
  rw [← evW_append m _ _ hvh]
  have hvc : Valid m (shiftW m v ++ capsW m) :=
    valid_append.mpr ⟨hv', by rw [hvh]; exact valid_capsW m _ (by omega)⟩
  rw [wLs_evW m hvc, shiftW_append, shiftW_shiftW,
    ← evW_append 0 _ _ (b := m + m) (by rw [ht_nestW]; omega), ← List.append_assoc]
  have h1 := evW_farCups (R := R) (δ := δ) m v (W := 0) hv (shiftW m (capsW m)) (m + n)
  refine h1.trans ?_
  rw [List.append_assoc, evW_append 0 v _ hn]
  have h2 := evW_snake' (R := R) (δ := δ) m (W := m + n) (by omega) [] (m + n)
  simp only [List.append_nil, evW_nil_self] at h2
  refine (h2.comp_left _).trans ?_
  rw [Category.comp_id]
  exact PmEq.refl _

/-! ## Crossingless matchings of diagrams -/

/-- The crossingless matching of the identity diagram of `m` strands (bent): `+1^m -1^m`. -/
def nestD (m : ℕ) : List (Fin 2) := List.replicate m 0 ++ List.replicate m 1

theorem trackW_nestW (m : ℕ) : trackW [] (nestW m) = (nestD m, 0) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [nestW_succ', trackW_append, ih]
    simp only [trackW_cup, trackW_nil, add_zero, Prod.mk.injEq, and_true]
    rw [nestD, ins_rep, nestD, List.replicate_succ', List.replicate_succ, List.append_assoc]
    rfl

/-- The crossingless matchings from `m` points to `n` points, encoded by the Dyck sequences of
their bent versions (the `m` bottom points read from right to left, then the `n` top points
from left to right). -/
abbrev CrossinglessMatching (m n : ℕ) : Type := DyckSeq (m + n)

/-- The (bent) crossingless matching of a diagram `d : m → n`. -/
def matchingOf {m n : ℕ} (d : strands m ⟶ strands n) : List (Fin 2) :=
  (trackW (nestD m) (shiftW m (steps d))).1

/-- The number of closed loops of a diagram. -/
def loopsOf {m n : ℕ} (d : strands m ⟶ strands n) : ℕ :=
  (trackW (nestD m) (shiftW m (steps d))).2

theorem bend_diag_eq {m n : ℕ} (d : strands m ⟶ strands n) :
    bend R δ m n ((pres R δ).diag d) = evW R δ 0 (nestW m ++ shiftW m (steps d)) (m + n) := by
  simp only [bend, LinearMap.coe_mk, AddHom.coe_mk]
  rw [diag_eq_evW, wLs_evW m (valid_steps d), evW_append 0 _ _ (b := m + m) (by rw [ht_nestW]; omega)]

/-- **Isotopy invariance up to sign.** Bending a diagram gives, up to sign, `δ` to the number
of its closed loops times the canonical cup diagram of its crossingless matching. -/
theorem bend_diag {m n : ℕ} (d : strands m ⟶ strands n) :
    IsDyck (matchingOf d) ∧ (matchingOf d).length = m + n ∧
      PmEq (bend R δ m n ((pres R δ).diag d)) (δ ^ loopsOf d • canon R δ (m + n) (matchingOf d)) := by
  have hv : Valid 0 (nestW m ++ shiftW m (steps d)) :=
    valid_append.mpr ⟨valid_nestW m 0, by
      rw [ht_nestW]; simpa using valid_shiftW m m (valid_steps d)⟩
  have hh : ht 0 (nestW m ++ shiftW m (steps d)) = m + n := by
    rw [ht_append, ht_nestW, zero_add, ht_shiftW m m (valid_steps d), ht_steps]
  obtain ⟨h1, h2, h3⟩ := canon_comp_evW (R := R) (δ := δ) _ 0 [] isDyck_nil rfl hv
  rw [trackW_append, trackW_nestW] at h1 h2 h3
  rw [hh] at h2 h3
  rw [canon_zero, Category.id_comp] at h3
  refine ⟨h1, h2, ?_⟩
  rw [bend_diag_eq]
  simpa [matchingOf, loopsOf] using h3

/-- A set of representatives for the isotopy classes of crossingless matchings from `m` to `n`
points: diagrams without closed loops realizing every crossingless matching. -/
def IsRepresentatives {m n : ℕ} (r : CrossinglessMatching m n → (strands m ⟶ strands n)) : Prop :=
  ∀ M, matchingOf (r M) = M.1 ∧ loopsOf (r M) = 0

/-- `bend` of a word, up to sign. -/
theorem bend_evW {m n : ℕ} {u : List Step} (hu : Valid m u) (hn : ht m u = n) :
    IsDyck (trackW (nestD m) (shiftW m u)).1 ∧ (trackW (nestD m) (shiftW m u)).1.length = m + n ∧
      PmEq (bend R δ m n (evW R δ m u n))
        (δ ^ (trackW (nestD m) (shiftW m u)).2 •
          canon R δ (m + n) (trackW (nestD m) (shiftW m u)).1) := by
  have hv : Valid 0 (nestW m ++ shiftW m u) :=
    valid_append.mpr ⟨valid_nestW m 0, by rw [ht_nestW]; simpa using valid_shiftW m m hu⟩
  have hh : ht 0 (nestW m ++ shiftW m u) = m + n := by
    rw [ht_append, ht_nestW, zero_add, ht_shiftW m m hu, hn]
  obtain ⟨h1, h2, h3⟩ := canon_comp_evW (R := R) (δ := δ) _ 0 [] isDyck_nil rfl hv
  rw [trackW_append, trackW_nestW] at h1 h2 h3
  rw [hh] at h2 h3
  rw [canon_zero, Category.id_comp] at h3
  refine ⟨h1, h2, ?_⟩
  simp only [bend, LinearMap.coe_mk, AddHom.coe_mk]
  rw [wLs_evW m hu, evW_append 0 _ _ (b := m + m) (by rw [ht_nestW]; omega)] at *
  simpa using h3

/-- The bent-back canonical cup diagrams span `Hom(m, n)`. -/
theorem span_unbend_canon (m n : ℕ) :
    Submodule.span R (Set.range fun M : CrossinglessMatching m n =>
      unbend R δ m n (canon R δ (m + n) M.1)) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro f
  induction f using hom_induction_evW with
  | word u hu hn =>
    obtain ⟨h1, h2, h3⟩ := bend_evW (R := R) (δ := δ) hu hn
    have h4 := (unbend_bend_evW (R := R) (δ := δ) hu hn).symm.trans
      (h3.map (unbend R δ m n).toAddMonoidHom)
    simp only [LinearMap.toAddMonoidHom_coe, map_smul] at h4
    have hmem : unbend R δ m n (canon R δ (m + n) (trackW (nestD m) (shiftW m u)).1) ∈
        Submodule.span R (Set.range fun M : CrossinglessMatching m n =>
          unbend R δ m n (canon R δ (m + n) M.1)) :=
      Submodule.subset_span ⟨⟨_, h1, h2⟩, rfl⟩
    rcases h4 with h | h <;> rw [h]
    · exact Submodule.smul_mem _ _ hmem
    · exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hmem)
  | zero => exact Submodule.zero_mem _
  | add f g hf hg => exact Submodule.add_mem _ hf hg
  | smul r f hf => exact Submodule.smul_mem _ r hf

theorem PmEq.exists_units {M : Type*} [AddCommGroup M] [Module R M] {x y : M} (h : PmEq x y) :
    ∃ u : Rˣ, x = u • y := by
  rcases h with h | h
  · exact ⟨1, by rw [h, one_smul]⟩
  · exact ⟨-1, by rw [h, Units.neg_smul, one_smul]⟩

/-- Every diagram is, up to sign, `δ` to the number of its closed loops times the representative
of its crossingless matching. -/
theorem diag_pmEq_representative {m n : ℕ} {r : CrossinglessMatching m n → (strands m ⟶ strands n)}
    (hr : IsRepresentatives r) (d : strands m ⟶ strands n) :
    PmEq ((pres R δ).diag d) (δ ^ loopsOf d • (pres R δ).diag (r ⟨matchingOf d,
      (bend_diag (R := R) (δ := δ) d).1, (bend_diag (R := R) (δ := δ) d).2.1⟩)) := by
  set M : CrossinglessMatching m n := ⟨matchingOf d, (bend_diag (R := R) (δ := δ) d).1,
    (bend_diag (R := R) (δ := δ) d).2.1⟩
  have e1 : PmEq ((pres R δ).diag d) (δ ^ loopsOf d • unbend R δ m n (canon R δ (m + n) M.1)) := by
    rw [diag_eq_evW]
    refine (unbend_bend_evW (valid_steps d) (ht_steps d)).symm.trans ?_
    rw [← diag_eq_evW, ← map_smul]
    exact (bend_diag d).2.2.map (unbend R δ m n).toAddMonoidHom
  have e2 : PmEq ((pres R δ).diag (r M)) (unbend R δ m n (canon R δ (m + n) M.1)) := by
    rw [diag_eq_evW]
    refine (unbend_bend_evW (valid_steps (r M)) (ht_steps (r M))).symm.trans ?_
    rw [← diag_eq_evW]
    have := (bend_diag (R := R) (δ := δ) (r M)).2.2
    rw [(hr M).1, (hr M).2, pow_zero, one_smul] at this
    exact this.map (unbend R δ m n).toAddMonoidHom
  exact e1.trans (e2.symm.smul _)

variable (q : Rˣ)

/-- **Theorem A.2.** For a commutative ring `R`, a unit `q` and `δ = -(q - q⁻¹)`, any set of
representatives for the isotopy classes of crossingless matchings from `m` points to `n` points
is linearly independent and spans `Hom(m, n)` in `STL(δ)`. -/
theorem linearIndependent_and_span_of_representatives {m n : ℕ}
    {r : CrossinglessMatching m n → (strands m ⟶ strands n)} (hr : IsRepresentatives r) :
    LinearIndependent R (fun M => (pres R (delta q)).diag (r M)) ∧
      Submodule.span R (Set.range fun M => (pres R (delta q)).diag (r M)) = ⊤ := by
  constructor
  · -- bending sends the family to the canonical cup diagrams, up to signs
    have hs : ∀ M : CrossinglessMatching m n, ∃ u : Rˣ,
        bend R (delta q) m n ((pres R (delta q)).diag (r M)) = u • canon R (delta q) (m + n) M.1 := by
      intro M
      have := (bend_diag (R := R) (δ := delta q) (r M)).2.2
      rw [(hr M).1, (hr M).2, pow_zero, one_smul] at this
      exact this.exists_units
    choose u hu using hs
    apply LinearIndependent.of_comp (bend R (delta q) m n)
    have : (bend R (delta q) m n) ∘ (fun M => (pres R (delta q)).diag (r M)) =
        u • fun M : CrossinglessMatching m n => canon R (delta q) (m + n) M.1 := by
      funext M; exact hu M
    rw [this]
    exact (linearIndependent_canon q (m + n)).units_smul u
  · rw [eq_top_iff, ← span_unbend_canon (R := R) (δ := delta q) m n]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨M, rfl⟩
    have h2 : PmEq ((pres R (delta q)).diag (r M)) (unbend R (delta q) m n (canon R (delta q) (m + n) M.1)) := by
      rw [diag_eq_evW]
      refine (unbend_bend_evW (valid_steps (r M)) (ht_steps (r M))).symm.trans ?_
      rw [← diag_eq_evW]
      have := (bend_diag (R := R) (δ := delta q) (r M)).2.2
      rw [(hr M).1, (hr M).2, pow_zero, one_smul] at this
      exact this.map (unbend R (delta q) m n).toAddMonoidHom
    dsimp only
    rcases h2.symm with h | h <;> rw [h]
    · exact Submodule.subset_span ⟨M, rfl⟩
    · exact Submodule.neg_mem _ (Submodule.subset_span ⟨M, rfl⟩)

/-- **Theorem A.2**, as a basis of `Hom(m, n)` indexed by the crossingless matchings. -/
def basisOfRepresentatives {m n : ℕ} {r : CrossinglessMatching m n → (strands m ⟶ strands n)}
    (hr : IsRepresentatives r) :
    Basis (CrossinglessMatching m n) R (X R (delta q) m ⟶ X R (delta q) n) :=
  Basis.mk (linearIndependent_and_span_of_representatives q hr).1
    (linearIndependent_and_span_of_representatives q hr).2.ge

@[simp] theorem basisOfRepresentatives_apply {m n : ℕ}
    {r : CrossinglessMatching m n → (strands m ⟶ strands n)} (hr : IsRepresentatives r)
    (M : CrossinglessMatching m n) :
    basisOfRepresentatives q hr M = (pres R (delta q)).diag (r M) := Basis.mk_apply _ _ _

/-! ## Existence of representatives -/

/-- A Dyck sequence of length `n + 2` is its first adjacent pair inserted into a Dyck sequence
of length `n`. -/
theorem dyck_split {w : List (Fin 2)} (hw : IsDyck w) {n : ℕ} (hl : w.length = n + 2) :
    firstPair w ≤ n ∧ IsDyck (del (firstPair w) w) ∧ (del (firstPair w) w).length = n ∧
      w = ins (firstPair w) 0 1 (del (firstPair w) w) := by
  have hne : w ≠ [] := by rintro rfl; simp at hl
  obtain ⟨r, hr⟩ := dyck_decomp hw hne
  generalize hp : firstPair w = p at hr
  have hlr : p + r.length = n := by rw [hr] at hl; simp at hl; omega
  have hd : del p w = List.replicate p 0 ++ r := by rw [hr, del_rep]
  refine ⟨by omega, ?_, by rw [hd]; simp; omega, by rw [hd, hr, ins_rep]⟩
  have := hw.del_pair (p := p) (by omega)
    (by rw [hr]; simp [getD_rep_add p 0 0 (0 :: 1 :: r)])
    (by rw [hr]; simp [getD_rep_add p 1 0 (0 :: 1 :: r)])
  exact this

/-- The word of the canonical cup diagram. -/
def canonW : ℕ → List (Fin 2) → List Step
  | 0, _ => []
  | 1, _ => []
  | n + 2, w => canonW n (del (firstPair w) w) ++ [.cup (firstPair w)]

theorem canonW_spec (n : ℕ) : ∀ w : List (Fin 2), IsDyck w → w.length = n →
    Valid 0 (canonW n w) ∧ ht 0 (canonW n w) = n ∧
      evW R δ 0 (canonW n w) n = canon R δ n w := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w hw hl
  match n, ih, hl with
  | 0, _, _ => exact ⟨trivial, rfl, by simp [canonW, canon_zero]⟩
  | 1, _, hl => exact absurd (hl ▸ hw.length_even) (by decide)
  | n + 2, ih, hl =>
    obtain ⟨hp, hd, hdl, -⟩ := dyck_split hw hl
    obtain ⟨h1, h2, h3⟩ := ih n (by omega) _ hd hdl
    refine ⟨valid_append.mpr ⟨h1, by rw [h2]; exact ⟨hp, trivial⟩⟩,
      by rw [canonW, ht_append, h2]; rfl, ?_⟩
    rw [canonW, evW_append 0 _ _ h2, h3, canon_succ_succ, evW_cup, evW_nil_self,
      Category.comp_id]

/-- The diagram of a valid word. -/
def wordDiagram : (a : ℕ) → (u : List Step) → Valid a u → (strands a ⟶ strands (ht a u))
  | _, [], _ => 𝟙 _
  | a, .cup i :: u, h => dcup h.1 ≫ wordDiagram (a + 2) u h.2
  | a, .cap i :: u, h => eqToHom (congrArg strands (by have := h.1; omega : a = a - 2 + 2)) ≫
      dcap (m := a - 2) (i := i) (by have := h.1; omega) ≫ wordDiagram (a - 2) u h.2

theorem steps_wordDiagram (a : ℕ) (u : List Step) (h : Valid a u) :
    steps (wordDiagram a u h) = u := by
  induction u generalizing a with
  | nil => rfl
  | cons s u ih => cases s with
    | cup i =>
      have := ih (a + 2) h.2
      simp only [steps, wordDiagram, Diagram.layers_comp, dcup, Diagram.layers_layer,
        List.singleton_append, List.map_cons, toStep] at this ⊢
      simp [this]
    | cap i =>
      have := ih (a - 2) h.2
      simp only [steps, wordDiagram, Diagram.layers_comp, dcap, Diagram.layers_layer,
        List.singleton_append, List.map_cons, toStep, Diagram.layers_eqToHom,
        List.nil_append] at this ⊢
      simp [this]

theorem unbend_evW {m n : ℕ} {v : List Step} (hv : Valid 0 v) (hn : ht 0 v = m + n) :
    unbend R δ m n (evW R δ 0 v (m + n)) = evW R δ m (shiftW m v ++ capsW m) n := by
  simp only [unbend, LinearMap.coe_mk, AddHom.coe_mk]
  have hvh : ht m (shiftW m v) = m + (m + n) := by
    have := ht_shiftW m 0 hv; rw [add_zero] at this; rw [this, hn]
  rw [wLs_evW m hv]
  dsimp only [Nat.add_zero]
  rw [← evW_append m _ _ hvh]

/-- The word of the bent-back canonical cup diagram of a crossingless matching. -/
def repWord {m n : ℕ} (M : CrossinglessMatching m n) : List Step :=
  shiftW m (canonW (m + n) M.1) ++ capsW m

theorem valid_repWord {m n : ℕ} (M : CrossinglessMatching m n) : Valid m (repWord M) := by
  obtain ⟨h1, h2, -⟩ := canonW_spec (R := ℤ) (δ := 0) (m + n) M.1 M.2.1 M.2.2
  have hvh : ht m (shiftW m (canonW (m + n) M.1)) = m + (m + n) := by
    have := ht_shiftW m 0 h1; rw [add_zero] at this; rw [this, h2]
  refine valid_append.mpr ⟨by simpa using valid_shiftW m 0 h1, ?_⟩
  rw [hvh]; exact valid_capsW m _ (by omega)

theorem ht_repWord {m n : ℕ} (M : CrossinglessMatching m n) : ht m (repWord M) = n := by
  obtain ⟨h1, h2, -⟩ := canonW_spec (R := ℤ) (δ := 0) (m + n) M.1 M.2.1 M.2.2
  have hvh : ht m (shiftW m (canonW (m + n) M.1)) = m + (m + n) := by
    have := ht_shiftW m 0 h1; rw [add_zero] at this; rw [this, h2]
  rw [repWord, ht_append, hvh, ht_capsW]; omega

/-- The bent-back canonical cup diagram of a crossingless matching, as a diagram. -/
def repDiagram {m n : ℕ} (M : CrossinglessMatching m n) : strands m ⟶ strands n :=
  wordDiagram m (repWord M) (valid_repWord M) ≫ eqToHom (congrArg strands (ht_repWord M))

theorem steps_repDiagram {m n : ℕ} (M : CrossinglessMatching m n) :
    steps (repDiagram M) = repWord M := by
  rw [← steps_wordDiagram m (repWord M) (valid_repWord M)]
  simp [steps, repDiagram, Diagram.layers_comp, Diagram.layers_eqToHom]

/-- The rational numbers with `q = 2` are used to show that the bent-back canonical cup diagrams
realize their crossingless matchings: the tracking of arcs does not depend on the ground ring. -/
theorem trackW_repWord {m n : ℕ} (M : CrossinglessMatching m n) :
    trackW (nestD m) (shiftW m (repWord M)) = (M.1, 0) := by
  classical
  set q₀ : ℚˣ := Units.mk0 2 (by norm_num)
  obtain ⟨h1, h2, h3⟩ := bend_evW (R := ℚ) (δ := delta q₀) (valid_repWord M) (ht_repWord M)
  obtain ⟨c1, c2, c3⟩ := canonW_spec (R := ℚ) (δ := delta q₀) (m + n) M.1 M.2.1 M.2.2
  have h4 := bend_unbend_evW (R := ℚ) (δ := delta q₀) (m := m) (n := n) c1 c2
  rw [unbend_evW c1 c2, c3] at h4
  rw [repWord] at h1 h2 h3
  have key := h4.symm.trans h3
  set M' : DyckSeq (m + n) := ⟨_, h1, h2⟩
  set ℓ := (trackW (nestD m) (shiftW m (shiftW m (canonW (m + n) M.1) ++ capsW m))).2
  have hli := linearIndependent_canon q₀ (m + n)
  obtain ⟨s, hs, hsv⟩ : ∃ s : ℚ, (s = 1 ∨ s = -1) ∧
      canon ℚ (delta q₀) (m + n) M.1 = (s * delta q₀ ^ ℓ) • canon ℚ (delta q₀) (m + n) M'.1 := by
    rcases key with h | h
    · exact ⟨1, Or.inl rfl, by rw [h, one_mul]⟩
    · exact ⟨-1, Or.inr rfl, by rw [h, neg_one_mul, neg_smul]⟩
  have hMM : M = M' := by
    by_contra hne
    have := (linearIndependent_iff'.mp hli) {M, M'}
      (fun j => if j = M then 1 else -(s * delta q₀ ^ ℓ)) (by
        rw [Finset.sum_pair hne]
        simp only [if_true, one_smul, if_neg (Ne.symm hne), neg_smul]
        rw [← hsv, add_neg_cancel]) M (by simp)
    simp at this
  have hℓ : ℓ = 0 := by
    rw [← hMM] at hsv
    have hsv' : (1 - s * delta q₀ ^ ℓ) • canon ℚ (delta q₀) (m + n) M.1 = 0 := by
      rw [sub_smul, one_smul, ← hsv, sub_self]
    have h0 := (linearIndependent_iff'.mp hli) {M} (fun _ => 1 - s * delta q₀ ^ ℓ)
      (by simpa using hsv') M (by simp)
    simp only at h0
    have hδ : delta q₀ = -(3 / 2) := by simp [delta, q₀]; norm_num
    have habs : |s * delta q₀ ^ ℓ| = 1 := by rw [← sub_eq_zero.mp h0]; simp
    rw [abs_mul, abs_pow, hδ, abs_neg, abs_of_pos (by norm_num : (0 : ℚ) < 3 / 2)] at habs
    have hs1 : |s| = 1 := by rcases hs with rfl | rfl <;> simp
    rw [hs1, one_mul] at habs
    rcases Nat.eq_zero_or_pos ℓ with hz | hpos
    · exact hz
    · have := one_lt_pow₀ (by norm_num : (1 : ℚ) < 3 / 2) hpos.ne'
      rw [habs] at this
      exact absurd this (lt_irrefl _)
  rw [repWord]
  exact Prod.ext (congrArg Subtype.val hMM).symm hℓ

/-- The bent-back canonical cup diagrams form a set of representatives. -/
theorem isRepresentatives_repDiagram (m n : ℕ) :
    IsRepresentatives (fun M : CrossinglessMatching m n => repDiagram M) := by
  intro M
  simp [matchingOf, loopsOf, steps_repDiagram, trackW_repWord]

/-- Sets of representatives exist. -/
theorem exists_representatives (m n : ℕ) :
    ∃ r : CrossinglessMatching m n → (strands m ⟶ strands n), IsRepresentatives r :=
  ⟨_, isRepresentatives_repDiagram m n⟩

/-- The canonical basis of `Hom(m, n)`: the bent-back canonical cup diagrams. -/
def basisRep (m n : ℕ) : Basis (CrossinglessMatching m n) R (X R (delta q) m ⟶ X R (delta q) n) :=
  basisOfRepresentatives q (isRepresentatives_repDiagram m n)

/-- **Theorem A.2**, with the standing hypotheses of Appendix A: `k` a field of characteristic
different from `2`, `q ∈ k^×` not a root of unity, `δ = -[2] = -(q - q⁻¹)`. (The hypotheses on the
characteristic and on `q` are not used; see `linearIndependent_and_span_of_representatives`.) -/
theorem theoremA2 {k : Type*} [Field k] (_hchar : ringChar k ≠ 2) (q : kˣ)
    (_hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) {m n : ℕ}
    {r : CrossinglessMatching m n → (strands m ⟶ strands n)} (hr : IsRepresentatives r) :
    LinearIndependent k (fun M => (pres k (delta q)).diag (r M)) ∧
      Submodule.span k (Set.range fun M => (pres k (delta q)).diag (r M)) = ⊤ :=
  linearIndependent_and_span_of_representatives q hr

/-! ## Counting -/

/-- All words of length `N`. -/
def allWords : ℕ → List (List (Fin 2))
  | 0 => [[]]
  | N + 1 => (allWords N).flatMap fun w => [0 :: w, 1 :: w]

theorem mem_allWords {N : ℕ} {w : List (Fin 2)} : w ∈ allWords N ↔ w.length = N := by
  induction N generalizing w with
  | zero => simp [allWords]
  | succ N ih =>
    simp only [allWords, List.mem_flatMap, List.mem_cons, List.mem_singleton,
      List.not_mem_nil, or_false]
    constructor
    · rintro ⟨v, hv, rfl | rfl⟩ <;> simp [ih.mp hv]
    · intro h
      obtain ⟨a, v, rfl⟩ : ∃ a v, w = a :: v := by
        rcases w with _ | ⟨a, v⟩
        · simp at h
        · exact ⟨a, v, rfl⟩
      refine ⟨v, ih.mpr (by simpa using h), ?_⟩
      fin_cases a <;> simp

/-- The Dyck sequences of length `N`, as a list. -/
def dyckList (N : ℕ) : List (List (Fin 2)) := (allWords N).filter fun w => decide (IsDyck w)

instance (N : ℕ) : Fintype (DyckSeq N) :=
  Fintype.ofList ((dyckList N).attach.map fun w => ⟨w.1, by
    have := w.2
    simp only [dyckList, List.mem_filter, decide_eq_true_eq] at this
    exact ⟨this.2, mem_allWords.mp this.1⟩⟩) fun w => by
    simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists]
    exact ⟨w.1, by simp [dyckList, mem_allWords, w.2.1, w.2.2], rfl⟩

theorem card_dyckSeq_six : Fintype.card (DyckSeq 6) = 5 := by
  decide

/-- **`Hom(3, 3)` has dimension `5`** (the third Catalan number), for any nontrivial commutative
ring `R` and unit `q`, `δ = -(q - q⁻¹)`. -/
theorem finrank_hom_three_three [Nontrivial R] :
    Module.finrank R (X R (delta q) 3 ⟶ X R (delta q) 3) = 5 := by
  rw [Module.finrank_eq_card_basis (basisRep q 3 3)]
  exact card_dyckSeq_six

end StringDiagrams.OddTemperleyLieb

end
