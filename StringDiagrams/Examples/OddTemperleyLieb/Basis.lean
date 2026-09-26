import StringDiagrams.Examples.OddTemperleyLieb.Independence

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

end StringDiagrams.OddTemperleyLieb

end
