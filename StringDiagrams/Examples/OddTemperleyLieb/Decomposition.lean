import StringDiagrams.Examples.OddTemperleyLieb.HomSpaces

/-!
# The decomposition `f_{n-1} ⊗ f_1 = f_n + g_n`

J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, proof of Theorem A.3
(last paragraph).

For `n = N + 2`, set `f = f_{N+1}` and
* `g_n := -([N+1]/[N+2]) (f ⊗ 1) ≫ cap_N ≫ cup_N ≫ (f ⊗ 1)`, so that `f ⊗ 1 = f_n + g_n`
  (`wR1_jw_eq`);
* `v_n := (f ⊗ 1) ≫ cap_N : n → n - 2` and `u_n := -([N+1]/[N+2]) cup_N ≫ (f ⊗ 1) : n - 2 → n`,
  odd morphisms (one generator each; `vDec_mem_parity`, `uDec_mem_parity`).

Then `v_n ≫ u_n = g_n` and `u_n ≫ v_n = f_{n-2}` (`vDec_comp_uDec`, `uDec_comp_vDec`), hence
`g_n` is an idempotent (`gDec_idem`) orthogonal to `f_n` (`jw_comp_gDec`, `gDec_comp_jw`), and
`g_n` is equivalent to `f_{n-2}` through odd morphisms: in the super Karoubi envelope,
`(g_n)^0_0 ≅ (f_{n-2})^1_1`.

The parity of the evaluation of a word is its length modulo `2` (`evW_mem_parity`); in
particular even morphisms (`evenSpan`) have parity `0` (`evenSpan_le_parity`).
-/

noncomputable section

namespace StringDiagrams.OddTemperleyLieb

open CategoryTheory
open Rep (delta)

/-! ## Parities of words -/

section Parity

variable {R : Type*} [CommRing R] {δ : R}

theorem oddCount_eq_length {a b : Obj sig} (d : a ⟶ b) :
    Diagram.oddCount d = (Diagram.layers d).length := by
  simp only [Diagram.oddCount, Diagram.oddCountList]
  congr 1
  exact List.filter_eq_self.mpr fun L _ => rfl

/-- The evaluation of a word has the parity of its length. -/
theorem evW_mem_parity {a b : ℕ} {u : List Step} (hu : Valid a u) (hb : ht a u = b) :
    evW R δ a u b ∈
      (pres R δ).homDeg (Presentation.parityDeg sig) (strands a) (strands b) (u.length : ZMod 2) := by
  set d : strands a ⟶ strands b := wordDiagram a u hu ≫ eqToHom (congrArg strands hb)
  have hs : steps d = u := by
    rw [← steps_wordDiagram a u hu]
    simp [d, steps, Diagram.layers_comp, Diagram.layers_eqToHom]
  have h := (pres R δ).diag_mem_homDeg (deg := Presentation.parityDeg sig) d
  rw [Diagram.degree_parityDeg, oddCount_eq_length, diag_eq_evW, hs] at h
  have hl : (Diagram.layers d).length = u.length := by rw [← hs]; simp [steps]
  rwa [hl] at h

theorem evenSpan_le_parity (a b : ℕ) :
    evenSpan R δ a b ≤
      (pres R δ).homDeg (Presentation.parityDeg sig) (strands a) (strands b) 0 := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨u, hu, hb, he, rfl⟩
  have := evW_mem_parity (R := R) (δ := δ) hu hb
  rwa [ZMod.eq_zero_iff_even.mpr he] at this

theorem cup_mem_parity {a i : ℕ} (hi : i ≤ a) :
    cup R δ a i ∈
      (pres R δ).homDeg (Presentation.parityDeg sig) (strands a) (strands (a + 2)) 1 := by
  have := evW_mem_parity (R := R) (δ := δ) (a := a) (u := [.cup i]) (b := a + 2) ⟨hi, trivial⟩ rfl
  simpa using this

theorem cap_mem_parity {a i : ℕ} (hi : i ≤ a) :
    cap R δ a i ∈
      (pres R δ).homDeg (Presentation.parityDeg sig) (strands (a + 2)) (strands a) 1 := by
  have := evW_mem_parity (R := R) (δ := δ) (a := a + 2) (u := [.cap i]) (b := a)
    ⟨by omega, trivial⟩ rfl
  simpa using this

end Parity

/-! ## The decomposition -/

variable {k : Type*} [Field k] {q : kˣ}

local notation "δq" => delta q

variable (q) in
/-- `g_{N+2} = -([N+1]/[N+2]) (f_{N+1} ⊗ 1) ≫ cap_N ≫ cup_N ≫ (f_{N+1} ⊗ 1)`. -/
def gDec (N : ℕ) : X k δq (N + 2) ⟶ X k δq (N + 2) :=
  -jwCoeff q (N + 1) • (wR1 k δq (jw q (N + 1)) ≫ cap k δq N N ≫ cup k δq N N ≫
    wR1 k δq (jw q (N + 1)))

variable (q) in
/-- `v_{N+2} = (f_{N+1} ⊗ 1) ≫ cap_N`. -/
def vDec (N : ℕ) : X k δq (N + 2) ⟶ X k δq N := wR1 k δq (jw q (N + 1)) ≫ cap k δq N N

variable (q) in
/-- `u_{N+2} = -([N+1]/[N+2]) cup_N ≫ (f_{N+1} ⊗ 1)`. -/
def uDec (N : ℕ) : X k δq N ⟶ X k δq (N + 2) :=
  -jwCoeff q (N + 1) • (cup k δq N N ≫ wR1 k δq (jw q (N + 1)))

/-- `f_{n-1} ⊗ 1 = f_n + g_n`. -/
theorem wR1_jw_eq (N : ℕ) : wR1 k δq (jw q (N + 1)) = jw q (N + 2) + gDec q N := by
  rw [jw_succ_succ, gDec, neg_smul]; abel

theorem vDec_comp_uDec (N : ℕ) : vDec q N ≫ uDec q N = gDec q N := by
  simp [vDec, uDec, gDec, Category.assoc]

theorem uDec_comp_vDec (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) (N : ℕ) :
    uDec q N ≫ vDec q N = jw q N := by
  have hI : wR1 k δq (jw q (N + 1)) ≫ wR1 k δq (jw q (N + 1)) = wR1 k δq (jw q (N + 1)) := by
    rw [← wR1_comp, jw_idem hq]
  rw [uDec, vDec, Linear.smul_comp, Category.assoc, ← Category.assoc (wR1 k δq _), hI,
    jw_partial_trace hq, smul_smul, neg_mul, mul_neg, neg_neg, jwCoeff]
  rw [div_mul_div_comm, mul_comm (qint q (N + 1)), div_self, one_smul]
  exact mul_ne_zero (qint_ne_zero hq (by omega)) (qint_ne_zero hq (by omega))

theorem vDec_comp_jw (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) (N : ℕ) :
    vDec q N ≫ jw q N = vDec q N := by
  rw [vDec, Category.assoc, ← wR2_comp_cap_right (jw_mem_evenSpan q N), ← Category.assoc,
    ← wR1_comp, jw_comp_wR1 hq]

theorem jw_comp_uDec (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) (N : ℕ) :
    jw q N ≫ uDec q N = uDec q N := by
  rw [uDec, Linear.comp_smul, ← Category.assoc, comp_cup_right (jw_mem_evenSpan q N),
    Category.assoc, ← wR1_comp, wR1_comp_jw hq]

/-- `g_n` is an idempotent. -/
theorem gDec_idem (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) (N : ℕ) : gDec q N ≫ gDec q N = gDec q N := by
  rw [← vDec_comp_uDec, Category.assoc, ← Category.assoc (uDec q N), uDec_comp_vDec hq,
    ← Category.assoc, vDec_comp_jw hq]

/-- `f_n ≫ g_n = 0`. -/
theorem jw_comp_gDec (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) (N : ℕ) :
    jw q (N + 2) ≫ gDec q N = 0 := by
  rw [← vDec_comp_uDec, vDec, ← Category.assoc, ← Category.assoc, jw_comp_wR1 hq,
    jw_comp_cap hq le_rfl, Limits.zero_comp]

/-- `g_n ≫ f_n = 0`. -/
theorem gDec_comp_jw (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) (N : ℕ) :
    gDec q N ≫ jw q (N + 2) = 0 := by
  rw [← vDec_comp_uDec, Category.assoc, uDec, Linear.smul_comp, Category.assoc, wR1_comp_jw hq,
    cup_comp_jw hq le_rfl, smul_zero, Limits.comp_zero]

theorem gDec_comp_vDec (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) (N : ℕ) :
    gDec q N ≫ vDec q N = vDec q N := by
  rw [← vDec_comp_uDec, Category.assoc, uDec_comp_vDec hq, vDec_comp_jw hq]

theorem uDec_comp_gDec (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1) (N : ℕ) :
    uDec q N ≫ gDec q N = uDec q N := by
  rw [← vDec_comp_uDec, ← Category.assoc, uDec_comp_vDec hq, jw_comp_uDec hq]

/-- `u_n`, `v_n` are odd. -/
theorem vDec_mem_parity (N : ℕ) :
    vDec q N ∈ (pres k δq).homDeg (Presentation.parityDeg sig) (strands (N + 2)) (strands N) 1 := by
  have h := Presentation.comp_mem_homDeg
    (evenSpan_le_parity _ _ (wR1_mem_evenSpan (jw_mem_evenSpan q (N + 1))))
    (cap_mem_parity (R := k) (δ := δq) (le_refl N))
  rwa [zero_add] at h

theorem uDec_mem_parity (N : ℕ) :
    uDec q N ∈ (pres k δq).homDeg (Presentation.parityDeg sig) (strands N) (strands (N + 2)) 1 := by
  have h := Presentation.comp_mem_homDeg (cup_mem_parity (R := k) (δ := δq) (le_refl N))
    (evenSpan_le_parity _ _ (wR1_mem_evenSpan (jw_mem_evenSpan q (N + 1))))
  rw [add_zero] at h
  exact Submodule.smul_mem _ _ h

theorem gDec_mem_parity (N : ℕ) :
    gDec q N ∈ (pres k δq).homDeg (Presentation.parityDeg sig) (strands (N + 2)) (strands (N + 2)) 0 := by
  rw [← vDec_comp_uDec]
  have := Presentation.comp_mem_homDeg (vDec_mem_parity (q := q) N) (uDec_mem_parity (q := q) N)
  simpa using this

end StringDiagrams.OddTemperleyLieb

end
