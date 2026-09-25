import Mathlib

noncomputable section

namespace StringDiagrams.NilHecke

open MvPolynomial

variable {R : Type*} [CommRing R]

abbrev P (R : Type*) [CommRing R] := MvPolynomial ℕ R

def swapVars (i : ℕ) : MvPolynomial ℕ R →ₐ[R] MvPolynomial ℕ R :=
  rename (Equiv.swap i (i + 1))

theorem swapVars_X (i j : ℕ) :
    swapVars (R := R) i (X j) = X (Equiv.swap i (i + 1) j) := rename_X _ _

@[simp] theorem swapVars_X_self (i : ℕ) : swapVars (R := R) i (X i) = X (i + 1) := by
  simp [swapVars_X]

@[simp] theorem swapVars_X_succ (i : ℕ) : swapVars (R := R) i (X (i + 1)) = X i := by
  simp [swapVars_X]

theorem swapVars_X_of_ne {i j : ℕ} (h : j ≠ i) (h' : j ≠ i + 1) :
    swapVars (R := R) i (X j) = X j := by
  rw [swapVars_X, Equiv.swap_apply_of_ne_of_ne h h']

@[simp] theorem swapVars_swapVars (i : ℕ) (f : MvPolynomial ℕ R) :
    swapVars i (swapVars i f) = f := by
  have : (⇑(Equiv.swap i (i + 1)) ∘ ⇑(Equiv.swap i (i + 1))) = id :=
    funext fun k => Equiv.swap_apply_self _ _ _
  rw [swapVars, rename_rename, this, rename_id, AlgHom.id_apply]

def taylor (i : ℕ) : MvPolynomial ℕ R →ₐ[R] Polynomial (MvPolynomial ℕ R) :=
  aeval fun j => if j = i then Polynomial.C (X (i + 1)) + Polynomial.X else Polynomial.C (X j)

theorem eval_taylor (i : ℕ) (f : MvPolynomial ℕ R) :
    (taylor i f).eval (X i - X (i + 1)) = f := by
  have : ((Polynomial.aeval (X i - X (i + 1) : MvPolynomial ℕ R)).restrictScalars R).comp
      (taylor i) = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro j
    by_cases hj : j = i
    · subst hj; simp [taylor]
    · simp [taylor, hj]
  simpa [Polynomial.coe_aeval_eq_eval] using congrArg (fun g => g f) this

theorem coeff_zero_taylor_swapVars (i : ℕ) (f : MvPolynomial ℕ R) :
    (taylor i (swapVars i f)).coeff 0 = (taylor i f).coeff 0 := by
  have : ((Polynomial.aeval (0 : MvPolynomial ℕ R)).restrictScalars R).comp
      ((taylor i).comp (swapVars i)) =
      ((Polynomial.aeval (0 : MvPolynomial ℕ R)).restrictScalars R).comp (taylor i) := by
    apply MvPolynomial.algHom_ext
    intro j
    by_cases hj : j = i
    · subst hj; simp [taylor]
    by_cases hj' : j = i + 1
    · subst hj'; simp [taylor]
    · simp [taylor, swapVars_X_of_ne hj hj', hj]
  simpa [Polynomial.coe_aeval_eq_eval, Polynomial.coeff_zero_eq_eval_zero]
    using congrArg (fun g => g f) this

theorem divX_smul (c : R) (p : Polynomial (MvPolynomial ℕ R)) :
    Polynomial.divX (c • p) = c • Polynomial.divX p := by
  ext n; simp [Polynomial.coeff_divX]

def divDiff (i : ℕ) : MvPolynomial ℕ R →ₗ[R] MvPolynomial ℕ R where
  toFun f := (Polynomial.divX (taylor i f - taylor i (swapVars i f))).eval (X i - X (i + 1))
  map_add' f g := by
    simp only [map_add]
    rw [add_sub_add_comm, Polynomial.divX_add, Polynomial.eval_add]
  map_smul' c f := by
    simp only [map_smul, ← smul_sub, divX_smul, Polynomial.eval_smul, RingHom.id_apply]

theorem mul_divDiff (i : ℕ) (f : MvPolynomial ℕ R) :
    (X i - X (i + 1)) * divDiff i f = f - swapVars i f := by
  have h := Polynomial.divX_mul_X_add (taylor i f - taylor i (swapVars i f))
  have h2 := congrArg (Polynomial.eval (X i - X (i + 1) : MvPolynomial ℕ R)) h
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_sub, eval_taylor, Polynomial.coeff_sub, coeff_zero_taylor_swapVars,
    sub_self, add_zero] at h2
  rw [← h2, mul_comm]
  rfl

/-- `X i - X j` is a non-zero-divisor for `i ≠ j`, over any commutative ring. -/
theorem eq_zero_of_X_sub_X_mul_eq_zero {i j : ℕ} (hij : i ≠ j) {p : MvPolynomial ℕ R}
    (h : (X i - X j) * p = 0) : p = 0 := by
  classical
  let τ : MvPolynomial ℕ R →ₐ[R] MvPolynomial ℕ R :=
    aeval fun k => if k = i then X i + X j else X k
  let τ' : MvPolynomial ℕ R →ₐ[R] MvPolynomial ℕ R :=
    aeval fun k => if k = i then X i - X j else X k
  have hτ : τ'.comp τ = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro k
    by_cases hk : k = i
    · subst hk; simp [τ, τ', Ne.symm hij]
    · simp [τ, τ', hk]
  have h1 : X i * τ p = 0 := by
    have := congrArg τ h
    simpa [τ, Ne.symm hij] using this
  have h2 : τ p = 0 := by
    ext m
    have := congrArg (coeff (Finsupp.single i 1 + m)) h1
    simpa [coeff_X_mul] using this
  have := congrArg (fun g => g p) hτ
  simpa [h2] using this.symm

theorem X_sub_X_mul_cancel {i j : ℕ} (hij : i ≠ j) {p q : MvPolynomial ℕ R}
    (h : (X i - X j) * p = (X i - X j) * q) : p = q :=
  sub_eq_zero.mp (eq_zero_of_X_sub_X_mul_eq_zero hij (by rw [mul_sub, h, sub_self]))

theorem divDiff_eq_of_mul {i : ℕ} {f g : MvPolynomial ℕ R}
    (h : (X i - X (i + 1)) * g = f - swapVars i f) : divDiff i f = g :=
  X_sub_X_mul_cancel (i := i) (j := i + 1) (by omega) (by rw [mul_divDiff, h])

@[simp] theorem divDiff_X_self (i : ℕ) : divDiff (R := R) i (X i) = 1 :=
  divDiff_eq_of_mul (by simp)

@[simp] theorem divDiff_X_succ (i : ℕ) : divDiff (R := R) i (X (i + 1)) = -1 :=
  divDiff_eq_of_mul (by simp)

theorem divDiff_X_of_ne {i j : ℕ} (h : j ≠ i) (h' : j ≠ i + 1) :
    divDiff (R := R) i (X j) = 0 :=
  divDiff_eq_of_mul (by simp [swapVars_X_of_ne h h'])

theorem divDiff_of_swap_eq {i : ℕ} {f : MvPolynomial ℕ R} (h : swapVars i f = f) :
    divDiff i f = 0 :=
  divDiff_eq_of_mul (by simp [h])

theorem divDiff_mul (i : ℕ) (f g : MvPolynomial ℕ R) :
    divDiff i (f * g) = divDiff i f * g + swapVars i f * divDiff i g := by
  apply divDiff_eq_of_mul
  rw [mul_add, ← mul_assoc, mul_divDiff, mul_left_comm, mul_divDiff, map_mul]
  ring

@[simp] theorem swapVars_divDiff (i : ℕ) (f : MvPolynomial ℕ R) :
    swapVars i (divDiff i f) = divDiff i f := by
  apply X_sub_X_mul_cancel (show i ≠ i + 1 by omega)
  have h := congrArg (swapVars i) (mul_divDiff i f)
  simp only [map_mul, map_sub, swapVars_X_self, swapVars_X_succ, swapVars_swapVars] at h
  linear_combination -h - mul_divDiff i f

@[simp] theorem divDiff_divDiff_apply (i : ℕ) (f : MvPolynomial ℕ R) :
    divDiff i (divDiff i f) = 0 :=
  divDiff_of_swap_eq (swapVars_divDiff i f)

theorem divDiff_mul_of_swap_eq {i : ℕ} {g : MvPolynomial ℕ R} (h : swapVars i g = g)
    (f : MvPolynomial ℕ R) : divDiff i (g * f) = g * divDiff i f := by
  rw [divDiff_mul, divDiff_of_swap_eq h, zero_mul, zero_add, h]

theorem divDiff_X_mul_of_ne {i j : ℕ} (h : j ≠ i) (h' : j ≠ i + 1) (f : MvPolynomial ℕ R) :
    divDiff i (X j * f) = X j * divDiff i f :=
  divDiff_mul_of_swap_eq (swapVars_X_of_ne h h') f

theorem divDiff_X_self_mul (i : ℕ) (f : MvPolynomial ℕ R) :
    divDiff i (X i * f) = f + X (i + 1) * divDiff i f := by
  simp [divDiff_mul]

theorem divDiff_X_succ_mul (i : ℕ) (f : MvPolynomial ℕ R) :
    divDiff i (X (i + 1) * f) = -f + X i * divDiff i f := by
  simp [divDiff_mul]

theorem swapVars_comm {i j : ℕ} (h : i + 1 < j ∨ j + 1 < i) (f : MvPolynomial ℕ R) :
    swapVars i (swapVars j f) = swapVars j (swapVars i f) := by
  simp only [swapVars, rename_rename]
  congr 2
  funext k
  simp only [Function.comp_apply, Equiv.swap_apply_def]
  split_ifs <;> omega

theorem swapVars_divDiff_of_far {i j : ℕ} (h : i + 1 < j ∨ j + 1 < i) (f : MvPolynomial ℕ R) :
    swapVars j (divDiff i f) = divDiff i (swapVars j f) := by
  symm
  apply divDiff_eq_of_mul
  have h1 := congrArg (swapVars j) (mul_divDiff i f)
  rw [map_mul, map_sub, map_sub, swapVars_X_of_ne (by omega) (by omega),
    swapVars_X_of_ne (by omega) (by omega), ← swapVars_comm h] at h1
  exact h1

theorem divDiff_comm_apply {i j : ℕ} (h : i + 1 < j ∨ j + 1 < i) (f : MvPolynomial ℕ R) :
    divDiff i (divDiff j f) = divDiff j (divDiff i f) := by
  apply X_sub_X_mul_cancel (show j ≠ j + 1 by omega)
  have hs : swapVars i (X j - X (j + 1) : MvPolynomial ℕ R) = X j - X (j + 1) := by
    rw [map_sub, swapVars_X_of_ne (by omega) (by omega), swapVars_X_of_ne (by omega) (by omega)]
  rw [← divDiff_mul_of_swap_eq hs, mul_divDiff, mul_divDiff, map_sub,
    swapVars_divDiff_of_far (by omega)]

/-- The alternating sum over the symmetric group on `X i, X (i+1), X (i+2)`, written with
`s = swapVars i`, `t = swapVars (i+1)`. -/
theorem vandermonde_divDiff_braid_left (i : ℕ) (f : MvPolynomial ℕ R) :
    (X i - X (i + 1)) * (X i - X (i + 2)) * (X (i + 1) - X (i + 2)) *
        divDiff i (divDiff (i + 1) (divDiff i f)) =
      f - swapVars i f - swapVars (i + 1) f + swapVars (i + 1) (swapVars i f) +
        swapVars i (swapVars (i + 1) f) - swapVars i (swapVars (i + 1) (swapVars i f)) := by
  have s0 : swapVars (R := R) i (X i) = X (i + 1) := swapVars_X_self i
  have s1 : swapVars (R := R) i (X (i + 1)) = X i := swapVars_X_succ i
  have s2 : swapVars (R := R) i (X (i + 2)) = X (i + 2) := swapVars_X_of_ne (by omega) (by omega)
  have t0 : swapVars (R := R) (i + 1) (X i) = X i := swapVars_X_of_ne (by omega) (by omega)
  have t1 : swapVars (R := R) (i + 1) (X (i + 1)) = X (i + 2) := swapVars_X_self (i + 1)
  have t2 : swapVars (R := R) (i + 1) (X (i + 2)) = X (i + 1) := swapVars_X_succ (i + 1)
  set a := divDiff i f with ha
  set b := divDiff (i + 1) a with hb
  set c := divDiff i b with hc
  have h1 := mul_divDiff i f
  have h2 := mul_divDiff (i + 1) a
  have h3 := mul_divDiff i b
  rw [← ha] at h1
  rw [← hb] at h2
  rw [← hc] at h3
  have hsa : swapVars i a = a := swapVars_divDiff i f
  have h5 := congrArg (swapVars (i + 1)) h1
  have h6 := congrArg (swapVars i) h2
  have h7 := congrArg (fun g => swapVars i (swapVars (i + 1) g)) h1
  simp only [map_mul, map_sub, s0, s1, s2, t0, t1, t2, hsa] at h5 h6 h7
  linear_combination (X i - X (i + 2)) * (X (i + 1) - X (i + 2)) * h3 + (X i - X (i + 2)) * h2
    - (X (i + 1) - X (i + 2)) * h6 - h5 + h7 + h1

theorem vandermonde_divDiff_braid_right (i : ℕ) (f : MvPolynomial ℕ R) :
    (X i - X (i + 1)) * (X i - X (i + 2)) * (X (i + 1) - X (i + 2)) *
        divDiff (i + 1) (divDiff i (divDiff (i + 1) f)) =
      f - swapVars i f - swapVars (i + 1) f + swapVars (i + 1) (swapVars i f) +
        swapVars i (swapVars (i + 1) f) -
          swapVars (i + 1) (swapVars i (swapVars (i + 1) f)) := by
  have s0 : swapVars (R := R) i (X i) = X (i + 1) := swapVars_X_self i
  have s1 : swapVars (R := R) i (X (i + 1)) = X i := swapVars_X_succ i
  have s2 : swapVars (R := R) i (X (i + 2)) = X (i + 2) := swapVars_X_of_ne (by omega) (by omega)
  have t0 : swapVars (R := R) (i + 1) (X i) = X i := swapVars_X_of_ne (by omega) (by omega)
  have t1 : swapVars (R := R) (i + 1) (X (i + 1)) = X (i + 2) := swapVars_X_self (i + 1)
  have t2 : swapVars (R := R) (i + 1) (X (i + 2)) = X (i + 1) := swapVars_X_succ (i + 1)
  set a := divDiff (i + 1) f with ha
  set b := divDiff i a with hb
  set c := divDiff (i + 1) b with hc
  have g1 := mul_divDiff (i + 1) f
  have g2 := mul_divDiff i a
  have g3 := mul_divDiff (i + 1) b
  rw [← ha] at g1
  rw [← hb] at g2
  rw [← hc] at g3
  have hta : swapVars (i + 1) a = a := swapVars_divDiff (i + 1) f
  have g4 := congrArg (swapVars (i + 1)) g2
  have g5 := congrArg (swapVars i) g1
  have g6 := congrArg (fun g => swapVars (i + 1) (swapVars i g)) g1
  simp only [map_mul, map_sub, s0, s1, s2, t0, t1, t2, hta] at g4 g5 g6
  simp only [show i + 1 + 1 = i + 2 from rfl] at g1 g3
  linear_combination (X i - X (i + 1)) * (X i - X (i + 2)) * g3 + (X i - X (i + 2)) * g2
    - (X i - X (i + 1)) * g4 - g5 + g6 + g1

theorem swapVars_braid (i : ℕ) (f : MvPolynomial ℕ R) :
    swapVars i (swapVars (i + 1) (swapVars i f)) =
      swapVars (i + 1) (swapVars i (swapVars (i + 1) f)) := by
  have : (swapVars (R := R) i).comp ((swapVars (i + 1)).comp (swapVars i)) =
      (swapVars (i + 1)).comp ((swapVars i).comp (swapVars (i + 1))) := by
    apply MvPolynomial.algHom_ext
    intro k
    have s2 : swapVars (R := R) i (X (i + 2)) = X (i + 2) :=
      swapVars_X_of_ne (by omega) (by omega)
    have t0 : swapVars (R := R) (i + 1) (X i) = X i := swapVars_X_of_ne (by omega) (by omega)
    have t1 : swapVars (R := R) (i + 1) (X (i + 1)) = X (i + 2) := swapVars_X_self (i + 1)
    have t2 : swapVars (R := R) (i + 1) (X (i + 2)) = X (i + 1) := swapVars_X_succ (i + 1)
    rcases (show k = i ∨ k = i + 1 ∨ k = i + 2 ∨ (k ≠ i ∧ k ≠ i + 1 ∧ k ≠ i + 2) by omega) with
      rfl | rfl | rfl | ⟨h0, h1, h2⟩
    · simp only [AlgHom.comp_apply, swapVars_X_self, swapVars_X_succ, s2, t0, t1, t2]
    · simp only [AlgHom.comp_apply, swapVars_X_self, swapVars_X_succ, s2, t0, t1, t2]
    · simp only [AlgHom.comp_apply, swapVars_X_self, swapVars_X_succ, s2, t0, t1, t2]
    · have a1 : swapVars (R := R) i (X k) = X k := swapVars_X_of_ne h0 h1
      have a2 : swapVars (R := R) (i + 1) (X k) = X k := swapVars_X_of_ne h1 h2
      simp only [AlgHom.comp_apply, a1, a2]
  exact congrArg (fun g => g f) this

theorem divDiff_braid_apply (i : ℕ) (f : MvPolynomial ℕ R) :
    divDiff i (divDiff (i + 1) (divDiff i f)) =
      divDiff (i + 1) (divDiff i (divDiff (i + 1) f)) := by
  have h := (vandermonde_divDiff_braid_left i f).trans
    ((swapVars_braid i f ▸ vandermonde_divDiff_braid_right i f).symm)
  rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc] at h
  have h' := X_sub_X_mul_cancel (by omega) h
  have h'' := X_sub_X_mul_cancel (by omega) h'
  exact X_sub_X_mul_cancel (by omega) h''

end StringDiagrams.NilHecke
