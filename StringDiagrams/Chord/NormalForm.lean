import StringDiagrams.Chord.Basic
import Mathlib.Tactic.Cases

/-!
# The normal form theorem for chord diagrams

For the states, moves and canonical diagrams of `StringDiagrams.Chord.Basic`:

* `canon_cup`: in a pairing, the cup of any adjacent arc can be taken as the last move of the
  canonical diagram, up to `Equiv`;
* `canon_ilv`: a crossing of any two interleaved arcs at adjacent positions can be taken as the
  last move of the canonical diagram, up to `Equiv` (the proof uses the pitchfork move when the
  two arcs meet a third endpoint of one of them, and the braid relation when three arcs pairwise
  interleave);
* `equiv_canon_or_reducible` (**the normal form theorem**): every diagram that fits on the empty
  state is reducible (equivalent to a diagram containing a double crossing or a curl) or
  equivalent to the canonical diagram of its final pairing.

The argument follows A. Lauda, arXiv:0803.3652v3, §8, and M. Khovanov, A. Lauda,
arXiv:0807.3250v1, §3.2.3.
-/

namespace StringDiagrams.Chord

/-! ## Taking a cup last -/

section CupLast

variable {α : Type*}

theorem getElem_eq_of_getElem? {β : Type*} {l l' : List β} {i j : ℕ} (hi : i < l.length)
    (hj : j < l'.length) (h : l[i]? = l'[j]?) : l[i] = l'[j] := by
  rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj] at h
  exact Option.some.inj h

theorem rmAt_rmAt {β : Type*} (s : List β) {r₀ m : ℕ} (h : r₀ ≤ m) (hl : m + 4 ≤ s.length) :
    rmAt (rmAt s (m + 2)) r₀ = rmAt (rmAt s r₀) m := by
  apply List.ext_getElem?; intro i
  rw [getElem?_rmAt _ (by rw [length_rmAt _ (by omega)]; omega), getElem?_rmAt _ (by omega),
    getElem?_rmAt _ (by rw [length_rmAt _ (by omega)]; omega), getElem?_rmAt _ (by omega)]
  congr 1; unfold rmIdx; split_ifs <;> omega

/-- In a pairing, the cup of any adjacent arc can be taken as the last move of the
canonical diagram. -/
theorem canon_cup {s : List (ℕ × α)} (hv : Valid s) {r : ℕ} (hr : Same s r (r + 1)) :
    Equiv (canon s) (canon (rmAt s r) ++ [.cup r (s[r]'hr.lt_left).2]) := by
  induction' hn : s.length using Nat.strong_induction_on with n ih generalizing s r
  classical
  have h : ∃ r, Same s r (r + 1) := ⟨r, hr⟩
  obtain ⟨r₀, hr₀, hmin, hle⟩ : ∃ r₀, Same s r₀ (r₀ + 1) ∧ (∀ r' < r₀, ¬ Same s r' (r' + 1)) ∧
      r₀ ≤ r := ⟨Nat.find h, Nat.find_spec h, fun _ => Nat.find_min h, Nat.find_min' h hr⟩
  rw [canon_adj hv hr₀ hmin]
  rcases hle.eq_or_lt with e | hlt
  · subst e; exact Equiv.refl _
  have h2 : r₀ + 2 ≤ r := by
    by_contra hc
    have e : r = r₀ + 1 := by omega
    subst e
    have := hv.unique hr₀.symm hr
    omega
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by omega⟩
  have hl : m + 4 ≤ s.length := hr.lt_right
  have hr' : Same (rmAt s r₀) m (m + 1) := by
    rw [same_rmAt (by omega)]; simp only [rmIdx]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]; exact hr
  have hr₀' : Same (rmAt s (m + 2)) r₀ (r₀ + 1) := by
    rw [same_rmAt (by omega)]; simp only [rmIdx]
    rw [ite_eq_left (by omega), ite_eq_left (by omega)]; exact hr₀
  have ih1 := ih _ (by rw [← hn, length_rmAt s (by omega)]; omega) (hv.rmAt hr₀) hr' rfl
  have ih2 := ih _ (by rw [← hn, length_rmAt s (by omega)]; omega) (hv.rmAt hr) hr₀' rfl
  have ea' : (rmAt s r₀)[m]? = s[m + 2]? := by
    rw [getElem?_rmAt s (by omega)]; simp only [rmIdx]; rw [ite_eq_right (by omega)]
  have eb' : (rmAt s (m + 2))[r₀]? = s[r₀]? := by
    rw [getElem?_rmAt s (by omega)]; simp only [rmIdx]; rw [ite_eq_left (by omega)]
  have ea : ((rmAt s r₀)[m]'hr'.lt_left).2 = (s[m + 2]'hr.lt_left).2 := by
    rw [getElem_eq_of_getElem? hr'.lt_left hr.lt_left ea']
  have eb : ((rmAt s (m + 2))[r₀]'hr₀'.lt_left).2 = (s[r₀]'hr₀.lt_left).2 := by
    rw [getElem_eq_of_getElem? hr₀'.lt_left hr₀.lt_left eb']
  rw [ea] at ih1
  rw [eb, rmAt_rmAt s (by omega) hl] at ih2
  refine (ih1.append_right _).trans (Equiv.trans ?_ (ih2.symm.append_right _))
  have := Equiv.step_mid (Step.uu (s[m + 2]'hr.lt_left).2 (s[r₀]'hr₀.lt_left).2 (g := m)
    (g' := r₀) (by omega)) (canon (rmAt (rmAt s r₀) m)) []
  simpa using this

end CupLast

/-! ## Taking a crossing last -/

section CrossLast

variable {α : Type*}

theorem tau_left (p : ℕ) : tau p p = p + 1 := by simp [tau]

theorem tau_right (p : ℕ) : tau p (p + 1) = p := by simp [tau]

theorem tau_of_ne {p i : ℕ} (h1 : i ≠ p) (h2 : i ≠ p + 1) : tau p i = i := by simp [tau, h1, h2]

theorem swapAt_comm {β : Type*} (s : List β) {p p' : ℕ} (h : p + 2 ≤ p') (hl : p' + 1 < s.length) :
    swapAt (swapAt s p) p' = swapAt (swapAt s p') p := by
  apply List.ext_getElem?; intro i
  rw [getElem?_swapAt _ (by simp; omega), getElem?_swapAt _ (by omega),
    getElem?_swapAt _ (by simp; omega), getElem?_swapAt _ (by omega)]
  congr 1; unfold tau; split_ifs <;> omega

theorem tau_braid (p i : ℕ) : tau p (tau (p + 1) (tau p i)) = tau (p + 1) (tau p (tau (p + 1) i)) := by
  rcases (show i = p ∨ i = p + 1 ∨ i = p + 1 + 1 ∨ (i ≠ p ∧ i ≠ p + 1 ∧ i ≠ p + 1 + 1) by omega) with
    rfl | rfl | rfl | ⟨h1, h2, h3⟩
  · simp (disch := omega) only [tau_left, tau_of_ne]
  · simp (disch := omega) only [tau_left, tau_right, tau_of_ne]
  · simp (disch := omega) only [tau_right, tau_of_ne]
  · simp (disch := omega) only [tau_of_ne]

theorem swapAt_braid {β : Type*} (s : List β) {p : ℕ} (hl : p + 2 < s.length) :
    swapAt (swapAt (swapAt s p) (p + 1)) p = swapAt (swapAt (swapAt s (p + 1)) p) (p + 1) := by
  apply List.ext_getElem?; intro i
  rw [getElem?_swapAt _ (by simp; omega), getElem?_swapAt _ (by simp; omega),
    getElem?_swapAt _ (by omega), getElem?_swapAt _ (by simp; omega),
    getElem?_swapAt _ (by simp; omega), getElem?_swapAt _ (by omega)]
  rw [tau_braid]

theorem rmAt_swapAt {β : Type*} (s : List β) {q q' r : ℕ}
    (h : (q + 2 ≤ r ∧ q' = q) ∨ (r + 2 ≤ q ∧ q' + 2 = q))
    (hq : q + 1 < s.length) (hr : r + 2 ≤ s.length) :
    rmAt (swapAt s q) r = swapAt (rmAt s r) q' := by
  apply List.ext_getElem?; intro i
  rw [getElem?_rmAt _ (by simp; omega), getElem?_swapAt _ hq,
    getElem?_swapAt _ (by rw [length_rmAt _ hr]; omega), getElem?_rmAt _ hr]
  congr 1; unfold tau rmIdx; split_ifs <;> omega

theorem rmAt_swapAt_pitch {β : Type*} (s : List β) {q : ℕ} (hl : q + 2 < s.length) :
    rmAt (swapAt s q) (q + 1) = rmAt (swapAt s (q + 1)) q := by
  apply List.ext_getElem?; intro i
  rw [getElem?_rmAt _ (by simp; omega), getElem?_swapAt _ (by omega),
    getElem?_rmAt _ (by simp; omega), getElem?_swapAt _ (by omega)]
  congr 1; unfold tau rmIdx; split_ifs <;> omega

theorem swapAt_getElem? {β : Type*} (s : List β) {p i : ℕ} (hp : p + 1 < s.length) (h1 : i ≠ p)
    (h2 : i ≠ p + 1) : (swapAt s p)[i]? = s[i]? := by
  rw [getElem?_swapAt s hp, tau_of_ne h1 h2]

/-- A partner in a swapped state. -/
theorem same_swapAt_of {s : List (ℕ × α)} {p x y : ℕ} (hp : p + 1 < s.length)
    (h : Same s (tau p x) y) : Same (swapAt s p) x (tau p y) := by
  rw [same_swapAt hp, tau_tau]; exact h

theorem Valid.eq_of_same {s : List (ℕ × α)} (hv : Valid s) {x y x' y' : ℕ} (h : Same s x y)
    (h' : Same s x' y') (e : x = x') : y = y' := by
  subst e; exact hv.unique h h'

/-- The induction hypothesis of `canon_ilv`. -/
def ExHyp (n : ℕ) : Prop :=
  ∀ t : List (ℕ × α), t.length + cr t < n → Valid t → ∀ q, Ilv t q →
    Equiv (canon t) (canon (swapAt t q) ++ [.cross q])

theorem ExHyp.apply {n : ℕ} (ih : ExHyp (α := α) n) {t : List (ℕ × α)} (hv : Valid t) {q : ℕ}
    (h : Ilv t q) (hn : t.length + cr t < n) :
    Equiv (canon t) (canon (swapAt t q) ++ [.cross q]) := ih t hn hv q h

end CrossLast

section CrossLastCases

variable {α : Type*}

/-- `canon_ilv`, the case of a pairing with an adjacent arc. -/
theorem ex_adj {t : List (ℕ × α)} (hv : Valid t) {q r : ℕ} (h : Ilv t q)
    (hr : Same t r (r + 1)) (ih : ExHyp (α := α) (t.length + cr t)) :
    Equiv (canon t) (canon (swapAt t q) ++ [.cross q]) := by
  have hq := h.lt
  obtain ⟨a, ha⟩ := hv.exists (show q < t.length by omega)
  obtain ⟨b, hb⟩ := hv.exists hq
  have hilv := (ilv_iff hv ha hb).1 h
  have hl2 : r + 2 ≤ t.length := hr.lt_right
  have u1 : q = r → a = r + 1 := fun e => hv.eq_of_same ha hr e
  have u2 : q = r + 1 → a = r := fun e => hv.eq_of_same ha hr.symm e
  have u3 : q + 1 = r → b = r + 1 := fun e => hv.eq_of_same hb hr e
  have u4 : q + 1 = r + 1 → b = r := fun e => hv.eq_of_same hb hr.symm e
  have u5 : a = r → q = r + 1 := fun e => hv.eq_of_same ha.symm hr e
  have u6 : a = r + 1 → q = r := fun e => hv.eq_of_same ha.symm hr.symm e
  have u7 : b = r → q + 1 = r + 1 := fun e => hv.eq_of_same hb.symm hr e
  have u8 : b = r + 1 → q + 1 = r := fun e => hv.eq_of_same hb.symm hr.symm e
  have hqa := ha.ne
  have hqb := hb.ne
  obtain ⟨q', hq'⟩ : ∃ q', (q + 2 ≤ r ∧ q' = q) ∨ (r + 2 ≤ q ∧ q' + 2 = q) := by
    by_cases hc : q + 2 ≤ r
    · exact ⟨q, Or.inl ⟨hc, rfl⟩⟩
    · exact ⟨q - 2, Or.inr ⟨by omega, by omega⟩⟩
  have ht0 := hv.rmAt hr
  have ra : rmIdx r (if a < r then a else a - 2) = a := by unfold rmIdx; split_ifs <;> omega
  have rb : rmIdx r (if b < r then b else b - 2) = b := by unfold rmIdx; split_ifs <;> omega
  have rq : rmIdx r q' = q := by unfold rmIdx; split_ifs <;> omega
  have rq1 : rmIdx r (q' + 1) = q + 1 := by unfold rmIdx; split_ifs <;> omega
  have ha0 : Same (rmAt t r) q' (if a < r then a else a - 2) := by
    rw [same_rmAt hl2, ra, rq]; exact ha
  have hb0 : Same (rmAt t r) (q' + 1) (if b < r then b else b - 2) := by
    rw [same_rmAt hl2, rb, rq1]; exact hb
  have hilv0 : Ilv (rmAt t r) q' := by
    rw [ilv_iff ht0 ha0 hb0]; split_ifs <;> omega
  have e1 := ih.apply ht0 hilv0 (by
    rw [length_rmAt t hl2]; have := cr_rmAt_le (s := t) hl2; omega)
  have c1 := canon_cup hv hr
  have hr' : Same (swapAt t q) r (r + 1) := by
    rw [same_swapAt hq, tau_of_ne (by omega) (by omega), tau_of_ne (by omega) (by omega)]
    exact hr
  have c2 := canon_cup (hv.swapAt hq) hr'
  rw [rmAt_swapAt t hq' hq hl2] at c2
  have ex : ((swapAt t q)[r]'hr'.lt_left).2 = (t[r]'hr.lt_left).2 := by
    rw [getElem_eq_of_getElem? hr'.lt_left hr.lt_left
      (swapAt_getElem? t hq (by omega) (by omega))]
  rw [ex] at c2
  refine c1.trans ((e1.append_right _).trans (Equiv.trans ?_ (c2.symm.append_right _)))
  rcases hq' with ⟨hc, rfl⟩ | ⟨hc, rfl⟩
  · simpa using Equiv.step_mid (Step.xuL (t[r]'hr.lt_left).2 hc) (canon (swapAt (rmAt t r) q')) []
  · simpa using Equiv.step_mid (Step.xuR (t[r]'hr.lt_left).2 (show r ≤ q' by omega))
      (canon (swapAt (rmAt t r) q')) []

theorem tau_cases (p i : ℕ) : (i = p ∧ tau p i = p + 1) ∨ (i = p + 1 ∧ tau p i = p) ∨
    (i ≠ p ∧ i ≠ p + 1 ∧ tau p i = i) := by
  unfold tau; split_ifs <;> omega

/-- Exchanging two adjacent endpoints away from `q, q + 1` does not change whether the arcs at
`q, q + 1` interleave, unless these are the two arcs exchanged. -/
theorem ilv_swapAt_of_ne {t : List (ℕ × α)} (hv : Valid t) {p q a b : ℕ}
    (hp : p + 1 < t.length) (far : q + 2 ≤ p ∨ p + 2 ≤ q) (ha : Same t q a)
    (hb : Same t (q + 1) b) (hpair : ¬ (a = p ∧ b = p + 1) ∧ ¬ (a = p + 1 ∧ b = p)) :
    Ilv (swapAt t p) q ↔ Ilv t q := by
  have ha' : Same (swapAt t p) q (tau p a) :=
    same_swapAt_of hp (by rw [tau_of_ne (by omega) (by omega)]; exact ha)
  have hb' : Same (swapAt t p) (q + 1) (tau p b) :=
    same_swapAt_of hp (by rw [tau_of_ne (by omega) (by omega)]; exact hb)
  have hab : a ≠ b := fun e => by subst e; have := hv.unique ha.symm hb.symm; omega
  have := ha.ne; have := hb.ne
  rw [ilv_iff (hv.swapAt hp) ha' hb', ilv_iff hv ha hb]
  rcases tau_cases p a with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h1', h2⟩ <;>
    rcases tau_cases p b with ⟨h4, h5⟩ | ⟨h4, h5⟩ | ⟨h4, h4', h5⟩ <;>
    rw [h2, h5] <;> constructor <;> intro <;> omega

/-- `canon_ilv`, the case of crossings at distant positions. -/
theorem ex_far {t : List (ℕ × α)} (hv : Valid t) {q q₀ : ℕ} (h : Ilv t q)
    (hno : ∀ r, ¬ Same t r (r + 1)) (ho : Opn t q₀) (hc : Cls t (q₀ + 1))
    (hcanon : canon t = canon (swapAt t q₀) ++ [.cross q₀])
    (far : q + 2 ≤ q₀ ∨ q₀ + 2 ≤ q) (ih : ExHyp (α := α) (t.length + cr t)) :
    Equiv (canon t) (canon (swapAt t q) ++ [.cross q]) := by
  have hq := h.lt
  obtain ⟨a₀, hqa₀, ha₀⟩ := ho
  obtain ⟨b₀, hb₀q, hb₀⟩ := hc
  have hq₀ : q₀ + 1 < t.length := hb₀.lt_left
  have n1 : a₀ ≠ q₀ + 1 := fun e => hno q₀ (e ▸ ha₀)
  have n2 : b₀ ≠ q₀ := fun e => hno q₀ (e ▸ hb₀).symm
  have hilv₀ : Ilv t q₀ := by rw [ilv_iff hv ha₀ hb₀]; omega
  obtain ⟨a, ha⟩ := hv.exists (show q < t.length by omega)
  obtain ⟨b, hb⟩ := hv.exists hq
  have u1 : a = q₀ → q = a₀ := fun e => hv.eq_of_same ha.symm ha₀ e
  have u2 : a = q₀ + 1 → q = b₀ := fun e => hv.eq_of_same ha.symm hb₀ e
  have u3 : b = q₀ → q + 1 = a₀ := fun e => hv.eq_of_same hb.symm ha₀ e
  have u4 : b = q₀ + 1 → q + 1 = b₀ := fun e => hv.eq_of_same hb.symm hb₀ e
  have u5 : a₀ = q → q₀ = a := fun e => hv.eq_of_same ha₀.symm ha e
  have u6 : a₀ = q + 1 → q₀ = b := fun e => hv.eq_of_same ha₀.symm hb e
  have u7 : b₀ = q → q₀ + 1 = a := fun e => hv.eq_of_same hb₀.symm ha e
  have u8 : b₀ = q + 1 → q₀ + 1 = b := fun e => hv.eq_of_same hb₀.symm hb e
  have hilv1 : Ilv (swapAt t q₀) q :=
    (ilv_swapAt_of_ne hv hq₀ far ha hb ⟨by omega, by omega⟩).2 h
  have e1 := ih.apply (hv.swapAt hq₀) hilv1
    (by rw [length_swapAt]; have := cr_swapAt_lt hv hilv₀; omega)
  have hilv2 : Ilv (swapAt t q) q₀ :=
    (ilv_swapAt_of_ne hv hq (by omega) ha₀ hb₀ ⟨by omega, by omega⟩).2 hilv₀
  have e2 := ih.apply (hv.swapAt hq) hilv2
    (by rw [length_swapAt]; have := cr_swapAt_lt hv h; omega)
  have ecomm : swapAt (swapAt t q₀) q = swapAt (swapAt t q) q₀ := by
    rcases far with hf | hf
    · exact (swapAt_comm t hf hq₀).symm
    · exact swapAt_comm t hf hq
  rw [ecomm] at e1
  rw [hcanon]
  refine (e1.append_right _).trans (Equiv.trans ?_ (e2.symm.append_right _))
  rcases far with hf | hf
  · simpa using Equiv.step_mid (Step.xx (α := α) hf) (canon (swapAt (swapAt t q) q₀)) []
  · simpa using (Equiv.step_mid (Step.xx (α := α) hf) (canon (swapAt (swapAt t q) q₀)) []).symm

/-- `canon_ilv`, the case `q = q₀ + 1`. Either the arc at `q₀` ends at `q₀ + 2` (a pitchfork
move) or the three arcs at `q₀, q₀ + 1, q₀ + 2` pairwise interleave (a braid move). -/
theorem ex_right {t : List (ℕ × α)} (hv : Valid t) {q₀ : ℕ} (h : Ilv t (q₀ + 1))
    (hno : ∀ r, ¬ Same t r (r + 1)) (ho : Opn t q₀) (hc : Cls t (q₀ + 1))
    (hcanon : canon t = canon (swapAt t q₀) ++ [.cross q₀])
    (ih : ExHyp (α := α) (t.length + cr t)) :
    Equiv (canon t) (canon (swapAt t (q₀ + 1)) ++ [.cross (q₀ + 1)]) := by
  have hq := h.lt
  obtain ⟨a₀, hqa₀, ha₀⟩ := ho
  obtain ⟨b₀, hb₀q, hb₀⟩ := hc
  have hq₀ : q₀ + 1 < t.length := hb₀.lt_left
  have n1 : a₀ ≠ q₀ + 1 := fun e => hno q₀ (e ▸ ha₀)
  have n2 : b₀ ≠ q₀ := fun e => hno q₀ (e ▸ hb₀).symm
  have hilv₀ : Ilv t q₀ := by rw [ilv_iff hv ha₀ hb₀]; omega
  obtain ⟨c, hc⟩ := hv.exists hq
  have hcb := (ilv_iff hv hb₀ hc).1 h
  have hc1 : c ≠ q₀ + 1 := by omega
  have u1 : c = q₀ → a₀ = q₀ + 1 + 1 := fun e => hv.eq_of_same ha₀ hc.symm e.symm
  have u2 : a₀ = q₀ + 1 + 1 → c = q₀ := fun e => hv.eq_of_same hc ha₀.symm e.symm
  rw [hcanon]
  rcases (show c = q₀ ∨ c < q₀ by omega) with hcq | hcq
  · -- the pitchfork configuration
    have ea := u1 hcq
    subst ea
    have hs1 : Same (swapAt t q₀) (q₀ + 1) (q₀ + 1 + 1) := by
      have := same_swapAt_of (x := q₀ + 1) hq₀ (by rw [tau_right]; exact ha₀)
      rwa [tau_of_ne (by omega) (by omega)] at this
    have hs2 : Same (swapAt t (q₀ + 1)) q₀ (q₀ + 1) := by
      have := same_swapAt_of (x := q₀) hq (by rw [tau_of_ne (by omega) (by omega)]; exact ha₀)
      rwa [tau_right] at this
    have c1 := canon_cup (hv.swapAt hq₀) hs1
    have c2 := canon_cup (hv.swapAt hq) hs2
    have x1 : ((swapAt t q₀)[q₀ + 1]'hs1.lt_left).2 = (t[q₀]'(by omega)).2 := by
      rw [getElem_eq_of_getElem? (l := swapAt t q₀) (l' := t) (i := q₀ + 1) (j := q₀) hs1.lt_left (by omega)
        (by rw [getElem?_swapAt t hq₀, tau_right])]
    have x2 : ((swapAt t (q₀ + 1))[q₀]'hs2.lt_left).2 = (t[q₀]'(by omega)).2 := by
      rw [getElem_eq_of_getElem? (l := swapAt t (q₀ + 1)) (l' := t) (i := q₀) (j := q₀) hs2.lt_left (by omega)
        (by rw [getElem?_swapAt t hq, tau_of_ne (by omega) (by omega)])]
    rw [x1, rmAt_swapAt_pitch t hq] at c1
    rw [x2] at c2
    refine (c1.append_right _).trans (Equiv.trans ?_ (c2.symm.append_right _))
    have := (Equiv.step_mid (Step.pitch q₀ (t[q₀]'(by omega)).2)
      (canon (rmAt (swapAt t (q₀ + 1)) q₀)) []).symm
    simpa using this
  · -- the triangle configuration
    have ha₀' : q₀ + 1 + 1 < a₀ := by
      rcases (show a₀ = q₀ + 1 + 1 ∨ q₀ + 1 + 1 < a₀ by omega) with e | e
      · have := u2 e; omega
      · exact e
    set t₁ := swapAt t q₀ with ht₁
    set t₂ := swapAt t₁ (q₀ + 1) with ht₂
    set u := swapAt t (q₀ + 1) with hu
    set u₁ := swapAt u q₀ with hu₁
    have hv₁ : Valid t₁ := hv.swapAt hq₀
    have hq₁ : q₀ + 1 + 1 < t₁.length := by rw [ht₁, length_swapAt]; exact hq
    have hv₂ : Valid t₂ := hv₁.swapAt hq₁
    have hvu : Valid u := hv.swapAt hq
    have hqu : q₀ + 1 < u.length := by rw [hu, length_swapAt]; omega
    have hvu₁ : Valid u₁ := hvu.swapAt hqu
    -- partners in `t₁`
    have p1 : Same t₁ (q₀ + 1) a₀ := by
      have := same_swapAt_of (x := q₀ + 1) hq₀ (by rw [tau_right]; exact ha₀)
      rwa [tau_of_ne (by omega) (by omega)] at this
    have p2 : Same t₁ (q₀ + 1 + 1) c := by
      have := same_swapAt_of (x := q₀ + 1 + 1) hq₀
        (by rw [tau_of_ne (by omega) (by omega)]; exact hc)
      rwa [tau_of_ne (by omega) (by omega)] at this
    have p3 : Same t₁ q₀ b₀ := by
      have := same_swapAt_of (x := q₀) hq₀ (by rw [tau_left]; exact hb₀)
      rwa [tau_of_ne (by omega) (by omega)] at this
    have i1 : Ilv t₁ (q₀ + 1) := by rw [ilv_iff hv₁ p1 p2]; omega
    -- partners in `t₂`
    have p4 : Same t₂ q₀ b₀ := by
      have := same_swapAt_of (x := q₀) hq₁ (by rw [tau_of_ne (by omega) (by omega)]; exact p3)
      rwa [tau_of_ne (by omega) (by omega)] at this
    have p5 : Same t₂ (q₀ + 1) c := by
      have := same_swapAt_of (x := q₀ + 1) hq₁ (by rw [tau_left]; exact p2)
      rwa [tau_of_ne (by omega) (by omega)] at this
    have i2 : Ilv t₂ q₀ := by rw [ilv_iff hv₂ p4 p5]; omega
    -- partners in `u`
    have p6 : Same u q₀ a₀ := by
      have := same_swapAt_of (x := q₀) hq (by rw [tau_of_ne (by omega) (by omega)]; exact ha₀)
      rwa [tau_of_ne (by omega) (by omega)] at this
    have p7 : Same u (q₀ + 1) c := by
      have := same_swapAt_of (x := q₀ + 1) hq (by rw [tau_left]; exact hc)
      rwa [tau_of_ne (by omega) (by omega)] at this
    have p8 : Same u (q₀ + 1 + 1) b₀ := by
      have := same_swapAt_of (x := q₀ + 1 + 1) hq (by rw [tau_right]; exact hb₀)
      rwa [tau_of_ne (by omega) (by omega)] at this
    have i3 : Ilv u q₀ := by rw [ilv_iff hvu p6 p7]; omega
    -- partners in `u₁`
    have p9 : Same u₁ (q₀ + 1) a₀ := by
      have := same_swapAt_of (x := q₀ + 1) hqu (by rw [tau_right]; exact p6)
      rwa [tau_of_ne (by omega) (by omega)] at this
    have p10 : Same u₁ (q₀ + 1 + 1) b₀ := by
      have := same_swapAt_of (x := q₀ + 1 + 1) hqu
        (by rw [tau_of_ne (by omega) (by omega)]; exact p8)
      rwa [tau_of_ne (by omega) (by omega)] at this
    have i4 : Ilv u₁ (q₀ + 1) := by rw [ilv_iff hvu₁ p9 p10]; omega
    have m1 : cr t₁ < cr t := cr_swapAt_lt hv hilv₀
    have m2 : cr t₂ < cr t₁ := cr_swapAt_lt hv₁ i1
    have m3 : cr u < cr t := cr_swapAt_lt hv h
    have m4 : cr u₁ < cr u := cr_swapAt_lt hvu i3
    have l1 : t₁.length = t.length := by simp [ht₁]
    have e1 := ih.apply hv₁ i1 (by omega)
    have l2 : t₂.length = t.length := by simp [ht₂, ht₁]
    have e2 := ih.apply hv₂ i2 (by omega)
    have l3 : u.length = t.length := by simp [hu]
    have e3 := ih.apply hvu i3 (by omega)
    have l4 : u₁.length = t.length := by simp [hu₁, hu]
    have e4 := ih.apply hvu₁ i4 (by omega)
    have eb : swapAt t₂ q₀ = swapAt u₁ (q₀ + 1) := swapAt_braid t (by omega)
    rw [eb] at e2
    have s1 := e1.append_right [Move.cross q₀]
    have s2 := e2.append_right [Move.cross (q₀ + 1), Move.cross q₀]
    have s3 := Equiv.step_mid (Step.braid (α := α) q₀) (canon (swapAt u₁ (q₀ + 1))) []
    have s4 := e4.symm.append_right [Move.cross q₀, Move.cross (q₀ + 1)]
    have s5 := e3.symm.append_right [Move.cross (q₀ + 1)]
    simp only [List.append_assoc, List.cons_append, List.nil_append,
      List.append_nil] at s1 s2 s3 s4 s5 ⊢
    exact s1.trans (s2.trans (s3.trans (s4.trans s5)))

/-- `canon_ilv`, the case `q + 1 = q₀`: a pitchfork move or a braid move, mirror to
`ex_right`. -/
theorem ex_left {t : List (ℕ × α)} (hv : Valid t) {P : ℕ} (h : Ilv t P)
    (hno : ∀ r, ¬ Same t r (r + 1)) (ho : Opn t (P + 1)) (hc : Cls t (P + 1 + 1))
    (hcanon : canon t = canon (swapAt t (P + 1)) ++ [.cross (P + 1)])
    (ih : ExHyp (α := α) (t.length + cr t)) :
    Equiv (canon t) (canon (swapAt t P) ++ [.cross P]) := by
  have hP := h.lt
  obtain ⟨a₀, hqa₀, ha₀⟩ := ho
  obtain ⟨b₀, hb₀q, hb₀⟩ := hc
  have hq₀ : P + 1 + 1 < t.length := hb₀.lt_left
  have n1 : a₀ ≠ P + 1 + 1 := fun e => hno (P + 1) (e ▸ ha₀)
  have n2 : b₀ ≠ P + 1 := fun e => hno (P + 1) (e ▸ hb₀).symm
  have hilv₀ : Ilv t (P + 1) := by rw [ilv_iff hv ha₀ hb₀]; omega
  obtain ⟨d, hd⟩ := hv.exists (show P < t.length by omega)
  have hda := (ilv_iff hv hd ha₀).1 h
  have u1 : d = P + 1 + 1 → b₀ = P := fun e => hv.eq_of_same hb₀ hd.symm e.symm
  have u2 : b₀ = P → d = P + 1 + 1 := fun e => hv.eq_of_same hd hb₀.symm e.symm
  rw [hcanon]
  rcases (show d = P + 1 + 1 ∨ P + 1 + 1 < d by omega) with hdq | hdq
  · -- the pitchfork configuration
    have eb := u1 hdq
    subst hdq; subst b₀
    have hs1 : Same (swapAt t (P + 1)) P (P + 1) := by
      have := same_swapAt_of (x := P) hq₀ (by rw [tau_of_ne (by omega) (by omega)]; exact hd)
      rwa [tau_right] at this
    have hs2 : Same (swapAt t P) (P + 1) (P + 1 + 1) := by
      have := same_swapAt_of (x := P + 1) hP (by rw [tau_right]; exact hd)
      rwa [tau_of_ne (by omega) (by omega)] at this
    have c1 := canon_cup (hv.swapAt hq₀) hs1
    have c2 := canon_cup (hv.swapAt hP) hs2
    have x1 : ((swapAt t (P + 1))[P]'hs1.lt_left).2 = (t[P]'(by omega)).2 := by
      rw [getElem_eq_of_getElem? (l := swapAt t (P + 1)) (l' := t) (i := P) (j := P) hs1.lt_left
        (by omega) (by rw [getElem?_swapAt t hq₀, tau_of_ne (by omega) (by omega)])]
    have x2 : ((swapAt t P)[P + 1]'hs2.lt_left).2 = (t[P]'(by omega)).2 := by
      rw [getElem_eq_of_getElem? (l := swapAt t P) (l' := t) (i := P + 1) (j := P) hs2.lt_left
        (by omega) (by rw [getElem?_swapAt t hP, tau_right])]
    rw [x1] at c1
    rw [x2, rmAt_swapAt_pitch t hq₀] at c2
    refine (c1.append_right _).trans (Equiv.trans ?_ (c2.symm.append_right _))
    have := Equiv.step_mid (Step.pitch P (t[P]'(by omega)).2) (canon (rmAt (swapAt t (P + 1)) P)) []
    simpa using this
  · -- the triangle configuration
    have hb₀' : b₀ < P := by
      rcases (show b₀ = P ∨ b₀ < P by omega) with e | e
      · have := u2 e; omega
      · exact e
    set t₁ := swapAt t (P + 1) with ht₁
    set t₂ := swapAt t₁ P with ht₂
    set u := swapAt t P with hu
    set u₁ := swapAt u (P + 1) with hu₁
    have hv₁ : Valid t₁ := hv.swapAt hq₀
    have hq₁ : P + 1 < t₁.length := by rw [ht₁, length_swapAt]; exact hP
    have hv₂ : Valid t₂ := hv₁.swapAt hq₁
    have hvu : Valid u := hv.swapAt hP
    have hqu : P + 1 + 1 < u.length := by rw [hu, length_swapAt]; omega
    have hvu₁ : Valid u₁ := hvu.swapAt hqu
    -- partners in `t₁`
    have p1 : Same t₁ P d := by
      have := same_swapAt_of (x := P) hq₀ (by rw [tau_of_ne (by omega) (by omega)]; exact hd)
      rwa [tau_of_ne (by omega) (by omega)] at this
    have p2 : Same t₁ (P + 1) b₀ := by
      have := same_swapAt_of (x := P + 1) hq₀ (by rw [tau_left]; exact hb₀)
      rwa [tau_of_ne (by omega) (by omega)] at this
    have p3 : Same t₁ (P + 1 + 1) a₀ := by
      have := same_swapAt_of (x := P + 1 + 1) hq₀ (by rw [tau_right]; exact ha₀)
      rwa [tau_of_ne (by omega) (by omega)] at this
    have i1 : Ilv t₁ P := by rw [ilv_iff hv₁ p1 p2]; omega
    -- partners in `t₂`
    have p4 : Same t₂ (P + 1) d := by
      have := same_swapAt_of (x := P + 1) hq₁ (by rw [tau_right]; exact p1)
      rwa [tau_of_ne (by omega) (by omega)] at this
    have p5 : Same t₂ (P + 1 + 1) a₀ := by
      have := same_swapAt_of (x := P + 1 + 1) hq₁
        (by rw [tau_of_ne (by omega) (by omega)]; exact p3)
      rwa [tau_of_ne (by omega) (by omega)] at this
    have i2 : Ilv t₂ (P + 1) := by rw [ilv_iff hv₂ p4 p5]; omega
    -- partners in `u`
    have p6 : Same u (P + 1) d := by
      have := same_swapAt_of (x := P + 1) hP (by rw [tau_right]; exact hd)
      rwa [tau_of_ne (by omega) (by omega)] at this
    have p7 : Same u (P + 1 + 1) b₀ := by
      have := same_swapAt_of (x := P + 1 + 1) hP (by rw [tau_of_ne (by omega) (by omega)]; exact hb₀)
      rwa [tau_of_ne (by omega) (by omega)] at this
    have p8 : Same u P a₀ := by
      have := same_swapAt_of (x := P) hP (by rw [tau_left]; exact ha₀)
      rwa [tau_of_ne (by omega) (by omega)] at this
    have i3 : Ilv u (P + 1) := by rw [ilv_iff hvu p6 p7]; omega
    -- partners in `u₁`
    have p9 : Same u₁ P a₀ := by
      have := same_swapAt_of (x := P) hqu (by rw [tau_of_ne (by omega) (by omega)]; exact p8)
      rwa [tau_of_ne (by omega) (by omega)] at this
    have p10 : Same u₁ (P + 1) b₀ := by
      have := same_swapAt_of (x := P + 1) hqu (by rw [tau_left]; exact p7)
      rwa [tau_of_ne (by omega) (by omega)] at this
    have i4 : Ilv u₁ P := by rw [ilv_iff hvu₁ p9 p10]; omega
    have m1 : cr t₁ < cr t := cr_swapAt_lt hv hilv₀
    have m2 : cr t₂ < cr t₁ := cr_swapAt_lt hv₁ i1
    have m3 : cr u < cr t := cr_swapAt_lt hv h
    have m4 : cr u₁ < cr u := cr_swapAt_lt hvu i3
    have l1 : t₁.length = t.length := by simp [ht₁]
    have l2 : t₂.length = t.length := by simp [ht₂, ht₁]
    have l3 : u.length = t.length := by simp [hu]
    have l4 : u₁.length = t.length := by simp [hu₁, hu]
    have e1 := ih.apply hv₁ i1 (by omega)
    have e2 := ih.apply hv₂ i2 (by omega)
    have e3 := ih.apply hvu i3 (by omega)
    have e4 := ih.apply hvu₁ i4 (by omega)
    have eb : swapAt u₁ P = swapAt t₂ (P + 1) := swapAt_braid t (by omega)
    rw [← eb] at e2
    have s1 := e1.append_right [Move.cross (P + 1)]
    have s2 := e2.append_right [Move.cross P, Move.cross (P + 1)]
    have s3 := (Equiv.step_mid (Step.braid (α := α) P) (canon (swapAt u₁ P)) []).symm
    have s4 := e4.symm.append_right [Move.cross (P + 1), Move.cross P]
    have s5 := e3.symm.append_right [Move.cross P]
    simp only [List.append_assoc, List.cons_append, List.nil_append,
      List.append_nil] at s1 s2 s3 s4 s5 ⊢
    exact s1.trans (s2.trans (s3.trans (s4.trans s5)))

/-- In a pairing, if the arcs at `q` and `q + 1` interleave, the crossing at `q` can be
taken as the last move of the canonical diagram. -/
theorem canon_ilv {t : List (ℕ × α)} (hv : Valid t) {q : ℕ} (h : Ilv t q) :
    Equiv (canon t) (canon (swapAt t q) ++ [.cross q]) := by
  suffices H : ∀ n, ExHyp (α := α) n from H _ t (Nat.lt_succ_self _) hv q h
  intro n
  induction n with
  | zero => intro t ht; omega
  | succ n ih =>
    intro t ht hv q h
    have ih' : ExHyp (α := α) (t.length + cr t) := fun t' ht' => ih t' (by omega)
    by_cases hadj : ∃ r, Same t r (r + 1)
    · obtain ⟨r, hr⟩ := hadj
      exact ex_adj hv h hr ih'
    · have hno : ∀ r, ¬ Same t r (r + 1) := fun r hr => hadj ⟨r, hr⟩
      have hne : t ≠ [] := by
        rintro rfl; have := h.lt; simp at this
      obtain ⟨q₀, ho, hc, hcanon, -⟩ := canon_cross hv hno hne
      rcases (show q = q₀ ∨ q = q₀ + 1 ∨ q + 1 = q₀ ∨ q + 2 ≤ q₀ ∨ q₀ + 2 ≤ q by omega) with
        e | e | e | e | e
      · subst e; rw [hcanon]
      · subst e; exact ex_right hv h hno ho hc hcanon ih'
      · subst e; exact ex_left hv h hno ho hc hcanon ih'
      · exact ex_far hv h hno ho hc hcanon (Or.inl e) ih'
      · exact ex_far hv h hno ho hc hcanon (Or.inr e) ih'

end CrossLastCases

/-! ## Diagrams and the normal form theorem -/

section Run

variable {α : Type*} (d : α → α)

/-- Whether a move can be applied to a state with `n` strands. -/
def Move.Ok (n : ℕ) : Move α → Prop
  | .cup g _ => g ≤ n
  | .cross p => p + 1 < n

/-- The number of strands after a move. -/
def Move.len (n : ℕ) : Move α → ℕ
  | .cup _ _ => n + 2
  | .cross _ => n

/-- A diagram fits on `n` strands: every move can be applied. -/
def Fits : ℕ → List (Move α) → Prop
  | _, [] => True
  | n, m :: D => m.Ok n ∧ Fits (m.len n) D

/-- The effect of a move on a state; a cup gets the fresh id `s.length`. -/
def step (s : List (ℕ × α)) : Move α → List (ℕ × α)
  | .cup g a => insAt s g (s.length, a) (s.length, d a)
  | .cross p => swapAt s p

/-- The final state of a diagram (read from the bottom). -/
def run (D : List (Move α)) : List (ℕ × α) := D.foldl (step d) []

variable {d}

theorem length_step (s : List (ℕ × α)) (m : Move α) : (step d s m).length = m.len s.length := by
  cases m with
  | cup g a => simp [step, Move.len, insAt]; omega
  | cross p => simp [step, Move.len]

theorem fits_append : ∀ (n : ℕ) (D E : List (Move α)),
    Fits n (D ++ E) ↔ Fits n D ∧ Fits (D.foldl Move.len n) E
  | n, [], E => by simp [Fits]
  | n, m :: D, E => by
    simp only [List.cons_append, Fits, List.foldl_cons, fits_append _ D E, and_assoc]

theorem length_foldl_step : ∀ (s : List (ℕ × α)) (D : List (Move α)),
    (D.foldl (step d) s).length = D.foldl Move.len s.length
  | s, [] => rfl
  | s, m :: D => by
    simp only [List.foldl_cons, length_foldl_step _ D, length_step]

theorem run_append (D E : List (Move α)) : run d (D ++ E) = E.foldl (step d) (run d D) := by
  simp [run, List.foldl_append]

theorem fits_snoc {D : List (Move α)} {m : Move α} :
    Fits 0 (D ++ [m]) ↔ Fits 0 D ∧ m.Ok (run d D).length := by
  rw [fits_append]
  simp only [Fits, and_true]
  rw [show D.foldl Move.len 0 = (run d D).length by rw [run, length_foldl_step]; rfl]

theorem mem_swapAt {β : Type*} {s : List β} {p : ℕ} {x : β} (h : x ∈ swapAt s p) : x ∈ s := by
  by_cases hp : p + 1 < s.length
  · rw [List.mem_iff_getElem?] at h ⊢
    obtain ⟨i, hi⟩ := h
    exact ⟨tau p i, by rwa [getElem?_swapAt s hp] at hi⟩
  · rwa [swapAt_of_le s hp] at h

/-- The invariant of states reached by diagrams: a pairing with ids below the length. -/
def Inv (s : List (ℕ × α)) : Prop := Valid s ∧ ∀ x ∈ s, x.1 < s.length

theorem Inv.step {s : List (ℕ × α)} (hs : Inv s) {m : Move α} (hm : m.Ok s.length) :
    Inv (step d s m) := by
  cases m with
  | cup g a =>
    simp only [Move.Ok] at hm
    refine ⟨hs.1.insAt hm (fun x hx => (hs.2 x hx).ne) _ _, fun x hx => ?_⟩
    rw [length_step]; show x.1 < s.length + 2
    simp only [Chord.step, insAt, List.mem_append, List.mem_cons] at hx
    rcases hx with hx | rfl | rfl | hx
    · have := hs.2 x (List.mem_of_mem_take hx); omega
    · simp
    · simp
    · have := hs.2 x (List.mem_of_mem_drop hx); omega
  | cross p =>
    simp only [Move.Ok] at hm
    refine ⟨hs.1.swapAt hm, fun x hx => ?_⟩
    rw [length_step]; show x.1 < s.length
    have hx' : x ∈ swapAt s p := hx
    exact hs.2 x (mem_swapAt hx')

theorem inv_run : ∀ {D : List (Move α)}, Fits 0 D → Inv (run d D) := by
  intro D
  induction D using List.reverseRecOn with
  | nil => intro _; exact ⟨fun i hi => by simp [run] at hi, by simp [run]⟩
  | append_singleton D m ih =>
    intro h
    rw [fits_snoc (d := d)] at h
    rw [run_append]
    exact (ih h.1).step h.2

/-- **The normal form theorem.** Every diagram of cups and crossings is either reducible
(equivalent to a diagram containing a double crossing or a curl) or equivalent to the canonical
diagram of its final pairing. -/
theorem equiv_canon_or_reducible : ∀ {D : List (Move α)}, Fits 0 D →
    Reducible D ∨ Equiv D (canon (run d D)) := by
  intro D
  induction D using List.reverseRecOn with
  | nil => intro _; right; rw [run, List.foldl_nil, canon_nil]
  | append_singleton D m ih =>
    intro h
    have hi := inv_run (d := d) ((fits_snoc (d := d)).1 h).1
    have hm := ((fits_snoc (d := d)).1 h).2
    rcases ih ((fits_snoc (d := d)).1 h).1 with hr | he
    · exact Or.inl (hr.append _)
    have he' := he.append_right [m]
    rw [run_append, List.foldl_cons, List.foldl_nil]
    set s := run d D
    cases m with
    | cup g a =>
      simp only [Move.Ok] at hm
      right
      have hk : ∀ x ∈ s, x.1 ≠ s.length := fun x hx => (hi.2 x hx).ne
      have hs : Same (step d s (.cup g a)) g (g + 1) :=
        (same_insAt_iff hm hk a (d a)).2 (Or.inl ⟨rfl, rfl⟩)
      have c := canon_cup ((hi.step (d := d) (m := .cup g a) hm).1) hs
      have e1 : rmAt (step d s (.cup g a)) g = s := rmAt_insAt s g _ _ hm
      have e2 : ((step d s (.cup g a))[g]'hs.lt_left).2 = a := by
        have : (step d s (.cup g a))[g]? = some (s.length, a) := by
          rw [step, getElem?_insAt s hm]; simp
        rw [List.getElem?_eq_getElem hs.lt_left] at this
        rw [Option.some.inj this]
      rw [e1, e2] at c
      exact he'.trans c.symm
    | cross p =>
      simp only [Move.Ok] at hm
      by_cases hsame : Same s p (p + 1)
      · left
        have c := canon_cup hi.1 hsame
        exact ⟨canon (rmAt s p), [], p, Or.inr ⟨_, by simpa using he'.trans (c.append_right _)⟩⟩
      by_cases hilv : Ilv s p
      · left
        have c := canon_ilv hi.1 hilv
        exact ⟨canon (swapAt s p), [], p, Or.inl (by simpa using he'.trans (c.append_right _))⟩
      · right
        have hilv' : Ilv (swapAt s p) p := (ilv_swapAt_iff hi.1 hm hsame).2 hilv
        have c := canon_ilv (hi.1.swapAt hm) hilv'
        rw [swapAt_swapAt] at c
        exact he'.trans c.symm

end Run

end StringDiagrams.Chord
