import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Find
import Mathlib.Logic.Relation
import Mathlib.Tactic.SplitIfs

/-!
# Planar chord diagrams with one boundary: states, moves and the canonical diagram

A combinatorial normal form for planar diagrams of cups and crossings with all their endpoints on
one boundary (chord diagrams), up to isotopy and the braid and pitchfork moves. The argument
follows A. Lauda, *A categorification of quantum `sl(2)`*, arXiv:0803.3652v3, §8, and
M. Khovanov, A. Lauda, *A categorification of quantum `sl(n)`*, arXiv:0807.3250v1, §3.2.3
(proof of Proposition 3.11). This file sets up the objects; the normal form theorem is
`StringDiagrams.Chord.equiv_canon_or_reducible` (`StringDiagrams.Chord.NormalForm`).

## States

A *state* is a list of pairs `(arc id, letter)`, letters in a type `α` with a map
`d : α → α` (the dual letter; typically an involution). A *diagram* is a list of moves (`Move`),
applied from the bottom to the empty state (`step`, `run`):

* `cup g a`: insert `(k, a), (k, d a)` at position `g`, where `k` is a fresh id (a new arc, its
  left leg labelled `a`, its right leg `d a`);
* `cross p`: exchange the entries at positions `p` and `p + 1` (a crossing of two strands).

`Fits n D` says that every move of `D` makes sense starting from `n` strands. The final state of
a diagram is a pairing (`Valid`: each position has exactly one partner, `Same`).

## The canonical diagram

For a pairing `s`, `canon s` is defined by recursion on the number of positions plus the number
`cr s` of pairs of interleaved arcs: if `s` has an adjacent arc (positions `r, r + 1` joined),
take the leftmost one and put `canon (rmAt s r) ++ [cup r a]`; otherwise take the first position
`q` which is the left end of an arc followed by the right end of another, and put
`canon (swapAt s q) ++ [cross q]` (the two arcs interleave in `s` but not in `swapAt s q`). So the
cups of `canon s` are created last, above the crossings.

## Moves

`Equiv` is the equivalence on diagrams generated, in context, by `Step`:

* moves at disjoint places commute (`cross`/`cross`, `cross`/`cup`, `cup`/`cup`, with the index
  shifts);
* the braid relation `cross p, cross (p+1), cross p ~ cross (p+1), cross p, cross (p+1)`;
* the pitchfork move `cup g a, cross (g+1) ~ cup (g+1) a, cross g` (a strand passing a cup on
  either side).

A diagram is `Reducible` if it is equivalent to one containing a double crossing
`cross p, cross p` or a curl `cup p a, cross p`.
-/

namespace StringDiagrams.Chord

section ListOps

variable {β : Type*}

/-- The transposition of `p` and `p + 1`. -/
def tau (p i : ℕ) : ℕ := if i = p then p + 1 else if i = p + 1 then p else i

theorem tau_tau (p i : ℕ) : tau p (tau p i) = i := by unfold tau; split_ifs <;> omega

theorem tau_inj {p i j : ℕ} : tau p i = tau p j ↔ i = j :=
  ⟨fun h => by rw [← tau_tau p i, h, tau_tau], fun h => h ▸ rfl⟩

/-- Exchange the entries at positions `p` and `p + 1` (no change if `p + 1` is out of range). -/
def swapAt (s : List β) (p : ℕ) : List β :=
  if h : p + 1 < s.length then (s.set p s[p + 1]).set (p + 1) s[p] else s

/-- Remove the entries at positions `r` and `r + 1`. -/
def rmAt (s : List β) (r : ℕ) : List β := s.take r ++ s.drop (r + 2)

/-- Insert `x, y` at position `g`. -/
def insAt (s : List β) (g : ℕ) (x y : β) : List β := s.take g ++ x :: y :: s.drop g

/-- The position in `s` of the entry at position `i` of `rmAt s r`. -/
def rmIdx (r i : ℕ) : ℕ := if i < r then i else i + 2

@[simp] theorem length_swapAt (s : List β) (p : ℕ) : (swapAt s p).length = s.length := by
  unfold swapAt; split_ifs <;> simp

theorem length_rmAt (s : List β) {r : ℕ} (h : r + 2 ≤ s.length) :
    (rmAt s r).length = s.length - 2 := by simp [rmAt]; omega

theorem length_insAt (s : List β) {g : ℕ} (h : g ≤ s.length) (x y : β) :
    (insAt s g x y).length = s.length + 2 := by simp [insAt]; omega

theorem getElem?_swapAt (s : List β) {p : ℕ} (hp : p + 1 < s.length) (i : ℕ) :
    (swapAt s p)[i]? = s[tau p i]? := by
  have hp' : p < s.length := by omega
  rcases (show i = p ∨ i = p + 1 ∨ (i ≠ p ∧ i ≠ p + 1) by omega) with rfl | rfl | ⟨h1, h2⟩
  · simp [swapAt, hp, tau, hp']
  · simp [swapAt, hp, tau, hp']
  · simp [swapAt, hp, tau, h1, h2, Ne.symm h1, Ne.symm h2]

theorem getElem?_rmAt (s : List β) {r : ℕ} (hr : r + 2 ≤ s.length) (i : ℕ) :
    (rmAt s r)[i]? = s[rmIdx r i]? := by
  simp only [rmAt, rmIdx, List.getElem?_append, List.length_take, List.getElem?_take,
    List.getElem?_drop]
  split_ifs <;> first | rfl | (congr 1; omega)

theorem getElem?_insAt (s : List β) {g : ℕ} (hg : g ≤ s.length) (x y : β) (i : ℕ) :
    (insAt s g x y)[i]? = if i < g then s[i]? else if i = g then some x
      else if i = g + 1 then some y else s[i - 2]? := by
  simp only [insAt, List.getElem?_append, List.length_take, List.getElem?_take]
  rcases (show i < g ∨ i = g ∨ i = g + 1 ∨ g + 1 < i by omega) with h | rfl | rfl | h
  · simp [h]; omega
  · simp [Nat.min_eq_left hg]
  · simp [Nat.min_eq_left hg]
  · simp [Nat.min_eq_left hg, show ¬ i < g by omega, show i ≠ g by omega, show i ≠ g + 1 by omega]
    obtain ⟨m, rfl⟩ : ∃ m, i = g + 2 + m := ⟨i - g - 2, by omega⟩
    rw [show g + 2 + m - g = m + 2 by omega, show g + 2 + m - 2 = g + m by omega]
    simp [List.getElem?_drop]


theorem rmIdx_lt_iff (r : ℕ) {i j : ℕ} : rmIdx r i < rmIdx r j ↔ i < j := by
  unfold rmIdx; split_ifs <;> omega

theorem rmIdx_inj {r i j : ℕ} : rmIdx r i = rmIdx r j ↔ i = j := by
  unfold rmIdx; split_ifs <;> omega

theorem tau_lt_iff (p : ℕ) {i j : ℕ} (h : ¬ (i = p ∧ j = p + 1)) (h' : ¬ (i = p + 1 ∧ j = p)) :
    tau p i < tau p j ↔ i < j := by unfold tau; split_ifs <;> omega

theorem swapAt_swapAt (s : List β) (p : ℕ) : swapAt (swapAt s p) p = s := by
  by_cases hp : p + 1 < s.length
  · apply List.ext_getElem?; intro i
    rw [getElem?_swapAt _ (by simpa using hp), getElem?_swapAt _ hp, tau_tau]
  · simp [swapAt, hp]

theorem swapAt_of_le (s : List β) {p : ℕ} (hp : ¬ p + 1 < s.length) : swapAt s p = s := by
  simp [swapAt, hp]

theorem rmAt_insAt (s : List β) (g : ℕ) (x y : β) (hg : g ≤ s.length) :
    rmAt (insAt s g x y) g = s := by
  apply List.ext_getElem?; intro i
  rw [getElem?_rmAt _ (by rw [length_insAt s hg]; omega), getElem?_insAt s hg]
  unfold rmIdx; split_ifs <;> first | rfl | omega

theorem insAt_rmAt (s : List β) {r : ℕ} (hr : r + 1 < s.length) :
    insAt (rmAt s r) r s[r] s[r + 1] = s := by
  have hl := length_rmAt s (r := r) (by omega)
  apply List.ext_getElem?; intro i
  rw [getElem?_insAt _ (by omega)]
  simp only [getElem?_rmAt s (show r + 2 ≤ s.length by omega), rmIdx]
  rcases (show i < r ∨ i = r ∨ i = r + 1 ∨ r + 1 < i by omega) with h | rfl | rfl | h
  · simp [h]
  · simp
  · simp
  · simp [show ¬ i < r by omega, show i ≠ r by omega, show i ≠ r + 1 by omega,
      show ¬ i - 2 < r by omega, show i - 2 + 2 = i by omega]

end ListOps

/-! ## Pairings -/

section Pairings

variable {α : Type*}

/-- The arc id at position `i` (if any). -/
def idAt (s : List (ℕ × α)) (i : ℕ) : Option ℕ := (s[i]?).map Prod.fst

/-- Positions `i ≠ j` of `s` carry the same arc id. -/
def Same (s : List (ℕ × α)) (i j : ℕ) : Prop := i ≠ j ∧ idAt s i ≠ none ∧ idAt s i = idAt s j

/-- `s` is a pairing: every position has exactly one partner. -/
def Valid (s : List (ℕ × α)) : Prop := ∀ i < s.length, ∃! j, Same s i j

variable {s : List (ℕ × α)}

theorem idAt_ne_none_iff {i : ℕ} : idAt s i ≠ none ↔ i < s.length := by
  simp [idAt]

theorem Same.symm {i j : ℕ} (h : Same s i j) : Same s j i :=
  ⟨h.1.symm, h.2.2 ▸ h.2.1, h.2.2.symm⟩

theorem same_comm {i j : ℕ} : Same s i j ↔ Same s j i := ⟨Same.symm, Same.symm⟩

theorem Same.lt_left {i j : ℕ} (h : Same s i j) : i < s.length := idAt_ne_none_iff.1 h.2.1

theorem Same.lt_right {i j : ℕ} (h : Same s i j) : j < s.length := h.symm.lt_left

theorem Same.ne {i j : ℕ} (h : Same s i j) : i ≠ j := h.1

theorem Valid.unique (hv : Valid s) {i j j' : ℕ} (h : Same s i j) (h' : Same s i j') : j = j' :=
  (hv i h.lt_left).unique h h'

theorem Valid.exists (hv : Valid s) {i : ℕ} (hi : i < s.length) : ∃ j, Same s i j :=
  (hv i hi).exists

theorem idAt_swapAt {p : ℕ} (hp : p + 1 < s.length) (i : ℕ) :
    idAt (swapAt s p) i = idAt s (tau p i) := by
  simp [idAt, getElem?_swapAt s hp]

theorem same_swapAt {p : ℕ} (hp : p + 1 < s.length) {i j : ℕ} :
    Same (swapAt s p) i j ↔ Same s (tau p i) (tau p j) := by
  simp only [Same, idAt_swapAt hp, ne_eq, tau_inj]

theorem idAt_rmAt {r : ℕ} (hr : r + 2 ≤ s.length) (i : ℕ) :
    idAt (rmAt s r) i = idAt s (rmIdx r i) := by
  simp [idAt, getElem?_rmAt s hr]

theorem same_rmAt {r : ℕ} (hr : r + 2 ≤ s.length) {i j : ℕ} :
    Same (rmAt s r) i j ↔ Same s (rmIdx r i) (rmIdx r j) := by
  simp only [Same, idAt_rmAt hr, ne_eq, rmIdx_inj]

theorem Valid.swapAt (hv : Valid s) {p : ℕ} (hp : p + 1 < s.length) :
    Valid (Chord.swapAt s p) := by
  intro i hi
  have hi' : tau p i < s.length := by simp at hi; unfold tau; split_ifs <;> omega
  obtain ⟨j, hj, hu⟩ := hv (tau p i) hi'
  refine ⟨tau p j, ?_, fun k hk => ?_⟩
  · show Same _ _ _
    rw [same_swapAt hp, tau_tau]; exact hj
  · have hk' : Same (Chord.swapAt s p) i k := hk
    rw [same_swapAt hp] at hk'
    rw [← hu _ hk', tau_tau]

theorem Valid.rmAt (hv : Valid s) {r : ℕ} (hadj : Same s r (r + 1)) :
    Valid (Chord.rmAt s r) := by
  have hr : r + 2 ≤ s.length := hadj.lt_right
  intro i hi
  rw [length_rmAt s hr] at hi
  have hi' : rmIdx r i < s.length := by unfold rmIdx; split_ifs <;> omega
  obtain ⟨j, hj, hu⟩ := hv (rmIdx r i) hi'
  have hjr : j ≠ r ∧ j ≠ r + 1 := by
    constructor
    · rintro rfl
      have := hv.unique hadj hj.symm
      unfold rmIdx at this; split_ifs at this <;> omega
    · rintro rfl
      have := hv.unique hadj.symm hj.symm
      unfold rmIdx at this; split_ifs at this <;> omega
  refine ⟨if j < r then j else j - 2, ?_, fun k hk => ?_⟩
  · show Same _ _ _
    rw [same_rmAt hr]
    have e : rmIdx r (if j < r then j else j - 2) = j := by
      unfold rmIdx; split_ifs <;> omega
    rw [e]; exact hj
  · have hk' : Same (Chord.rmAt s r) i k := hk
    rw [same_rmAt hr] at hk'
    have := hu _ hk'
    unfold rmIdx at this; split_ifs at this ⊢ <;> omega

theorem idAt_insAt {g : ℕ} (hg : g ≤ s.length) (k : ℕ) (a b : α) (i : ℕ) :
    idAt (insAt s g (k, a) (k, b)) i = if i < g then idAt s i else if i = g then some k
      else if i = g + 1 then some k else idAt s (i - 2) := by
  simp only [idAt, getElem?_insAt s hg]
  split_ifs <;> rfl

theorem same_insAt_iff {g : ℕ} (hg : g ≤ s.length) {k : ℕ} (hk : ∀ x ∈ s, x.1 ≠ k) (a b : α)
    {i j : ℕ} : Same (insAt s g (k, a) (k, b)) i j ↔
      ((i = g ∧ j = g + 1) ∨ (i = g + 1 ∧ j = g) ∨
        (i ≠ g ∧ i ≠ g + 1 ∧ j ≠ g ∧ j ≠ g + 1 ∧ Same s (if i < g then i else i - 2)
          (if j < g then j else j - 2))) := by
  have hk' : ∀ i, idAt s i ≠ some k := by
    intro i h
    simp only [idAt, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, rfl⟩ := h
    exact hk x (List.mem_of_getElem? hx) rfl
  simp only [Same, idAt_insAt hg]
  constructor
  · rintro ⟨h1, h2, h3⟩
    split_ifs at h2 h3 <;> first
      | (left; omega) | (right; left; omega)
      | (exfalso; exact hk' _ h3) | (exfalso; exact hk' _ h3.symm)
      | (right; right; refine ⟨by omega, by omega, by omega, by omega, ?_⟩
         split_ifs; first | omega | exact ⟨by omega, h2, h3⟩)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨h1, h2, h3, h4, h5, h6, h7⟩)
    · simp
    · simp
    · refine ⟨fun e => ?_, ?_⟩
      · subst e; split_ifs at h5 <;> omega
      · split_ifs at h6 h7 ⊢ <;> first | omega | exact ⟨h6, h7⟩

theorem Valid.insAt (hv : Valid s) {g : ℕ} (hg : g ≤ s.length) {k : ℕ} (hk : ∀ x ∈ s, x.1 ≠ k)
    (a b : α) : Valid (Chord.insAt s g (k, a) (k, b)) := by
  intro i hi
  rw [length_insAt s hg] at hi
  by_cases h1 : i = g
  · subst h1
    refine ⟨i + 1, (same_insAt_iff hg hk a b).2 (Or.inl ⟨rfl, rfl⟩), fun j hj => ?_⟩
    have hj' : Same _ _ _ := hj
    rw [same_insAt_iff hg hk] at hj'; omega
  by_cases h2 : i = g + 1
  · subst h2
    refine ⟨g, (same_insAt_iff hg hk a b).2 (Or.inr (Or.inl ⟨rfl, rfl⟩)), fun j hj => ?_⟩
    have hj' : Same _ _ _ := hj
    rw [same_insAt_iff hg hk] at hj'; omega
  obtain ⟨j, hj, hu⟩ := hv (if i < g then i else i - 2) (by split_ifs <;> omega)
  have hjl := hj.lt_right
  refine ⟨if j < g then j else j + 2, ?_, fun j' hj' => ?_⟩
  · show Same _ _ _
    rw [same_insAt_iff hg hk]
    right; right
    refine ⟨h1, h2, by split_ifs <;> omega, by split_ifs <;> omega, ?_⟩
    have e : (if (if j < g then j else j + 2) < g then (if j < g then j else j + 2)
        else (if j < g then j else j + 2) - 2) = j := by split_ifs <;> omega
    rw [e]; exact hj
  · have hj'' : Same _ _ _ := hj'
    rw [same_insAt_iff hg hk] at hj''
    rcases hj'' with h | h | ⟨-, -, h3, h4, h5⟩
    · omega
    · omega
    · have := hu _ h5
      split_ifs at this ⊢ <;> omega

end Pairings

/-! ## Crossings -/

section Crossings

open scoped Classical

variable {α : Type*} {s : List (ℕ × α)}

/-- Positions `i < j < k < l` with `i, k` on one arc and `j, l` on another: a crossing. -/
def Cr4 (s : List (ℕ × α)) (i j k l : ℕ) : Prop := i < j ∧ j < k ∧ k < l ∧ Same s i k ∧ Same s j l

/-- The set of crossings, as quadruples of positions. -/
noncomputable def crSet (s : List (ℕ × α)) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  ((Finset.range s.length) ×ˢ (Finset.range s.length) ×ˢ (Finset.range s.length) ×ˢ
    (Finset.range s.length)).filter fun x => Cr4 s x.1 x.2.1 x.2.2.1 x.2.2.2

/-- The crossing number of a pairing: the number of pairs of interleaved arcs. -/
noncomputable def cr (s : List (ℕ × α)) : ℕ := (crSet s).card

theorem mem_crSet {x : ℕ × ℕ × ℕ × ℕ} : x ∈ crSet s ↔ Cr4 s x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  simp only [crSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range, and_iff_right_iff_imp]
  intro h
  exact ⟨h.2.2.2.1.lt_left, h.2.2.2.2.lt_left, h.2.2.2.1.lt_right, h.2.2.2.2.lt_right⟩

/-- The arcs at positions `q` and `q + 1` interleave. -/
def Ilv (s : List (ℕ × α)) (q : ℕ) : Prop :=
  ∃ i j k l, Cr4 s i j k l ∧ ((i = q ∧ j = q + 1) ∨ (j = q ∧ k = q + 1) ∨ (k = q ∧ l = q + 1))

/-- In a pairing, whether the arcs at `q` and `q + 1` (with partners `a` and `b`) interleave. -/
theorem ilv_iff (hv : Valid s) {q a b : ℕ} (ha : Same s q a) (hb : Same s (q + 1) b) :
    Ilv s q ↔ (q + 1 < a ∧ a < b) ∨ (b < q ∧ q + 1 < a) ∨ (a < b ∧ b < q) := by
  constructor
  · rintro ⟨i, j, k, l, ⟨h1, h2, h3, h4, h5⟩, h | h | h⟩ <;> obtain ⟨rfl, rfl⟩ := h
    · have := hv.unique ha h4; have := hv.unique hb h5; omega
    · have := hv.unique ha h5; have := hv.unique hb h4.symm; omega
    · have := hv.unique ha h4.symm; have := hv.unique hb h5.symm; omega
  · rintro (h | h | h)
    · exact ⟨q, q + 1, a, b, ⟨by omega, by omega, by omega, ha, hb⟩, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨b, q, q + 1, a, ⟨by omega, by omega, by omega, hb.symm, ha⟩,
        Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    · exact ⟨a, b, q, q + 1, ⟨by omega, by omega, by omega, ha.symm, hb.symm⟩,
        Or.inr (Or.inr ⟨rfl, rfl⟩)⟩

theorem Ilv.lt (h : Ilv s q) : q + 1 < s.length := by
  obtain ⟨i, j, k, l, ⟨h1, h2, h3, h4, h5⟩, h | h | h⟩ := h <;> obtain ⟨rfl, rfl⟩ := h
  · exact h5.lt_left
  · exact h4.lt_right
  · exact h5.lt_right

theorem Ilv.not_same (hv : Valid s) (h : Ilv s q) : ¬ Same s q (q + 1) := by
  intro hq
  obtain ⟨a, ha⟩ := hv.exists (show q < s.length by have := h.lt; omega)
  obtain ⟨b, hb⟩ := hv.exists h.lt
  have e1 := hv.unique ha hq
  have e2 := hv.unique hb hq.symm
  rw [ilv_iff hv ha hb] at h
  omega

/-- The partners of `q` and `q + 1` after exchanging them. -/
theorem swapAt_partners {p : ℕ} (hp : p + 1 < s.length) {a b : ℕ} (ha : Same s p a)
    (hb : Same s (p + 1) b) (hab : ¬ Same s p (p + 1)) :
    Same (swapAt s p) p b ∧ Same (swapAt s p) (p + 1) a := by
  have ha1 : a ≠ p + 1 := fun e => hab (e ▸ ha)
  have hb1 : b ≠ p := fun e => hab (e ▸ hb).symm
  have ta : tau p a = a := by unfold tau; have := ha.ne; split_ifs <;> omega
  have tb : tau p b = b := by unfold tau; have := hb.ne; split_ifs <;> omega
  have t1 : tau p p = p + 1 := by simp [tau]
  have t2 : tau p (p + 1) = p := by simp [tau]
  rw [same_swapAt hp, same_swapAt hp, ta, tb, t1, t2]
  exact ⟨hb, ha⟩

/-- Exchanging two adjacent endpoints of different arcs toggles their interleaving. -/
theorem ilv_swapAt_iff (hv : Valid s) {p : ℕ} (hp : p + 1 < s.length)
    (hab : ¬ Same s p (p + 1)) : Ilv (swapAt s p) p ↔ ¬ Ilv s p := by
  obtain ⟨a, ha⟩ := hv.exists (show p < s.length by omega)
  obtain ⟨b, hb⟩ := hv.exists hp
  obtain ⟨ha', hb'⟩ := swapAt_partners hp ha hb hab
  have hab' : a ≠ b := fun e => by subst e; have := hv.unique ha.symm hb.symm; omega
  have ha1 : a ≠ p + 1 := fun e => hab (e ▸ ha)
  have hb1 : b ≠ p := fun e => hab (e ▸ hb).symm
  rw [ilv_iff (hv.swapAt hp) ha' hb', ilv_iff hv ha hb]
  have := ha.ne; have := hb.ne
  omega

theorem cr_rmAt_le {r : ℕ} (hr : r + 2 ≤ s.length) : cr (rmAt s r) ≤ cr s := by
  unfold cr
  refine Finset.card_le_card_of_injOn (fun x => (rmIdx r x.1, rmIdx r x.2.1, rmIdx r x.2.2.1,
    rmIdx r x.2.2.2)) (fun x hx => ?_) (fun x _ y _ h => ?_)
  · obtain ⟨h1, h2, h3, h4, h5⟩ := mem_crSet.1 hx
    apply mem_crSet.2
    exact ⟨(rmIdx_lt_iff r).2 h1, (rmIdx_lt_iff r).2 h2, (rmIdx_lt_iff r).2 h3,
      (same_rmAt hr).1 h4, (same_rmAt hr).1 h5⟩
  · simp only [Prod.mk.injEq, rmIdx_inj] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 h4))

theorem cr_swapAt_lt (hv : Valid s) {p : ℕ} (h : Ilv s p) : cr (swapAt s p) < cr s := by
  have hp := h.lt
  have hn : ¬ Ilv (swapAt s p) p := by
    rw [ilv_swapAt_iff hv hp (h.not_same hv)]; exact not_not.2 h
  unfold cr
  let F : ℕ × ℕ × ℕ × ℕ → ℕ × ℕ × ℕ × ℕ := fun x => (tau p x.1, tau p x.2.1, tau p x.2.2.1,
    tau p x.2.2.2)
  have hF : Function.Injective F := by
    intro x y e
    simp only [F, Prod.mk.injEq, tau_inj] at e
    exact Prod.ext e.1 (Prod.ext e.2.1 (Prod.ext e.2.2.1 e.2.2.2))
  rw [← Finset.card_image_of_injective _ hF]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · obtain ⟨i, j, k, l, hc, hq⟩ := h
    refine ⟨(i, j, k, l), mem_crSet.2 hc, fun hm => ?_⟩
    obtain ⟨x, hx, e⟩ := Finset.mem_image.1 hm
    rw [mem_crSet] at hx
    have ex : x = F (i, j, k, l) := by rw [← e]; simp [F, tau_tau]
    subst ex
    obtain ⟨h1, h2, h3, -, -⟩ := hx
    simp only [F, tau] at h1 h2 h3
    rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      obtain ⟨h1', h2', h3', -, -⟩ := hc <;> split_ifs at h1 h2 h3 <;> omega
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    rw [mem_crSet] at hx ⊢
    obtain ⟨h1, h2, h3, h4, h5⟩ := hx
    have n1 : ¬ (x.1 = p ∧ x.2.1 = p + 1) := fun ⟨e1, e2⟩ =>
      hn ⟨_, _, _, _, ⟨h1, h2, h3, h4, h5⟩, Or.inl ⟨e1, e2⟩⟩
    have n2 : ¬ (x.2.1 = p ∧ x.2.2.1 = p + 1) := fun ⟨e1, e2⟩ =>
      hn ⟨_, _, _, _, ⟨h1, h2, h3, h4, h5⟩, Or.inr (Or.inl ⟨e1, e2⟩)⟩
    have n3 : ¬ (x.2.2.1 = p ∧ x.2.2.2 = p + 1) := fun ⟨e1, e2⟩ =>
      hn ⟨_, _, _, _, ⟨h1, h2, h3, h4, h5⟩, Or.inr (Or.inr ⟨e1, e2⟩)⟩
    exact ⟨(tau_lt_iff p n1 (by omega)).2 h1, (tau_lt_iff p n2 (by omega)).2 h2,
      (tau_lt_iff p n3 (by omega)).2 h3, (same_swapAt hp).1 h4, (same_swapAt hp).1 h5⟩

end Crossings

/-! ## Moves, the equivalence, and the canonical diagram -/

section Moves

variable {α : Type*}

/-- A move: a cup inserting a new arc at gap `g` with left leg labelled `a`, or a crossing of the
strands at positions `p` and `p + 1`. -/
inductive Move (α : Type*)
  | cup (g : ℕ) (a : α)
  | cross (p : ℕ)

/-- The generating relations (each one relating two short diagrams that are equal up to isotopy,
or, for `braid`, up to the Reidemeister III move):

* `xx`: crossings at distant positions commute;
* `xuL`, `xuR`: a crossing and a cup at distant positions commute;
* `uu`: two cups commute;
* `braid`: the braid relation;
* `pitch`: a strand crossing the right leg of a cup equals it crossing the left leg of the cup
  on its other side (a pitchfork move). -/
inductive Step : List (Move α) → List (Move α) → Prop
  | xx {p p' : ℕ} (h : p + 2 ≤ p') : Step [.cross p, .cross p'] [.cross p', .cross p]
  | xuL {p g : ℕ} (a : α) (h : p + 2 ≤ g) : Step [.cross p, .cup g a] [.cup g a, .cross p]
  | xuR {p g : ℕ} (a : α) (h : g ≤ p) : Step [.cross p, .cup g a] [.cup g a, .cross (p + 2)]
  | uu {g g' : ℕ} (a b : α) (h : g' ≤ g) :
      Step [.cup g a, .cup g' b] [.cup g' b, .cup (g + 2) a]
  | braid (p : ℕ) :
      Step [.cross p, .cross (p + 1), .cross p] [.cross (p + 1), .cross p, .cross (p + 1)]
  | pitch (g : ℕ) (a : α) : Step [.cup g a, .cross (g + 1)] [.cup (g + 1) a, .cross g]

/-- One generating relation applied in context. -/
def Rw (X Y : List (Move α)) : Prop :=
  ∃ A B L R, Step L R ∧ X = A ++ L ++ B ∧ Y = A ++ R ++ B

/-- The equivalence of diagrams generated by the moves `Step` in context. -/
def Equiv : List (Move α) → List (Move α) → Prop := Relation.EqvGen Rw

namespace Equiv

@[refl] theorem refl (X : List (Move α)) : Equiv X X := Relation.EqvGen.refl X

theorem symm {X Y : List (Move α)} (h : Equiv X Y) : Equiv Y X := Relation.EqvGen.symm _ _ h

theorem trans {X Y Z : List (Move α)} (h : Equiv X Y) (h' : Equiv Y Z) : Equiv X Z :=
  Relation.EqvGen.trans _ _ _ h h'

theorem of_step {L R : List (Move α)} (h : Step L R) : Equiv L R :=
  Relation.EqvGen.rel _ _ ⟨[], [], L, R, h, by simp, by simp⟩

theorem append_right {X Y : List (Move α)} (h : Equiv X Y) (Z : List (Move α)) :
    Equiv (X ++ Z) (Y ++ Z) := by
  induction h with
  | rel X Y h =>
    obtain ⟨A, B, L, R, h, rfl, rfl⟩ := h
    exact Relation.EqvGen.rel _ _ ⟨A, B ++ Z, L, R, h, by simp, by simp⟩
  | refl => exact refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

theorem append_left {X Y : List (Move α)} (h : Equiv X Y) (Z : List (Move α)) :
    Equiv (Z ++ X) (Z ++ Y) := by
  induction h with
  | rel X Y h =>
    obtain ⟨A, B, L, R, h, rfl, rfl⟩ := h
    exact Relation.EqvGen.rel _ _ ⟨Z ++ A, B, L, R, h, by simp, by simp⟩
  | refl => exact refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

/-- A move in context. -/
theorem step_mid {L R : List (Move α)} (h : Step L R) (A B : List (Move α)) :
    Equiv (A ++ L ++ B) (A ++ R ++ B) :=
  ((of_step h).append_left A).append_right B

end Equiv

/-- A diagram is *reducible* if it is equivalent to one containing a double crossing
`cross p, cross p` or a curl `cup p a, cross p`. -/
def Reducible (D : List (Move α)) : Prop :=
  ∃ A B : List (Move α), ∃ p : ℕ, (Equiv D (A ++ [.cross p, .cross p] ++ B)) ∨
    ∃ a : α, Equiv D (A ++ [.cup p a, .cross p] ++ B)

theorem Reducible.of_equiv {D D' : List (Move α)} (h : Reducible D') (e : Equiv D D') :
    Reducible D := by
  obtain ⟨A, B, p, h⟩ := h
  refine ⟨A, B, p, ?_⟩
  rcases h with h | ⟨a, h⟩
  · exact Or.inl (e.trans h)
  · exact Or.inr ⟨a, e.trans h⟩

theorem Reducible.append {D : List (Move α)} (h : Reducible D) (Z : List (Move α)) :
    Reducible (D ++ Z) := by
  obtain ⟨A, B, p, h⟩ := h
  refine ⟨A, B ++ Z, p, ?_⟩
  rcases h with h | ⟨a, h⟩
  · exact Or.inl (by simpa using h.append_right Z)
  · exact Or.inr ⟨a, by simpa using h.append_right Z⟩

/-- Position `q` is the left end of its arc. -/
def Opn (s : List (ℕ × α)) (q : ℕ) : Prop := ∃ j, q < j ∧ Same s q j

/-- Position `q` is the right end of its arc. -/
def Cls (s : List (ℕ × α)) (q : ℕ) : Prop := ∃ j, j < q ∧ Same s q j

theorem ilv_of_opn_cls {s : List (ℕ × α)} (hv : Valid s) {q : ℕ} (hn : ¬ Same s q (q + 1))
    (ho : Opn s q) (hc : Cls s (q + 1)) : Ilv s q := by
  obtain ⟨a, hqa, ha⟩ := ho
  obtain ⟨b, hbq, hb⟩ := hc
  have h1 : a ≠ q + 1 := fun e => hn (e ▸ ha)
  have h2 : b ≠ q := fun e => hn (e ▸ hb).symm
  rw [ilv_iff hv ha hb]; omega

open scoped Classical in
/-- The canonical diagram of a pairing: remove the leftmost adjacent arc (a cup, created last),
or else uncross the first pair of adjacent endpoints "left end, right end". -/
noncomputable def canon (s : List (ℕ × α)) : List (Move α) :=
  if hv : Valid s then
    if h : ∃ r, Same s r (r + 1) then
      canon (rmAt s (Nat.find h)) ++
        [.cup (Nat.find h) (s[Nat.find h]'((Nat.find_spec h).lt_left)).2]
    else if h' : ∃ q, Opn s q ∧ Cls s (q + 1) then
      canon (swapAt s (Nat.find h')) ++ [.cross (Nat.find h')]
    else []
  else []
termination_by s.length + cr s
decreasing_by
  · have h1 := (Nat.find_spec h).lt_right
    have := cr_rmAt_le (s := s) (r := Nat.find h) (by omega)
    rw [length_rmAt s (by omega)]; omega
  · have := cr_swapAt_lt hv (ilv_of_opn_cls hv (fun hs => h ⟨_, hs⟩) (Nat.find_spec h').1
      (Nat.find_spec h').2)
    rw [length_swapAt]; omega

theorem canon_adj {s : List (ℕ × α)} (hv : Valid s) {r : ℕ} (hr : Same s r (r + 1))
    (hmin : ∀ r' < r, ¬ Same s r' (r' + 1)) :
    canon s = canon (rmAt s r) ++ [.cup r (s[r]'hr.lt_left).2] := by
  classical
  have h : ∃ r, Same s r (r + 1) := ⟨r, hr⟩
  have e : Nat.find h = r := le_antisymm (Nat.find_min' h hr)
    (not_lt.1 fun hl => hmin _ hl (Nat.find_spec h))
  rw [canon, dite_eq_left hv, dite_eq_left h]
  subst e
  rfl

theorem canon_cross {s : List (ℕ × α)} (hv : Valid s) (hno : ∀ r, ¬ Same s r (r + 1))
    (hne : s ≠ []) : ∃ q, Opn s q ∧ Cls s (q + 1) ∧ canon s = canon (swapAt s q) ++ [.cross q] ∧
      ∀ q' < q, ¬ (Opn s q' ∧ Cls s (q' + 1)) := by
  classical
  have h : ¬ ∃ r, Same s r (r + 1) := fun ⟨r, hr⟩ => hno r hr
  have h' : ∃ q, Opn s q ∧ Cls s (q + 1) := by
    -- the first right end
    have hex : ∃ i, Cls s i := by
      obtain ⟨j, hj⟩ := hv.exists (show 0 < s.length from List.length_pos_of_ne_nil hne)
      exact ⟨j, 0, Nat.pos_of_ne_zero hj.ne.symm, hj.symm⟩
    have hi := Nat.find_spec hex
    have hpos : Nat.find hex ≠ 0 := by
      intro e; obtain ⟨j, hj, -⟩ := hi; omega
    refine ⟨Nat.find hex - 1, ?_, by rw [Nat.sub_add_cancel (by omega)]; exact hi⟩
    obtain ⟨j, hj⟩ := hv.exists (show Nat.find hex - 1 < s.length by
      obtain ⟨_, _, hc⟩ := hi; have := hc.lt_left; omega)
    refine ⟨j, ?_, hj⟩
    by_contra hlt
    have hj' : j < Nat.find hex - 1 := lt_of_le_of_ne (not_lt.1 hlt) hj.ne.symm
    exact Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega) ⟨j, hj', hj⟩
  refine ⟨Nat.find h', (Nat.find_spec h').1, (Nat.find_spec h').2, ?_,
    fun q' hq' => Nat.find_min h' hq'⟩
  rw [canon, dite_eq_left hv, dite_eq_right h, dite_eq_left h']

theorem canon_nil : canon ([] : List (ℕ × α)) = [] := by
  classical
  have hv : Valid ([] : List (ℕ × α)) := fun i hi => by simp at hi
  rw [canon, dite_eq_left hv, dite_eq_right (fun ⟨r, hr⟩ => by have := hr.lt_left; simp at this),
    dite_eq_right (fun ⟨q, ⟨j, _, hj⟩, _⟩ => by have := hj.lt_left; simp at this)]

end Moves

end StringDiagrams.Chord
