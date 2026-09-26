import StringDiagrams.Examples.OddTemperleyLieb.Representation
import StringDiagrams.Examples.OddTemperleyLieb.SKar
import StringDiagrams.Examples.OddTemperleyLieb.Decomposition
import StringDiagrams.Super.SVec

/-!
# `G : STL(δ) → SVec` as a monoidal superfunctor (Lemma A.1)

J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, Lemma A.1.

The representation `Rep.rep k q : STL(δ) ⥤ ModuleCat k` of `Representation.lean` (with
`δ = -(q - q⁻¹)`) models `V^{⊗n}` as the functions on words of length `n` over `Fin 2`, the
letter `0` standing for the even vector `v₁` and the letter `1` for the odd vector `v₋₁`. Here
this model is made into a superspace (`Rep.sv n`: a function is odd if it is supported on words
with an odd number of letters `1`), and `G` into a monoidal superfunctor into `SVec k`:

* `Rep.repS k q : STL(δ) ⥤ SVec k` with `repS.obj n = sv n` and the same maps as `rep`;
* `Rep.repS` is a superfunctor (`Rep.instIsSuperfunctor`): a diagram with `j` generators maps
  functions supported on words of parity `r` to functions supported on words of parity `r + j`;
* `Rep.repSMonoidal : MonoidalSuperfunctor k (repS k q)`, with coherence isomorphism
  `G(m) ⊗ G(n) ≅ G(m + n)` the concatenation isomorphism `v_u ⊗ v_w ↦ v_{uw}` (`Rep.catE`),
  which is `V^{⊗m} ⊗ V^{⊗n} = V^{⊗(m+n)}` on the tensor basis. Its naturality in the second
  variable is the Koszul sign rule: left whiskering by `m` strands multiplies a layer operator by
  the sign of the first `m` letters (`Rep.psign`).
-/

noncomputable section

universe u

namespace StringDiagrams.OddTemperleyLieb.Rep

open CategoryTheory MonoidalCategory Supercategory TensorProduct
open TemperleyLieb.Rep (Word ins del ext res Agree length_ins length_del ext_apply_of_length
  ext_apply_word res_apply)

variable {k : Type u} [CommRing k]

/-! ## Parities of words and the superspaces `V^{⊗n}` -/

/-- The parity of the basis vector `v_w`: the number of letters `1` modulo `2`. -/
def wpar (w : List (Fin 2)) : ZMod 2 := (nOdd w : ZMod 2)

theorem nOdd_append (u v : List (Fin 2)) : nOdd (u ++ v) = nOdd u + nOdd v := by
  induction u with
  | nil => simp
  | cons a u ih => simp [ih, Nat.add_assoc]

theorem wpar_append (u v : List (Fin 2)) : wpar (u ++ v) = wpar u + wpar v := by
  simp [wpar, nOdd_append]

@[simp] theorem wpar_nil : wpar [] = 0 := rfl

theorem neg_one_pow_eq_sign (n : ℕ) : (-1 : k) ^ n = sign k (n : ZMod 2) := by
  rcases Nat.even_or_odd n with h | h
  · rw [h.neg_one_pow, (ZMod.eq_zero_iff_even).mpr h, sign_zero]
  · rw [h.neg_one_pow, (ZMod.eq_one_iff_odd).mpr h, sign_one]

theorem psign_eq_sign (p : ℕ) (w : List (Fin 2)) : psign k p w = sign k (wpar (w.take p)) :=
  neg_one_pow_eq_sign _

variable (k)

/-- The projection onto the odd part: keep the coefficients of the odd words. -/
def oddProj (n : ℕ) : (Word n → k) →ₗ[k] (Word n → k) where
  toFun f w := if wpar w.1 = 1 then f w else 0
  map_add' f g := by funext w; split_ifs <;> simp_all
  map_smul' r f := by funext w; split_ifs <;> simp_all

/-- The superspace `V^{⊗n}`, as functions on words of length `n`. -/
def sv (n : ℕ) : SVec k where
  carrier := Word n → k
  odd := oddProj k n
  odd_comp_odd := by
    ext f w
    simp only [oddProj, LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply]
    split_ifs <;> rfl

variable {k}

theorem sv_proj_apply (n : ℕ) (p : ZMod 2) (f : sv k n) (w : Word n) :
    (sv k n).proj p f w = if wpar w.1 = p then f w else 0 := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [SVec.proj_zero]
    change f w - (if wpar w.1 = 1 then f w else 0) = _
    rcases parity_eq_zero_or_one (wpar w.1) with h | h <;> simp [h]
  · rw [SVec.proj_one]; rfl

theorem mem_sv_part {n : ℕ} {p : ZMod 2} {f : sv k n} :
    f ∈ (sv k n).part p ↔ ∀ w : Word n, wpar w.1 ≠ p → f w = 0 := by
  rw [SVec.mem_part_iff]
  constructor
  · intro h w hw
    rw [← h, sv_proj_apply, if_neg hw]
  · intro h
    funext w
    rw [sv_proj_apply]
    split_ifs with hw
    · rfl
    · exact (h w hw).symm


/-! ## Parities of layer operators -/

/-- `F` is supported on words of parity `r`. -/
def Supp (r : ZMod 2) (F : Fn k) : Prop := ∀ w, wpar w ≠ r → F w = 0

theorem nOdd_del (p : ℕ) (w : List (Fin 2)) :
    nOdd w = nOdd (del p w) + (w.getD p 0).val + (w.getD (p + 1) 0).val := by
  induction p generalizing w with
  | zero =>
    rcases w with _ | ⟨a, _ | ⟨b, w⟩⟩ <;> simp [del]; omega
  | succ p ih =>
    rcases w with _ | ⟨a, w⟩
    · simp [del]
    · simp only [del, nOdd_cons, List.getD_cons_succ, ih w]; omega

theorem nOdd_ins (p : ℕ) (a b : Fin 2) (w : List (Fin 2)) :
    nOdd (ins p a b w) = nOdd w + a.val + b.val := by
  induction p generalizing w with
  | zero => simp [ins]; omega
  | succ p ih =>
    rcases w with _ | ⟨c, w⟩
    · simp [ins]
    · simp only [ins, nOdd_cons, ih w]; omega

theorem cupCoeff_ne_zero {q : kˣ} {a b : Fin 2} (h : cupCoeff k q a b ≠ 0) : a.val + b.val = 1 := by
  fin_cases a <;> fin_cases b <;> simp_all

theorem capCoeff_ne_zero {q : kˣ} {a b : Fin 2} (h : capCoeff k q a b ≠ 0) : a.val + b.val = 1 := by
  fin_cases a <;> fin_cases b <;> simp_all

theorem Supp.cupOp {q : kˣ} {r : ZMod 2} {F : Fn k} (hF : Supp r F) (p : ℕ) :
    Supp (r + 1) (cupOp k q p F) := by
  intro w hw
  rw [cupOp_apply]
  by_cases hc : cupCoeff k q (w.getD p 0) (w.getD (p + 1) 0) = 0
  · rw [hc, zero_mul, mul_zero]
  · rw [hF (del p w), mul_zero, mul_zero]
    intro h
    apply hw
    have := cupCoeff_ne_zero hc
    rw [wpar, nOdd_del p w, Nat.add_assoc, this, ← h, wpar]
    push_cast; ring

theorem Supp.capOp {q : kˣ} {r : ZMod 2} {F : Fn k} (hF : Supp r F) (p : ℕ) :
    Supp (r + 1) (capOp k q p F) := by
  intro w hw
  rw [capOp_apply]
  refine (mul_eq_zero_of_right _ (Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_))
  by_cases hc : capCoeff k q a b = 0
  · rw [hc, zero_mul]
  · rw [hF (ins p a b w), mul_zero]
    intro h
    apply hw
    have h1 := capCoeff_ne_zero hc
    have h2 : wpar (ins p a b w) = wpar w + 1 := by
      rw [wpar, wpar, nOdd_ins, Nat.add_assoc, h1]; push_cast; rfl
    rw [← h, h2, add_assoc, SVec.zmod2_one_add_one, add_zero]

theorem Supp.op {q : kˣ} {r : ZMod 2} {F : Fn k} (hF : Supp r F) (L : Layer sig) :
    Supp (r + 1) (op k q L F) := by
  obtain ⟨s, l, g, r'⟩ := L
  cases g with
  | cup => exact hF.cupOp l.length
  | cap => exact hF.capOp l.length

theorem Supp.opList {q : kˣ} {r : ZMod 2} {F : Fn k} (hF : Supp r F) (ls : List (Layer sig)) :
    Supp (r + ls.length) ((loc k q).opList ls F) := by
  induction ls generalizing r F with
  | nil => simpa using hF
  | cons L ls ih =>
    have := ih (hF.op (q := q) L)
    rw [LocalInterpretation.opList_cons, LinearMap.comp_apply]
    convert this using 1
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring

theorem supp_ext {n : ℕ} {r : ZMod 2} {f : sv k n} (hf : f ∈ (sv k n).part r) :
    Supp r (ext k n f) := by
  intro w hw
  by_cases hl : w.length = n
  · rw [ext_apply_of_length k f hl]
    exact mem_sv_part.mp hf ⟨w, hl⟩ hw
  · exact dif_neg hl

/-! ## The superfunctor -/

variable (k) (q : kˣ)

local notation "δq" => delta q

/-- **Lemma A.1**: the functor `G : STL(δ) ⥤ SVec`, `n ↦ V^{⊗n}`, with the maps of `rep`. -/
def repS : STL k δq ⥤ SVec k where
  obj X := sv k ((pres k δq).toObj X).word.length
  map f := SVec.ofHom ((rep k q).map f).hom
  map_id X := by rw [CategoryTheory.Functor.map_id]; rfl
  map_comp f g := by rw [CategoryTheory.Functor.map_comp]; rfl

variable {k q}

theorem repS_map_apply {X Y : STL k δq} (f : X ⟶ Y) (x : (repS k q).obj X) :
    (repS k q).map f x = ((rep k q).map f).hom x := rfl

theorem repS_map_diag_apply {a b : Obj sig} (d : a ⟶ b) (x : (repS k q).obj ((pres k δq).obj a))
    (w : Word b.word.length) :
    (repS k q).map ((pres k δq).diag d) x w =
      (loc k q).opList (Diagram.layers d) (ext k _ x) w.1 :=
  rep_map_apply d x w

instance : (repS k q).Additive where
  map_add {X Y f g} := by
    change SVec.ofHom (V := (repS k q).obj X) (W := (repS k q).obj Y)
      ((rep k q).map (f + g)).hom = _
    rw [(rep k q).map_add]; rfl

instance : (repS k q).Linear k where
  map_smul {X Y} f r := by
    change SVec.ofHom (V := (repS k q).obj X) (W := (repS k q).obj Y)
      ((rep k q).map (r • f)).hom = _
    rw [(rep k q).map_smul]; rfl

/-- The value of `G` on the cup: `1 ↦ v₋₁ ⊗ v₁ - q v₁ ⊗ v₋₁`. -/
theorem repS_cup_vec (w : Word (strands 2).word.length) :
    (repS k q).map (cup k δq 0 0) (vec ⟨[], rfl⟩) w = cupCoeff k q (w.1.getD 0 0) (w.1.getD 1 0) :=
  rep_cup_vec w

/-- The value of `G` on the cap: `v_a ⊗ v_b ↦ β(a, b)`. -/
theorem repS_cap_vec (a b : Fin 2) :
    (repS k q).map (cap k δq 0 0) (vec ⟨[a, b], rfl⟩) ⟨[], rfl⟩ = capCoeff k q a b :=
  rep_cap_vec a b

theorem repS_map_diag_mem {a b : Obj sig} (d : a ⟶ b) :
    (repS k q).map ((pres k δq).diag d) ∈
      SVec.parityHom ((repS k q).obj ((pres k δq).obj a)) ((repS k q).obj ((pres k δq).obj b))
        ((Diagram.layers d).length : ZMod 2) := by
  refine SVec.mem_parityHom_of_apply_mem fun r x hx => mem_sv_part.mpr fun w hw => ?_
  rw [repS_map_diag_apply]
  exact (supp_ext hx).opList (q := q) _ _ hw

instance instIsSuperfunctor : IsSuperfunctor k (repS k q) where
  map_mem {X Y p f} hf := by
    change f ∈ (pres k δq).homDeg (Presentation.parityDeg sig) X.as Y.as p at hf
    refine Presentation.homDeg_induction (P := pres k δq)
      (motive := fun f => (repS k q).map f ∈ SVec.parityHom _ _ p) ?_ ?_ ?_ ?_ hf
    · intro d hd
      rw [Diagram.degree_parityDeg, oddCount_eq_length] at hd
      rw [← hd]
      exact repS_map_diag_mem d
    · show (repS k q).map 0 ∈ _
      rw [(repS k q).map_zero]; exact Submodule.zero_mem _
    · intro x y hx hy; show (repS k q).map (x + y) ∈ _; rw [(repS k q).map_add]; exact Submodule.add_mem _ hx hy
    · intro r x hx; show (repS k q).map (r • x) ∈ _; rw [(repS k q).map_smul]; exact Submodule.smul_mem _ r hx


/-! ## Concatenation of words -/

instance (n : ℕ) : Finite (Word n) := inferInstanceAs (Finite (List.Vector (Fin 2) n))

/-- Concatenation of words, `Word m × Word n ≃ Word L` for `L = m + n`. -/
def wordAppend {m n L : ℕ} (h : m + n = L) : Word m × Word n ≃ Word L where
  toFun u := ⟨u.1.1 ++ u.2.1, by rw [List.length_append, u.1.2, u.2.2, h]⟩
  invFun w := (⟨w.1.take m, by rw [List.length_take, w.2]; omega⟩,
    ⟨w.1.drop m, by rw [List.length_drop, w.2]; omega⟩)
  left_inv u := by
    obtain ⟨⟨u, rfl⟩, ⟨v, hv⟩⟩ := u
    ext <;> simp
  right_inv w := Subtype.ext (List.take_append_drop m w.1)

@[simp] theorem wordAppend_symm_fst {m n L : ℕ} (h : m + n = L) (w : Word L) :
    ((wordAppend h).symm w).1.1 = w.1.take m := rfl

@[simp] theorem wordAppend_symm_snd {m n L : ℕ} (h : m + n = L) (w : Word L) :
    ((wordAppend h).symm w).2.1 = w.1.drop m := rfl

variable (k) in
/-- The concatenation isomorphism `V^{⊗m} ⊗ V^{⊗n} ≅ V^{⊗L}`, `L = m + n`, sending
`v_u ⊗ v_w` to `v_{uw}`. -/
def catE {m n L : ℕ} (h : m + n = L) : (Word m → k) ⊗[k] (Word n → k) ≃ₗ[k] (Word L → k) :=
  ((Pi.basisFun k (Word m)).tensorProduct (Pi.basisFun k (Word n))).equiv
    (Pi.basisFun k (Word L)) (wordAppend h)

theorem catE_tmul {m n L : ℕ} (h : m + n = L) (x : Word m → k) (y : Word n → k) (w : Word L) :
    catE k h (x ⊗ₜ y) w = x ((wordAppend h).symm w).1 * y ((wordAppend h).symm w).2 := by
  let B : (Word m → k) →ₗ[k] (Word n → k) →ₗ[k] (Word L → k) :=
    LinearMap.mk₂ k (fun x y w => x ((wordAppend h).symm w).1 * y ((wordAppend h).symm w).2)
      (fun _ _ _ => by funext; simp [add_mul]) (fun _ _ _ => by funext; simp [mul_assoc])
      (fun _ _ _ => by funext; simp [mul_add]) (fun _ _ _ => by funext; simp [mul_left_comm])
  have e : (catE k h).toLinearMap = TensorProduct.lift B := by
    refine ((Pi.basisFun k (Word m)).tensorProduct (Pi.basisFun k (Word n))).ext fun i => ?_
    rw [LinearEquiv.coe_coe, catE, Basis.equiv_apply, Basis.tensorProduct_apply',
      TensorProduct.lift.tmul]
    funext w
    simp only [B, LinearMap.mk₂_apply, Pi.basisFun_apply, Pi.single_apply]
    have : w = wordAppend h i ↔ ((wordAppend h).symm w).1 = i.1 ∧ ((wordAppend h).symm w).2 = i.2 :=
      by rw [← Prod.ext_iff, Equiv.symm_apply_eq]
    by_cases h1 : ((wordAppend h).symm w).1 = i.1 <;> by_cases h2 : ((wordAppend h).symm w).2 = i.2 <;>
      simp [this, h1, h2]
  exact congrFun (LinearMap.congr_fun e (x ⊗ₜ y)) w

theorem catE_tmul' {m n L : ℕ} (h : m + n = L) (x : Word m → k) (y : Word n → k) (w : Word L) :
    catE k h (x ⊗ₜ y) w =
      x ⟨w.1.take m, by rw [List.length_take, w.2]; omega⟩ *
        y ⟨w.1.drop m, by rw [List.length_drop, w.2]; omega⟩ :=
  catE_tmul h x y w

/-- The concatenation product of functions on words: `(F · G)(w) = F(w_{<m}) G(w_{≥m})`. -/
def catF (m : ℕ) (F G : Fn k) : Fn k := fun w => F (w.take m) * G (w.drop m)

theorem ext_apply_of_ne {n : ℕ} (f : Word n → k) {w : List (Fin 2)} (h : w.length ≠ n) :
    ext k n f w = 0 := dif_neg h

theorem ext_catE {m n L : ℕ} (h : m + n = L) (x : Word m → k) (y : Word n → k) :
    ext k L (catE k h (x ⊗ₜ y)) = catF m (ext k m x) (ext k n y) := by
  funext w
  simp only [catF]
  by_cases hw : w.length = L
  · rw [ext_apply_of_length k _ hw, catE_tmul', ext_apply_of_length k x (by simp; omega),
      ext_apply_of_length k y (by simp; omega)]
  · rw [ext_apply_of_ne _ hw]
    by_cases ht : (w.take m).length = m
    · rw [ext_apply_of_ne y (by simp at ht ⊢; omega), mul_zero]
    · rw [ext_apply_of_ne x ht, zero_mul]


/-! ## Layer operators on concatenations -/

theorem del_eq_append (p : ℕ) (w : List (Fin 2)) : del p w = w.take p ++ w.drop (p + 2) := by
  induction p generalizing w with
  | zero => simp [del]
  | succ p ih =>
    rcases w with _ | ⟨a, w⟩
    · simp [del]
    · simp [del, ih, Nat.add_right_comm]

theorem take_del_add (m p : ℕ) (w : List (Fin 2)) : (del (m + p) w).take m = w.take m := by
  induction m generalizing w with
  | zero => simp
  | succ m ih =>
    rw [Nat.add_right_comm]
    rcases w with _ | ⟨x, w⟩
    · simp [del]
    · simp [del, ih]

theorem drop_del_add (m p : ℕ) (w : List (Fin 2)) :
    (del (m + p) w).drop m = del p (w.drop m) := by
  induction m generalizing w with
  | zero => simp
  | succ m ih =>
    rcases w with _ | ⟨x, w⟩
    · cases p <;> simp [del]
    · rw [Nat.add_right_comm]; simp [del, ih]

theorem take_del_of_le (p t : ℕ) (w : List (Fin 2)) :
    (del p w).take (p + t) = del p (w.take (p + t + 2)) := by
  induction p generalizing w with
  | zero => simp [del, List.drop_take]
  | succ p ih =>
    rcases w with _ | ⟨x, w⟩
    · simp [del]
    · rw [show p + 1 + t = (p + t) + 1 by omega, show p + t + 1 + 2 = (p + t + 2) + 1 by omega]
      simp [del, ih]

theorem drop_del_of_le (p t : ℕ) {w : List (Fin 2)} (hw : p + 2 ≤ w.length) :
    (del p w).drop (p + t) = w.drop (p + t + 2) := by
  induction p generalizing w with
  | zero => simp [del, Nat.add_comm]
  | succ p ih =>
    rcases w with _ | ⟨x, w⟩
    · simp at hw
    · rw [show p + 1 + t = (p + t) + 1 by omega, show p + t + 1 + 2 = (p + t + 2) + 1 by omega]
      simp only [del, List.drop_succ_cons]
      exact ih (by simp at hw; omega)

theorem psign_add (m p : ℕ) (w : List (Fin 2)) :
    psign k (m + p) w = psign k m w * psign k p (w.drop m) := by
  rw [psign, psign, psign, List.take_add, nOdd_append, pow_add]

theorem psign_take {p j : ℕ} (h : p ≤ j) (w : List (Fin 2)) : psign k p (w.take j) = psign k p w := by
  rw [psign, psign, List.take_take, Nat.min_eq_left h]

theorem getD_drop (m p : ℕ) (w : List (Fin 2)) : (w.drop m).getD p 0 = w.getD (m + p) 0 := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_take {p j : ℕ} (h : p < j) (w : List (Fin 2)) : (w.take j).getD p 0 = w.getD p 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, h]

theorem psign_mul_of_supp {r : ZMod 2} {F : Fn k} (hF : Supp r F) (m : ℕ) (w : List (Fin 2)) :
    psign k m w * F (w.take m) = sign k r * F (w.take m) := by
  by_cases h : wpar (w.take m) = r
  · rw [psign_eq_sign, h]
  · rw [hF _ h, mul_zero, mul_zero]

/-- A layer whiskered on the left by `m` strands acts on `F · G`, `F` of parity `r`, through the
Koszul sign `(-1)^r`. -/
theorem op_wl_catF (a : Obj sig) (L : Layer sig) {r : ZMod 2} {F : Fn k} (hF : Supp r F)
    (G : Fn k) {w : List (Fin 2)} (hw : a.word.length + L.left.length ≤ w.length) :
    op k q (L.wl a) (catF a.word.length F G) w =
      catF a.word.length F (sign k r • op k q L G) w := by
  obtain ⟨s, l, g, r'⟩ := L
  cases g with
  | cup =>
    change cupOp k q (a.word ++ l).length _ w = _
    simp only [List.length_append, cupOp_apply, catF, op_cup, LinearMap.smul_apply,
      Pi.smul_apply, smul_eq_mul] at hw ⊢
    generalize a.word.length = m at *
    rw [psign_add, getD_drop, getD_drop, take_del_add, drop_del_add, ← Nat.add_assoc]
    have := psign_mul_of_supp hF m w
    linear_combination (psign k l.length (w.drop m) * cupCoeff k q (w.getD (m + l.length) 0)
      (w.getD (m + l.length + 1) 0) * G (del l.length (w.drop m))) * this
  | cap =>
    change capOp k q (a.word ++ l).length _ w = _
    simp only [List.length_append, capOp_apply, catF, op_cap, LinearMap.smul_apply,
      Pi.smul_apply, smul_eq_mul] at hw ⊢
    generalize a.word.length = m at *
    rw [psign_add]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    rw [take_ins_le b c (by omega) (by omega), drop_ins_le b c (by omega) (by omega),
      Nat.add_sub_cancel_left]
    have := psign_mul_of_supp hF m w
    linear_combination (capCoeff k q b c * psign k l.length (w.drop m) *
      G (ins l.length b c (w.drop m))) * this

/-- A layer whiskered on the right acts on `F · G` through its action on `F`. -/
theorem op_wr_catF (L : Layer sig) (v : List Unit) (F G : Fn k) {w : List (Fin 2)}
    (hw : L.cod.word.length ≤ w.length) :
    op k q (L.wr v) (catF L.dom.word.length F G) w =
      catF L.cod.word.length (op k q L F) G w := by
  obtain ⟨s, l, g, r'⟩ := L
  cases g with
  | cup =>
    change cupOp k q l.length _ w = _
    simp only [Layer.dom_word, Layer.cod_word, List.length_append, sig_dom_cup, sig_cod_cup,
      List.length_nil, List.length_cons, cupOp_apply, catF, op_cup] at hw ⊢
    generalize l.length = p at *
    generalize r'.length = t at *
    rw [show p + 0 + t = p + t by omega, show p + (0 + 1 + 1) + t = p + t + 2 by omega]
    rw [psign_take (by omega), getD_take (by omega), getD_take (by omega), take_del_of_le,
      drop_del_of_le _ _ (by omega)]
    ring
  | cap =>
    change capOp k q l.length _ w = _
    simp only [Layer.dom_word, Layer.cod_word, List.length_append, sig_dom_cap, sig_cod_cap,
      List.length_nil, List.length_cons, capOp_apply, catF, op_cap] at hw ⊢
    generalize l.length = p at *
    generalize r'.length = t at *
    rw [show p + (0 + 1 + 1) + t = p + t + 2 by omega, show p + 0 + t = p + t by omega]
    rw [psign_take (by omega), mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [take_ins_ge b c (by omega) (by omega), drop_ins_ge b c (by omega) (by omega)]
    ring


theorem opList_agree {a b : Obj sig} {ls : List (Layer sig)} (hc : Chain a ls b)
    {F F' : Fn k} (h : Agree a.word.length F F') :
    Agree b.word.length ((loc k q).opList ls F) ((loc k q).opList ls F') := by
  induction ls generalizing a F F' with
  | nil => cases hc; exact h
  | cons L ls ih =>
    obtain ⟨-, rfl, hc⟩ := hc
    exact ih hc (op_agree L h)

/-- Left whiskering by `a` of a chain of layers acts on `F · G`, `F` of parity `r`, with the
Koszul sign `(-1)^{r·(number of layers)}`. -/
theorem opList_wl_catF (a : Obj sig) {b b' : Obj sig} {ls : List (Layer sig)} (hc : Chain b ls b')
    {r : ZMod 2} {F : Fn k} (hF : Supp r F) (G : Fn k) :
    Agree (a.word.length + b'.word.length)
      ((loc k q).opList (ls.map (·.wl a)) (catF a.word.length F G))
      (catF a.word.length F (sign k (r * ls.length) • (loc k q).opList ls G)) := by
  induction ls generalizing b G with
  | nil => cases hc; intro w _; simp [catF]
  | cons L ls ih =>
    obtain ⟨-, rfl, hc⟩ := hc
    intro w hw
    simp only [List.map_cons, LocalInterpretation.opList_cons, LinearMap.comp_apply]
    have h1 : Agree (a.tensor L.cod).word.length ((loc k q).op (L.wl a) (catF a.word.length F G))
        (catF a.word.length F (sign k r • (loc k q).op L G)) := by
      intro w' hw'
      simp only [Obj.tensor, List.length_append, Layer.cod_word] at hw'
      exact op_wl_catF a L hF G (by omega)
    rw [opList_agree (hc.wl a) h1 w (by simp [Obj.tensor]; omega), ih hc _ w hw]
    simp only [catF, map_smul, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, List.length_cons,
      Nat.cast_add, Nat.cast_one, mul_add, mul_one, sign_add]
    ring

/-- Right whiskering of a chain of layers acts on `F · G` through its action on `F`. -/
theorem opList_wr_catF {a a' : Obj sig} {ls : List (Layer sig)} (hc : Chain a ls a') (b : Obj sig)
    (F G : Fn k) :
    Agree (a'.word.length + b.word.length)
      ((loc k q).opList (ls.map (·.wr b.word)) (catF a.word.length F G))
      (catF a'.word.length ((loc k q).opList ls F) G) := by
  induction ls generalizing a F with
  | nil => cases hc; intro w _; rfl
  | cons L ls ih =>
    obtain ⟨-, rfl, hc⟩ := hc
    intro w hw
    simp only [List.map_cons, LocalInterpretation.opList_cons, LinearMap.comp_apply]
    have h1 : Agree (L.cod.tensor b).word.length ((loc k q).op (L.wr b.word)
        (catF L.dom.word.length F G)) (catF L.cod.word.length ((loc k q).op L F) G) := by
      intro w' hw'
      simp only [Obj.tensor, List.length_append] at hw'
      exact op_wr_catF L b.word F G (by omega)
    rw [opList_agree (hc.wr b) h1 w (by simp [Obj.tensor]; omega), ih hc _ w hw]


/-! ## The monoidal structure -/

theorem catE_mem_part {m n L : ℕ} (h : m + n = L) {a b : ZMod 2} {x : sv k m} {y : sv k n}
    (hx : x ∈ (sv k m).part a) (hy : y ∈ (sv k n).part b) :
    (catE k h (x ⊗ₜ y) : sv k L) ∈ (sv k L).part (a + b) := by
  rw [mem_sv_part]
  intro w hw
  rw [catE_tmul']
  by_cases h1 : wpar (w.1.take m) = a
  · rw [mem_sv_part.mp hy, mul_zero]
    intro h2
    apply hw
    rw [← List.take_append_drop m w.1, wpar_append, h1]
    exact congrArg (a + ·) h2
  · rw [mem_sv_part.mp hx _ h1, zero_mul]

variable (k)

/-- The unit isomorphism `k ≅ V^{⊗0}`. -/
def unitEquiv : k ≃ₗ[k] (Word 0 → k) where
  toFun r _ := r
  invFun f := f ⟨[], rfl⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv f := by
    funext w
    exact congrArg f (Subtype.ext (List.eq_nil_of_length_eq_zero w.2).symm)

variable {k}

theorem length_tensor (X Y : STL k δq) :
    ((pres k δq).toObj X).word.length + ((pres k δq).toObj Y).word.length =
      ((pres k δq).toObj (X ⊗ Y)).word.length :=
  List.length_append.symm

variable (k q)

/-- The coherence isomorphism `G(X) ⊗ G(Y) ≅ G(X ⊗ Y)`: concatenation of words. -/
def μIso (X Y : STL k δq) : (repS k q).obj X ⊗ (repS k q).obj Y ≅ (repS k q).obj (X ⊗ Y) :=
  SVec.isoOfLinearEquiv (V := (repS k q).obj X ⊗ (repS k q).obj Y)
    (catE k (length_tensor X Y))

/-- The coherence isomorphism `k ≅ G(0)`. -/
def εIso : 𝟙_ (SVec k) ≅ (repS k q).obj (𝟙_ (STL k δq)) :=
  SVec.isoOfLinearEquiv (V := 𝟙_ (SVec k)) (unitEquiv k)

variable {k q}

theorem μIso_hom_apply (X Y : STL k δq) (x : (repS k q).obj X) (y : (repS k q).obj Y)
    (w : Word ((pres k δq).toObj (X ⊗ Y)).word.length) :
    (μIso k q X Y).hom (x ⊗ₜ y) w =
      x ⟨w.1.take ((pres k δq).toObj X).word.length, by rw [List.length_take, w.2, ← length_tensor]; omega⟩ *
        y ⟨w.1.drop ((pres k δq).toObj X).word.length,
          by rw [List.length_drop, w.2, ← length_tensor]; omega⟩ :=
  catE_tmul' _ x y w

theorem μIso_mem (X Y : STL k δq) :
    (μIso k q X Y).hom ∈ parity (R := k) ((repS k q).obj X ⊗ (repS k q).obj Y)
      ((repS k q).obj (X ⊗ Y)) 0 := by
  intro r
  refine SVec.ext_tensor fun a b x y hx hy => ?_
  simp only [LinearMap.comp_apply, add_zero]
  erw [SVec.proj_apply_of_mem_part _ (SVec.tmul_mem_part hx hy)]
  erw [SVec.proj_apply_of_mem_part _ (catE_mem_part (length_tensor X Y) hx hy)]
  split_ifs
  · rfl
  · exact map_zero _

theorem εIso_mem : (εIso k q).hom ∈ parity (R := k) _ _ 0 := by
  intro r
  refine LinearMap.ext fun c => funext fun w => ?_
  simp only [LinearMap.comp_apply, add_zero]
  change (εIso k q).hom (SVec.unit.proj r c) w = (sv k 0).proj r ((εIso k q).hom c) w
  rw [sv_proj_apply]
  obtain rfl : w = ⟨[], rfl⟩ := Subtype.ext (List.eq_nil_of_length_eq_zero w.2)
  rcases parity_eq_zero_or_one r with rfl | rfl
  · exact (SVec.unit_proj_zero_apply (k := k) c).trans (if_pos rfl).symm
  · exact (SVec.unit_proj_one_apply (k := k) c).trans (if_neg (show wpar [] ≠ 1 by decide)).symm


omit [CommRing k] in
theorem app_congr {k : Type*} {n : ℕ} (x : Word n → k) {l l' : List (Fin 2)} (hl : l.length = n)
    (hl' : l'.length = n) (e : l = l') : x ⟨l, hl⟩ = x ⟨l', hl'⟩ := by
  subst e; rfl

theorem repS_map_eqToHom {X Y : STL k δq} (h : X = Y) (x : (repS k q).obj X)
    (w : Word ((pres k δq).toObj Y).word.length) :
    (repS k q).map (eqToHom h) x w = x ⟨w.1, by subst h; exact w.2⟩ := by
  subst h
  rw [eqToHom_refl, CategoryTheory.Functor.map_id]
  rfl

theorem μ_natural_left {X Y : STL k δq} (f : X ⟶ Y) (X' : STL k δq) :
    (repS k q).map f ▷ (repS k q).obj X' ≫ (μIso k q Y X').hom =
      (μIso k q X X').hom ≫ (repS k q).map (f ▷ X') := by
  induction f using (pres k δq).hom_induction with
  | diag d =>
    refine TensorProduct.ext' fun x y => funext fun w => ?_
    change (μIso k q _ X').hom ((repS k q).map ((pres k δq).diag d) x ⊗ₜ y) w =
      (repS k q).map ((pres k δq).diag d ▷ (pres k δq).obj X'.as)
        ((μIso k q _ X').hom (x ⊗ₜ y)) w
    rw [(pres k δq).diag_whiskerRight d X'.as]
    refine Eq.trans ?_ (repS_map_diag_apply (Diagram.whiskerR d X'.as) _ w).symm
    rw [Diagram.layers_whiskerR]
    change _ = (loc k q).opList _ (ext k _ (catE k _ (x ⊗ₜ y))) w.1
    rw [ext_catE]
    erw [opList_wr_catF (Diagram.chain d) X'.as _ _ w.1 (by rw [w.2]; exact List.length_append)]
    rw [μIso_hom_apply]
    simp only [catF]
    rw [repS_map_diag_apply, ext_apply_of_length k y
      (by rw [List.length_drop, w.2]; change (Y.as.word ++ X'.as.word).length - _ = _; simp; rfl)]
    rfl
  | zero =>
    rw [(repS k q).map_zero, MonoidalSupercategory.zero_whiskerRight k,
      MonoidalSupercategory.zero_whiskerRight k, (repS k q).map_zero, Limits.zero_comp,
      Limits.comp_zero]
  | add f g hf hg =>
    rw [(repS k q).map_add, MonoidalSupercategory.add_whiskerRight (R := k),
      MonoidalSupercategory.add_whiskerRight (R := k), (repS k q).map_add, Preadditive.add_comp,
      Preadditive.comp_add, hf, hg]
  | smul r f hf =>
    rw [(repS k q).map_smul, MonoidalSupercategory.smul_whiskerRight (R := k),
      MonoidalSupercategory.smul_whiskerRight (R := k), (repS k q).map_smul, Linear.smul_comp,
      Linear.comp_smul, hf]


theorem μ_natural_right {X Y : STL k δq} (X' : STL k δq) (f : X ⟶ Y) :
    (repS k q).obj X' ◁ (repS k q).map f ≫ (μIso k q X' Y).hom =
      (μIso k q X' X).hom ≫ (repS k q).map (X' ◁ f) := by
  induction f using (pres k δq).hom_induction with
  | diag d =>
    refine SVec.ext_tensor fun r s x y hx _ => funext fun w => ?_
    change (μIso k q X' _).hom (((repS k q).obj X' ◁ (repS k q).map ((pres k δq).diag d))
        (x ⊗ₜ y)) w =
      (repS k q).map ((pres k δq).obj X'.as ◁ (pres k δq).diag d)
        ((μIso k q X' _).hom (x ⊗ₜ y)) w
    rw [SVec.whiskerLeft_tmul' (repS_map_diag_mem d) hx, map_smul,
      (pres k δq).diag_whiskerLeft X'.as d]
    refine Eq.trans ?_ (repS_map_diag_apply (Diagram.whiskerL X'.as d) _ w).symm
    rw [Diagram.layers_whiskerL]
    change _ = (loc k q).opList _ (ext k _ (catE k _ (x ⊗ₜ y))) w.1
    rw [ext_catE]
    erw [opList_wl_catF X'.as (Diagram.chain d) (supp_ext hx) _ w.1
      (by rw [w.2]; exact List.length_append)]
    rw [Pi.smul_apply, μIso_hom_apply]
    simp only [catF, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    rw [repS_map_diag_apply, ext_apply_of_length k x
      (by rw [List.length_take, w.2]; change min _ (X'.as.word ++ Y.as.word).length = _; simp; rfl)]
    change _ = _ * (_ * (loc k q).opList (Diagram.layers d) _ _)
    ring_nf
    rfl
  | zero =>
    rw [(repS k q).map_zero, MonoidalSupercategory.whiskerLeft_zero k,
      MonoidalSupercategory.whiskerLeft_zero k, (repS k q).map_zero, Limits.zero_comp,
      Limits.comp_zero]
  | add f g hf hg =>
    rw [(repS k q).map_add, MonoidalSupercategory.whiskerLeft_add (R := k),
      MonoidalSupercategory.whiskerLeft_add (R := k), (repS k q).map_add, Preadditive.add_comp,
      Preadditive.comp_add, hf, hg]
  | smul r f hf =>
    rw [(repS k q).map_smul, MonoidalSupercategory.whiskerLeft_smul (R := k),
      MonoidalSupercategory.whiskerLeft_smul (R := k), (repS k q).map_smul, Linear.smul_comp,
      Linear.comp_smul, hf]


theorem μ_associativity (X Y Z : STL k δq) :
    (μIso k q X Y).hom ▷ (repS k q).obj Z ≫ (μIso k q (X ⊗ Y) Z).hom ≫
        (repS k q).map (α_ X Y Z).hom =
      (α_ ((repS k q).obj X) ((repS k q).obj Y) ((repS k q).obj Z)).hom ≫
        (repS k q).obj X ◁ (μIso k q Y Z).hom ≫ (μIso k q X (Y ⊗ Z)).hom := by
  change _ = _ ≫ SVec.whiskerLeft _ _ ≫ _
  rw [SVec.whiskerLeft_even _ (μIso_mem Y Z)]
  refine TensorProduct.ext_threefold fun x y z => funext fun w => ?_
  change (repS k q).map (eqToHom ((pres k δq).tensor_assoc_obj X Y Z)) ((μIso k q (X ⊗ Y) Z).hom ((μIso k q X Y).hom (x ⊗ₜ y) ⊗ₜ z)) w =
    (μIso k q X (Y ⊗ Z)).hom (x ⊗ₜ (μIso k q Y Z).hom (y ⊗ₜ z)) w
  rw [repS_map_eqToHom, μIso_hom_apply, μIso_hom_apply, μIso_hom_apply, μIso_hom_apply, mul_assoc]
  have h1 : (X ⊗ Y).as.word.length = X.as.word.length + Y.as.word.length := List.length_append
  have h2 : (X ⊗ Y ⊗ Z).as.word.length = X.as.word.length + (Y.as.word.length +
    Z.as.word.length) := by
    change (X.as.word ++ (Y.as.word ++ Z.as.word)).length = _; simp
  refine congr_arg₂ (· * ·) (app_congr x _ _ ?_)
    (congr_arg₂ (· * ·) (app_congr y _ _ ?_) (app_congr z _ _ ?_)) <;>
  simp [List.take_take, List.drop_take, List.drop_drop, Obj.tensor, Presentation.toObj, h1, h2]


theorem μ_left_unitality (X : STL k δq) :
    (λ_ ((repS k q).obj X)).hom =
      (εIso k q).hom ▷ (repS k q).obj X ≫ (μIso k q (𝟙_ _) X).hom ≫ (repS k q).map (λ_ X).hom := by
  refine TensorProduct.ext' fun (c : k) x => funext fun w => ?_
  change c • x w = (repS k q).map (eqToHom ((pres k δq).unit_tensor_obj X))
    ((μIso k q (𝟙_ _) X).hom ((εIso k q).hom c ⊗ₜ x)) w
  rw [repS_map_eqToHom, μIso_hom_apply, smul_eq_mul]
  exact congrArg (c * ·) (app_congr x _ _ List.drop_zero)

theorem μ_right_unitality (X : STL k δq) :
    (ρ_ ((repS k q).obj X)).hom =
      (repS k q).obj X ◁ (εIso k q).hom ≫ (μIso k q X (𝟙_ _)).hom ≫ (repS k q).map (ρ_ X).hom := by
  change _ = SVec.whiskerLeft _ _ ≫ _
  rw [SVec.whiskerLeft_even _ εIso_mem]
  refine TensorProduct.ext' fun x (c : k) => funext fun w => ?_
  change c • x w = (repS k q).map (eqToHom ((pres k δq).tensor_unit_obj X))
    ((μIso k q X (𝟙_ _)).hom (x ⊗ₜ (εIso k q).hom c)) w
  rw [repS_map_eqToHom, μIso_hom_apply, smul_eq_mul, mul_comm]
  exact congrArg (· * c) (app_congr x _ _ (List.take_of_length_le (by rw [w.2])).symm)

variable (k q)

/-- **Lemma A.1.** `G : STL(δ) → SVec`, `n ↦ V^{⊗n}` (`δ = -(q - q⁻¹)`), is a monoidal
superfunctor, with coherence maps the concatenation isomorphisms
`V^{⊗m} ⊗ V^{⊗n} ≅ V^{⊗(m+n)}` and `k ≅ V^{⊗0}`. -/
def repSMonoidal : MonoidalSuperfunctor k (repS k q) where
  μIso := μIso k q
  εIso := εIso k q
  μ_mem := μIso_mem
  ε_mem := εIso_mem
  μ_natural_left := μ_natural_left
  μ_natural_right := μ_natural_right
  associativity := μ_associativity
  left_unitality := μ_left_unitality
  right_unitality := μ_right_unitality

end StringDiagrams.OddTemperleyLieb.Rep
