import StringDiagrams.Examples.TemperleyLieb
import Mathlib.Data.Fintype.BigOperators

/-!
# The two-dimensional representation of the Temperley–Lieb category

Over a commutative ring `R`, let `V = R²` with basis `e₀, e₁`. This file constructs a functor
from the Temperley–Lieb category `pres R (-2)` to `R`-modules sending `n` strands to a model
of `V^{⊗n}`, the cup to the vector `u = e₀ ⊗ e₁ - e₁ ⊗ e₀` and the cap to the bilinear form
`β` with `β(e₀, e₁) = -1`, `β(e₁, e₀) = 1`, `β(eᵢ, eᵢ) = 0`.

## Conventions and the loop value

Write `U = (u_{ab})` and `B = (β_{ab})` for the coefficient matrices of the cup and the cap.
With the cup inserted at positions `p, p + 1` and the cap contracting positions `p, p + 1`,
the zigzag relations read `B U = 1` (`zigzagA`) and `U B = 1` (`zigzagB`), so `B = U⁻¹`; the
loop relation then forces `δ = Σ_{a b} u_{ab} β_{ab}`. For `U = [[0, 1], [-1, 0]]` this gives
`B = [[0, -1], [1, 0]]` and `δ = -2`. On `V ⊗ V`, `cup ∘ cap` is `P - 1` where `P` is the flip.

## The model of `V^{⊗n}`

The object with `n` strands is sent to `Word n → R`, where `Word n` is the type of lists of
length `n` over `Fin 2` (definitionally `List.Vector (Fin 2) n`; `Word n ≃ (Fin n → Fin 2)` by
`Equiv.vectorEquivFin`). A function `f : Word n → R` is the vector `Σ_w f(w) e_{w₁} ⊗ ⋯ ⊗ e_{wₙ}`.
Lists rather than `Fin n → Fin 2` are used because inserting and deleting two tensor factors
at a position are simple list operations (`ins`, `del`), and because the retyping of words along
equalities of lengths only changes a proof, never the underlying list.

The layer maps are first defined on the space `List (Fin 2) → R` of functions on words of all
lengths (`cupOp`, `capOp`, `op`), where no dependent types occur, and then restricted to words
of the right length (`restrict`). The value of the functor on a diagram is the composite of the
layer operators, evaluated on words of the target length (`map_apply`); this rests on the
locality of the layer operators (`op_agree`). All relations are then checked as identities of
functions on lists.

## Main declarations

* `Rep.interp R`: the interpretation, with a width-dependent object map.
* `Rep.respects R`: it respects the relations of `pres R (-2)` and the interchange law.
* `Rep.rep R : (pres R (-2)).Presented ⥤ ModuleCat R`: the induced functor.
* `Rep.e_ne_zero`: for nontrivial `R`, `e (-2) m i ≠ 0` whenever `i ≤ m`.
-/

noncomputable section

namespace StringDiagrams.TemperleyLieb.Rep

open CategoryTheory

/-! ## Words and the operations `ins`, `del` -/

/-- Basis words of `V^{⊗n}`: lists of length `n` over `Fin 2`. -/
abbrev Word (n : ℕ) : Type := {w : List (Fin 2) // w.length = n}

example (n : ℕ) : Word n = List.Vector (Fin 2) n := rfl

/-- `Word n` has `2 ^ n` elements. -/
theorem card_word (n : ℕ) : Fintype.card (List.Vector (Fin 2) n) = 2 ^ n := by
  simp [card_vector]

/-- Insert the letters `a, b` at positions `p, p + 1` (at the end if `p` exceeds the length). -/
def ins : ℕ → Fin 2 → Fin 2 → List (Fin 2) → List (Fin 2)
  | 0, a, b, w => a :: b :: w
  | _ + 1, a, b, [] => [a, b]
  | p + 1, a, b, x :: w => x :: ins p a b w

/-- Delete the letters at positions `p, p + 1`. -/
def del : ℕ → List (Fin 2) → List (Fin 2)
  | 0, w => w.drop 2
  | _ + 1, [] => []
  | p + 1, x :: w => x :: del p w

@[simp] theorem length_ins (p : ℕ) (a b : Fin 2) (w : List (Fin 2)) :
    (ins p a b w).length = w.length + 2 := by
  induction p generalizing w with
  | zero => simp [ins]
  | succ p ih => cases w with
    | nil => simp [ins]
    | cons x w => simp [ins, ih]

theorem length_del {p : ℕ} {w : List (Fin 2)} (h : p + 2 ≤ w.length) :
    (del p w).length + 2 = w.length := by
  induction p generalizing w with
  | zero => simp [del]; omega
  | succ p ih => cases w with
    | nil => simp at h
    | cons x w => simp [del]; have := ih (w := w) (by simp at h; omega); omega

theorem getD_ins_lt {p q : ℕ} (a b : Fin 2) {w : List (Fin 2)} (hq : q < p) (hp : p ≤ w.length) :
    (ins p a b w).getD q 0 = w.getD q 0 := by
  induction p generalizing w q with
  | zero => omega
  | succ p ih => cases w with
    | nil => simp at hp
    | cons x w => cases q with
      | zero => simp [ins]
      | succ q => simp only [ins, List.getD_cons_succ]; exact ih (by omega) (by simp at hp; omega)

@[simp] theorem getD_ins_self (p : ℕ) (a b : Fin 2) {w : List (Fin 2)} (hp : p ≤ w.length) :
    (ins p a b w).getD p 0 = a := by
  induction p generalizing w with
  | zero => simp [ins]
  | succ p ih => cases w with
    | nil => simp at hp
    | cons x w => simp only [ins, List.getD_cons_succ]; exact ih (by simp at hp; omega)

@[simp] theorem getD_ins_succ (p : ℕ) (a b : Fin 2) {w : List (Fin 2)} (hp : p ≤ w.length) :
    (ins p a b w).getD (p + 1) 0 = b := by
  induction p generalizing w with
  | zero => simp [ins]
  | succ p ih => cases w with
    | nil => simp at hp
    | cons x w => simp only [ins, List.getD_cons_succ]; exact ih (by simp at hp; omega)

theorem getD_ins_ge {p q : ℕ} (a b : Fin 2) {w : List (Fin 2)} (hq : p ≤ q) (hp : p ≤ w.length) :
    (ins p a b w).getD (q + 2) 0 = w.getD q 0 := by
  induction p generalizing w q with
  | zero => simp [ins]
  | succ p ih => cases w with
    | nil => simp at hp
    | cons x w =>
      obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      simp only [ins, show q + 1 + 2 = (q + 2) + 1 by omega, List.getD_cons_succ]
      exact ih (by omega) (by simp at hp; omega)

theorem getD_del_lt {p q : ℕ} {w : List (Fin 2)} (hq : q < p) (hp : p + 2 ≤ w.length) :
    (del p w).getD q 0 = w.getD q 0 := by
  induction p generalizing w q with
  | zero => omega
  | succ p ih => cases w with
    | nil => simp at hp
    | cons x w => cases q with
      | zero => simp [del]
      | succ q => simp only [del, List.getD_cons_succ]; exact ih (by omega) (by simp at hp; omega)

theorem getD_del_ge {p q : ℕ} {w : List (Fin 2)} (hq : p ≤ q) :
    (del p w).getD q 0 = w.getD (q + 2) 0 := by
  induction p generalizing w q with
  | zero => simp [del, List.getD_eq_getElem?_getD, add_comm]
  | succ p ih => cases w with
    | nil => simp [del]
    | cons x w =>
      obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      simp only [del, show q + 1 + 2 = (q + 2) + 1 by omega, List.getD_cons_succ]
      exact ih (by omega)

@[simp] theorem del_ins (p : ℕ) (a b : Fin 2) {w : List (Fin 2)} (hp : p ≤ w.length) :
    del p (ins p a b w) = w := by
  induction p generalizing w with
  | zero => simp [ins, del]
  | succ p ih => cases w with
    | nil => simp at hp
    | cons x w => simp only [ins, del]; rw [ih (by simp at hp; omega)]

theorem del_succ_ins {p : ℕ} (a b : Fin 2) {w : List (Fin 2)} (hp : p < w.length) :
    del (p + 1) (ins p a b w) = w.set p a := by
  induction p generalizing w with
  | zero => cases w with
    | nil => simp at hp
    | cons x w => simp [ins, del]
  | succ p ih => cases w with
    | nil => simp at hp
    | cons x w => simp only [ins, del, List.set_cons_succ]; rw [ih (by simp at hp; omega)]

theorem del_ins_succ {p : ℕ} (a b : Fin 2) {w : List (Fin 2)} (hp : p < w.length) :
    del p (ins (p + 1) a b w) = w.set p b := by
  induction p generalizing w with
  | zero => cases w with
    | nil => simp at hp
    | cons x w => simp [ins, del]
  | succ p ih => cases w with
    | nil => simp at hp
    | cons x w => simp only [ins, del, List.set_cons_succ]; rw [ih (by simp at hp; omega)]

theorem set_getD_self {p : ℕ} {w : List (Fin 2)} (hp : p < w.length) : w.set p (w.getD p 0) = w := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp, Option.getD_some]
  exact List.set_getElem_self hp

theorem ins_ins {p k : ℕ} (a b c d : Fin 2) {w : List (Fin 2)} (h : p + k ≤ w.length) :
    ins (p + 2 + k) c d (ins p a b w) = ins p a b (ins (p + k) c d w) := by
  induction p generalizing w with
  | zero => simp [ins, show 2 + k = k + 1 + 1 by omega]
  | succ p ih => cases w with
    | nil => simp at h
    | cons x w =>
      simp only [show p + 1 + 2 + k = (p + 2 + k) + 1 by omega, show p + 1 + k = (p + k) + 1 by omega,
        ins]
      rw [ih (by simp at h; omega)]

theorem del_del {p k : ℕ} {w : List (Fin 2)} (h : p + k + 4 ≤ w.length) :
    del p (del (p + 2 + k) w) = del (p + k) (del p w) := by
  induction p generalizing w with
  | zero =>
    obtain ⟨x, y, w, rfl⟩ : ∃ x y w', w = x :: y :: w' := by
      rcases w with _ | ⟨x, _ | ⟨y, w'⟩⟩
      · simp at h
      · simp at h
      · exact ⟨x, y, w', rfl⟩
    simp [del, show 2 + k = k + 1 + 1 by omega]
  | succ p ih => cases w with
    | nil => simp at h
    | cons x w =>
      simp only [show p + 1 + 2 + k = (p + 2 + k) + 1 by omega, show p + 1 + k = (p + k) + 1 by omega,
        del]
      rw [ih (by simp at h; omega)]

theorem del_ins_far {p k : ℕ} (a b : Fin 2) {w : List (Fin 2)} (h : p + k + 2 ≤ w.length) :
    del (p + 2 + k) (ins p a b w) = ins p a b (del (p + k) w) := by
  induction p generalizing w with
  | zero => simp [ins, del, show 2 + k = k + 1 + 1 by omega]
  | succ p ih => cases w with
    | nil => simp at h
    | cons x w =>
      simp only [show p + 1 + 2 + k = (p + 2 + k) + 1 by omega, show p + 1 + k = (p + k) + 1 by omega,
        ins, del]
      rw [ih (by simp at h; omega)]

theorem del_ins_far' {p k : ℕ} (c d : Fin 2) {w : List (Fin 2)} (h : p + 2 + k ≤ w.length) :
    del p (ins (p + 2 + k) c d w) = ins (p + k) c d (del p w) := by
  induction p generalizing w with
  | zero =>
    obtain ⟨x, y, w, rfl⟩ : ∃ x y w', w = x :: y :: w' := by
      rcases w with _ | ⟨x, _ | ⟨y, w'⟩⟩
      · simp at h
      · simp at h; omega
      · exact ⟨x, y, w', rfl⟩
    simp [ins, del, show 2 + k = k + 1 + 1 by omega]
  | succ p ih => cases w with
    | nil => simp at h
    | cons x w =>
      simp only [show p + 1 + 2 + k = (p + 2 + k) + 1 by omega, show p + 1 + k = (p + k) + 1 by omega,
        ins, del]
      rw [ih (by simp at h; omega)]


/-! ## The layer operators on functions of words of all lengths -/

variable (R : Type*) [CommRing R]

/-- Coefficients of the cup vector `u = e₀ ⊗ e₁ - e₁ ⊗ e₀`. -/
def cupCoeff : Fin 2 → Fin 2 → R := ![![0, 1], ![-1, 0]]

/-- Coefficients of the cap form `β`: `β(e₀, e₁) = -1`, `β(e₁, e₀) = 1`. -/
def capCoeff : Fin 2 → Fin 2 → R := ![![0, -1], ![1, 0]]

/-- Functions on words of all lengths. -/
abbrev Fn : Type _ := List (Fin 2) → R

/-- The cup at position `p`: `(cup F)(w) = u(w_p, w_{p+1}) F(w without w_p, w_{p+1})`. -/
def cupOp (p : ℕ) : Fn R →ₗ[R] Fn R where
  toFun F w := cupCoeff R (w.getD p 0) (w.getD (p + 1) 0) * F (del p w)
  map_add' F G := by funext w; simp [mul_add]
  map_smul' r F := by funext w; simp [mul_left_comm]

/-- The cap at position `p`: `(cap F)(w) = Σ_{a b} β(a, b) F(w with a, b inserted at p)`. -/
def capOp (p : ℕ) : Fn R →ₗ[R] Fn R where
  toFun F w := ∑ a : Fin 2, ∑ b : Fin 2, capCoeff R a b * F (ins p a b w)
  map_add' F G := by funext w; simp [mul_add, Finset.sum_add_distrib]
  map_smul' r F := by funext w; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
    Finset.mul_sum, mul_left_comm]

@[simp] theorem cupOp_apply (p : ℕ) (F : Fn R) (w : List (Fin 2)) :
    cupOp R p F w = cupCoeff R (w.getD p 0) (w.getD (p + 1) 0) * F (del p w) := rfl

@[simp] theorem capOp_apply (p : ℕ) (F : Fn R) (w : List (Fin 2)) :
    capOp R p F w = ∑ a : Fin 2, ∑ b : Fin 2, capCoeff R a b * F (ins p a b w) := rfl

/-- The operator of a layer: a cup or a cap at the position given by its left strands. -/
def op (L : Layer sig) : Fn R →ₗ[R] Fn R :=
  match (L.gen : Gen) with
  | .cup => cupOp R L.left.length
  | .cap => capOp R L.left.length

/-- The composite of the operators of a list of layers, the first layer acting first. -/
def evalLayers : List (Layer sig) → (Fn R →ₗ[R] Fn R)
  | [] => LinearMap.id
  | L :: ls => evalLayers ls ∘ₗ op R L

@[simp] theorem evalLayers_nil : evalLayers R [] = LinearMap.id := rfl

@[simp] theorem evalLayers_cons (L : Layer sig) (ls : List (Layer sig)) :
    evalLayers R (L :: ls) = evalLayers R ls ∘ₗ op R L := rfl

/-! ### Locality -/

variable {R}

/-- `F` and `F'` agree on words of length `n`. -/
def Agree (n : ℕ) (F F' : Fn R) : Prop := ∀ w : List (Fin 2), w.length = n → F w = F' w

theorem op_agree (L : Layer sig) {F F' : Fn R} (h : Agree L.dom.word.length F F') :
    Agree L.cod.word.length (op R L F) (op R L F') := by
  obtain ⟨s, l, g, r⟩ := L
  intro w hw
  cases g with
  | cup =>
    simp only [Layer.cod_word, List.length_append, sig, List.length_cons, List.length_nil] at hw
    have := length_del (p := l.length) (w := w) (by omega)
    simp only [op, cupOp_apply]
    rw [h _ (by simp [sig]; omega)]
  | cap =>
    simp only [Layer.cod_word, List.length_append, sig, List.length_nil] at hw
    simp only [op, capOp_apply]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [h _ (by simp [sig]; omega)]

theorem evalLayers_agree {a b : Obj sig} {ls : List (Layer sig)} (hc : Chain a ls b)
    {F F' : Fn R} (h : Agree a.word.length F F') :
    Agree b.word.length (evalLayers R ls F) (evalLayers R ls F') := by
  induction ls generalizing a F F' with
  | nil => cases hc; exact h
  | cons L ls ih =>
    obtain ⟨-, rfl, hc⟩ := hc
    exact ih hc (op_agree L h)

/-! ## The interpretation -/

variable (R)

/-- Extension by zero of a function on words of length `n`. -/
def ext (n : ℕ) : (Word n → R) →ₗ[R] Fn R where
  toFun f w := if h : w.length = n then f ⟨w, h⟩ else 0
  map_add' f g := by funext w; by_cases h : w.length = n <;> simp [h]
  map_smul' r f := by funext w; by_cases h : w.length = n <;> simp [h]

theorem ext_apply_of_length {n : ℕ} (f : Word n → R) {w : List (Fin 2)} (h : w.length = n) :
    ext R n f w = f ⟨w, h⟩ := dif_pos h

@[simp] theorem ext_apply_word {n : ℕ} (f : Word n → R) (w : Word n) : ext R n f w.1 = f w :=
  dif_pos w.2

/-- The restriction of an operator on `Fn R` to words of lengths `n` (source) and `m`
(target). -/
def restrict (n m : ℕ) (T : Fn R →ₗ[R] Fn R) : (Word n → R) →ₗ[R] (Word m → R) where
  toFun f w := T (ext R n f) w.1
  map_add' f g := by funext w; simp
  map_smul' r f := by funext w; simp

@[simp] theorem restrict_apply (n m : ℕ) (T : Fn R →ₗ[R] Fn R) (f : Word n → R) (w : Word m) :
    restrict R n m T f w = T (ext R n f) w.1 := rfl

/-- The interpretation: `n` strands go to `Word n → R`, a model of `(R²)^{⊗n}`, and a layer
goes to the restriction of its operator. -/
def interp : Interpretation sig (ModuleCat R) where
  obj a := ModuleCat.of R (Word a.word.length → R)
  layer L _ := ModuleCat.ofHom (restrict R _ _ (op R L))

theorem mapChain_apply {a b : Obj sig} (ls : List (Layer sig)) (h : Chain a ls b)
    (f : Word a.word.length → R) (w : Word b.word.length) :
    ((interp R).mapChain a ls b h).hom f w = evalLayers R ls (ext R _ f) w.1 := by
  induction ls generalizing a with
  | nil =>
    cases h
    simp [Interpretation.mapChain]
  | cons L ls ih =>
    obtain ⟨hv, rfl, hc⟩ := h
    simp only [Interpretation.mapChain, eqToHom_refl, Category.id_comp, ModuleCat.hom_comp,
      LinearMap.comp_apply, ih, evalLayers_cons]
    refine evalLayers_agree hc (fun v hv => ?_) _ w.2
    rw [ext_apply_of_length R _ hv]
    rfl

/-- The functor of the interpretation on a diagram: the composite of the layer operators,
evaluated on words of the target length. -/
theorem map_apply {a b : Obj sig} (d : a ⟶ b) (f : Word a.word.length → R)
    (w : Word b.word.length) :
    ((interp R).functor.map d).hom f w = evalLayers R (Diagram.layers d) (ext R _ f) w.1 :=
  mapChain_apply R _ _ f w

/-! ## The relations as identities of operators -/

variable {R}

@[simp] theorem op_cup (s : Unit) (l r : List Unit) : op R ⟨s, l, .cup, r⟩ = cupOp R l.length := rfl

@[simp] theorem op_cap (s : Unit) (l r : List Unit) : op R ⟨s, l, .cap, r⟩ = capOp R l.length := rfl

/-- The loop relation: `cap_p ∘ cup_p = -2`. -/
theorem loop_op {p : ℕ} (F : Fn R) {w : List (Fin 2)} (hp : p ≤ w.length) :
    capOp R p (cupOp R p F) w = -2 * F w := by
  simp only [capOp_apply, cupOp_apply, getD_ins_self _ _ _ hp, getD_ins_succ _ _ _ hp,
    del_ins _ _ _ hp, Fin.sum_univ_two, cupCoeff, capCoeff]
  simp; ring

/-- The zigzag relation `cap_p ∘ cup_{p+1} = 1`. -/
theorem zigzagA_op {p : ℕ} (F : Fn R) {w : List (Fin 2)} (hp : p < w.length) :
    capOp R p (cupOp R (p + 1) F) w = F w := by
  have e : F w = F (w.set p (w.getD p 0)) := by rw [set_getD_self hp]
  simp only [capOp_apply, cupOp_apply, getD_ins_succ _ _ _ hp.le,
    show p + 1 + 1 = p + 2 from rfl, getD_ins_ge _ _ le_rfl hp.le, del_succ_ins _ _ hp, e]
  generalize w.getD p 0 = c
  fin_cases c <;> simp [Fin.sum_univ_two, cupCoeff, capCoeff]

/-- The zigzag relation `cap_{p+1} ∘ cup_p = 1`. -/
theorem zigzagB_op {p : ℕ} (F : Fn R) {w : List (Fin 2)} (hp : p < w.length) :
    capOp R (p + 1) (cupOp R p F) w = F w := by
  have e : F w = F (w.set p (w.getD p 0)) := by rw [set_getD_self hp]
  simp only [capOp_apply, cupOp_apply, getD_ins_lt _ _ (Nat.lt_succ_self p) hp,
    getD_ins_self _ _ _ hp, del_ins_succ _ _ hp, e]
  generalize w.getD p 0 = c
  fin_cases c <;> simp [Fin.sum_univ_two, cupCoeff, capCoeff]

/-- Interchange of two caps. -/
theorem cap_cap_op {p k : ℕ} (F : Fn R) {w : List (Fin 2)} (h : p + k ≤ w.length) :
    capOp R (p + k) (capOp R p F) w = capOp R p (capOp R (p + 2 + k) F) w := by
  simp only [capOp_apply, ins_ins _ _ _ _ h, Fin.sum_univ_two]
  ring

/-- Interchange of two cups. -/
theorem cup_cup_op {p k : ℕ} (F : Fn R) {w : List (Fin 2)} (h : p + k + 4 ≤ w.length) :
    cupOp R (p + 2 + k) (cupOp R p F) w = cupOp R p (cupOp R (p + k) F) w := by
  simp only [cupOp_apply]
  rw [getD_del_lt (show p < p + 2 + k by omega) (by omega),
    getD_del_lt (show p + 1 < p + 2 + k by omega) (by omega),
    getD_del_ge (show p ≤ p + k by omega), getD_del_ge (show p ≤ p + k + 1 by omega),
    show p + k + 2 = p + 2 + k by omega, show p + k + 1 + 2 = p + 2 + k + 1 by omega, del_del h]
  ring

/-- Interchange of a cap (on the left) and a cup (on the right). -/
theorem cap_cup_op {p k : ℕ} (F : Fn R) {w : List (Fin 2)} (h : p + k + 2 ≤ w.length) :
    cupOp R (p + k) (capOp R p F) w = capOp R p (cupOp R (p + 2 + k) F) w := by
  simp only [cupOp_apply, capOp_apply]
  simp only [del_ins_far _ _ h]
  simp only [show p + 2 + k + 1 = (p + k + 1) + 2 by omega, show p + 2 + k = (p + k) + 2 by omega,
    getD_ins_ge _ _ (show p ≤ p + k by omega) (show p ≤ w.length by omega),
    getD_ins_ge _ _ (show p ≤ p + k + 1 by omega) (show p ≤ w.length by omega), Fin.sum_univ_two]
  ring

/-- Interchange of a cup (on the left) and a cap (on the right). -/
theorem cup_cap_op {p k : ℕ} (F : Fn R) {w : List (Fin 2)} (h : p + 2 + k ≤ w.length) :
    capOp R (p + 2 + k) (cupOp R p F) w = cupOp R p (capOp R (p + k) F) w := by
  simp only [cupOp_apply, capOp_apply, del_ins_far' _ _ h,
    getD_ins_lt _ _ (show p < p + 2 + k by omega) h,
    getD_ins_lt _ _ (show p + 1 < p + 2 + k by omega) h, Fin.sum_univ_two]
  ring

/-! ## Soundness -/

@[simp] theorem sig_dom_cup : sig.dom .cup = [] := rfl
@[simp] theorem sig_cod_cup : sig.cod .cup = [(), ()] := rfl
@[simp] theorem sig_dom_cap : sig.dom .cap = [(), ()] := rfl
@[simp] theorem sig_cod_cap : sig.cod .cap = [] := rfl

variable (R)

/-- The interpretation respects the relations of `pres R (-2)` (at every position) and every
instance of the interchange law. -/
theorem respects : (pres R (-2)).Respects (interp R).functor where
  rel r u v hw := by
    cases r <;>
    simp only [pres, relation, LinDiagram.whisker_sub, LinDiagram.whisker_smul,
      LinDiagram.whisker_of, Functor.map_sub, Functor.map_smul, freeLift_map_of, sub_eq_zero] <;>
    apply ModuleCat.hom_ext <;>
    refine LinearMap.ext fun f => ?_
    · rw [ModuleCat.hom_smul, LinearMap.smul_apply, ← map_smul]
      funext w
      have hl : w.1.length = u.word.length + v.length :=
        w.2.trans (by simp [Free.of, Obj.whisker, strands, Rel.width])
      rw [map_apply, map_apply, map_smul]
      simp only [Diagram.layers_whisker, Diagram.layers_comp, Diagram.layers_layer, dcup, dcap,
        lay, List.map_cons, List.map_nil, List.cons_append, List.nil_append, evalLayers_cons,
        evalLayers_nil, LinearMap.comp_apply, LinearMap.id_apply, Layer.whisker, op_cup, op_cap,
        List.length_append, List.length_replicate, add_zero]
      erw [Diagram.layers_id]
      rw [List.map_nil, evalLayers_nil, LinearMap.id_apply, loop_op _ (by omega)]
      rfl
    all_goals
      funext w
      have hl : w.1.length = u.word.length + 1 + v.length :=
        w.2.trans (by simp [Free.of, Obj.whisker, strands, Rel.width]; omega)
      rw [map_apply, map_apply]
      simp only [Diagram.layers_whisker, Diagram.layers_comp, Diagram.layers_layer, dcup, dcap,
        lay, List.map_cons, List.map_nil, List.cons_append, List.nil_append, evalLayers_cons,
        evalLayers_nil, LinearMap.comp_apply, LinearMap.id_apply, Layer.whisker, op_cup, op_cap,
        List.length_append, List.length_replicate, add_zero]
      erw [Diagram.layers_id]
      rw [List.map_nil, evalLayers_nil, LinearMap.id_apply]
    · exact zigzagA_op _ (by omega)
    · exact zigzagB_op _ (by omega)
  interchange x hx u v hw := by
    have hs : ((x.sign : ℤ) : R) = 1 := by simp [InterchangeData.sign, sig]
    simp only [InterchangeData.rel, LinDiagram.whisker_sub, LinDiagram.whisker_smul,
      LinDiagram.whisker_of, Functor.map_sub, Functor.map_smul, freeLift_map_of, hs, one_smul,
      sub_eq_zero]
    apply ModuleCat.hom_ext
    refine LinearMap.ext fun f => funext fun w => ?_
    rw [map_apply, map_apply]
    obtain ⟨s, g, mid, h⟩ := x
    have hl := w.2
    simp only [Free.of, InterchangeData.cod, Obj.whisker] at hl
    cases g <;> cases h <;>
    simp only [sig_dom_cup, sig_cod_cup, sig_dom_cap, sig_cod_cap, List.length_append,
      List.length_nil, List.length_cons] at hl <;>
    simp only [InterchangeData.ghDiagram, InterchangeData.hgDiagram, Diagram.layers_mk,
      Diagram.layers_whisker, InterchangeData.gh₁, InterchangeData.gh₂, InterchangeData.hg₁,
      InterchangeData.hg₂, List.map_cons, List.map_nil, evalLayers_cons, evalLayers_nil,
      LinearMap.comp_apply, LinearMap.id_apply, Layer.whisker, sig_dom_cup, sig_cod_cup,
      sig_dom_cap, sig_cod_cap, op_cup, op_cap,
      List.length_append, List.length_nil, List.length_cons, List.nil_append, List.append_nil]
    all_goals rw [show u.word.length + (0 + 1 + 1 + mid.length) = u.word.length + 2 + mid.length by
      omega]
    · exact cup_cup_op _ (by omega)
    · exact cup_cap_op _ (by omega)
    · exact cap_cup_op _ (by omega)
    · exact cap_cap_op _ (by omega)

/-- The representation of the Temperley–Lieb category with loop value `-2` on `(R²)^{⊗n}`. -/
def rep : (pres R (-2)).Presented ⥤ ModuleCat R := (pres R (-2)).lift (respects R)

instance : (rep R).Additive := Presentation.lift_additive _

instance : (rep R).Linear R := Presentation.lift_linear _

@[simp] theorem rep_map_diag {a b : Obj sig} (d : a ⟶ b) :
    (rep R).map ((pres R (-2)).diag d) = (interp R).functor.map d :=
  Presentation.lift_diag _ d

/-! ## Non-vacuity -/

variable {R}

theorem ins_inj {p : ℕ} {a b a' b' : Fin 2} {w : List (Fin 2)} (hp : p ≤ w.length)
    (h : ins p a b w = ins p a' b' w) : a = a' ∧ b = b' := by
  have h₁ := congrArg (fun l => l.getD p 0) h
  have h₂ := congrArg (fun l => l.getD (p + 1) 0) h
  simp only [getD_ins_self _ _ _ hp, getD_ins_succ _ _ _ hp] at h₁ h₂
  exact ⟨h₁, h₂⟩

/-- The value of `e_i = cup_i ∘ cap_i` of `rep R` on the basis vector `…e₀ ⊗ e₁…` (with `e₀`
in position `i`), read off at the same basis vector, is `-1`. -/
theorem rep_e_apply {m i : ℕ} (h : i ≤ m) :
    ((rep R).map (e (R := R) (-2) m i)).hom
        (fun w => if w.1 = ins i 0 1 (List.replicate m 0) then 1 else 0)
        ⟨ins i 0 1 (List.replicate m 0), by
          show _ = (List.replicate (m + 2) ()).length; simp⟩ = -1 := by
  have hz : i ≤ (List.replicate m (0 : Fin 2)).length := by simp [h]
  rw [e_def (-2) h, ← Presentation.diag_comp, rep_map_diag]
  refine (map_apply R _ _ _).trans ?_
  simp only [Diagram.layers_comp, Diagram.layers_layer, dcup, dcap, lay, List.cons_append,
    List.nil_append, evalLayers_cons, evalLayers_nil, LinearMap.comp_apply, LinearMap.id_apply,
    op_cup, op_cap, List.length_replicate, cupOp_apply, capOp_apply, getD_ins_self _ _ _ hz,
    getD_ins_succ _ _ _ hz, del_ins _ _ _ hz]
  have hl : ∀ a b : Fin 2, (ins i a b (List.replicate m 0)).length =
      (strands (m + 2)).word.length := by simp [strands]
  simp only [ext_apply_of_length R _ (hl _ _), Fin.sum_univ_two]
  have h₁ : ins i 1 0 (List.replicate m 0) ≠ ins i 0 1 (List.replicate m 0) := fun e =>
    absurd (ins_inj hz e).1 (by decide)
  simp [h₁, cupCoeff, capCoeff]

/-- Non-vacuity: over a nontrivial ring, the Temperley–Lieb generators `e i` on `m + 2` strands
are non-zero for `i ≤ m` in the presented category with loop value `-2`. -/
theorem e_ne_zero [Nontrivial R] {m i : ℕ} (h : i ≤ m) : e (R := R) (-2) m i ≠ 0 := by
  intro he
  have hv := rep_e_apply (R := R) h
  rw [he, Functor.map_zero] at hv
  exact neg_ne_zero.mpr one_ne_zero hv.symm

end StringDiagrams.TemperleyLieb.Rep

end
