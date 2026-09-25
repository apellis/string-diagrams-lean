import StringDiagrams.Interchange
import StringDiagrams.Generation
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.Module

/-!
# Local super-derivations of presented categories

A *local* (diagrammatically local) differential on a presented linear 2-category is one that
is determined by its values on the generating 2-cells and is compatible with placing diagrams
side by side. This file constructs such differentials from their values on generators and
shows when they descend to the presented category.

## Data

A `LocalDerivation S R` assigns to every generator `g` a value
`δ g : LinDiagram R (S.genDom g) (S.genCod g)` on the minimal object `dom g ⟶ cod g`, which
must be homogeneous of parity `|g| + 1` (`LinDiagram.HasParity`): every diagram in its
support has `oddCount ≡ |g| + 1 (mod 2)`. So the differential is odd.

## The sign convention

Diagrams are read from bottom to top. In an endomorphism algebra (`CategoryTheory.End`) the
product is `f * g = g ≫ f`, that is, `f` is drawn *above* `g`; this is the convention of
Ellis–Qi (arXiv:1504.01712v2, §2.3), where the product `xy` places `x` above `y`. The super
Leibniz rule of Ellis–Qi (2.3),

  `d(xy) = d(x) y + (-1)^{p(x)} x d(y)`,

then says: when the lower factor `y` is differentiated, the sign is the parity of everything
*above* it. Accordingly the derivative of a diagram with layers `L₁, …, Lₘ` (bottom to top)
is

  `d(L₁ ⋯ Lₘ) = ∑ₖ (-1)^{|L_{k+1}| + ⋯ + |Lₘ|} L₁ ⋯ L_{k-1} (δ Lₖ) L_{k+1} ⋯ Lₘ`,

where `δ Lₖ` replaces the generator of the layer `Lₖ` by the whiskered value of `δ`, and the
Koszul sign counts the odd generators *above* the differentiated layer
(`LocalDerivation.derivList`). In composition order this is the Leibniz rule
`d(f ≫ g) = (-1)^{|g|} d(f) ≫ g + f ≫ d(g)` (`LocalDerivation.derivDiag_comp`), and for
linear combinations `d(F ≫ G) = d F ≫ σ G + F ≫ d G`, where `σ` is the parity involution
(`LinDiagram.parityInv`). For endomorphisms this is exactly Ellis–Qi (2.3)
(`Presentation.deriv_mul`). Identity strands are even, so `d` commutes with whiskering
(`LocalDerivation.derivFree_whisker`); together with the Leibniz rule this is the
compatibility with horizontal juxtaposition required of a diagrammatically local differential
(Ellis–Qi §2.3).

## Main definitions and results

* `LocalDerivation.derivFree`: the derivation of the free linear 2-category, with
  `derivFree_comp` (Leibniz rule), `derivFree_whisker`, `derivFree_cast`,
  `parityInv_derivFree` (the derivation is odd).
* `LocalDerivation.Compatible D P`: the defining relations of `P` are homogeneous and are
  sent to zero in the presented category. Homogeneity is needed because the Leibniz rule
  involves the parity involution, which must preserve the ideal.
* `LocalDerivation.derivFree_mem_ideal` (descent): if `D` is compatible with `P` then
  `derivFree` preserves the tensor ideal of `P`. The instances of the super interchange law
  need no hypothesis (`LocalDerivation.lin_derivFree_interchange`); this uses the parity of
  `δ` and the Koszul sign. Monoidal signatures only.
* `Presentation.deriv hP`: the induced linear map on morphisms of `P.Presented`, with
  `deriv_comp` / `deriv_mul` (Leibniz), `deriv_whisk`, `deriv_ofGen` (value on a generator).
* `Presentation.deriv_deriv_eq_zero`: `d ∘ d` is an even derivation, so `d² = 0` as soon as
  `d² = 0` on every generator.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory

universe w v u₀ u₁ u₂

variable {S : Signature.{u₀, u₁, u₂}}

/-! ## Generators as objects and diagrams -/

namespace Signature

variable (S)

/-- The bottom boundary of a generator, as an object starting at the region to its left. -/
def genDom (g : S.Gen) : Obj S := ⟨S.left g, S.dom g⟩

/-- The top boundary of a generator, as an object starting at the region to its left. -/
def genCod (g : S.Gen) : Obj S := ⟨S.left g, S.cod g⟩

end Signature

theorem Layer.Valid.genWhiskerOK {L : Layer S} (hv : L.Valid) :
    (S.genDom L.gen).WhiskerOK ⟨L.start, L.left⟩ L.right := by
  refine ⟨hv.left_ok, hv.left_end, ?_⟩
  show S.ok (S.endR (S.left L.gen) (S.dom L.gen)) L.right
  rw [hv.dom_end]; exact hv.right_ok

namespace Diagram

variable {a b c : Obj S}

theorem oddCountList_append (ls ms : List (Layer S)) :
    oddCountList (ls ++ ms) = oddCountList ls + oddCountList ms := by
  simp [oddCountList, List.filter_append]

@[simp] theorem oddCountList_map_whisker (ls : List (Layer S)) (u : Obj S) (v : List S.Colour) :
    oddCountList (ls.map (·.whisker u v)) = oddCountList ls := by
  simp [oddCountList, List.filter_map, Function.comp_def, Layer.whisker]

theorem oddCountList_singleton (L : Layer S) : oddCountList [L] = (S.odd L.gen).toNat := by
  cases h : S.odd L.gen <;> simp [oddCountList, List.filter_cons, h]

theorem oddCount_comp (f : a ⟶ b) (g : b ⟶ c) : oddCount (f ≫ g) = oddCount f + oddCount g :=
  oddCountList_append _ _

@[simp] theorem oddCount_whisker (f : a ⟶ b) (u : Obj S) (v : List S.Colour)
    (hw : a.WhiskerOK u v) : oddCount (whisker f u v hw) = oddCount f :=
  oddCountList_map_whisker _ _ _

@[simp] theorem oddCount_cast {a' b' : Obj S} (f : a ⟶ b) (ha : a = a') (hb : b = b') :
    oddCount (cast f ha hb) = oddCount f := rfl

end Diagram

/-! ## Parity of linear combinations of diagrams -/

namespace LinDiagram

variable {R : Type w} [CommRing R] {a b c : Obj S}

/-- `F` is homogeneous of parity `p`: every diagram in its support has `p` odd generators
modulo `2`. -/
def HasParity (F : LinDiagram R a b) (p : ℕ) : Prop :=
  ∀ d ∈ Finsupp.support F, Diagram.oddCount d % 2 = p % 2

theorem hasParity_zero (p : ℕ) : HasParity (0 : LinDiagram R a b) p := by
  intro d hd; simp at hd

theorem hasParity_single {d : a ⟶ b} {p : ℕ} (h : Diagram.oddCount d % 2 = p % 2) (r : R) :
    HasParity (Finsupp.single d r : LinDiagram R a b) p := by
  intro e he
  rw [Finset.mem_singleton.mp (Finsupp.support_single_subset he)]; exact h

theorem hasParity_of {d : a ⟶ b} {p : ℕ} (h : Diagram.oddCount d % 2 = p % 2) :
    HasParity (of d : LinDiagram R a b) p :=
  hasParity_single h 1

theorem HasParity.smul {F : LinDiagram R a b} {p : ℕ} (hF : F.HasParity p) (r : R) :
    HasParity (r • F) p :=
  fun d hd => hF d (Finsupp.support_smul hd)

theorem HasParity.add {F G : LinDiagram R a b} {p : ℕ} (hF : F.HasParity p) (hG : G.HasParity p) :
    HasParity (F + G) p := by
  classical
  intro d hd
  rcases Finset.mem_union.mp (Finsupp.support_add hd) with h | h
  · exact hF d h
  · exact hG d h

/-- The parity involution: `σ d = (-1)^{|d|} d` on diagrams. -/
def parityInv : LinDiagram R a b →ₗ[R] LinDiagram R a b :=
  Finsupp.linearCombination R (fun d : a ⟶ b => ((-1 : R) ^ Diagram.oddCount d) • of d)

theorem parityInv_single (d : a ⟶ b) (r : R) :
    parityInv (Finsupp.single d r : LinDiagram R a b) =
      ((-1 : R) ^ Diagram.oddCount d) • (Finsupp.single d r : LinDiagram R a b) := by
  refine (Finsupp.linearCombination_single R (v := fun d : a ⟶ b =>
    ((-1 : R) ^ Diagram.oddCount d) • (of d : LinDiagram R a b)) r d).trans ?_
  rw [smul_comm, Finsupp.smul_single_one]

theorem parityInv_of (d : a ⟶ b) :
    parityInv (of d : LinDiagram R a b) = ((-1 : R) ^ Diagram.oddCount d) • of d :=
  parityInv_single d 1

theorem parityInv_eq_of_hasParity {F : LinDiagram R a b} {p : ℕ} (hF : F.HasParity p) :
    parityInv F = ((-1 : R) ^ p) • F := by
  conv_lhs => rw [← Finsupp.sum_single F]
  conv_rhs => rw [← Finsupp.sum_single F]
  rw [map_finsuppSum, Finsupp.smul_sum]
  refine Finsupp.sum_congr fun d hd => ?_
  rw [parityInv_single, neg_one_pow_eq_pow_mod_two, hF d hd, ← neg_one_pow_eq_pow_mod_two]

theorem single_eq_smul_of (d : a ⟶ b) (r : R) :
    (Finsupp.single d r : LinDiagram R a b) = r • of d :=
  (Finsupp.smul_single_one d r).symm

theorem smul_comp_lin (r : R) (F : LinDiagram R a b) (G : LinDiagram R b c) :
    (r • F) ≫ G = r • (F ≫ G) := Linear.smul_comp _ _ _ _ _ _

theorem comp_smul_lin (F : LinDiagram R a b) (r : R) (G : LinDiagram R b c) :
    F ≫ (r • G) = r • (F ≫ G) := Linear.comp_smul _ _ _ _ _ _

theorem single_comp_single (d : a ⟶ b) (e : b ⟶ c) (r s : R) :
    (Finsupp.single d r ≫ Finsupp.single e s : Free.of R a ⟶ Free.of R c) =
      Finsupp.single (d ≫ e) (r * s) :=
  Free.single_comp_single R (Obj S) d e r s

theorem parityInv_comp (F : LinDiagram R a b) (G : LinDiagram R b c) :
    parityInv (F ≫ G) = parityInv F ≫ parityInv G := by
  induction F using Finsupp.induction_linear with
  | zero => simp
  | add F₁ F₂ h₁ h₂ => rw [Preadditive.add_comp, map_add, h₁, h₂, map_add, Preadditive.add_comp]
  | single d r =>
    induction G using Finsupp.induction_linear with
    | zero => simp
    | add G₁ G₂ h₁ h₂ =>
      rw [Preadditive.comp_add, map_add, h₁, h₂, map_add, Preadditive.comp_add]
    | single e s =>
      rw [single_comp_single, parityInv_single, parityInv_single, parityInv_single,
        Linear.smul_comp, Linear.comp_smul, single_comp_single, smul_smul, Diagram.oddCount_comp,
        pow_add, mul_comm ((-1 : R) ^ _)]

theorem parityInv_parityInv (F : LinDiagram R a b) : parityInv (parityInv F) = F := by
  induction F using Finsupp.induction_linear with
  | zero => simp
  | add F₁ F₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
  | single d r =>
    rw [parityInv_single, map_smul, parityInv_single, smul_smul, ← pow_add, ← two_mul, pow_mul,
      neg_one_sq, one_pow, one_smul]

theorem parityInv_whisker (F : LinDiagram R a b) (u : Obj S) (v : List S.Colour)
    (hw : a.WhiskerOK u v) : parityInv (whisker F u v hw) = whisker (parityInv F) u v hw := by
  induction F using Finsupp.induction_linear with
  | zero => simp [whisker]
  | add F₁ F₂ h₁ h₂ => rw [whisker_add, map_add, h₁, h₂, map_add, whisker_add]
  | single d r =>
    rw [whisker_single, parityInv_single, parityInv_single, whisker_smul, whisker_single,
      Diagram.oddCount_whisker]

theorem parityInv_cast {a' b' : Obj S} (F : LinDiagram R a b) (ha : a = a') (hb : b = b') :
    parityInv (cast F ha hb) = cast (parityInv F) ha hb := by
  subst ha hb; simp

/-! ### Underlying layer lists

Forgetting the typing, a linear combination of diagrams is a linear combination of lists of
layers (`toList`), injectively. This is used to compare linear combinations of diagrams whose
types agree only up to equality of objects. -/

/-- The underlying linear combination of layer lists. -/
def toList : LinDiagram R a b →ₗ[R] (List (Layer S) →₀ R) :=
  Finsupp.lmapDomain R R (Diagram.layers (a := a) (b := b))

theorem toList_apply (F : LinDiagram R a b) :
    toList F = Finsupp.mapDomain Diagram.layers F := rfl

theorem toList_single (d : a ⟶ b) (r : R) :
    toList (Finsupp.single d r : LinDiagram R a b) = Finsupp.single (Diagram.layers d) r :=
  Finsupp.mapDomain_single

theorem toList_of (d : a ⟶ b) :
    toList (of d : LinDiagram R a b) = Finsupp.single (Diagram.layers d) 1 :=
  toList_single d 1

theorem toList_injective : Function.Injective (toList : LinDiagram R a b → _) :=
  Finsupp.mapDomain_injective fun _ _ h => Diagram.ext h

theorem toList_mapDomain {a' b' : Obj S} (φ : (a ⟶ b) → (a' ⟶ b'))
    (ψ : List (Layer S) → List (Layer S)) (h : ∀ d, Diagram.layers (φ d) = ψ (Diagram.layers d))
    (F : LinDiagram R a b) :
    toList (Finsupp.mapDomain φ F : LinDiagram R a' b') = Finsupp.mapDomain ψ (toList F) := by
  rw [toList_apply, toList_apply, ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  congr 1; funext d; exact h d

theorem toList_cast {a' b' : Obj S} (F : LinDiagram R a b) (ha : a = a') (hb : b = b') :
    toList (cast F ha hb) = toList F := by
  rw [cast, toList_mapDomain (fun d => Diagram.cast d ha hb) id (fun _ => rfl),
    Finsupp.mapDomain_id]

theorem toList_whisker (F : LinDiagram R a b) (u : Obj S) (v : List S.Colour)
    (hw : a.WhiskerOK u v) :
    toList (whisker F u v hw) = Finsupp.mapDomain (List.map (·.whisker u v)) (toList F) :=
  toList_mapDomain _ _ (fun _ => rfl) F

theorem toList_comp_of (F : LinDiagram R a b) (g : b ⟶ c) :
    toList (F ≫ of g) = Finsupp.mapDomain (· ++ Diagram.layers g) (toList F) := by
  induction F using Finsupp.induction_linear with
  | zero => simp
  | add F₁ F₂ h₁ h₂ => rw [Preadditive.add_comp, map_add, h₁, h₂, map_add, Finsupp.mapDomain_add]
  | single d r =>
    rw [single_comp_single, mul_one, toList_single, toList_single, Finsupp.mapDomain_single,
      Diagram.layers_comp]

theorem toList_of_comp (f : a ⟶ b) (G : LinDiagram R b c) :
    toList (of f ≫ G) = Finsupp.mapDomain (Diagram.layers f ++ ·) (toList G) := by
  induction G using Finsupp.induction_linear with
  | zero => simp
  | add G₁ G₂ h₁ h₂ => rw [Preadditive.comp_add, map_add, h₁, h₂, map_add, Finsupp.mapDomain_add]
  | single d r =>
    rw [single_comp_single, one_mul, toList_single, toList_single, Finsupp.mapDomain_single,
      Diagram.layers_comp]

/-- The parity involution on linear combinations of layer lists. -/
def parityList : (List (Layer S) →₀ R) →ₗ[R] (List (Layer S) →₀ R) :=
  Finsupp.linearCombination R
    (fun l => ((-1 : R) ^ Diagram.oddCountList l) • Finsupp.single l (1 : R))

theorem parityList_single (l : List (Layer S)) (r : R) :
    parityList (Finsupp.single l r) = ((-1 : R) ^ Diagram.oddCountList l) • Finsupp.single l r := by
  refine (Finsupp.linearCombination_single R (v := fun l : List (Layer S) =>
    ((-1 : R) ^ Diagram.oddCountList l) • Finsupp.single l (1 : R)) r l).trans ?_
  rw [smul_comm, Finsupp.smul_single_one]

theorem toList_parityInv (F : LinDiagram R a b) : toList (parityInv F) = parityList (toList F) := by
  induction F using Finsupp.induction_linear with
  | zero => simp
  | add F₁ F₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, map_add]
  | single d r =>
    rw [parityInv_single, map_smul, toList_single, parityList_single]; rfl

theorem parityList_mapDomain (φ : List (Layer S) → List (Layer S)) (k : ℕ)
    (hφ : ∀ l, Diagram.oddCountList (φ l) = Diagram.oddCountList l + k)
    (X : List (Layer S) →₀ R) :
    parityList (Finsupp.mapDomain φ X) = ((-1 : R) ^ k) • Finsupp.mapDomain φ (parityList X) := by
  induction X using Finsupp.induction_linear with
  | zero => simp
  | add X₁ X₂ h₁ h₂ => rw [Finsupp.mapDomain_add, map_add, h₁, h₂, map_add,
      Finsupp.mapDomain_add, smul_add]
  | single l r =>
    rw [Finsupp.mapDomain_single, parityList_single, parityList_single, Finsupp.mapDomain_smul,
      Finsupp.mapDomain_single, smul_smul, hφ, pow_add, mul_comm]

end LinDiagram

/-! ## Local derivations -/

/-- The values of a local odd derivation on the generators: for each generator `g`, a linear
combination of diagrams `δ g : dom g ⟶ cod g`, homogeneous of parity `|g| + 1`. -/
structure LocalDerivation (S : Signature.{u₀, u₁, u₂}) (R : Type w) [CommRing R] where
  /-- The value on a generator. -/
  δ : (g : S.Gen) → LinDiagram R (S.genDom g) (S.genCod g)
  /-- The value on `g` has parity `|g| + 1`: the derivation is odd. -/
  hasParity : ∀ g, (δ g).HasParity ((S.odd g).toNat + 1)

namespace LocalDerivation

open LinDiagram Diagram

variable {R : Type w} [CommRing R] (D : LocalDerivation S R) {a b c : Obj S}

/-- The derivation on linear combinations of layer lists (the typing is forgotten): the signed
sum over layers `L` of the list of replacing `L` by the whiskered value of `δ` on its
generator, with the Koszul sign of the odd generators above `L`. -/
def derivL : List (Layer S) → (List (Layer S) →₀ R)
  | [] => 0
  | L :: ls => ((-1 : R) ^ oddCountList ls) •
      Finsupp.mapDomain (fun l => l.map (·.whisker ⟨L.start, L.left⟩ L.right) ++ ls)
        (toList (D.δ L.gen)) +
      Finsupp.mapDomain (L :: ·) (derivL ls)

@[simp] theorem derivL_nil : D.derivL [] = 0 := rfl

theorem derivL_cons (L : Layer S) (ls : List (Layer S)) :
    D.derivL (L :: ls) = ((-1 : R) ^ oddCountList ls) •
      Finsupp.mapDomain (fun l => l.map (·.whisker ⟨L.start, L.left⟩ L.right) ++ ls)
        (toList (D.δ L.gen)) +
      Finsupp.mapDomain (L :: ·) (D.derivL ls) := rfl

/-- Replacing the generator of a well-formed layer by the whiskered value of `δ`. -/
def layerDeriv (L : Layer S) (hv : L.Valid) : LinDiagram R L.dom L.cod :=
  LinDiagram.whisker (D.δ L.gen) ⟨L.start, L.left⟩ L.right hv.genWhiskerOK

theorem toList_layerDeriv (L : Layer S) (hv : L.Valid) :
    toList (D.layerDeriv L hv) =
      Finsupp.mapDomain (List.map (·.whisker ⟨L.start, L.left⟩ L.right)) (toList (D.δ L.gen)) :=
  toList_whisker _ _ _ _

/-- The derivative of a diagram given by a chain of layers: the signed sum over layers `L`
of replacing `L` by `layerDeriv L`, with sign `(-1)^{#odd generators above L}`. -/
def derivList : (a : Obj S) → (ls : List (Layer S)) → (b : Obj S) → Chain a ls b →
    LinDiagram R a b
  | _, [], _, _ => 0
  | _, L :: ls, b, h => LinDiagram.cast
      (((-1 : R) ^ oddCountList ls) • (D.layerDeriv L h.1 ≫ of (Diagram.mk ls h.2.2)) +
        of (Diagram.ofLayer L h.1) ≫ derivList L.cod ls b h.2.2) h.2.1 rfl

theorem toList_derivList (a : Obj S) (ls : List (Layer S)) (b : Obj S) (h : Chain a ls b) :
    toList (D.derivList a ls b h) = D.derivL ls := by
  induction ls generalizing a with
  | nil => simp [derivList]
  | cons L ls ih =>
    rw [derivList, toList_cast, map_add, map_smul, toList_comp_of, toList_of_comp, ih,
      toList_layerDeriv, ← Finsupp.mapDomain_comp, derivL_cons]
    rfl

/-- The derivative of a diagram. -/
def derivDiag (d : a ⟶ b) : LinDiagram R a b :=
  D.derivList a (Diagram.layers d) b (Diagram.chain d)

theorem toList_derivDiag (d : a ⟶ b) : toList (D.derivDiag d) = D.derivL (Diagram.layers d) :=
  D.toList_derivList _ _ _ _

/-- The derivation of the free linear 2-category determined by `δ`. -/
def derivFree : LinDiagram R a b →ₗ[R] LinDiagram R a b :=
  Finsupp.linearCombination R D.derivDiag

theorem derivFree_single (d : a ⟶ b) (r : R) :
    D.derivFree (Finsupp.single d r : LinDiagram R a b) = r • D.derivDiag d :=
  Finsupp.linearCombination_single R r d

@[simp] theorem derivFree_of (d : a ⟶ b) : D.derivFree (of d : LinDiagram R a b) = D.derivDiag d := by
  rw [derivFree_single, one_smul]

/-- The derivative of a single layer is the whiskered value of `δ` on its generator. -/
theorem derivDiag_layer (L : Layer S) (hv : L.Valid) (ha : L.dom = a) (hb : L.cod = b) :
    D.derivDiag (Diagram.layer L hv ha hb) = LinDiagram.cast (D.layerDeriv L hv) ha hb := by
  apply toList_injective
  rw [toList_derivDiag, toList_cast, toList_layerDeriv, layers_layer, derivL_cons, derivL_nil,
    Finsupp.mapDomain_zero, add_zero, oddCountList_nil, pow_zero, one_smul]
  simp only [List.append_nil]

/-- The derivative of a single layer whose generator has a single diagram as value. -/
theorem derivDiag_layer_of (L : Layer S) (hv : L.Valid) (ha : L.dom = a) (hb : L.cod = b)
    (d : S.genDom L.gen ⟶ S.genCod L.gen) (hd : D.δ L.gen = of d) :
    D.derivDiag (Diagram.layer L hv ha hb) =
      of (Diagram.cast (Diagram.whisker d ⟨L.start, L.left⟩ L.right hv.genWhiskerOK) ha hb) := by
  rw [derivDiag_layer, layerDeriv, hd, whisker_of, cast_of]

theorem derivDiag_id (a : Obj S) : D.derivDiag (𝟙 a) = (0 : LinDiagram R a a) := rfl

theorem derivDiag_eqToHom (h : a = b) : D.derivDiag (eqToHom h) = (0 : LinDiagram R a b) := by
  subst h; rfl

/-! ### The Leibniz rule -/

theorem derivL_append (ls ms : List (Layer S)) :
    D.derivL (ls ++ ms) = ((-1 : R) ^ oddCountList ms) •
      Finsupp.mapDomain (· ++ ms) (D.derivL ls) + Finsupp.mapDomain (ls ++ ·) (D.derivL ms) := by
  induction ls with
  | nil =>
    simp only [derivL_nil, Finsupp.mapDomain_zero, smul_zero, zero_add, List.nil_append]
    exact Finsupp.mapDomain_id.symm
  | cons L ls ih =>
    rw [List.cons_append, derivL_cons, derivL_cons, ih, oddCountList_append]
    simp only [Finsupp.mapDomain_add, Finsupp.mapDomain_smul, ← Finsupp.mapDomain_comp,
      Function.comp_def, List.append_assoc, List.cons_append, smul_add, smul_smul, pow_add]
    rw [mul_comm ((-1 : R) ^ oddCountList ms)]
    abel

/-- The Leibniz rule for diagrams: `d(f ≫ g) = (-1)^{|g|} d f ≫ g + f ≫ d g`. -/
theorem derivDiag_comp (f : a ⟶ b) (g : b ⟶ c) :
    D.derivDiag (f ≫ g) =
      ((-1 : R) ^ oddCount g) • (D.derivDiag f ≫ of g) + of f ≫ D.derivDiag g := by
  apply toList_injective
  rw [toList_derivDiag, layers_comp, derivL_append, map_add, map_smul, toList_comp_of,
    toList_of_comp, toList_derivDiag, toList_derivDiag]
  rfl

theorem derivFree_single_comp_single (d : a ⟶ b) (e : b ⟶ c) (r s : R) :
    D.derivFree ((Finsupp.single d r : LinDiagram R a b) ≫ (Finsupp.single e s : LinDiagram R b c)) =
      D.derivFree (Finsupp.single d r : LinDiagram R a b) ≫
          parityInv (Finsupp.single e s : LinDiagram R b c) +
        (Finsupp.single d r : LinDiagram R a b) ≫ D.derivFree (Finsupp.single e s) := by
  rw [single_comp_single, derivFree_single, derivFree_single, derivFree_single,
    parityInv_single, derivDiag_comp, single_eq_smul_of d r, single_eq_smul_of e s]
  simp only [LinDiagram.smul_comp_lin, LinDiagram.comp_smul_lin, smul_add, smul_smul]
  rw [LinDiagram.comp_smul_lin, LinDiagram.smul_comp_lin, smul_smul, smul_smul]
  module

/-- The Leibniz rule for the free linear 2-category: `d(F ≫ G) = d F ≫ σ G + F ≫ d G`. -/
theorem derivFree_comp (F : LinDiagram R a b) (G : LinDiagram R b c) :
    D.derivFree (F ≫ G) = D.derivFree F ≫ parityInv G + F ≫ D.derivFree G := by
  induction F using Finsupp.induction_linear with
  | zero => simp
  | add F₁ F₂ h₁ h₂ =>
    rw [Preadditive.add_comp, map_add, h₁, h₂, map_add, Preadditive.add_comp,
      Preadditive.add_comp]
    abel
  | single d r =>
    induction G using Finsupp.induction_linear with
    | zero => simp
    | add G₁ G₂ h₁ h₂ =>
      rw [Preadditive.comp_add, map_add, h₁, h₂, map_add, map_add, Preadditive.comp_add,
        Preadditive.comp_add]
      abel
    | single e s => exact D.derivFree_single_comp_single d e r s

/-! ### Whiskering and retyping -/

theorem derivL_map_whisker (ls : List (Layer S)) (u : Obj S) (v : List S.Colour) :
    D.derivL (ls.map (·.whisker u v)) =
      Finsupp.mapDomain (List.map (·.whisker u v)) (D.derivL ls) := by
  induction ls with
  | nil => simp
  | cons L ls ih =>
    rw [List.map_cons, derivL_cons, derivL_cons, ih, oddCountList_map_whisker]
    simp only [Finsupp.mapDomain_add, Finsupp.mapDomain_smul, ← Finsupp.mapDomain_comp,
      Function.comp_def, List.map_append, List.map_map, List.map_cons]
    congr 3
    funext l
    congr 1
    apply List.map_congr_left
    intro X _
    simp [Layer.whisker, Obj.tensor, List.append_assoc]

theorem derivDiag_whisker (d : a ⟶ b) (u : Obj S) (v : List S.Colour) (hw : a.WhiskerOK u v) :
    D.derivDiag (Diagram.whisker d u v hw) = LinDiagram.whisker (D.derivDiag d) u v hw := by
  apply toList_injective
  rw [toList_derivDiag, toList_whisker, toList_derivDiag, layers_whisker, derivL_map_whisker]

/-- The derivation commutes with whiskering: identity strands are even. -/
theorem derivFree_whisker (F : LinDiagram R a b) (u : Obj S) (v : List S.Colour)
    (hw : a.WhiskerOK u v) :
    D.derivFree (LinDiagram.whisker F u v hw) = LinDiagram.whisker (D.derivFree F) u v hw := by
  induction F using Finsupp.induction_linear with
  | zero => simp [LinDiagram.whisker]
  | add F₁ F₂ h₁ h₂ => rw [whisker_add, map_add, h₁, h₂, map_add, whisker_add]
  | single d r =>
    rw [whisker_single, derivFree_single, derivFree_single, whisker_smul, derivDiag_whisker]

theorem derivFree_whisk (F : LinDiagram R a b) (u : Obj S) (v : List S.Colour) :
    D.derivFree (LinDiagram.whisk F u v) = LinDiagram.whisk (D.derivFree F) u v := by
  by_cases h : a.WhiskerOK u v
  · rw [whisk_of_ok _ h, whisk_of_ok _ h, derivFree_whisker]
  · rw [whisk_of_not_ok _ h, whisk_of_not_ok _ h, map_zero]

theorem derivFree_cast {a' b' : Obj S} (F : LinDiagram R a b) (ha : a = a') (hb : b = b') :
    D.derivFree (LinDiagram.cast F ha hb) = LinDiagram.cast (D.derivFree F) ha hb := by
  subst ha hb; simp

/-! ### The derivation is odd -/

theorem parityList_derivL (ls : List (Layer S)) :
    parityList (D.derivL ls) = -(((-1 : R) ^ oddCountList ls) • D.derivL ls) := by
  induction ls with
  | nil => simp
  | cons L ls ih =>
    have hδ : parityList (toList (D.δ L.gen)) =
        ((-1 : R) ^ ((S.odd L.gen).toNat + 1)) • toList (D.δ L.gen) := by
      rw [← toList_parityInv, parityInv_eq_of_hasParity (D.hasParity L.gen), map_smul]
    rw [derivL_cons, map_add, map_smul,
      parityList_mapDomain _ (oddCountList ls) (fun l => by
        rw [oddCountList_append, oddCountList_map_whisker]),
      parityList_mapDomain _ (S.odd L.gen).toNat (fun l => by
        rw [oddCountList_cons, oddCountList_singleton, add_comm]),
      hδ, ih, oddCountList_cons, oddCountList_singleton]
    simp only [Finsupp.mapDomain_smul, map_neg, (Finsupp.lmapDomain R R _).map_neg]
    have e : ∀ X : List (Layer S) →₀ R, ∀ f : List (Layer S) → List (Layer S),
        Finsupp.mapDomain f (-X) = -Finsupp.mapDomain f X :=
      fun X f => (Finsupp.lmapDomain R R f).map_neg X
    rw [e]
    simp only [smul_add, smul_neg, smul_smul, pow_add, pow_one, Finsupp.mapDomain_smul]
    module

theorem parityInv_derivDiag (d : a ⟶ b) :
    parityInv (D.derivDiag d) = -(((-1 : R) ^ oddCount d) • D.derivDiag d) := by
  apply toList_injective
  rw [toList_parityInv, toList_derivDiag, parityList_derivL, map_neg, map_smul, toList_derivDiag]
  rfl

/-- The derivation is odd: `σ ∘ d = - d ∘ σ`. -/
theorem parityInv_derivFree (F : LinDiagram R a b) :
    parityInv (D.derivFree F) = -D.derivFree (parityInv F) := by
  induction F using Finsupp.induction_linear with
  | zero => simp
  | add F₁ F₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, map_add, neg_add]
  | single d r =>
    rw [derivFree_single, map_smul, parityInv_derivDiag, parityInv_single, map_smul,
      derivFree_single, smul_neg, smul_smul, smul_smul, mul_comm]

/-- The square of the derivation is an even derivation. -/
theorem derivFree_derivFree_comp (F : LinDiagram R a b) (G : LinDiagram R b c) :
    D.derivFree (D.derivFree (F ≫ G)) =
      D.derivFree (D.derivFree F) ≫ G + F ≫ D.derivFree (D.derivFree G) := by
  rw [derivFree_comp, map_add, derivFree_comp, derivFree_comp, parityInv_parityInv,
    parityInv_derivFree, Preadditive.comp_neg]
  abel

end LocalDerivation

/-! ## Generators as diagrams (monoidal signatures) -/

namespace Signature

variable (S)

/-- The layer consisting of a single generator. -/
def genLayer (g : S.Gen) : Layer S := ⟨S.left g, [], g, []⟩

end Signature

theorem Layer.whisker_nil_nil [Subsingleton S.Region] (L : Layer S) (r : S.Region) :
    L.whisker ⟨r, []⟩ [] = L :=
  Layer.ext (Subsingleton.elim _ _) rfl rfl (List.append_nil _)

namespace Diagram

variable [Subsingleton S.Region]

/-- A generator as a diagram `dom g ⟶ cod g` (monoidal signatures). -/
def ofGen (g : S.Gen) : S.genDom g ⟶ S.genCod g :=
  Diagram.layer (S.genLayer g) (Layer.valid_of_subsingleton _)
    (by simp [Signature.genLayer, Layer.dom, Signature.genDom])
    (by simp [Signature.genLayer, Layer.cod, Signature.genCod])

@[simp] theorem layers_ofGen (g : S.Gen) : layers (ofGen g) = [S.genLayer g] := rfl

@[simp] theorem oddCount_ofGen (g : S.Gen) : oddCount (ofGen g) = (S.odd g).toNat :=
  oddCountList_singleton _

@[simp] theorem oddCount_whiskerL {b b' : Obj S} (a : Obj S) (g : b ⟶ b') :
    oddCount (whiskerL a g) = oddCount g :=
  oddCountList_map_wl _ _

@[simp] theorem oddCount_whiskerR {a a' : Obj S} (f : a ⟶ a') (b : Obj S) :
    oddCount (whiskerR f b) = oddCount f :=
  oddCountList_map_wr _ _

theorem ofLayer_eq_whisker_ofGen (L : Layer S) (hv : L.Valid) :
    ofLayer L hv = whisker (ofGen L.gen) ⟨L.start, L.left⟩ L.right hv.genWhiskerOK := by
  ext; simp [Signature.genLayer, Layer.whisker]

end Diagram

/-! ## The interchange law and the derivation -/

namespace InterchangeData

open Diagram

variable [Subsingleton S.Region] (x : InterchangeData S)

/-- The strands between the two generators. -/
def midObj : Obj S := ⟨x.start, x.mid⟩

/-- The object `mid ⊗ dom h`. -/
def rightDom : Obj S := x.midObj.tensor (S.genDom x.h)

/-- The object `mid ⊗ cod h`. -/
def rightCod : Obj S := x.midObj.tensor (S.genCod x.h)

/-- The right generator with the middle strands on its left. -/
def rightGen : x.rightDom ⟶ x.rightCod := whiskerL x.midObj (ofGen x.h)

theorem tensor_dom : (S.genDom x.g).tensor x.rightDom = x.dom :=
  Obj.ext (Subsingleton.elim _ _)
    (by simp [Obj.tensor, rightDom, midObj, Signature.genDom, InterchangeData.dom])

theorem tensor_cod : (S.genCod x.g).tensor x.rightCod = x.cod :=
  Obj.ext (Subsingleton.elim _ _)
    (by simp [Obj.tensor, rightCod, midObj, Signature.genCod, InterchangeData.cod])

/-- A diagram `f : dom g ⟶ cod g` on the left, below the right generator `h`. -/
def leftBelow (f : S.genDom x.g ⟶ S.genCod x.g) : x.dom ⟶ x.cod :=
  cast (whiskerR f x.rightDom ≫ whiskerL (S.genCod x.g) x.rightGen) x.tensor_dom x.tensor_cod

/-- A diagram `f : dom g ⟶ cod g` on the left, above the right generator `h`. -/
def leftAbove (f : S.genDom x.g ⟶ S.genCod x.g) : x.dom ⟶ x.cod :=
  cast (whiskerL (S.genDom x.g) x.rightGen ≫ whiskerR f x.rightCod) x.tensor_dom x.tensor_cod

/-- A diagram `e : dom h ⟶ cod h` on the right, above the left generator `g`. -/
def rightAbove (e : S.genDom x.h ⟶ S.genCod x.h) : x.dom ⟶ x.cod :=
  cast (whiskerR (ofGen x.g) x.rightDom ≫ whiskerL (S.genCod x.g) (whiskerL x.midObj e))
    x.tensor_dom x.tensor_cod

/-- A diagram `e : dom h ⟶ cod h` on the right, below the left generator `g`. -/
def rightBelow (e : S.genDom x.h ⟶ S.genCod x.h) : x.dom ⟶ x.cod :=
  cast (whiskerL (S.genDom x.g) (whiskerL x.midObj e) ≫ whiskerR (ofGen x.g) x.rightCod)
    x.tensor_dom x.tensor_cod

theorem layers_leftBelow (f : S.genDom x.g ⟶ S.genCod x.g) :
    layers (x.leftBelow f) =
      (layers f).map (·.whisker ⟨x.start, []⟩ (x.mid ++ S.dom x.h)) ++ [x.gh₂] := by
  simp only [leftBelow, rightGen, layers_cast, layers_comp, layers_whiskerR, layers_whiskerL,
    layers_ofGen, List.map_cons, List.map_nil]
  congr 1
  · exact List.map_congr_left fun L _ => Layer.ext (Subsingleton.elim _ _) rfl rfl rfl
  · congr 1
    exact Layer.ext (Subsingleton.elim _ _)
      (by simp [Layer.wl, Signature.genLayer, Signature.genCod, midObj, gh₂]) rfl rfl

theorem layers_leftAbove (f : S.genDom x.g ⟶ S.genCod x.g) :
    layers (x.leftAbove f) =
      x.hg₁ :: (layers f).map (·.whisker ⟨x.start, []⟩ (x.mid ++ S.cod x.h)) := by
  simp only [leftAbove, rightGen, layers_cast, layers_comp, layers_whiskerR, layers_whiskerL,
    layers_ofGen, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  congr 1
  · exact Layer.ext (Subsingleton.elim _ _)
      (by simp [Layer.wl, Signature.genLayer, Signature.genDom, midObj, hg₁]) rfl rfl
  · exact List.map_congr_left fun L _ => Layer.ext (Subsingleton.elim _ _) rfl rfl rfl

theorem layers_rightAbove (e : S.genDom x.h ⟶ S.genCod x.h) :
    layers (x.rightAbove e) =
      x.gh₁ :: (layers e).map (·.whisker ⟨x.start, S.cod x.g ++ x.mid⟩ []) := by
  simp only [rightAbove, layers_cast, layers_comp, layers_whiskerR, layers_whiskerL,
    layers_ofGen, List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.map_map]
  congr 1
  · exact Layer.ext (Subsingleton.elim _ _) rfl rfl
      (by simp [Layer.wr, Signature.genLayer, rightDom, midObj, Obj.tensor, Signature.genDom,
        gh₁])
  · exact List.map_congr_left fun L _ => Layer.ext (Subsingleton.elim _ _)
      (by simp [Layer.wl, Layer.whisker, Signature.genCod, midObj]) rfl (by simp [Layer.wl, Layer.whisker])

theorem layers_rightBelow (e : S.genDom x.h ⟶ S.genCod x.h) :
    layers (x.rightBelow e) =
      (layers e).map (·.whisker ⟨x.start, S.dom x.g ++ x.mid⟩ []) ++ [x.hg₂] := by
  simp only [rightBelow, layers_cast, layers_comp, layers_whiskerR, layers_whiskerL,
    layers_ofGen, List.map_cons, List.map_nil, List.map_map]
  congr 1
  · exact List.map_congr_left fun L _ => Layer.ext (Subsingleton.elim _ _)
      (by simp [Layer.wl, Layer.whisker, Signature.genDom, midObj]) rfl (by simp [Layer.wl, Layer.whisker])
  · congr 1
    exact Layer.ext (Subsingleton.elim _ _) rfl rfl
      (by simp [Layer.wr, Signature.genLayer, rightCod, midObj, Obj.tensor, Signature.genCod,
        hg₂])

omit [Subsingleton S.Region] in
theorem oddCount_gh_eq_hg (hx : x.Valid) : oddCount (ghDiagram hx) = oddCount (hgDiagram hx) := by
  show oddCountList [x.gh₁, x.gh₂] = oddCountList [x.hg₁, x.hg₂]
  rw [oddCountList_cons, oddCountList_cons x.hg₁, oddCountList_singleton, oddCountList_singleton,
    oddCountList_singleton, oddCountList_singleton]
  exact add_comm _ _

omit [Subsingleton S.Region] in
theorem sign_eq (R : Type w) [CommRing R] :
    ((x.sign : ℤ) : R) = (-1 : R) ^ ((S.odd x.g).toNat * (S.odd x.h).toNat) := by
  unfold sign
  cases S.odd x.g <;> cases S.odd x.h <;> simp

end InterchangeData

namespace LocalDerivation

open LinDiagram Diagram

variable {R : Type w} [CommRing R] (D : LocalDerivation S R)

section Monoidal

variable [Subsingleton S.Region]

theorem derivDiag_ofGen (g : S.Gen) : D.derivDiag (ofGen g) = D.δ g := by
  apply toList_injective
  rw [toList_derivDiag, layers_ofGen, derivL_cons, derivL_nil, Finsupp.mapDomain_zero, add_zero,
    oddCountList_nil, pow_zero, one_smul]
  have e : (fun l : List (Layer S) =>
      l.map (·.whisker ⟨(S.genLayer g).start, (S.genLayer g).left⟩ (S.genLayer g).right) ++
        []) = id := by
    funext l; simp [Layer.whisker_nil_nil, Signature.genLayer]
  rw [e, Finsupp.mapDomain_id]
  rfl

theorem derivDiag_gh (x : InterchangeData S) (hx : x.Valid) :
    D.derivDiag (InterchangeData.ghDiagram hx) =
      ((-1 : R) ^ (S.odd x.h).toNat) • Finsupp.mapDomain x.leftBelow (D.δ x.g) +
        Finsupp.mapDomain x.rightAbove (D.δ x.h) := by
  apply toList_injective
  rw [map_add, map_smul, toList_mapDomain _ (fun l => l.map (·.whisker ⟨x.start, []⟩ (x.mid ++ S.dom x.h)) ++ [x.gh₂])
      x.layers_leftBelow,
    toList_mapDomain _ (fun l => x.gh₁ :: l.map (·.whisker ⟨x.start, S.cod x.g ++ x.mid⟩ []))
      x.layers_rightAbove, toList_derivDiag]
  show D.derivL [x.gh₁, x.gh₂] = _
  rw [derivL_cons, derivL_cons, derivL_nil, Finsupp.mapDomain_zero, add_zero, oddCountList_nil,
    pow_zero, one_smul, oddCountList_singleton, ← Finsupp.mapDomain_comp]
  simp only [Function.comp_def, List.append_nil]
  rfl

theorem derivDiag_hg (x : InterchangeData S) (hx : x.Valid) :
    D.derivDiag (InterchangeData.hgDiagram hx) =
      ((-1 : R) ^ (S.odd x.g).toNat) • Finsupp.mapDomain x.rightBelow (D.δ x.h) +
        Finsupp.mapDomain x.leftAbove (D.δ x.g) := by
  apply toList_injective
  rw [map_add, map_smul, toList_mapDomain _ (fun l => l.map (·.whisker ⟨x.start, S.dom x.g ++ x.mid⟩ []) ++ [x.hg₂])
      x.layers_rightBelow,
    toList_mapDomain _ (fun l => x.hg₁ :: l.map (·.whisker ⟨x.start, []⟩ (x.mid ++ S.cod x.h)))
      x.layers_leftAbove, toList_derivDiag]
  show D.derivL [x.hg₁, x.hg₂] = _
  rw [derivL_cons, derivL_cons, derivL_nil, Finsupp.mapDomain_zero, add_zero, oddCountList_nil,
    pow_zero, one_smul, oddCountList_singleton, ← Finsupp.mapDomain_comp]
  simp only [Function.comp_def, List.append_nil]
  rfl

variable (P : Presentation.{w, v} S R)

/-- The interchange law for arbitrary diagrams, retyped along equalities of objects. -/
theorem diag_cast_interchange {a a' b b' c c' : Obj S} (f : a ⟶ a') (g : b ⟶ b')
    (hc : a.tensor b = c) (hc' : a'.tensor b' = c') :
    P.diag (cast (whiskerR f b ≫ whiskerL a' g) hc hc') =
      ((-1 : R) ^ (oddCount f * oddCount g)) •
        P.diag (cast (whiskerL a g ≫ whiskerR f b') hc hc') := by
  subst hc hc'
  rw [cast_rfl, cast_rfl, P.diag_interchange_diagrams, ← Int.cast_smul_eq_zsmul R]
  push_cast; rfl

omit [Subsingleton S.Region] in
/-- If `φ d = k • ψ d` in the presented category for every diagram `d` in the support of `F`,
then the same holds for `F`. -/
theorem lin_mapDomain_eq_smul {a b c d : Obj S} (φ ψ : (a ⟶ b) → (c ⟶ d))
    (F : LinDiagram R a b) (k : R)
    (h : ∀ e ∈ Finsupp.support F, P.diag (φ e) = k • P.diag (ψ e)) :
    P.lin (Finsupp.mapDomain φ F : LinDiagram R c d) =
      k • P.lin (Finsupp.mapDomain ψ F : LinDiagram R c d) := by
  have hF : ∀ χ : (a ⟶ b) → (c ⟶ d), P.lin (Finsupp.mapDomain χ F : LinDiagram R c d) =
      F.sum fun e r => r • P.diag (χ e) := by
    intro χ
    show (P.linFunctor.mapLinearMap R) (F.sum fun e r => Finsupp.single (χ e) r) = _
    rw [map_finsuppSum]
    exact Finsupp.sum_congr fun e _ => P.lin_single (χ e) _
  rw [hF, hF, Finsupp.smul_sum]
  exact Finsupp.sum_congr fun e he => by rw [h e he, smul_comm]

theorem neg_one_pow_of_mod {m n : ℕ} (h : m % 2 = n % 2) : (-1 : R) ^ m = (-1) ^ n := by
  rw [neg_one_pow_eq_pow_mod_two, h, ← neg_one_pow_eq_pow_mod_two]

/-- The crux of descent: the derivation of an instance of the super interchange law vanishes
in the presented category. This uses that `δ g` has parity `|g| + 1` and the Koszul sign of
the Leibniz rule. -/
theorem lin_derivFree_interchange (x : InterchangeData S) (hx : x.Valid) :
    P.lin (D.derivFree (InterchangeData.rel R hx)) = 0 := by
  have h₁ : P.lin (Finsupp.mapDomain x.leftBelow (D.δ x.g) : LinDiagram R x.dom x.cod) =
      ((-1 : R) ^ (((S.odd x.g).toNat + 1) * (S.odd x.h).toNat)) •
        P.lin (Finsupp.mapDomain x.leftAbove (D.δ x.g) : LinDiagram R x.dom x.cod) := by
    refine lin_mapDomain_eq_smul P _ _ _ _ fun e he => ?_
    refine (diag_cast_interchange P e x.rightGen _ _).trans ?_
    rw [InterchangeData.rightGen, oddCount_whiskerL, oddCount_ofGen, pow_mul, pow_mul,
      neg_one_pow_of_mod (D.hasParity x.g e he)]
    rfl
  have h₂ : P.lin (Finsupp.mapDomain x.rightAbove (D.δ x.h) : LinDiagram R x.dom x.cod) =
      ((-1 : R) ^ ((S.odd x.g).toNat * ((S.odd x.h).toNat + 1))) •
        P.lin (Finsupp.mapDomain x.rightBelow (D.δ x.h) : LinDiagram R x.dom x.cod) := by
    refine lin_mapDomain_eq_smul P _ _ _ _ fun e he => ?_
    refine (diag_cast_interchange P (ofGen x.g) (whiskerL x.midObj e) _ _).trans ?_
    rw [oddCount_whiskerL, oddCount_ofGen, mul_comm, pow_mul,
      neg_one_pow_of_mod (D.hasParity x.h e he), ← pow_mul, mul_comm]
    rfl
  rw [InterchangeData.rel, map_sub, map_smul, derivFree_of, derivFree_of, derivDiag_gh,
    derivDiag_hg, P.lin_sub, P.lin_smul, P.lin_add, P.lin_add, P.lin_smul, P.lin_smul, h₁, h₂,
    InterchangeData.sign_eq]
  cases S.odd x.g <;> cases S.odd x.h <;> simp <;> abel

/-! ### Descent -/

/-- A local derivation is compatible with a presentation if every defining relation is
homogeneous and its derivative vanishes in the presented category. -/
structure Compatible : Prop where
  /-- Each defining relation is homogeneous. -/
  hasParity : ∀ i, ∃ p, (P.rel i).HasParity p
  /-- The derivative of each defining relation vanishes in the presented category. -/
  rel : ∀ i, P.lin (D.derivFree (P.rel i)) = 0

variable {D P}

omit [Subsingleton S.Region] in
theorem Compatible.parityInv_allRel (hP : D.Compatible P) (k : P.AllRel) :
    ∃ p : ℕ, parityInv k.rel = ((-1 : R) ^ p) • k.rel := by
  cases k with
  | user i =>
    obtain ⟨p, hp⟩ := hP.hasParity i
    exact ⟨p, parityInv_eq_of_hasParity hp⟩
  | interchange x hx =>
    refine ⟨oddCount (InterchangeData.ghDiagram hx), ?_⟩
    show parityInv (InterchangeData.rel R hx) = _ • InterchangeData.rel R hx
    rw [InterchangeData.rel, map_sub, map_smul, parityInv_of, parityInv_of,
      x.oddCount_gh_eq_hg hx, smul_sub, smul_comm]

theorem Compatible.derivFree_allRel_mem_ideal (hP : D.Compatible P) (k : P.AllRel) :
    D.derivFree k.rel ∈ P.ideal k.dom k.cod := by
  have h : P.lin (D.derivFree k.rel) = 0 := by
    cases k with
    | user i => exact hP.rel i
    | interchange x hx => exact D.lin_derivFree_interchange P x hx
  rw [← P.lin_zero, P.lin_eq_iff, sub_zero] at h
  exact h

variable (D P) in
/-- Descent: a derivation compatible with a presentation preserves its tensor ideal. -/
theorem derivFree_mem_ideal (hP : D.Compatible P) {a b : Obj S} {F : LinDiagram R a b}
    (hF : F ∈ P.ideal a b) : D.derivFree F ∈ P.ideal a b := by
  induction hF using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, u, v, hw, pre, post⟩ := hy
    have hW : LinDiagram.whisker k.rel u v hw ∈ P.ideal _ _ := P.whisker_rel_mem_ideal k u v hw
    have hdW : D.derivFree (LinDiagram.whisker k.rel u v hw) ∈ P.ideal _ _ := by
      rw [derivFree_whisker, ← LinDiagram.whisk_of_ok _ hw]
      exact P.whisk_mem_ideal (hP.derivFree_allRel_mem_ideal k) u v
    have hσW : parityInv (LinDiagram.whisker k.rel u v hw) ∈ P.ideal _ _ := by
      obtain ⟨p, hp⟩ := hP.parityInv_allRel k
      rw [parityInv_whisker, hp, whisker_smul]
      exact Submodule.smul_mem _ _ hW
    rw [derivFree_comp, derivFree_comp, parityInv_comp]
    exact Submodule.add_mem _ (P.comp_mem_ideal _ (P.mem_ideal_comp hσW _))
      (P.comp_mem_ideal _ (Submodule.add_mem _ (P.mem_ideal_comp hdW _) (P.mem_ideal_comp hW _)))
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul r y _ hy => rw [map_smul]; exact Submodule.smul_mem _ r hy

end Monoidal

end LocalDerivation

/-! ## The derivation of the presented category -/

namespace Presentation

open LinDiagram Diagram LocalDerivation

variable {R : Type w} [CommRing R] [Subsingleton S.Region] (P : Presentation.{w, v} S R)
  {D : LocalDerivation S R} (hP : D.Compatible P) {a b c : Obj S}

/-- The derivation of the presented category induced by a compatible local derivation. -/
def deriv : (P.obj a ⟶ P.obj b) →ₗ[R] (P.obj a ⟶ P.obj b) where
  toFun f := Quot.lift (fun F : LinDiagram R a b => P.lin (D.derivFree F))
    (fun F₁ F₂ h => by
      have h' : P.homRel F₁ F₂ := by
        rwa [CategoryTheory.Quotient.compClosure_eq_self] at h
      rw [lin_eq_iff, ← map_sub]
      exact D.derivFree_mem_ideal P hP h') f
  map_add' f g := by
    obtain ⟨f, rfl⟩ := P.lin_surjective f
    obtain ⟨g, rfl⟩ := P.lin_surjective g
    rw [← lin_add]
    show P.lin (D.derivFree (f + g)) = P.lin (D.derivFree f) + P.lin (D.derivFree g)
    rw [map_add, lin_add]
  map_smul' r f := by
    obtain ⟨f, rfl⟩ := P.lin_surjective f
    rw [← lin_smul]
    show P.lin (D.derivFree (r • f)) = r • P.lin (D.derivFree f)
    rw [map_smul, lin_smul]

@[simp] theorem deriv_lin (F : LinDiagram R a b) : P.deriv hP (P.lin F) = P.lin (D.derivFree F) :=
  rfl

theorem deriv_diag (d : a ⟶ b) : P.deriv hP (P.diag d) = P.lin (D.derivDiag d) := by
  rw [diag, deriv_lin, derivFree_of]

/-- The value of the derivation on a generator. -/
theorem deriv_ofGen (g : S.Gen) : P.deriv hP (P.diag (ofGen g)) = P.lin (D.δ g) := by
  rw [deriv_diag, derivDiag_ofGen]

theorem deriv_layer (L : Layer S) (hv : L.Valid) (ha : L.dom = a) (hb : L.cod = b) :
    P.deriv hP (P.diag (Diagram.layer L hv ha hb)) =
      P.lin (LinDiagram.cast (D.layerDeriv L hv) ha hb) := by
  rw [deriv_diag, derivDiag_layer]

theorem deriv_layer_of (L : Layer S) (hv : L.Valid) (ha : L.dom = a) (hb : L.cod = b)
    (d : S.genDom L.gen ⟶ S.genCod L.gen) (hd : D.δ L.gen = LinDiagram.of d) :
    P.deriv hP (P.diag (Diagram.layer L hv ha hb)) =
      P.diag (Diagram.cast (Diagram.whisker d ⟨L.start, L.left⟩ L.right hv.genWhiskerOK) ha hb) := by
  rw [deriv_diag, derivDiag_layer_of D L hv ha hb d hd, lin_of]

theorem deriv_id (a : Obj S) : P.deriv hP (𝟙 (P.obj a)) = 0 := by
  rw [← diag_id, deriv_diag, derivDiag_id, lin_zero]

/-- The Leibniz rule with an arbitrary lower factor. -/
theorem deriv_comp_lin (F : LinDiagram R a b) (G : LinDiagram R b c) :
    P.deriv hP (P.lin F ≫ P.lin G) =
      P.deriv hP (P.lin F) ≫ P.lin (parityInv G) + P.lin F ≫ P.deriv hP (P.lin G) := by
  rw [← lin_comp, deriv_lin, derivFree_comp, lin_add, lin_comp, lin_comp]; rfl

/-- The Leibniz rule `d(f ≫ g) = (-1)^{|g|} d f ≫ g + f ≫ d g` for `g` homogeneous of parity
`p`. -/
theorem deriv_comp (f : P.obj a ⟶ P.obj b) {G : LinDiagram R b c} {p : ℕ} (hG : G.HasParity p) :
    P.deriv hP (f ≫ P.lin G) =
      ((-1 : R) ^ p) • (P.deriv hP f ≫ P.lin G) + f ≫ P.deriv hP (P.lin G) := by
  obtain ⟨F, rfl⟩ := P.lin_surjective f
  rw [deriv_comp_lin, parityInv_eq_of_hasParity hG, lin_smul, Linear.comp_smul]

theorem deriv_comp_diag (f : P.obj a ⟶ P.obj b) (g : b ⟶ c) :
    P.deriv hP (f ≫ P.diag g) =
      ((-1 : R) ^ oddCount g) • (P.deriv hP f ≫ P.diag g) + f ≫ P.deriv hP (P.diag g) :=
  P.deriv_comp hP f (hasParity_of rfl)

/-- The derivation on the endomorphism algebra `End (P.obj a)`. -/
def derivEnd (a : Obj S) : End (P.obj a) →ₗ[R] End (P.obj a) := P.deriv hP

theorem derivEnd_apply (f : End (P.obj a)) : P.derivEnd hP a f = P.deriv hP f := rfl

/-- The super Leibniz rule of Ellis–Qi (2.3) in an endomorphism algebra, where
`f * g = g ≫ f`: `d(f g) = d(f) g + (-1)^{|f|} f d(g)` for `f` homogeneous of parity `p`. -/
theorem deriv_mul (f g : End (P.obj a)) {F : LinDiagram R a a} {p : ℕ} (hF : F.HasParity p)
    (hf : P.lin F = f) :
    P.derivEnd hP a (f * g) = P.derivEnd hP a f * g + ((-1 : R) ^ p) • (f * P.derivEnd hP a g) := by
  subst hf
  rw [End.mul_def, End.mul_def, End.mul_def, derivEnd_apply, derivEnd_apply, derivEnd_apply,
    P.deriv_comp hP g hF, add_comm]

/-- The derivation commutes with whiskering. -/
theorem deriv_whisk (f : P.obj a ⟶ P.obj b) (u : Obj S) (v : List S.Colour) :
    P.deriv hP (P.whisk f u v) = P.whisk (P.deriv hP f) u v := by
  obtain ⟨F, rfl⟩ := P.lin_surjective f
  rw [whisk_lin, deriv_lin, deriv_lin, whisk_lin, derivFree_whisk]

/-- The square of the derivation is an even derivation. -/
theorem deriv_deriv_comp (f : P.obj a ⟶ P.obj b) (g : P.obj b ⟶ P.obj c) :
    P.deriv hP (P.deriv hP (f ≫ g)) =
      P.deriv hP (P.deriv hP f) ≫ g + f ≫ P.deriv hP (P.deriv hP g) := by
  obtain ⟨F, rfl⟩ := P.lin_surjective f
  obtain ⟨G, rfl⟩ := P.lin_surjective g
  rw [← lin_comp, deriv_lin, deriv_lin, derivFree_derivFree_comp, lin_add, lin_comp, lin_comp]
  rfl

/-- `d² = 0` can be checked on generators. -/
theorem deriv_deriv_eq_zero
    (h : ∀ g : S.Gen, P.deriv hP (P.deriv hP (P.diag (ofGen g))) = 0) {a b : Obj S}
    (f : P.obj a ⟶ P.obj b) : P.deriv hP (P.deriv hP f) = 0 := by
  refine P.hom_induction_layers (p := fun f => P.deriv hP (P.deriv hP f) = 0) ?_ ?_ ?_ ?_ ?_ ?_ f
  · intro a b e
    subst e
    rw [eqToHom_refl, diag_id, deriv_id, map_zero]
  · intro L hv
    have e : P.diag (ofLayer L hv) = P.whisk (P.diag (ofGen L.gen)) ⟨L.start, L.left⟩ L.right := by
      rw [P.whisk_diag _ _ _ hv.genWhiskerOK, ofLayer_eq_whisker_ofGen]
    have h₂ : P.deriv hP (P.deriv hP
        (P.whisk (P.diag (ofGen L.gen)) ⟨L.start, L.left⟩ L.right)) = 0 := by
      rw [deriv_whisk, deriv_whisk, h, whisk_zero]
    show P.deriv hP (P.deriv hP (P.diag (ofLayer L hv))) = 0
    rw [e]; exact h₂
  · intro a b c f g hf hg
    show P.deriv hP (P.deriv hP (f ≫ g)) = 0
    rw [deriv_deriv_comp, hf, hg, Limits.zero_comp, Limits.comp_zero, add_zero]
  · intro a b
    show P.deriv hP (P.deriv hP 0) = 0
    rw [map_zero, map_zero]
  · intro a b f g hf hg
    show P.deriv hP (P.deriv hP (f + g)) = 0
    rw [map_add, map_add, hf, hg, add_zero]
  · intro a b r f hf
    show P.deriv hP (P.deriv hP (r • f)) = 0
    rw [map_smul, map_smul, hf, smul_zero]

end Presentation

end StringDiagrams

end
