import StringDiagrams.Examples.NilHecke.Relations
import StringDiagrams.Examples.NilHecke.DividedDifference
import StringDiagrams.LocalInterpretation

/-!
# The polynomial representation of the nilHecke category

The nilHecke category acts on polynomials: every object is sent to the polynomial ring
`MvPolynomial ℕ R` in the variables `X 0, X 1, …`, a dot with `i` strands to its left acts
by multiplication by `X i`, and a crossing with `i` strands to its left acts by the divided
difference operator `∂_i` (`mulX i`, `divDiff i`; see
`StringDiagrams.Examples.NilHecke.DividedDifference`).

Source: M. Khovanov, A. D. Lauda, *A diagrammatic approach to categorification of quantum
groups I*, arXiv:0803.4121v2: §2.2, Example 3 (p. 10), the nilHecke ring and its action on
polynomials; §2.3, the action of `R(ν)` on `Pol_ν` and Proposition 2.3 ("These rules define a
left action"), specialised to a single colour, where a dot acts by multiplication by a
variable and a crossing of equally labelled strands by the divided difference operator
`f ↦ (f - s_k f) / (x_k - x_{k+1})`. Indices are shifted to start at `0` (the paper's `x_a`
and `∂_a` are `X (a - 1)` and `divDiff (a - 1)` here), and the ground ring `ℤ` is replaced by
an arbitrary commutative ring `R`.

The endomorphisms of `n` strands only involve the first `n` variables, so they preserve the
subring `R[X 0, …, X (n - 1)]`; the paper's module `Pol_{n i} = ℤ[x_1, …, x_n]` corresponds
to that subring. Here every object is sent to the full ring `MvPolynomial ℕ R`, which gives a
single target module for all widths and suffices for the nonvanishing results below.
Faithfulness of the representation is not addressed here.

## Choice of target

The target is `ModuleCat R`, whose morphisms are bundled linear maps (`ModuleCat.Hom.hom`,
`ModuleCat.ofHom`). Since `MvPolynomial ℕ R` lives in the same universe as `R`, no universe
lifting is needed.

## Main declarations

* `NilHecke.polyLocal R`: the representation as an interpretation by local operators
  (`StringDiagrams.LocalInterpretation.uniform`, a single module for all objects);
  `NilHecke.polyInterp R` the resulting interpretation of the free 2-category in
  `ModuleCat R` and `NilHecke.polyFunctor R` the functor; its value on a diagram is the
  composite of the operators of its layers (`polyFunctor_map_hom`).
* `NilHecke.polyFunctor_respects`: soundness hypotheses, i.e. every whiskered defining
  relation and every whiskered instance of the interchange law holds; each reduces to an
  identity of operators by linear evaluation (`LocalInterpretation.evalW`), and interchange to
  the commutation of generators at disjoint positions (`genOp_comm`).
* `NilHecke.polyRep R : NH R ⥤ ModuleCat R`, an `R`-linear functor, with
  `polyRep_map_x` and `polyRep_map_ψ` computing the images of dots and crossings.
* `NilHecke.x_ne_zero`, `NilHecke.ψ_ne_zero`: over a nontrivial ring, dots and crossings are
  nonzero in `NH R`, so the presentation does not collapse.
-/

noncomputable section

namespace StringDiagrams.NilHecke

open CategoryTheory MvPolynomial

universe u

variable (R : Type u) [CommRing R]

/-! ## Operators of generators and layers -/

/-- The operator of a generator with `i` strands to its left. -/
def genOp : Gen → ℕ → (MvPolynomial ℕ R →ₗ[R] MvPolynomial ℕ R)
  | .dot, i => mulX i
  | .cross, i => divDiff i

@[simp] theorem genOp_dot (i : ℕ) : genOp R .dot i = mulX i := rfl

@[simp] theorem genOp_cross (i : ℕ) : genOp R .cross i = divDiff i := rfl

/-- The operator of a layer: its generator, acting at the position given by the number of
strands to its left. -/
def layerOp (L : Layer sig) : MvPolynomial ℕ R →ₗ[R] MvPolynomial ℕ R :=
  genOp R L.gen L.left.length

/-- The operator of a list of layers, read from bottom to top (the first layer acts first). -/
def layersOp : List (Layer sig) → (MvPolynomial ℕ R →ₗ[R] MvPolynomial ℕ R)
  | [] => LinearMap.id
  | L :: ls => layersOp ls ∘ₗ layerOp R L

@[simp] theorem layersOp_nil : layersOp R [] = LinearMap.id := rfl

@[simp] theorem layersOp_cons (L : Layer sig) (ls : List (Layer sig)) :
    layersOp R (L :: ls) = layersOp R ls ∘ₗ layerOp R L := rfl

/-- Generators at positions `i` and `j`, with `g` entirely to the left of `h`, act by
commuting operators. -/
theorem genOp_comm (g h : Gen) {i j : ℕ} (hij : i + g.arity ≤ j) :
    genOp R h j ∘ₗ genOp R g i = genOp R g i ∘ₗ genOp R h j := by
  cases g <;> cases h <;> simp only [Gen.arity] at hij <;> simp only [genOp]
  · exact mulX_comm j i
  · exact (mulX_divDiff_comm (show i ≠ j by omega) (show i ≠ j + 1 by omega)).symm
  · exact mulX_divDiff_comm (show j ≠ i by omega) (show j ≠ i + 1 by omega)
  · exact (divDiff_comm (show i + 1 < j ∨ j + 1 < i by omega)).symm

/-! ## The interpretation -/

/-- The polynomial ring `MvPolynomial ℕ R` as an object of `ModuleCat R`. -/
abbrev polyModule : ModuleCat.{u} R := ModuleCat.of R (MvPolynomial ℕ R)

/-- The polynomial interpretation as an interpretation by local operators, with a single
module for all objects. -/
def polyLocal :
    LocalInterpretation sig R (MvPolynomial ℕ R) (fun _ : Unit => MvPolynomial ℕ R) :=
  LocalInterpretation.uniform (layerOp R)

theorem polyLocal_opList (ls : List (Layer sig)) : (polyLocal R).opList ls = layersOp R ls := by
  induction ls with
  | nil => rfl
  | cons L ls ih => rw [LocalInterpretation.opList_cons, ih]; rfl

/-- The interpretation of the free 2-category on the nilHecke signature: every object goes
to `MvPolynomial ℕ R`, every layer to the operator of its generator at its position. -/
def polyInterp : Interpretation sig (ModuleCat.{u} R) := (polyLocal R).interp

/-- The functor from the free 2-category determined by `polyInterp`. -/
def polyFunctor : Obj sig ⥤ ModuleCat.{u} R := (polyInterp R).functor

/-- All objects have the same image, so the transport morphisms along equalities of objects
are identities. -/
theorem polyInterp_eqToHom {a b : Obj sig}
    (h : (polyInterp R).obj a = (polyInterp R).obj b) : eqToHom h = 𝟙 (polyModule R) :=
  eqToHom_refl (polyModule R) h

/-- The image of a chain of layers is the composite of the operators of its layers. -/
theorem polyInterp_mapChain_hom {a b : Obj sig} (ls : List (Layer sig)) (h : Chain a ls b) :
    ((polyInterp R).mapChain a ls b h).hom = layersOp R ls := by
  show ((polyLocal R).interp.mapChain a ls b h).hom = _
  rw [(polyLocal R).interp_mapChain_hom, polyLocal_opList]
  rfl

/-- The image of a diagram is the composite of the operators of its layers. -/
theorem polyFunctor_map_hom {a b : Obj sig} (f : a ⟶ b) :
    ((polyFunctor R).map f).hom = layersOp R (Diagram.layers f) :=
  polyInterp_mapChain_hom R _ _

@[simp] theorem layers_dlay {n i : ℕ} {g : Gen} (h : i + g.arity ≤ n) :
    Diagram.layers (dlay h) = [lay n i g] := rfl

/-! ## Soundness hypotheses -/

section Respects

variable {R}

open LinDiagram LocalInterpretation

private theorem layerOp_whisker (L : Layer sig) (u : Obj sig) (v : List sig.Colour) :
    layerOp R (L.whisker u v) = genOp R L.gen (u.word.length + L.left.length) := by
  simp [layerOp, Layer.whisker]

/-- A whiskered linear combination of diagrams is killed as soon as its evaluation is. -/
private theorem polyFunctor_map_whisker_eq_zero {a b : Obj sig} {u : Obj sig}
    {v : List sig.Colour} {X : LinDiagram R a b} (hw : a.WhiskerOK u v)
    (h : (polyLocal R).evalW () () u v X = 0) :
    (freeLift R (polyFunctor R)).map (whisker X u v hw) = 0 :=
  (polyLocal R).freeLift_map_whisker_eq_zero rfl rfl hw h

private theorem polyLocal_evalW_of {a b : Obj sig} (u : Obj sig) (v : List sig.Colour)
    (d : a ⟶ b) : (polyLocal R).evalW () () u v (of d : LinDiagram R a b) =
      layersOp R ((Diagram.layers d).map (·.whisker u v)) :=
  (uniform_evalW_of (layerOp R) () () u v d).trans (polyLocal_opList R _)

/-- Evaluation of a whiskered relation as a combination of composites of operators. -/
local macro "eval_relation" : tactic => `(tactic| simp only [relation, evalW_sub,
  polyLocal_evalW_of, Diagram.layers_comp, Diagram.layers_id, layers_dlay, List.cons_append,
  List.nil_append, List.map_cons, List.map_nil, layersOp_cons, layersOp_nil, LinearMap.id_comp,
  layerOp_whisker, lay, List.length_replicate, add_zero, genOp_cross, genOp_dot, sub_eq_zero])

theorem polyFunctor_rel_crossSq (u : Obj sig) (v : List sig.Colour)
    (hw : (strands 2).WhiskerOK u v) :
    (freeLift R (polyFunctor R)).map (whisker (relation R .crossSq) u v hw) = 0 :=
  polyFunctor_map_whisker_eq_zero hw (by eval_relation; exact divDiff_divDiff u.word.length)

theorem polyFunctor_rel_braid (u : Obj sig) (v : List sig.Colour)
    (hw : (strands 3).WhiskerOK u v) :
    (freeLift R (polyFunctor R)).map (whisker (relation R .braid) u v hw) = 0 :=
  polyFunctor_map_whisker_eq_zero hw
    (by eval_relation; exact LinearMap.ext (divDiff_braid_apply u.word.length))

theorem polyFunctor_rel_slideA (u : Obj sig) (v : List sig.Colour)
    (hw : (strands 2).WhiskerOK u v) :
    (freeLift R (polyFunctor R)).map (whisker (relation R .slideA) u v hw) = 0 :=
  polyFunctor_map_whisker_eq_zero hw (by eval_relation; exact mulX_divDiff_sub u.word.length)

theorem polyFunctor_rel_slideB (u : Obj sig) (v : List sig.Colour)
    (hw : (strands 2).WhiskerOK u v) :
    (freeLift R (polyFunctor R)).map (whisker (relation R .slideB) u v hw) = 0 :=
  polyFunctor_map_whisker_eq_zero hw (by eval_relation; exact divDiff_mulX_sub u.word.length)

theorem polyFunctor_interchange (x : InterchangeData sig) (hx : x.Valid) (u : Obj sig)
    (v : List sig.Colour) (hw : x.dom.WhiskerOK u v) :
    (freeLift R (polyFunctor R)).map (whisker (InterchangeData.rel R hx) u v hw) = 0 := by
  refine polyFunctor_map_whisker_eq_zero hw ((polyLocal R).evalW_interchange_eq_zero_of_comm
    (fun s l m r g g' => ?_) x hx u v)
  have hs : (((⟨s, g, m, g'⟩ : InterchangeData sig).sign : ℤ) : R) = 1 := by
    simp [InterchangeData.sign, sig]
  have hc : (sig.cod g).length = (sig.dom g).length := rfl
  simp only [polyLocal, uniform_op, layerOp, List.length_append, hs, one_smul, hc]
  exact genOp_comm R g g' (by simp [sig])

/-- `polyFunctor` respects the nilHecke presentation: every whiskered defining relation and
every whiskered instance of the interchange law is sent to zero. -/
theorem polyFunctor_respects : (pres R).Respects (polyFunctor R) where
  rel r u v hw := by
    cases r
    · exact polyFunctor_rel_crossSq u v hw
    · exact polyFunctor_rel_braid u v hw
    · exact polyFunctor_rel_slideA u v hw
    · exact polyFunctor_rel_slideB u v hw
  interchange := polyFunctor_interchange

end Respects

/-! ## The polynomial representation -/

/-- The polynomial representation of the nilHecke category. -/
def polyRep : NH R ⥤ ModuleCat.{u} R := (pres R).lift (polyFunctor_respects (R := R))

instance : (polyRep R).Additive := Presentation.lift_additive _

instance : (polyRep R).Linear R := Presentation.lift_linear _

@[simp] theorem polyRep_obj (n : ℕ) : (polyRep R).obj (NH.obj R n) = polyModule R := rfl

/-- The class of a diagram acts by the composite of the operators of its layers. -/
@[simp] theorem polyRep_map_diag {a b : Obj sig} (f : a ⟶ b) :
    (polyRep R).map ((pres R).diag f) = (polyFunctor R).map f :=
  Presentation.lift_diag _ f

/-- A dot on strand `i` acts by multiplication by `X i`. -/
theorem polyRep_map_x {n i : ℕ} (h : i < n) :
    (polyRep R).map (x R n i) = ModuleCat.ofHom (mulX i) := by
  rw [x_def R h, polyRep_map_diag]
  apply ModuleCat.hom_ext
  simp [polyFunctor_map_hom, layerOp, lay]

/-- The crossing of strands `i` and `i + 1` acts by the divided difference operator `∂_i`. -/
theorem polyRep_map_ψ {n i : ℕ} (h : i + 1 < n) :
    (polyRep R).map (ψ R n i) = ModuleCat.ofHom (divDiff i) := by
  rw [ψ_def R h, polyRep_map_diag]
  apply ModuleCat.hom_ext
  simp [polyFunctor_map_hom, layerOp, lay]

/-! ## Nonvanishing -/

/-- Over a nontrivial ring, a dot on any strand is nonzero in the nilHecke category. -/
theorem x_ne_zero [Nontrivial R] {n i : ℕ} (h : i < n) : x R n i ≠ 0 := by
  intro h0
  have h1 : (ModuleCat.ofHom (mulX i) : polyModule R ⟶ polyModule R) = 0 := by
    rw [← polyRep_map_x R h, h0, Functor.map_zero]
  have h2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h1) 1
  rw [ModuleCat.hom_ofHom, ModuleCat.hom_zero, mulX_apply, mul_one, LinearMap.zero_apply] at h2
  exact MvPolynomial.X_ne_zero i h2

/-- Over a nontrivial ring, a crossing of adjacent strands is nonzero in the nilHecke
category. -/
theorem ψ_ne_zero [Nontrivial R] {n i : ℕ} (h : i + 1 < n) : ψ R n i ≠ 0 := by
  intro h0
  have h1 : (ModuleCat.ofHom (divDiff i) : polyModule R ⟶ polyModule R) = 0 := by
    rw [← polyRep_map_ψ R h, h0, Functor.map_zero]
  have h2 := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h1) (X i)
  rw [ModuleCat.hom_ofHom, ModuleCat.hom_zero, divDiff_X_self, LinearMap.zero_apply] at h2
  exact one_ne_zero h2

end StringDiagrams.NilHecke

end
