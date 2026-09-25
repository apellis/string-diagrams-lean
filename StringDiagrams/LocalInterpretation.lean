import StringDiagrams.Generation
import StringDiagrams.Interpretation

/-!
# Interpretations by local operators

Many representations of presented categories are given by *local operators*: each object
`a` is sent to a module `M (κ a)` depending only on an index `κ a` (typically the number of
strands, or the word itself), and a layer acts by an operator determined by its generator
and its position. This file packages the transport and soundness bookkeeping common to all
such representations, so that it is done once.

## Setting

A `LocalInterpretation S R V M` consists of

* an index map `κ : Obj S → ι` and modules `M i`;
* a common *ambient* module `V` with, for every index `i`, a section `ext i : M i → V` and a
  retraction `res i : V → M i` (`res i ∘ ext i = id`);
* for every layer `L` an operator `op L : V → V` which is *local*: the component of
  `op L x` of index `κ L.cod` only depends on the component of `x` of index `κ L.dom`.

The image of a layer is `res (κ L.cod) ∘ op L ∘ ext (κ L.dom)`. Because all operators act on
the single module `V`, composites of layers never need to be transported along equalities of
indices; indices only appear at the two ends (`res`, `ext`), and there any equality of indices
can be absorbed by `subst`.

Three common shapes are covered:

* a single module for all objects (`LocalInterpretation.uniform`, `ι = Unit`,
  `ext = res = id`);
* width-dependent modules embedded in a big module of functions, as for the
  Temperley–Lieb representation on functions of words, where `ext` is extension by zero and
  `res` is restriction;
* width-preserving layers acting componentwise on `Π i, M i` (`LocalInterpretation.pi`),
  where every diagram between objects of index `i` acts on `M i` by the product of the
  component operators of its layers (`pi_functor_map_transport`).

## Main results

* `LocalInterpretation.interp`, `LocalInterpretation.functor`: the interpretation in
  `ModuleCat R` and the functor out of the free 2-category.
* `functor_map_hom`: the image of a diagram `f : a ⟶ b` is
  `res (κ b) ∘ opList (layers f) ∘ ext (κ a)`, where `opList` composes the layer operators
  (bottom layer first); `functor_map_transport` is the same statement after transport along
  arbitrary equalities `κ a = i`, `κ b = j`. Proved once, by induction on the layers, from
  locality.
* `eval`, `evalW`: linear evaluation of linear combinations of diagrams (the latter after
  whiskering by `u` and `v`), with simp lemmas for `of`, `single`, `+`, `-`, `•`, `0`;
  `freeLift_map_hom`, `freeLift_map_whisker_hom` identify them with the linear extension
  `freeLift`, so that `Presentation.Respects` need never be unfolded.
* `respects_of`: `P.Respects Q.functor` from the vanishing of `evalW` on every whiskered
  relation and interchange instance; `evalW_interchange_eq_zero` derives the interchange part
  from a commutation (Koszul sign) hypothesis on pairs of layers at disjoint positions.
* `Presentation.int_smul_eq_zsmul`, `Presentation.hom_induction_int`: over `R = ℤ`, the
  scalar multiplication of the linear structure of a presented category agrees with `zsmul`,
  and induction on morphisms needs no scalar case.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory

universe w w₁ w₂ w₃ u₀ u₁ u₂

/-- An interpretation of the free 2-category on `S` by local operators on an ambient module
`V`, with the object `a` sent to `M (κ a)`. See the module documentation. -/
structure LocalInterpretation (S : Signature.{u₀, u₁, u₂}) (R : Type w) [CommRing R]
    {ι : Type w₁} (V : Type w₃) [AddCommGroup V] [Module R V]
    (M : ι → Type w₂) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] where
  /-- The index of an object. -/
  κ : Obj S → ι
  /-- The inclusion of `M i` into the ambient module. -/
  ext : ∀ i, M i →ₗ[R] V
  /-- The projection of the ambient module onto `M i`. -/
  res : ∀ i, V →ₗ[R] M i
  /-- The operator of a layer on the ambient module. -/
  op : Layer S → V →ₗ[R] V
  res_comp_ext : ∀ i, res i ∘ₗ ext i = LinearMap.id
  /-- Locality: the output component of index `κ L.cod` only depends on the input component
  of index `κ L.dom`. -/
  res_op_ext_res : ∀ L : Layer S, L.Valid →
    res (κ L.cod) ∘ₗ op L ∘ₗ ext (κ L.dom) ∘ₗ res (κ L.dom) = res (κ L.cod) ∘ₗ op L

namespace LocalInterpretation

variable {S : Signature.{u₀, u₁, u₂}} {R : Type w} [CommRing R] {ι : Type w₁}
  {V : Type w₃} [AddCommGroup V] [Module R V]
  {M : ι → Type w₂} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  (Q : LocalInterpretation S R V M)

@[simp] theorem res_ext_apply (i : ι) (x : M i) : Q.res i (Q.ext i x) = x :=
  LinearMap.congr_fun (Q.res_comp_ext i) x

/-! ## Operators of lists of layers -/

/-- The composite of the operators of a list of layers; the first (bottom) layer acts
first. -/
def opList : List (Layer S) → (V →ₗ[R] V)
  | [] => LinearMap.id
  | L :: ls => opList ls ∘ₗ Q.op L

@[simp] theorem opList_nil : Q.opList [] = LinearMap.id := rfl

@[simp] theorem opList_cons (L : Layer S) (ls : List (Layer S)) :
    Q.opList (L :: ls) = Q.opList ls ∘ₗ Q.op L := rfl

@[simp] theorem opList_append (ls ms : List (Layer S)) :
    Q.opList (ls ++ ms) = Q.opList ms ∘ₗ Q.opList ls := by
  induction ls with
  | nil => rfl
  | cons L ls ih => rw [List.cons_append, opList_cons, ih, opList_cons, LinearMap.comp_assoc]

/-- Locality of a chain of layers. -/
theorem res_opList_ext_res {a b : Obj S} {ls : List (Layer S)} (h : Chain a ls b) (x : V) :
    Q.res (Q.κ b) (Q.opList ls (Q.ext (Q.κ a) (Q.res (Q.κ a) x))) =
      Q.res (Q.κ b) (Q.opList ls x) := by
  induction ls generalizing a x with
  | nil =>
    cases h
    simp
  | cons L ls ih =>
    obtain ⟨hv, rfl, hc⟩ := h
    have hL := LinearMap.congr_fun (Q.res_op_ext_res L hv) x
    simp only [LinearMap.comp_apply] at hL
    simp only [opList_cons, LinearMap.comp_apply]
    rw [← ih hc, hL, ih hc]

/-! ## The interpretation -/

/-- The module `M i` as an object of `ModuleCat R`. -/
abbrev mod (i : ι) : ModuleCat.{w₂} R := ModuleCat.of R (M i)

/-- The interpretation: `a` goes to `M (κ a)`, a layer `L` to
`res (κ L.cod) ∘ op L ∘ ext (κ L.dom)`. -/
def interp : Interpretation S (ModuleCat.{w₂} R) where
  obj a := mod (M := M) (Q.κ a)
  layer L _ := ModuleCat.ofHom (Q.res (Q.κ L.cod) ∘ₗ Q.op L ∘ₗ Q.ext (Q.κ L.dom))

/-- The functor from the free 2-category. -/
def functor : Obj S ⥤ ModuleCat.{w₂} R := Q.interp.functor

@[simp] theorem functor_obj (a : Obj S) : Q.functor.obj a = mod (M := M) (Q.κ a) := rfl

@[simp] theorem interp_obj (a : Obj S) : Q.interp.obj a = mod (M := M) (Q.κ a) := rfl

@[simp] theorem interp_layer (L : Layer S) (hv : L.Valid) :
    Q.interp.layer L hv = ModuleCat.ofHom (Q.res (Q.κ L.cod) ∘ₗ Q.op L ∘ₗ Q.ext (Q.κ L.dom)) :=
  rfl

/-- The image of a chain of layers. -/
theorem interp_mapChain_hom {a b : Obj S} (ls : List (Layer S)) (h : Chain a ls b) :
    (Q.interp.mapChain a ls b h).hom = Q.res (Q.κ b) ∘ₗ Q.opList ls ∘ₗ Q.ext (Q.κ a) := by
  induction ls generalizing a with
  | nil =>
    cases h
    refine LinearMap.ext fun x => ?_
    simp only [Interpretation.mapChain, eqToHom_refl, ModuleCat.hom_id, opList_nil,
      LinearMap.id_comp, LinearMap.id_apply]
    exact (Q.res_ext_apply _ x).symm
  | cons L ls ih =>
    obtain ⟨hv, rfl, hc⟩ := h
    refine LinearMap.ext fun x => ?_
    simp only [Interpretation.mapChain, eqToHom_refl, Category.id_comp, ModuleCat.hom_comp, ih hc,
      interp_layer, ModuleCat.hom_ofHom, LinearMap.comp_apply, opList_cons]
    exact Q.res_opList_ext_res hc _

/-- **The image of a diagram** is the composite of the operators of its layers, between the
inclusion and the projection of the end indices. -/
theorem functor_map_hom {a b : Obj S} (f : a ⟶ b) :
    (Q.functor.map f).hom = Q.res (Q.κ b) ∘ₗ Q.opList (Diagram.layers f) ∘ₗ Q.ext (Q.κ a) :=
  Q.interp_mapChain_hom _ _

theorem functor_map_apply {a b : Obj S} (f : a ⟶ b) (x : M (Q.κ a)) :
    (Q.functor.map f).hom x = Q.res (Q.κ b) (Q.opList (Diagram.layers f) (Q.ext (Q.κ a) x)) := by
  rw [functor_map_hom]; rfl

/-- The image of a diagram, transported along arbitrary equalities of the end indices. -/
theorem functor_map_transport {a b : Obj S} {i j : ι} (f : a ⟶ b) (ha : Q.κ a = i)
    (hb : Q.κ b = j) :
    eqToHom (congrArg (mod (M := M)) ha.symm) ≫ Q.functor.map f ≫
        eqToHom (congrArg (mod (M := M)) hb) =
      ModuleCat.ofHom (Q.res j ∘ₗ Q.opList (Diagram.layers f) ∘ₗ Q.ext i) := by
  subst ha hb
  apply ModuleCat.hom_ext
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id, functor_map_hom,
    ModuleCat.hom_ofHom]

/-- The image of a single layer. -/
theorem functor_map_layer_hom (L : Layer S) (hv : L.Valid) {a b : Obj S} (ha : L.dom = a)
    (hb : L.cod = b) :
    (Q.functor.map (Diagram.layer L hv ha hb)).hom =
      Q.res (Q.κ b) ∘ₗ Q.op L ∘ₗ Q.ext (Q.κ a) := by
  rw [functor_map_hom, Diagram.layers_layer, opList_cons, opList_nil, LinearMap.id_comp]

/-! ## Linear evaluation -/

/-- Linear evaluation of linear combinations of diagrams from `a` to `b`, between the indices
`i` and `j`: a diagram `d` goes to `res j ∘ opList (layers d) ∘ ext i`. -/
def eval (i j : ι) {a b : Obj S} : ((a ⟶ b) →₀ R) →ₗ[R] (M i →ₗ[R] M j) :=
  Finsupp.linearCombination R fun d : a ⟶ b =>
    Q.res j ∘ₗ Q.opList (Diagram.layers d) ∘ₗ Q.ext i

/-- Linear evaluation after whiskering by `u` on the left and `v` on the right: a diagram `d`
goes to `res j ∘ opList (layers (u ⊗ d ⊗ v)) ∘ ext i`. -/
def evalW (i j : ι) (u : Obj S) (v : List S.Colour) {a b : Obj S} :
    ((a ⟶ b) →₀ R) →ₗ[R] (M i →ₗ[R] M j) :=
  Finsupp.linearCombination R fun d : a ⟶ b =>
    Q.res j ∘ₗ Q.opList ((Diagram.layers d).map (·.whisker u v)) ∘ₗ Q.ext i

section EvalLemmas

variable (i j : ι) {a b : Obj S}

@[simp] theorem eval_single (d : a ⟶ b) (r : R) :
    Q.eval i j (Finsupp.single d r : LinDiagram R a b) =
      r • (Q.res j ∘ₗ Q.opList (Diagram.layers d) ∘ₗ Q.ext i) :=
  Finsupp.linearCombination_single R r d

@[simp] theorem eval_of (d : a ⟶ b) :
    Q.eval i j (LinDiagram.of d : LinDiagram R a b) =
      Q.res j ∘ₗ Q.opList (Diagram.layers d) ∘ₗ Q.ext i := by
  rw [LinDiagram.of, eval_single, one_smul]

@[simp] theorem eval_zero : Q.eval i j (0 : LinDiagram R a b) = 0 := map_zero _

@[simp] theorem eval_add (X Y : LinDiagram R a b) :
    Q.eval i j (X + Y : LinDiagram R a b) = Q.eval i j X + Q.eval i j Y := map_add _ X Y

@[simp] theorem eval_sub (X Y : LinDiagram R a b) :
    Q.eval i j (X - Y : LinDiagram R a b) = Q.eval i j X - Q.eval i j Y := map_sub _ X Y

@[simp] theorem eval_neg (X : LinDiagram R a b) :
    Q.eval i j (-X : LinDiagram R a b) = -Q.eval i j X := map_neg _ X

@[simp] theorem eval_smul (r : R) (X : LinDiagram R a b) :
    Q.eval i j (r • X : LinDiagram R a b) = r • Q.eval i j X := map_smul _ r X

variable (u : Obj S) (v : List S.Colour)

@[simp] theorem evalW_single (d : a ⟶ b) (r : R) :
    Q.evalW i j u v (Finsupp.single d r : LinDiagram R a b) =
      r • (Q.res j ∘ₗ Q.opList ((Diagram.layers d).map (·.whisker u v)) ∘ₗ Q.ext i) :=
  Finsupp.linearCombination_single R r d

@[simp] theorem evalW_of (d : a ⟶ b) :
    Q.evalW i j u v (LinDiagram.of d : LinDiagram R a b) =
      Q.res j ∘ₗ Q.opList ((Diagram.layers d).map (·.whisker u v)) ∘ₗ Q.ext i := by
  rw [LinDiagram.of, evalW_single, one_smul]

@[simp] theorem evalW_zero : Q.evalW i j u v (0 : LinDiagram R a b) = 0 := map_zero _

@[simp] theorem evalW_add (X Y : LinDiagram R a b) :
    Q.evalW i j u v (X + Y : LinDiagram R a b) = Q.evalW i j u v X + Q.evalW i j u v Y :=
  map_add _ X Y

@[simp] theorem evalW_sub (X Y : LinDiagram R a b) :
    Q.evalW i j u v (X - Y : LinDiagram R a b) = Q.evalW i j u v X - Q.evalW i j u v Y :=
  map_sub _ X Y

@[simp] theorem evalW_neg (X : LinDiagram R a b) :
    Q.evalW i j u v (-X : LinDiagram R a b) = -Q.evalW i j u v X := map_neg _ X

@[simp] theorem evalW_smul (r : R) (X : LinDiagram R a b) :
    Q.evalW i j u v (r • X : LinDiagram R a b) = r • Q.evalW i j u v X := map_smul _ r X

/-- Evaluating a whiskered linear combination is whiskered evaluation. -/
theorem eval_whisker (X : LinDiagram R a b) (hw : a.WhiskerOK u v) :
    Q.eval i j (LinDiagram.whisker X u v hw) = Q.evalW i j u v X := by
  rw [eval, LinDiagram.whisker, Finsupp.linearCombination_mapDomain]
  rfl

end EvalLemmas

/-! ## The linear extension -/

/-- The linear extension of `Q.functor` is linear evaluation. -/
theorem freeLift_map_hom {a b : Obj S} (X : LinDiagram R a b) :
    ((freeLift R Q.functor).map X).hom = Q.eval (Q.κ a) (Q.κ b) X := by
  induction X using Finsupp.induction_linear with
  | zero =>
    rw [CategoryTheory.Functor.map_zero]
    exact (Q.eval_zero _ _).symm
  | add X Y hX hY =>
    rw [CategoryTheory.Functor.map_add, ModuleCat.hom_add, hX, hY]
    exact (Q.eval_add _ _ X Y).symm
  | single d r =>
    rw [freeLift_map_single, ModuleCat.hom_smul, eval_single]
    exact congrArg (r • ·) (Q.functor_map_hom d)

/-- The linear extension of `Q.functor` on a whiskered linear combination. -/
theorem freeLift_map_whisker_hom {a b : Obj S} (X : LinDiagram R a b) (u : Obj S)
    (v : List S.Colour) (hw : a.WhiskerOK u v) :
    ((freeLift R Q.functor).map (LinDiagram.whisker X u v hw)).hom =
      Q.evalW (Q.κ (a.whisker u v)) (Q.κ (b.whisker u v)) u v X := by
  rw [freeLift_map_hom, eval_whisker]

/-- A linear combination of diagrams is sent to zero as soon as its evaluation vanishes, at
any indices equal to those of its ends. -/
theorem freeLift_map_eq_zero {a b : Obj S} {i j : ι} (ha : Q.κ a = i) (hb : Q.κ b = j)
    {X : LinDiagram R a b} (h : Q.eval i j X = 0) : (freeLift R Q.functor).map X = 0 := by
  subst ha hb
  apply ModuleCat.hom_ext
  rw [freeLift_map_hom, h]
  rfl

/-- A whiskered linear combination of diagrams is sent to zero as soon as its whiskered
evaluation vanishes, at any indices equal to those of its ends. -/
theorem freeLift_map_whisker_eq_zero {a b : Obj S} {u : Obj S} {v : List S.Colour} {i j : ι}
    (ha : Q.κ (a.whisker u v) = i) (hb : Q.κ (b.whisker u v) = j) {X : LinDiagram R a b}
    (hw : a.WhiskerOK u v) (h : Q.evalW i j u v X = 0) :
    (freeLift R Q.functor).map (LinDiagram.whisker X u v hw) = 0 :=
  Q.freeLift_map_eq_zero ha hb (by rw [eval_whisker, h])

/-! ## Soundness -/

section Respects

variable (P : Presentation S R)

/-- Soundness hypotheses from linear evaluation: `Q.functor` respects `P` as soon as the
whiskered evaluation of every relation and of every interchange relation vanishes. -/
theorem respects_of
    (hrel : ∀ (r : P.Rel) (u : Obj S) (v : List S.Colour), (P.dom r).WhiskerOK u v →
      Q.evalW (Q.κ ((P.dom r).whisker u v)) (Q.κ ((P.cod r).whisker u v)) u v (P.rel r) = 0)
    (hint : ∀ (x : InterchangeData S) (hx : x.Valid) (u : Obj S) (v : List S.Colour),
      x.dom.WhiskerOK u v →
      Q.evalW (Q.κ (x.dom.whisker u v)) (Q.κ (x.cod.whisker u v)) u v
        (InterchangeData.rel R hx) = 0) :
    P.Respects Q.functor where
  rel r u v hw := Q.freeLift_map_whisker_eq_zero rfl rfl hw (hrel r u v hw)
  interchange x hx u v hw := Q.freeLift_map_whisker_eq_zero rfl rfl hw (hint x hx u v hw)

/-- The whiskered evaluation of an interchange relation: the two orders of the layers of
`g` (left) and `h` (right), with the Koszul sign. -/
theorem evalW_interchange (x : InterchangeData S) (hx : x.Valid) (u : Obj S)
    (v : List S.Colour) (i j : ι) :
    Q.evalW i j u v (InterchangeData.rel R hx) =
      Q.res j ∘ₗ Q.op ⟨u.start, u.word ++ (S.cod x.g ++ x.mid), x.h, v⟩ ∘ₗ
          Q.op ⟨u.start, u.word, x.g, x.mid ++ (S.dom x.h ++ v)⟩ ∘ₗ Q.ext i -
        ((x.sign : ℤ) : R) •
          (Q.res j ∘ₗ Q.op ⟨u.start, u.word, x.g, x.mid ++ (S.cod x.h ++ v)⟩ ∘ₗ
            Q.op ⟨u.start, u.word ++ (S.dom x.g ++ x.mid), x.h, v⟩ ∘ₗ Q.ext i) := by
  simp only [InterchangeData.rel, evalW_sub, evalW_smul, evalW_of, InterchangeData.ghDiagram,
    InterchangeData.hgDiagram, Diagram.layers_mk, List.map_cons, List.map_nil, opList_cons,
    opList_nil, LinearMap.id_comp, LinearMap.comp_assoc, InterchangeData.gh₁,
    InterchangeData.gh₂, InterchangeData.hg₁, InterchangeData.hg₂, Layer.whisker,
    List.append_nil, List.nil_append, List.append_assoc]

/-- The interchange part of the soundness hypotheses from a commutation hypothesis: for all
generators `g`, `g'` separated by the word `m`, with `l` to the left and `r` to the right,
applying `g` then `g'` equals the Koszul sign times applying `g'` then `g`, between the
inclusion and the projection of the end indices. -/
theorem evalW_interchange_eq_zero
    (hcomm : ∀ (s : S.Region) (l m r : List S.Colour) (g g' : S.Gen),
      Q.res (Q.κ ⟨s, l ++ (S.cod g ++ (m ++ (S.cod g' ++ r)))⟩) ∘ₗ
          Q.op ⟨s, l ++ (S.cod g ++ m), g', r⟩ ∘ₗ Q.op ⟨s, l, g, m ++ (S.dom g' ++ r)⟩ ∘ₗ
          Q.ext (Q.κ ⟨s, l ++ (S.dom g ++ (m ++ (S.dom g' ++ r)))⟩) =
        (((⟨s, g, m, g'⟩ : InterchangeData S).sign : ℤ) : R) •
          (Q.res (Q.κ ⟨s, l ++ (S.cod g ++ (m ++ (S.cod g' ++ r)))⟩) ∘ₗ
            Q.op ⟨s, l, g, m ++ (S.cod g' ++ r)⟩ ∘ₗ Q.op ⟨s, l ++ (S.dom g ++ m), g', r⟩ ∘ₗ
            Q.ext (Q.κ ⟨s, l ++ (S.dom g ++ (m ++ (S.dom g' ++ r)))⟩)))
    (x : InterchangeData S) (hx : x.Valid) (u : Obj S) (v : List S.Colour) :
    Q.evalW (Q.κ (x.dom.whisker u v)) (Q.κ (x.cod.whisker u v)) u v
      (InterchangeData.rel R hx) = 0 := by
  have hd : x.dom.whisker u v =
      ⟨u.start, u.word ++ (S.dom x.g ++ (x.mid ++ (S.dom x.h ++ v)))⟩ := by
    simp [InterchangeData.dom, Obj.whisker]
  have hc : x.cod.whisker u v =
      ⟨u.start, u.word ++ (S.cod x.g ++ (x.mid ++ (S.cod x.h ++ v)))⟩ := by
    simp [InterchangeData.cod, Obj.whisker]
  rw [hd, hc, evalW_interchange, hcomm u.start u.word x.mid v x.g x.h, sub_eq_zero]
  rfl

/-- The same, from a commutation hypothesis on the ambient module (without projecting). -/
theorem evalW_interchange_eq_zero_of_comm
    (hcomm : ∀ (s : S.Region) (l m r : List S.Colour) (g g' : S.Gen),
      Q.op ⟨s, l ++ (S.cod g ++ m), g', r⟩ ∘ₗ Q.op ⟨s, l, g, m ++ (S.dom g' ++ r)⟩ =
        (((⟨s, g, m, g'⟩ : InterchangeData S).sign : ℤ) : R) •
          (Q.op ⟨s, l, g, m ++ (S.cod g' ++ r)⟩ ∘ₗ Q.op ⟨s, l ++ (S.dom g ++ m), g', r⟩))
    (x : InterchangeData S) (hx : x.Valid) (u : Obj S) (v : List S.Colour) :
    Q.evalW (Q.κ (x.dom.whisker u v)) (Q.κ (x.cod.whisker u v)) u v
      (InterchangeData.rel R hx) = 0 := by
  refine Q.evalW_interchange_eq_zero (fun s l m r g g' => LinearMap.ext fun y => ?_) x hx u v
  have h := congrArg (Q.res (Q.κ ⟨s, l ++ (S.cod g ++ (m ++ (S.cod g' ++ r)))⟩))
    (LinearMap.congr_fun (hcomm s l m r g g')
      (Q.ext (Q.κ ⟨s, l ++ (S.dom g ++ (m ++ (S.dom g' ++ r)))⟩) y))
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul] at h ⊢
  exact h

end Respects

/-! ## A single module for all objects -/

section Uniform

/-- All objects are sent to the same module `V`, and layers act by the operators `op`. -/
def uniform (op : Layer S → V →ₗ[R] V) : LocalInterpretation S R V (fun _ : Unit => V) where
  κ _ := ()
  ext _ := LinearMap.id
  res _ := LinearMap.id
  op := op
  res_comp_ext _ := rfl
  res_op_ext_res _ _ := rfl

variable (op : Layer S → V →ₗ[R] V)

@[simp] theorem uniform_ext (i : Unit) : (uniform op).ext i = LinearMap.id := rfl

@[simp] theorem uniform_res (i : Unit) : (uniform op).res i = LinearMap.id := rfl

@[simp] theorem uniform_op (L : Layer S) : (uniform op).op L = op L := rfl

/-- The image of a diagram under a uniform interpretation. -/
theorem uniform_functor_map_hom {a b : Obj S} (f : a ⟶ b) :
    ((uniform op).functor.map f).hom = (uniform op).opList (Diagram.layers f) :=
  (uniform op).functor_map_hom f

@[simp] theorem uniform_opList_cons (L : Layer S) (ls : List (Layer S)) :
    (uniform op).opList (L :: ls) = (uniform op).opList ls ∘ₗ op L := rfl

@[simp] theorem uniform_eval_of (i j : Unit) {a b : Obj S} (d : a ⟶ b) :
    (uniform op).eval i j (LinDiagram.of d : LinDiagram R a b) =
      (uniform op).opList (Diagram.layers d) :=
  (uniform op).eval_of i j d

@[simp] theorem uniform_evalW_of (i j : Unit) (u : Obj S) (v : List S.Colour) {a b : Obj S}
    (d : a ⟶ b) :
    (uniform op).evalW i j u v (LinDiagram.of d : LinDiagram R a b) =
      (uniform op).opList ((Diagram.layers d).map (·.whisker u v)) :=
  (uniform op).evalW_of i j u v d

end Uniform

/-! ## Componentwise operators for index-preserving layers -/

section Pi

variable (κ : Obj S → ι) (A : Layer S → ∀ i, Module.End R (M i))
  (hκ : ∀ L : Layer S, L.Valid → κ L.cod = κ L.dom)

open Classical in
/-- Layers that preserve the index, acting on `Π i, M i` componentwise: the component of
index `i` of `op L` is `A L i`. -/
def pi : LocalInterpretation S R (∀ i, M i) M where
  κ := κ
  ext i := LinearMap.single R M i
  res i := LinearMap.proj i
  op L := LinearMap.pi fun i => A L i ∘ₗ LinearMap.proj i
  res_comp_ext i := LinearMap.ext fun x => by simp
  res_op_ext_res L hv := LinearMap.ext fun F => by
    simp only [LinearMap.comp_apply, LinearMap.pi_apply, LinearMap.coe_proj,
      Function.eval, LinearMap.single_apply]
    rw [hκ L hv, Pi.single_eq_same]

/-- The product of the component operators of a list of layers at index `i`; the first
(bottom) layer acts first. -/
def piList (i : ι) : List (Layer S) → Module.End R (M i)
  | [] => 1
  | L :: ls => piList i ls * A L i

@[simp] theorem piList_nil (i : ι) : piList A i [] = 1 := rfl

@[simp] theorem piList_cons (i : ι) (L : Layer S) (ls : List (Layer S)) :
    piList A i (L :: ls) = piList A i ls * A L i := rfl

variable {κ A hκ}

@[simp] theorem pi_op_apply (L : Layer S) (F : ∀ i, M i) (i : ι) :
    (pi κ A hκ).op L F i = A L i (F i) := rfl

@[simp] theorem pi_res_apply (i : ι) (F : ∀ i, M i) : (pi κ A hκ).res i F = F i := rfl

open Classical in
@[simp] theorem pi_ext_apply (i : ι) (x : M i) : (pi κ A hκ).ext i x = Pi.single i x := rfl

theorem pi_opList_apply (ls : List (Layer S)) (F : ∀ i, M i) (i : ι) :
    (pi κ A hκ).opList ls F i = piList A i ls (F i) := by
  induction ls generalizing F with
  | nil => rfl
  | cons L ls ih => simp [ih, Module.End.mul_apply]

/-- Evaluation of a list of layers between the same index is the product of the component
operators. -/
theorem pi_res_opList_ext (i : ι) (ls : List (Layer S)) :
    (pi κ A hκ).res i ∘ₗ (pi κ A hκ).opList ls ∘ₗ (pi κ A hκ).ext i = piList A i ls := by
  classical
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.comp_apply, pi_res_apply, pi_opList_apply]
  congr 1
  exact Pi.single_eq_same (f := M) i x

/-- The image of a diagram between objects of index `i`, transported to `M i`, is the product
of the component operators of its layers. -/
theorem pi_functor_map_transport {a b : Obj S} {i : ι} (f : a ⟶ b) (ha : κ a = i)
    (hb : κ b = i) :
    eqToHom (congrArg (mod (M := M)) ha.symm) ≫ (pi κ A hκ).functor.map f ≫
        eqToHom (congrArg (mod (M := M)) hb) =
      ModuleCat.ofHom (piList A i (Diagram.layers f)) := by
  rw [(pi κ A hκ).functor_map_transport f ha hb, pi_res_opList_ext]

/-- Whiskered evaluation between the same index `i`, for index-preserving componentwise
operators. -/
theorem pi_evalW_of (i : ι) (u : Obj S) (v : List S.Colour) {a b : Obj S} (d : a ⟶ b) :
    (pi κ A hκ).evalW i i u v (LinDiagram.of d : LinDiagram R a b) =
      piList A i ((Diagram.layers d).map (·.whisker u v)) := by
  rw [evalW_of, pi_res_opList_ext]

end Pi

end LocalInterpretation

/-! ## Integer coefficients -/

namespace Presentation

variable {S : Signature.{u₀, u₁, u₂}} {a b : Obj S}

/-- Over `R = ℤ`, the scalar multiplication of the linear structure `instLinear` of a
presented category is `zsmul`. The left-hand side is the scalar multiplication occurring in
`Presentation.hom_induction` for `R = ℤ`. -/
theorem int_smul_eq_zsmul (P : Presentation S ℤ) (n : ℤ) (f : P.obj a ⟶ P.obj b) :
    @HSMul.hSMul ℤ _ _ (@instHSMul _ _ (@SMulZeroClass.toSMul _ _ _
      (@DistribSMul.toSMulZeroClass _ _ _ (@DistribMulAction.toDistribSMul _ _ _ _
        (@Module.toDistribMulAction _ _ _ _ (P.instLinear.homModule (P.obj a) (P.obj b)))))))
      n f = n • f :=
  _root_.int_smul_eq_zsmul (P.instLinear.homModule (P.obj a) (P.obj b)) n f

/-- Induction on morphisms of a presented category over `ℤ`: classes of diagrams, zero, sums
and negatives. -/
theorem hom_induction_int (P : Presentation S ℤ) {p : (P.obj a ⟶ P.obj b) → Prop}
    (diag : ∀ d : a ⟶ b, p (P.diag d)) (zero : p 0) (add : ∀ f g, p f → p g → p (f + g))
    (neg : ∀ f, p f → p (-f)) (f : P.obj a ⟶ P.obj b) : p f := by
  refine P.hom_induction diag zero add (fun n g hg => ?_) f
  rw [P.int_smul_eq_zsmul]
  have hn : ∀ k : ℕ, p ((k : ℤ) • g) := by
    intro k
    induction k with
    | zero => rw [Nat.cast_zero, zero_smul]; exact zero
    | succ k ih => rw [Nat.cast_succ, add_smul, one_smul]; exact add _ _ ih hg
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · exact hn k
  · rw [neg_smul]; exact neg _ (hn k)

end Presentation

end StringDiagrams

end
