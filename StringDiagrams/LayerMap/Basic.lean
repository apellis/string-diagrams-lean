import StringDiagrams.Interpretation
import StringDiagrams.Monoidal
import StringDiagrams.Horizontal
import StringDiagrams.Super.Basic

/-!
# Functors between presented categories from maps of layers

A functor out of a presented category `P.Presented` is usually constructed with
`Presentation.lift`, whose hypothesis `Presentation.Respects` asks that every relation *and
every instance of the interchange law*, whiskered by arbitrary objects on either side, be sent
to zero. This file reduces that hypothesis to the unwhiskered relations for functors that
commute with whiskering, and provides such functors from maps of layers.

## The reduction

`Presentation.respects_of_whisker`: for a family of functors `F i : Obj S ⥤ D` such that the
image under `F i` of a whiskered linear combination of diagrams vanishes as soon as the
images of the combination itself under all `F j` vanish, `P.Respects (F i)` follows from the
vanishing of the images of the relations of `P` and of the (unwhiskered) instances of the
interchange law. A family is allowed because whiskering may change the functor: for example a
functor placing diagrams in a region labelled by `μ` may need the label of the region on the
right of a whiskered diagram to depend on the whiskering word.

## Layer maps

A `LayerMap S S'` sends objects to objects and layers to layers, compatibly with the
boundaries of well-formed layers. It is *not* required to come from a map of signatures: the
image of a layer may depend on its position, i.e. on the strands and regions around its
generator. It induces a functor of free 2-categories (`LayerMap.functor`; the image of a
diagram is the list of the images of its layers, `LayerMap.map`) and, for a presentation `Q`
of `S'` and a *weight* `χ : S.Gen → R`, a functor `LayerMap.toPresented Q χ : Obj S ⥤ Q.Presented`
sending a diagram `d` to `(∏ χ) • [φ d]`, the product being over the generators of `d`
(`Diagram.weight`). Weights `χ = 1` give the plain images; weights `±1` or units encode
rescalings of generators and the signs of symmetries.

Compatibility with whiskering is the datum `LayerMap.WhiskerData`: for a family of layer maps
`φ i`, whiskering by `u` and `v` before applying `φ i` is whiskering by `u'` and `v'` after
applying `φ j`, for some `j`, `u'` and `v'` depending on `i`, `u`, `v` and the source object,
on all layers reachable from that object. Then (`LayerMap.respects`, `LayerMap.lift`)
the functors descend to `P.Presented ⥤ Q.Presented` as soon as the relations of `P` and the
interchange law are respected without whiskering. For the interchange law, it suffices that the
images of the four layers of an instance are the four layers of an instance of the target
(`LayerMap.toPresented_interchange`), or of the instance with the two generators exchanged,
as for a left–right reflection (`LayerMap.toPresented_interchange_swap`); in both cases the
Koszul signs must agree.

Layer maps preserving degrees (`LayerMap.PreservesDeg`) induce degree-preserving functors
(`LayerMap.lift_mem_homDeg`); for the parity grading this is parity preservation.

Contravariant layer maps (reflections in a horizontal axis) are in
`StringDiagrams.LayerMap.Op`, arbitrary morphisms as images of layers in
`StringDiagrams.LayerMap.Local`, and the layer maps induced by maps of generators (including
the reflections in a vertical axis, which reverse the order of 1-morphisms) in
`StringDiagrams.LayerMap.Generators`.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory

universe w w₁ w₂ v v' u₀ u₁ u₂ u₀' u₁' u₂'

variable {S : Signature.{u₀, u₁, u₂}}

/-! ## Layers reachable from an object -/

theorem Chain.valid_of_mem {a b : Obj S} {ls : List (Layer S)} (h : Chain a ls b) {L : Layer S}
    (hL : L ∈ ls) : L.Valid := by
  induction ls generalizing a with
  | nil => cases hL
  | cons M ls ih =>
    obtain ⟨hv, rfl, hc⟩ := h
    rcases List.mem_cons.1 hL with rfl | hL
    · exact hv
    · exact ih hc hL

/-- Every layer of a diagram from `a` has a bottom boundary reachable from `a`. -/
theorem Chain.nonempty_of_mem {a b : Obj S} {ls : List (Layer S)} (h : Chain a ls b)
    {L : Layer S} (hL : L ∈ ls) : Nonempty (a ⟶ L.dom) := by
  induction ls generalizing a with
  | nil => cases hL
  | cons M ls ih =>
    obtain ⟨hv, rfl, hc⟩ := h
    rcases List.mem_cons.1 hL with rfl | hL
    · exact ⟨𝟙 _⟩
    · obtain ⟨d⟩ := ih hc hL
      exact ⟨Diagram.ofLayer M hv ≫ d⟩

/-- The top boundary of a well-formed layer is reachable from its bottom boundary. -/
theorem Layer.Valid.nonempty_cod {a : Obj S} {L : Layer S} (hv : L.Valid)
    (h : Nonempty (a ⟶ L.dom)) : Nonempty (a ⟶ L.cod) :=
  h.map fun d => d ≫ Diagram.ofLayer L hv

/-! ## Boundaries of the layers of an instance of the interchange law -/

namespace InterchangeData

variable (x : InterchangeData S)

theorem gh₁_dom : x.gh₁.dom = x.dom := by simp [gh₁, dom, Layer.dom]
theorem gh₂_cod : x.gh₂.cod = x.cod := by simp [gh₂, cod, Layer.cod]
theorem hg₁_dom : x.hg₁.dom = x.dom := by simp [hg₁, dom, Layer.dom]
theorem hg₂_cod : x.hg₂.cod = x.cod := by simp [hg₂, cod, Layer.cod]

end InterchangeData

/-! ## Weights of diagrams -/

namespace Diagram

variable {R : Type w} [CommRing R] (χ : S.Gen → R)

/-- The weight of a list of layers for a function `χ` on generators: the product of the values
of `χ` on the generators of the layers. -/
def weightList (ls : List (Layer S)) : R := (ls.map fun L => χ L.gen).prod

@[simp] theorem weightList_nil : weightList χ [] = 1 := rfl

@[simp] theorem weightList_cons (L : Layer S) (ls : List (Layer S)) :
    weightList χ (L :: ls) = χ L.gen * weightList χ ls := by
  simp [weightList]

theorem weightList_append (ls ms : List (Layer S)) :
    weightList χ (ls ++ ms) = weightList χ ls * weightList χ ms := by
  simp [weightList]

theorem weightList_reverse (ls : List (Layer S)) :
    weightList χ ls.reverse = weightList χ ls := by
  simp [weightList, List.prod_reverse]

@[simp] theorem weightList_one (ls : List (Layer S)) : weightList (fun _ => (1 : R)) ls = 1 := by
  simp [weightList]

theorem weightList_map {S' : Signature.{u₀', u₁', u₂'}} (χ' : S'.Gen → R) (f : Layer S → Layer S')
    (hf : ∀ L, χ' (f L).gen = χ L.gen) (ls : List (Layer S)) :
    weightList χ' (ls.map f) = weightList χ ls := by
  simp [weightList, Function.comp_def, hf]

theorem weightList_map_whisker (ls : List (Layer S)) (u : Obj S) (v : List S.Colour) :
    weightList χ (ls.map (·.whisker u v)) = weightList χ ls :=
  weightList_map χ χ (fun L => L.whisker u v) (fun _ => rfl) ls

variable {a b c : Obj S}

/-- The weight of a diagram: the product of the values of `χ` on its generators. -/
def weight (d : a ⟶ b) : R := weightList χ (layers d)

@[simp] theorem weight_id (a : Obj S) : weight χ (𝟙 a) = 1 := rfl

@[simp] theorem weight_comp (f : a ⟶ b) (g : b ⟶ c) :
    weight χ (f ≫ g) = weight χ f * weight χ g :=
  weightList_append χ _ _

@[simp] theorem weight_eqToHom (h : a = b) : weight χ (eqToHom h) = 1 := by
  simp [weight]

@[simp] theorem weight_cast {a' b' : Obj S} (f : a ⟶ b) (ha : a = a') (hb : b = b') :
    weight χ (cast f ha hb) = weight χ f := rfl

@[simp] theorem weight_whisker (f : a ⟶ b) (u : Obj S) (v : List S.Colour)
    (hw : a.WhiskerOK u v) : weight χ (whisker f u v hw) = weight χ f :=
  weightList_map_whisker χ _ u v

@[simp] theorem weight_ofLayer (L : Layer S) (hv : L.Valid) :
    weight χ (ofLayer L hv) = χ L.gen := by
  simp [weight]

@[simp] theorem weight_one (f : a ⟶ b) : weight (fun _ => (1 : R)) f = 1 :=
  weightList_one _

end Diagram

/-! ## The reduction of soundness to unwhiskered relations -/

section Reduction

variable {R : Type w} [CommRing R] {D : Type w₁} [Category.{w₂} D] [Preadditive D] [Linear R D]

/-- The linear extension of a functor, along a map of diagrams that is intertwined with an
`R`-linear map `T` of Hom-modules. -/
theorem freeLift_map_mapDomain {S₁ : Signature.{u₀', u₁', u₂'}} {F : Obj S ⥤ D}
    {G : Obj S₁ ⥤ D} {a b : Obj S} {a₁ b₁ : Obj S₁} (τ : (a ⟶ b) → (a₁ ⟶ b₁))
    (T : (F.obj a ⟶ F.obj b) →ₗ[R] (G.obj a₁ ⟶ G.obj b₁)) (h : ∀ d, G.map (τ d) = T (F.map d))
    (f : LinDiagram R a b) :
    (freeLift R G).map (Finsupp.mapDomain τ f : LinDiagram R a₁ b₁) =
      T ((freeLift R F).map f) := by
  induction f using Finsupp.induction_linear with
  | zero =>
    rw [Finsupp.mapDomain_zero]
    exact ((freeLift R G).map_zero _ _).trans (by rw [Functor.map_zero, map_zero])
  | add f g hf hg =>
    rw [Finsupp.mapDomain_add]
    exact ((freeLift R G).map_add).trans (by rw [hf, hg, Functor.map_add, map_add])
  | single d r =>
    rw [Finsupp.mapDomain_single, freeLift_map_single, freeLift_map_single, h, map_smul]

namespace Presentation

variable (P : Presentation.{w, v} S R)

/-- **Soundness from unwhiskered relations.** Let `F i` be a family of functors out of the free
2-category such that, whenever a linear combination of diagrams is killed by every `F j`, all
its whiskerings are killed by every `F i`. Then `F i` respects `P` as soon as every `F i`
kills the relations of `P` and the instances of the interchange law. -/
theorem respects_of_whisker {ι : Sort*} (F : ι → Obj S ⥤ D)
    (hwhisk : ∀ (i : ι) {a b : Obj S} (f : LinDiagram R a b) (u : Obj S) (v : List S.Colour)
      (hw : a.WhiskerOK u v), (∀ j, (freeLift R (F j)).map f = 0) →
        (freeLift R (F i)).map (LinDiagram.whisker f u v hw) = 0)
    (hrel : ∀ i r, (freeLift R (F i)).map (P.rel r) = 0)
    (hint : ∀ i (x : InterchangeData S) (hx : x.Valid),
      (freeLift R (F i)).map (InterchangeData.rel R hx) = 0) (i : ι) : P.Respects (F i) where
  rel r u v hw := hwhisk i _ u v hw fun j => hrel j r
  interchange x hx u v hw := hwhisk i _ u v hw fun j => hint j x hx

/-- Every relation of the presentation has a well-formed bottom boundary. This holds for every
presentation of a monoidal signature (`Presentation.wfDom_of_subsingleton`). -/
def WFDom : Prop := ∀ r, (P.dom r).WF

theorem wfDom_of_subsingleton [Subsingleton S.Region] : P.WFDom :=
  fun _ => Signature.ok_of_subsingleton _ _

/-- The bottom boundary of a well-formed instance of the interchange law is well formed. -/
theorem _root_.StringDiagrams.InterchangeData.Valid.wf_dom {x : InterchangeData S}
    (hx : x.Valid) : x.dom.WF :=
  x.gh₁_dom ▸ hx.gh₁.wf_dom

/-- **Soundness from unwhiskered relations**, for functors compatible with whiskering on a
class `A` of objects only (for example the well-formed objects), containing the bottom
boundaries of the relations of `P` and of the instances of the interchange law. -/
theorem respects_of_whisker_on {ι : Sort*} (F : ι → Obj S ⥤ D) (A : Obj S → Prop)
    (hA : ∀ r, A (P.dom r)) (hAx : ∀ x : InterchangeData S, x.Valid → A x.dom)
    (hwhisk : ∀ (i : ι) {a b : Obj S} (f : LinDiagram R a b) (u : Obj S) (v : List S.Colour),
      A a → ∀ (hw : a.WhiskerOK u v), (∀ j, (freeLift R (F j)).map f = 0) →
        (freeLift R (F i)).map (LinDiagram.whisker f u v hw) = 0)
    (hrel : ∀ i r, (freeLift R (F i)).map (P.rel r) = 0)
    (hint : ∀ i (x : InterchangeData S) (hx : x.Valid),
      (freeLift R (F i)).map (InterchangeData.rel R hx) = 0) (i : ι) : P.Respects (F i) where
  rel r u v hw := hwhisk i _ u v (hA r) hw fun j => hrel j r
  interchange x hx u v hw := hwhisk i _ u v (hAx x hx) hw fun j => hint j x hx

end Presentation

/-- The interchange law without whiskering: `[g below h] = (-1)^{|g||h|} [h below g]`. -/
theorem Presentation.diag_ghDiagram (P : Presentation.{w, v} S R) {x : InterchangeData S}
    (hx : x.Valid) :
    P.diag (InterchangeData.ghDiagram hx) =
      ((x.sign : ℤ) : R) • P.diag (InterchangeData.hgDiagram hx) := by
  have hw : x.dom.WhiskerOK ⟨x.start, []⟩ [] := ⟨trivial, rfl, trivial⟩
  have ha : x.dom.whisker ⟨x.start, []⟩ [] = x.dom := Obj.ext rfl (by simp [Obj.whisker])
  have hb : x.cod.whisker ⟨x.start, []⟩ [] = x.cod := Obj.ext rfl (by simp [Obj.whisker])
  have key := P.diag_interchange x hx ⟨x.start, []⟩ [] hw ha hb
  refine Eq.trans (P.diag_eq_of_layers_eq ?_) (key.trans (congrArg _ (P.diag_eq_of_layers_eq ?_)))
  all_goals
    simp [InterchangeData.ghDiagram, InterchangeData.hgDiagram, InterchangeData.gh₁,
      InterchangeData.gh₂, InterchangeData.hg₁, InterchangeData.hg₂, Layer.whisker]

theorem InterchangeData.sign_mul_self (x : InterchangeData S) : x.sign * x.sign = 1 := by
  unfold sign; split <;> norm_num

theorem InterchangeData.sign_cast_mul_self (x : InterchangeData S) :
    ((x.sign : ℤ) : R) * ((x.sign : ℤ) : R) = 1 := by
  rw [← Int.cast_mul, x.sign_mul_self, Int.cast_one]

theorem InterchangeData.sign_cast_mul_self_assoc (x : InterchangeData S) (r : R) :
    ((x.sign : ℤ) : R) * (r * ((x.sign : ℤ) : R)) = r := by
  rw [mul_comm r, ← mul_assoc, x.sign_cast_mul_self, one_mul]

theorem InterchangeData.weight_hg (χ : S.Gen → R) {x : InterchangeData S} (hx : x.Valid) :
    Diagram.weight χ (InterchangeData.hgDiagram hx) =
      Diagram.weight χ (InterchangeData.ghDiagram hx) := by
  simp [Diagram.weight, InterchangeData.ghDiagram, InterchangeData.hgDiagram,
    InterchangeData.gh₁, InterchangeData.gh₂, InterchangeData.hg₁, InterchangeData.hg₂, mul_comm]

/-- The interchange law without whiskering, read the other way. -/
theorem Presentation.diag_hgDiagram (P : Presentation.{w, v} S R) {x : InterchangeData S}
    (hx : x.Valid) :
    P.diag (InterchangeData.hgDiagram hx) =
      ((x.sign : ℤ) : R) • P.diag (InterchangeData.ghDiagram hx) := by
  rw [P.diag_ghDiagram hx, smul_smul, ← Int.cast_mul, x.sign_mul_self, Int.cast_one, one_smul]

end Reduction

/-! ## Layer maps -/

/-- A map of layers from the signature `S` to the signature `S'`: images of objects and of
layers, compatible with the boundaries of well-formed layers. The image of a layer may depend
on the strands around its generator; it need not come from a map of signatures. -/
structure LayerMap (S : Signature.{u₀, u₁, u₂}) (S' : Signature.{u₀', u₁', u₂'}) where
  /-- The image of an object. -/
  obj : Obj S → Obj S'
  /-- The image of a layer. -/
  layer : Layer S → Layer S'
  /-- Well-formed layers go to well-formed layers. -/
  valid : ∀ {L : Layer S}, L.Valid → (layer L).Valid
  /-- Compatibility with bottom boundaries. -/
  dom_eq : ∀ {L : Layer S}, L.Valid → (layer L).dom = obj L.dom
  /-- Compatibility with top boundaries. -/
  cod_eq : ∀ {L : Layer S}, L.Valid → (layer L).cod = obj L.cod

namespace LayerMap

variable {S' : Signature.{u₀', u₁', u₂'}} (φ : LayerMap S S')

theorem chain {a b : Obj S} {ls : List (Layer S)} (h : Chain a ls b) :
    Chain (φ.obj a) (ls.map φ.layer) (φ.obj b) := by
  induction ls generalizing a with
  | nil => exact congrArg φ.obj h
  | cons L ls ih =>
    obtain ⟨hv, rfl, hc⟩ := h
    exact ⟨φ.valid hv, φ.dom_eq hv, by rw [φ.cod_eq hv]; exact ih hc⟩

/-- The image of a diagram: the images of its layers. -/
def map {a b : Obj S} (d : a ⟶ b) : φ.obj a ⟶ φ.obj b :=
  Diagram.mk ((Diagram.layers d).map φ.layer) (φ.chain (Diagram.chain d))

@[simp] theorem layers_map {a b : Obj S} (d : a ⟶ b) :
    Diagram.layers (φ.map d) = (Diagram.layers d).map φ.layer := rfl

@[simp] theorem map_id (a : Obj S) : φ.map (𝟙 a) = 𝟙 (φ.obj a) := rfl

@[simp] theorem map_comp {a b c : Obj S} (f : a ⟶ b) (g : b ⟶ c) :
    φ.map (f ≫ g) = φ.map f ≫ φ.map g :=
  Diagram.ext List.map_append

theorem map_cast {a b a' b' : Obj S} (d : a ⟶ b) (ha : a = a') (hb : b = b') :
    φ.map (Diagram.cast d ha hb) =
      Diagram.cast (φ.map d) (congrArg φ.obj ha) (congrArg φ.obj hb) := rfl

theorem map_eqToHom {a b : Obj S} (h : a = b) : φ.map (eqToHom h) = eqToHom (congrArg φ.obj h) :=
  Diagram.ext (by simp)

theorem map_ofLayer (L : Layer S) (hv : L.Valid) :
    φ.map (Diagram.ofLayer L hv) =
      Diagram.layer (φ.layer L) (φ.valid hv) (φ.dom_eq hv) (φ.cod_eq hv) := rfl

/-- The functor of free 2-categories induced by a layer map. -/
@[simps]
def functor : Obj S ⥤ Obj S' where
  obj := φ.obj
  map := φ.map
  map_id := φ.map_id
  map_comp := φ.map_comp

/-- The composite of layer maps. -/
@[simps]
def comp {S'' : Signature.{u₀, u₁, u₂}} (ψ : LayerMap S' S'') : LayerMap S S'' where
  obj := ψ.obj ∘ φ.obj
  layer := ψ.layer ∘ φ.layer
  valid hv := ψ.valid (φ.valid hv)
  dom_eq hv := by simp [ψ.dom_eq (φ.valid hv), φ.dom_eq hv]
  cod_eq hv := by simp [ψ.cod_eq (φ.valid hv), φ.cod_eq hv]

/-- The identity layer map. -/
@[simps]
protected def id (S : Signature.{u₀, u₁, u₂}) : LayerMap S S where
  obj := id
  layer := id
  valid hv := hv
  dom_eq _ := rfl
  cod_eq _ := rfl

/-! ### Linear combinations and presented categories -/

section Presented

variable {R : Type w} [CommRing R]

/-- The image of a linear combination of diagrams. -/
def lin {a b : Obj S} (f : LinDiagram R a b) : LinDiagram R (φ.obj a) (φ.obj b) :=
  Finsupp.mapDomain φ.map f

@[simp] theorem lin_of {a b : Obj S} (d : a ⟶ b) :
    φ.lin (LinDiagram.of d : LinDiagram R a b) = LinDiagram.of (φ.map d) :=
  Finsupp.mapDomain_single

/-- `φ.lin` as an `R`-linear map. -/
def linMap (a b : Obj S) : LinDiagram R a b →ₗ[R] LinDiagram R (φ.obj a) (φ.obj b) :=
  Finsupp.lmapDomain R R φ.map

@[simp] theorem linMap_apply {a b : Obj S} (f : LinDiagram R a b) :
    φ.linMap a b f = φ.lin f := rfl

theorem lin_add {a b : Obj S} (f g : LinDiagram R a b) : φ.lin (f + g) = φ.lin f + φ.lin g :=
  (φ.linMap a b).map_add f g

theorem lin_sub {a b : Obj S} (f g : LinDiagram R a b) : φ.lin (f - g) = φ.lin f - φ.lin g :=
  (φ.linMap a b).map_sub f g

theorem lin_smul {a b : Obj S} (r : R) (f : LinDiagram R a b) : φ.lin (r • f) = r • φ.lin f :=
  (φ.linMap a b).map_smul r f

variable (Q : Presentation.{w, v'} S' R) (χ : S.Gen → R)

/-- The functor `Obj S ⥤ Q.Presented` induced by a layer map `φ` and weights `χ` of the
generators: a diagram `d` goes to `weight χ d • [φ d]`. -/
def toPresented : Obj S ⥤ Q.Presented where
  obj a := Q.obj (φ.obj a)
  map d := Diagram.weight χ d • Q.diag (φ.map d)
  map_id a := by rw [Diagram.weight_id, one_smul, map_id, Q.diag_id]
  map_comp f g := by
    rw [Diagram.weight_comp, map_comp, Q.diag_comp, Linear.smul_comp, Linear.comp_smul,
      smul_smul, mul_comm]

@[simp] theorem toPresented_obj (a : Obj S) : (φ.toPresented Q χ).obj a = Q.obj (φ.obj a) := rfl

@[simp] theorem toPresented_map {a b : Obj S} (d : a ⟶ b) :
    (φ.toPresented Q χ).map d = Diagram.weight χ d • Q.diag (φ.map d) := rfl

theorem freeLift_toPresented_of {a b : Obj S} (d : a ⟶ b) :
    (freeLift R (φ.toPresented Q χ)).map (LinDiagram.of d : LinDiagram R a b) =
      Diagram.weight χ d • Q.diag (φ.map d) :=
  freeLift_map_of _ d

/-- With trivial weights, the linear extension is the class of the image. -/
theorem freeLift_toPresented_one {a b : Obj S} (f : LinDiagram R a b) :
    (freeLift R (φ.toPresented Q fun _ => 1)).map f = Q.lin (φ.lin f) := by
  induction f using Finsupp.induction_linear with
  | zero => rw [Functor.map_zero, lin, Finsupp.mapDomain_zero, Q.lin_zero]
  | add f g hf hg =>
    rw [Functor.map_add, hf, hg, lin_add, Q.lin_add]
  | single d r =>
    rw [freeLift_map_single, lin, Finsupp.mapDomain_single, Q.lin_single, toPresented_map,
      Diagram.weight_one, one_smul]

/-! ### Whiskering -/

/-- Compatibility of a family of layer maps with whiskering: whiskering a layer reachable from
`a` by `u` on the left and `v` on the right and then applying `φ i` is the same as applying
`φ (idx i a u v)` and then whiskering by `left i a u v` and `right i a u v`. -/
structure WhiskerData {ι : Type*} (φ : ι → LayerMap S S') where
  /-- The objects on which compatibility with whiskering is required (for example all objects,
  or the well-formed ones). -/
  Admissible : Obj S → Prop
  /-- The bottom boundaries of the instances of the interchange law are admissible. -/
  admissible_interchange : ∀ {x : InterchangeData S}, x.Valid → Admissible x.dom
  /-- The layer map to apply before whiskering. -/
  idx : ι → Obj S → Obj S → List S.Colour → ι
  /-- The object by which images are whiskered on the left. -/
  left : ι → Obj S → Obj S → List S.Colour → Obj S'
  /-- The word by which images are whiskered on the right. -/
  right : ι → Obj S → Obj S → List S.Colour → List S'.Colour
  /-- The whiskering of images is well formed. -/
  whiskerOK : ∀ {i : ι} {a u : Obj S} {v : List S.Colour}, Admissible a → a.WhiskerOK u v →
    ((φ (idx i a u v)).obj a).WhiskerOK (left i a u v) (right i a u v)
  /-- Compatibility on objects reachable from `a`. -/
  obj_whisker : ∀ {i : ι} {a u : Obj S} {v : List S.Colour}, Admissible a → a.WhiskerOK u v →
    ∀ {b : Obj S}, Nonempty (a ⟶ b) →
      ((φ (idx i a u v)).obj b).whisker (left i a u v) (right i a u v) =
        (φ i).obj (b.whisker u v)
  /-- Compatibility on layers reachable from `a`. -/
  layer_whisker : ∀ {i : ι} {a u : Obj S} {v : List S.Colour}, Admissible a → a.WhiskerOK u v →
    ∀ {L : Layer S}, L.Valid → Nonempty (a ⟶ L.dom) →
      (φ i).layer (L.whisker u v) =
        ((φ (idx i a u v)).layer L).whisker (left i a u v) (right i a u v)

namespace WhiskerData

variable {ι : Type*} {φ : ι → LayerMap S S'} (W : WhiskerData φ)

/-- Compatibility of the image of a diagram with whiskering. -/
theorem map_whisker {i : ι} {a b : Obj S} (d : a ⟶ b) (u : Obj S) (v : List S.Colour)
    (ha : W.Admissible a) (hw : a.WhiskerOK u v) :
    (φ i).map (Diagram.whisker d u v hw) =
      Diagram.cast (Diagram.whisker ((φ (W.idx i a u v)).map d) (W.left i a u v)
          (W.right i a u v) (W.whiskerOK ha hw))
        (W.obj_whisker ha hw ⟨𝟙 a⟩) (W.obj_whisker ha hw ⟨d⟩) := by
  apply Diagram.ext
  simp only [layers_map, Diagram.layers_whisker, Diagram.layers_cast, List.map_map]
  refine List.map_congr_left fun L hL => ?_
  exact W.layer_whisker ha hw ((Diagram.chain d).valid_of_mem hL)
    ((Diagram.chain d).nonempty_of_mem hL)

theorem toPresented_map_whisker {i : ι} {a b : Obj S} (d : a ⟶ b) (u : Obj S)
    (v : List S.Colour) (ha : W.Admissible a) (hw : a.WhiskerOK u v) :
    ((φ i).toPresented Q χ).map (Diagram.whisker d u v hw) =
      eqToHom (congrArg Q.obj (W.obj_whisker ha hw ⟨𝟙 a⟩).symm) ≫
        Q.whisk (((φ (W.idx i a u v)).toPresented Q χ).map d) (W.left i a u v)
          (W.right i a u v) ≫
        eqToHom (congrArg Q.obj (W.obj_whisker ha hw ⟨d⟩)) := by
  rw [toPresented_map, toPresented_map, W.map_whisker _ _ _ ha, Diagram.weight_whisker, Q.diag_cast,
    Q.whisk_smul, Q.whisk_diag _ _ _ (W.whiskerOK ha hw), Linear.smul_comp, Linear.comp_smul]

/-- The hypothesis on whiskering of `Presentation.respects_of_whisker`, for the functors
induced by a family of layer maps compatible with whiskering. -/
theorem freeLift_whisker_eq_zero {i : ι} {a b : Obj S} (f : LinDiagram R a b) (u : Obj S)
    (v : List S.Colour) (ha : W.Admissible a) (hw : a.WhiskerOK u v)
    (hf : (freeLift R ((φ (W.idx i a u v)).toPresented Q χ)).map f = 0) :
    (freeLift R ((φ i).toPresented Q χ)).map (LinDiagram.whisker f u v hw) = 0 := by
  by_cases h0 : f = 0
  · subst h0
    rw [show LinDiagram.whisker (0 : LinDiagram R a b) u v hw = 0 from Finsupp.mapDomain_zero,
      Functor.map_zero]
  obtain ⟨d₀, -⟩ := Finsupp.ne_iff.mp h0
  have ea := congrArg Q.obj (W.obj_whisker (i := i) ha hw ⟨𝟙 a⟩).symm
  have eb := congrArg Q.obj (W.obj_whisker (i := i) ha hw ⟨d₀⟩)
  let T : (Q.obj ((φ (W.idx i a u v)).obj a) ⟶ Q.obj ((φ (W.idx i a u v)).obj b)) →ₗ[R]
      (Q.obj ((φ i).obj (a.whisker u v)) ⟶ Q.obj ((φ i).obj (b.whisker u v))) :=
    { toFun := fun x => eqToHom ea ≫ Q.whisk x (W.left i a u v) (W.right i a u v) ≫ eqToHom eb
      map_add' := fun x y => by
        simp only [Q.whisk_add, Preadditive.add_comp, Preadditive.comp_add]
      map_smul' := fun r x => by
        simp only [Q.whisk_smul, Linear.smul_comp, Linear.comp_smul, RingHom.id_apply] }
  have := freeLift_map_mapDomain (F := (φ (W.idx i a u v)).toPresented Q χ)
    (G := (φ i).toPresented Q χ) (fun d => Diagram.whisker d u v hw) T
    (fun d => W.toPresented_map_whisker Q χ d u v ha hw) f
  exact this.trans (by rw [hf, map_zero])

end WhiskerData

/-! ### Soundness -/

variable {ι : Type*} (P : Presentation.{w, v} S R) {Q χ}

/-- **Functors from layer maps.** A family of layer maps compatible with whiskering, with
weights `χ`, respects a presentation `P` as soon as the relations of `P` and the interchange
law are respected without whiskering. -/
theorem respects {φ : ι → LayerMap S S'} (W : WhiskerData φ)
    (hadm : ∀ r, W.Admissible (P.dom r))
    (hrel : ∀ i r, (freeLift R ((φ i).toPresented Q χ)).map (P.rel r) = 0)
    (hint : ∀ i (x : InterchangeData S) (hx : x.Valid),
      (freeLift R ((φ i).toPresented Q χ)).map (InterchangeData.rel R hx) = 0) (i : ι) :
    P.Respects ((φ i).toPresented Q χ) :=
  P.respects_of_whisker_on (fun i => (φ i).toPresented Q χ) W.Admissible hadm
    (fun _ => W.admissible_interchange)
    (fun _ _ _ f u v ha hw hf => W.freeLift_whisker_eq_zero Q χ f u v ha hw (hf _)) hrel hint i

/-- The functor `P.Presented ⥤ Q.Presented` induced by a family of layer maps compatible with
whiskering (`LayerMap.respects`): the class of a diagram `d` goes to `weight χ d • [φ i d]`
(`LayerMap.lift_diag`). -/
def lift {φ : ι → LayerMap S S'} (W : WhiskerData φ)
    (hadm : ∀ r, W.Admissible (P.dom r))
    (hrel : ∀ i r, (freeLift R ((φ i).toPresented Q χ)).map (P.rel r) = 0)
    (hint : ∀ i (x : InterchangeData S) (hx : x.Valid),
      (freeLift R ((φ i).toPresented Q χ)).map (InterchangeData.rel R hx) = 0) (i : ι) :
    P.Presented ⥤ Q.Presented :=
  P.lift (respects P W hadm hrel hint i)

section Lift

variable {P} {φ : ι → LayerMap S S'} (W : WhiskerData φ) (hadm : ∀ r, W.Admissible (P.dom r))
  (hrel : ∀ i r, (freeLift R ((φ i).toPresented Q χ)).map (P.rel r) = 0)
  (hint : ∀ i (x : InterchangeData S) (hx : x.Valid),
    (freeLift R ((φ i).toPresented Q χ)).map (InterchangeData.rel R hx) = 0) (i : ι)

instance lift_additive : (lift P W hadm hrel hint i).Additive := P.lift_additive _

instance lift_linear : (lift P W hadm hrel hint i).Linear R := P.lift_linear _

@[simp] theorem lift_obj (a : Obj S) : (lift P W hadm hrel hint i).obj (P.obj a) = Q.obj ((φ i).obj a) :=
  rfl

@[simp] theorem lift_diag {a b : Obj S} (d : a ⟶ b) :
    (lift P W hadm hrel hint i).map (P.diag d) = Diagram.weight χ d • Q.diag ((φ i).map d) :=
  P.lift_diag _ d

theorem lift_lin {a b : Obj S} (f : LinDiagram R a b) :
    (lift P W hadm hrel hint i).map (P.lin f) = (freeLift R ((φ i).toPresented Q χ)).map f :=
  P.lift_lin _ f

/-- The induced functors commute with whiskering: whiskering by `u` and `v` in `P` becomes
whiskering by `W.left i a u v` and `W.right i a u v` in `Q`. -/
theorem lift_whisk {a b : Obj S} (f : P.obj a ⟶ P.obj b) {u : Obj S} {v : List S.Colour}
    (ha : W.Admissible a) (hw : a.WhiskerOK u v) (hb : Nonempty (a ⟶ b)) :
    (lift P W hadm hrel hint i).map (P.whisk f u v) =
      eqToHom (congrArg Q.obj (W.obj_whisker ha hw ⟨𝟙 a⟩).symm) ≫
        Q.whisk ((lift P W hadm hrel hint (W.idx i a u v)).map f) (W.left i a u v)
          (W.right i a u v) ≫
        eqToHom (congrArg Q.obj (W.obj_whisker ha hw hb)) := by
  obtain ⟨f, rfl⟩ := P.lin_surjective f
  rw [Presentation.whisk_lin, LinDiagram.whisk_of_ok _ hw, lift_lin, lift_lin]
  exact freeLift_map_mapDomain (F := (φ (W.idx i a u v)).toPresented Q χ)
    (G := (φ i).toPresented Q χ) (fun d => Diagram.whisker d u v hw)
    { toFun := fun x => eqToHom (congrArg Q.obj (W.obj_whisker ha hw ⟨𝟙 a⟩).symm) ≫
        Q.whisk x (W.left i a u v) (W.right i a u v) ≫
          eqToHom (congrArg Q.obj (W.obj_whisker ha hw hb))
      map_add' := fun x y => by
        simp only [Q.whisk_add, Preadditive.add_comp, Preadditive.comp_add]
      map_smul' := fun r x => by
        simp only [Q.whisk_smul, Linear.smul_comp, Linear.comp_smul, RingHom.id_apply] }
    (fun d => W.toPresented_map_whisker Q χ d u v ha hw) f

end Lift

/-! ### The interchange law -/

variable (Q χ)

/-- A layer map sending the four layers of an instance `x` of the interchange law to the four
layers of an instance `x'` with the same Koszul sign respects the interchange law. -/
theorem toPresented_interchange {x : InterchangeData S} (hx : x.Valid) (x' : InterchangeData S')
    (h₁ : φ.layer x.gh₁ = x'.gh₁) (h₂ : φ.layer x.gh₂ = x'.gh₂) (h₃ : φ.layer x.hg₁ = x'.hg₁)
    (h₄ : φ.layer x.hg₂ = x'.hg₂) (hs : x'.sign = x.sign) :
    (freeLift R (φ.toPresented Q χ)).map (InterchangeData.rel R hx) = 0 := by
  have hx' : x'.Valid :=
    ⟨h₁ ▸ φ.valid hx.gh₁, h₂ ▸ φ.valid hx.gh₂, h₃ ▸ φ.valid hx.hg₁, h₄ ▸ φ.valid hx.hg₂⟩
  have ha : φ.obj x.dom = x'.dom := by
    rw [← x.gh₁_dom, ← φ.dom_eq hx.gh₁, h₁, x'.gh₁_dom]
  have hb : φ.obj x.cod = x'.cod := by
    rw [← x.gh₂_cod, ← φ.cod_eq hx.gh₂, h₂, x'.gh₂_cod]
  have e₁ := Q.diag_eq_of_layers_eq' (φ.map (InterchangeData.ghDiagram hx))
    (InterchangeData.ghDiagram hx') ha hb (by simp [InterchangeData.ghDiagram, h₁, h₂])
  have e₂ := Q.diag_eq_of_layers_eq' (φ.map (InterchangeData.hgDiagram hx))
    (InterchangeData.hgDiagram hx') ha hb (by simp [InterchangeData.hgDiagram, h₃, h₄])
  rw [InterchangeData.rel, Functor.map_sub, Functor.map_smul, freeLift_toPresented_of,
    freeLift_toPresented_of, e₁, e₂, Q.diag_ghDiagram hx', hs, InterchangeData.weight_hg,
    sub_eq_zero]
  simp only [Linear.smul_comp, Linear.comp_smul, smul_comm (Diagram.weight χ _)]

/-- A layer map sending the four layers of an instance `x` of the interchange law to the four
layers of an instance `x'` with the roles of the two generators exchanged (as for a reflection
in a vertical axis), with the same Koszul sign, respects the interchange law. -/
theorem toPresented_interchange_swap {x : InterchangeData S} (hx : x.Valid)
    (x' : InterchangeData S') (h₁ : φ.layer x.gh₁ = x'.hg₁) (h₂ : φ.layer x.gh₂ = x'.hg₂)
    (h₃ : φ.layer x.hg₁ = x'.gh₁) (h₄ : φ.layer x.hg₂ = x'.gh₂) (hs : x'.sign = x.sign) :
    (freeLift R (φ.toPresented Q χ)).map (InterchangeData.rel R hx) = 0 := by
  have hx' : x'.Valid :=
    ⟨h₃ ▸ φ.valid hx.hg₁, h₄ ▸ φ.valid hx.hg₂, h₁ ▸ φ.valid hx.gh₁, h₂ ▸ φ.valid hx.gh₂⟩
  have ha : φ.obj x.dom = x'.dom := by
    rw [← x.gh₁_dom, ← φ.dom_eq hx.gh₁, h₁, x'.hg₁_dom]
  have hb : φ.obj x.cod = x'.cod := by
    rw [← x.gh₂_cod, ← φ.cod_eq hx.gh₂, h₂, x'.hg₂_cod]
  have e₁ := Q.diag_eq_of_layers_eq' (φ.map (InterchangeData.ghDiagram hx))
    (InterchangeData.hgDiagram hx') ha hb (by simp [InterchangeData.ghDiagram,
      InterchangeData.hgDiagram, h₁, h₂])
  have e₂ := Q.diag_eq_of_layers_eq' (φ.map (InterchangeData.hgDiagram hx))
    (InterchangeData.ghDiagram hx') ha hb (by simp [InterchangeData.ghDiagram,
      InterchangeData.hgDiagram, h₃, h₄])
  rw [InterchangeData.rel, Functor.map_sub, Functor.map_smul, freeLift_toPresented_of,
    freeLift_toPresented_of, e₁, e₂, Q.diag_ghDiagram hx', hs, InterchangeData.weight_hg,
    sub_eq_zero]
  simp only [Linear.smul_comp, Linear.comp_smul, smul_smul, x.sign_cast_mul_self_assoc]

/-! ### Degrees -/

section Degree

variable {A : Type*} [AddCommMonoid A] (deg : S.Gen → A) (deg' : S'.Gen → A)

/-- A layer map preserves degrees: the generator of the image of a well-formed layer has the
degree of the generator of the layer. -/
def PreservesDeg : Prop := ∀ {L : Layer S}, L.Valid → deg' (φ.layer L).gen = deg L.gen

variable {φ deg deg'}

theorem PreservesDeg.degree_map (h : φ.PreservesDeg deg deg') {a b : Obj S} (d : a ⟶ b) :
    Diagram.degree deg' (φ.map d) = Diagram.degree deg d := by
  simp only [Diagram.degree, layers_map, List.map_map]
  congr 1
  exact List.map_congr_left fun L hL => h ((Diagram.chain d).valid_of_mem hL)

/-- Parity-preserving layer maps preserve the parity grading. -/
theorem preservesDeg_parityDeg
    (h : ∀ {L : Layer S}, L.Valid → S'.odd (φ.layer L).gen = S.odd L.gen) :
    φ.PreservesDeg (Presentation.parityDeg S) (Presentation.parityDeg S') := fun hv => by
  simp only [Presentation.parityDeg, h hv]

theorem PreservesDeg.toPresented_mem_homDeg (h : φ.PreservesDeg deg deg') {a b : Obj S}
    {f : LinDiagram R a b} {e : A} (hf : f ∈ LinDiagram.homDeg R deg a b e) :
    (freeLift R (φ.toPresented Q χ)).map f ∈ Q.homDeg deg' (φ.obj a) (φ.obj b) e := by
  rw [LinDiagram.homDeg, Finsupp.supported_eq_span_single] at hf
  induction hf using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨d, hd, rfl⟩ := hy
    rw [freeLift_map_single, toPresented_map, smul_smul]
    exact Submodule.smul_mem _ _ (Presentation.diag_mem_homDeg' ((h.degree_map d).trans hd))
  | zero => rw [Functor.map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [Functor.map_add]; exact Submodule.add_mem _ hy hz
  | smul r y _ hy => rw [Functor.map_smul]; exact Submodule.smul_mem _ r hy

variable {Q χ}

/-- **Degree-preserving layer maps induce degree-preserving functors.** -/
theorem lift_mem_homDeg {P : Presentation.{w, v} S R} {φ : ι → LayerMap S S'} (W : WhiskerData φ)
    (hadm : ∀ r, W.Admissible (P.dom r))
    (hrel : ∀ i r, (freeLift R ((φ i).toPresented Q χ)).map (P.rel r) = 0)
    (hint : ∀ i (x : InterchangeData S) (hx : x.Valid),
      (freeLift R ((φ i).toPresented Q χ)).map (InterchangeData.rel R hx) = 0) (i : ι)
    (h : (φ i).PreservesDeg deg deg') {a b : Obj S} {x : P.obj a ⟶ P.obj b} {e : A}
    (hx : x ∈ P.homDeg deg a b e) :
    (lift P W hadm hrel hint i).map x ∈ Q.homDeg deg' ((φ i).obj a) ((φ i).obj b) e := by
  obtain ⟨f, hf, rfl⟩ := Presentation.mem_homDeg_iff.mp hx
  rw [lift_lin]
  exact h.toPresented_mem_homDeg Q χ hf

end Degree

end Presented

end LayerMap

end StringDiagrams

end
