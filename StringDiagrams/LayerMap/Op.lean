import StringDiagrams.LayerMap.Basic
import Mathlib.CategoryTheory.Preadditive.Opposite

/-!
# Contravariant layer maps

A *contravariant* layer map (`OpLayerMap S S'`) sends a layer `L` to a layer from the image of
the top boundary of `L` to the image of its bottom boundary. It reverses the order of the
layers of a diagram, so a diagram `d : a ⟶ b` goes to a diagram `φ.map d : φ.obj b ⟶ φ.obj a`
(`OpLayerMap.map`, `OpLayerMap.map_comp`), and it induces functors into opposite categories:
`OpLayerMap.functor : Obj S ⥤ (Obj S')ᵒᵖ` and, for a presentation `Q` of `S'` and weights
`χ : S.Gen → R`, `OpLayerMap.toPresented Q χ : Obj S ⥤ Q.Presentedᵒᵖ`. The typical example is
a reflection of diagrams in a horizontal axis ("upside down"), possibly combined with a change
of labels; it preserves the order of 1-morphisms and reverses the order of 2-morphisms.

As for covariant layer maps (`StringDiagrams.LayerMap.Basic`), a family of contravariant layer
maps compatible with whiskering (`OpLayerMap.WhiskerData`) descends to functors
`P.Presented ⥤ Q.Presentedᵒᵖ` (`OpLayerMap.lift`) as soon as the relations of `P` and the
interchange law are respected without whiskering. For the interchange law it suffices that the
four layers of an instance go to the four layers of an instance of the target, either as for a
reflection in a horizontal axis (`OpLayerMap.toPresented_interchange_reflect`: the lower layer
of the image is the image of the upper layer, on the same side) or as for a rotation by a half
turn (`OpLayerMap.toPresented_interchange_rotate`: the generators also change sides), with the
same Koszul sign.

## Signs

No signs are needed for well-definedness: an instance of the interchange law
`[g below h] = (-1)^{|g||h|} [h below g]` is sent to `[h' below g'] = (-1)^{|g||h|} [g' below h']`,
which is the same instance of the interchange law of the target, as the Koszul sign is
symmetric. For odd generators, the reflection is then *not* a superfunctor of the naive
opposite supercategory with respect to horizontal composition: see
`StringDiagrams.LayerMap.Generators` for the resulting Koszul signs.
-/

noncomputable section

namespace CategoryTheory

universe w₀ v₀ u₀

/-- The opposite of an `R`-linear category is `R`-linear, with `r • f = (r • f.unop).op`.
(A local copy, to be replaced by the corresponding general instance.) -/
private instance linearOppositeOfLinear (R : Type w₀) [Semiring R] (C : Type u₀) [Category.{v₀} C]
    [Preadditive C] [Linear R C] : Linear R Cᵒᵖ where
  homModule _ _ :=
    { smul := fun r f => (r • f.unop).op
      one_smul := fun f => Quiver.Hom.unop_inj (one_smul R f.unop)
      mul_smul := fun r s f => Quiver.Hom.unop_inj (mul_smul r s f.unop)
      smul_zero := fun r => Quiver.Hom.unop_inj (smul_zero r)
      smul_add := fun r f g => Quiver.Hom.unop_inj (smul_add r f.unop g.unop)
      add_smul := fun r s f => Quiver.Hom.unop_inj (add_smul r s f.unop)
      zero_smul := fun f => Quiver.Hom.unop_inj (zero_smul R f.unop) }
  smul_comp _ _ _ r f g := Quiver.Hom.unop_inj (Linear.comp_smul _ _ _ g.unop r f.unop)
  comp_smul _ _ _ f r g := Quiver.Hom.unop_inj (Linear.smul_comp _ _ _ r g.unop f.unop)

end CategoryTheory

namespace StringDiagrams

open CategoryTheory Opposite

universe w v v' u₀ u₁ u₂ u₀' u₁' u₂'

variable {S : Signature.{u₀, u₁, u₂}}

/-- A contravariant map of layers from `S` to `S'`: images of objects and of layers, where the
image of a well-formed layer goes from the image of its top boundary to the image of its bottom
boundary. -/
structure OpLayerMap (S : Signature.{u₀, u₁, u₂}) (S' : Signature.{u₀', u₁', u₂'}) where
  /-- The image of an object. -/
  obj : Obj S → Obj S'
  /-- The image of a layer. -/
  layer : Layer S → Layer S'
  /-- Well-formed layers go to well-formed layers. -/
  valid : ∀ {L : Layer S}, L.Valid → (layer L).Valid
  /-- The bottom boundary of the image is the image of the top boundary. -/
  dom_eq : ∀ {L : Layer S}, L.Valid → (layer L).dom = obj L.cod
  /-- The top boundary of the image is the image of the bottom boundary. -/
  cod_eq : ∀ {L : Layer S}, L.Valid → (layer L).cod = obj L.dom

namespace OpLayerMap

variable {S' : Signature.{u₀', u₁', u₂'}} (φ : OpLayerMap S S')

theorem chain {a b : Obj S} {ls : List (Layer S)} (h : Chain a ls b) :
    Chain (φ.obj b) (ls.map φ.layer).reverse (φ.obj a) := by
  induction ls generalizing a with
  | nil => exact (congrArg φ.obj h).symm
  | cons L ls ih =>
    obtain ⟨hv, rfl, hc⟩ := h
    rw [List.map_cons, List.reverse_cons]
    exact (ih hc).append ⟨φ.valid hv, φ.dom_eq hv, φ.cod_eq hv⟩

/-- The image of a diagram `d : a ⟶ b`, a diagram `φ.obj b ⟶ φ.obj a`: the images of the layers
of `d`, in the reverse order. -/
def map {a b : Obj S} (d : a ⟶ b) : φ.obj b ⟶ φ.obj a :=
  Diagram.mk ((Diagram.layers d).map φ.layer).reverse (φ.chain (Diagram.chain d))

@[simp] theorem layers_map {a b : Obj S} (d : a ⟶ b) :
    Diagram.layers (φ.map d) = ((Diagram.layers d).map φ.layer).reverse := rfl

@[simp] theorem map_id (a : Obj S) : φ.map (𝟙 a) = 𝟙 (φ.obj a) := rfl

@[simp] theorem map_comp {a b c : Obj S} (f : a ⟶ b) (g : b ⟶ c) :
    φ.map (f ≫ g) = φ.map g ≫ φ.map f :=
  Diagram.ext (by simp)

theorem map_cast {a b a' b' : Obj S} (d : a ⟶ b) (ha : a = a') (hb : b = b') :
    φ.map (Diagram.cast d ha hb) =
      Diagram.cast (φ.map d) (congrArg φ.obj hb) (congrArg φ.obj ha) := rfl

theorem map_eqToHom {a b : Obj S} (h : a = b) :
    φ.map (eqToHom h) = eqToHom (congrArg φ.obj h.symm) :=
  Diagram.ext (by simp)

theorem map_ofLayer (L : Layer S) (hv : L.Valid) :
    φ.map (Diagram.ofLayer L hv) =
      Diagram.layer (φ.layer L) (φ.valid hv) (φ.dom_eq hv) (φ.cod_eq hv) := rfl

/-- The functor of free 2-categories into the opposite category induced by a contravariant layer
map. -/
@[simps]
def functor : Obj S ⥤ (Obj S')ᵒᵖ where
  obj a := op (φ.obj a)
  map d := (φ.map d).op
  map_id _ := rfl
  map_comp f g := by rw [map_comp]; rfl

/-- The composite of two contravariant layer maps is a (covariant) layer map. -/
@[simps]
def comp {S'' : Signature.{u₀, u₁, u₂}} (ψ : OpLayerMap S' S'') : LayerMap S S'' where
  obj := ψ.obj ∘ φ.obj
  layer := ψ.layer ∘ φ.layer
  valid hv := ψ.valid (φ.valid hv)
  dom_eq hv := by simp [ψ.dom_eq (φ.valid hv), φ.cod_eq hv]
  cod_eq hv := by simp [ψ.cod_eq (φ.valid hv), φ.dom_eq hv]

theorem comp_map {S'' : Signature.{u₀, u₁, u₂}} (ψ : OpLayerMap S' S'') {a b : Obj S}
    (d : a ⟶ b) : (φ.comp ψ).map d = ψ.map (φ.map d) :=
  Diagram.ext (by simp [List.map_reverse, Function.comp_def])

/-- A contravariant layer map followed by a covariant one. -/
@[simps]
def compLayerMap {S'' : Signature.{u₀, u₁, u₂}} (ψ : LayerMap S' S'') : OpLayerMap S S'' where
  obj := ψ.obj ∘ φ.obj
  layer := ψ.layer ∘ φ.layer
  valid hv := ψ.valid (φ.valid hv)
  dom_eq hv := by simp [ψ.dom_eq (φ.valid hv), φ.dom_eq hv]
  cod_eq hv := by simp [ψ.cod_eq (φ.valid hv), φ.cod_eq hv]

/-! ### Presented categories -/

section Presented

variable {R : Type w} [CommRing R]

/-- The image of a linear combination of diagrams. -/
def lin {a b : Obj S} (f : LinDiagram R a b) : LinDiagram R (φ.obj b) (φ.obj a) :=
  Finsupp.mapDomain φ.map f

@[simp] theorem lin_of {a b : Obj S} (d : a ⟶ b) :
    φ.lin (LinDiagram.of d : LinDiagram R a b) = LinDiagram.of (φ.map d) :=
  Finsupp.mapDomain_single

/-- `φ.lin` as an `R`-linear map. -/
def linMap (a b : Obj S) : LinDiagram R a b →ₗ[R] LinDiagram R (φ.obj b) (φ.obj a) :=
  Finsupp.lmapDomain R R φ.map

@[simp] theorem linMap_apply {a b : Obj S} (f : LinDiagram R a b) :
    φ.linMap a b f = φ.lin f := rfl

theorem lin_add {a b : Obj S} (f g : LinDiagram R a b) : φ.lin (f + g) = φ.lin f + φ.lin g :=
  (φ.linMap a b).map_add f g

theorem lin_sub {a b : Obj S} (f g : LinDiagram R a b) : φ.lin (f - g) = φ.lin f - φ.lin g :=
  (φ.linMap a b).map_sub f g

theorem lin_smul {a b : Obj S} (r : R) (f : LinDiagram R a b) : φ.lin (r • f) = r • φ.lin f :=
  (φ.linMap a b).map_smul r f

theorem lin_zero {a b : Obj S} : φ.lin (0 : LinDiagram R a b) = 0 := Finsupp.mapDomain_zero

theorem lin_comp {a b c : Obj S} (f : LinDiagram R a b) (g : LinDiagram R b c) :
    φ.lin (f ≫ g) = φ.lin g ≫ φ.lin f := by
  induction f using Finsupp.induction_linear with
  | zero => rw [Limits.zero_comp, lin_zero, lin_zero, Limits.comp_zero]
  | add f₁ f₂ h₁ h₂ =>
    rw [Preadditive.add_comp, lin_add, lin_add, h₁, h₂, Preadditive.comp_add]
  | single d r =>
    induction g using Finsupp.induction_linear with
    | zero => rw [Limits.comp_zero, lin_zero, lin_zero, Limits.zero_comp]
    | add g₁ g₂ h₁ h₂ =>
      rw [Preadditive.comp_add, lin_add, lin_add, h₁, h₂, Preadditive.add_comp]
    | single e s =>
      erw [Free.single_comp_single]
      rw [lin, lin, lin, Finsupp.mapDomain_single, Finsupp.mapDomain_single,
        Finsupp.mapDomain_single, map_comp]
      erw [Free.single_comp_single]
      rw [mul_comm]

variable (Q : Presentation.{w, v'} S' R) (χ : S.Gen → R)

/-- The functor `Obj S ⥤ Q.Presentedᵒᵖ` induced by a contravariant layer map `φ` and weights `χ`
of the generators: a diagram `d` goes to `weight χ d • [φ d]`. -/
def toPresented : Obj S ⥤ Q.Presentedᵒᵖ where
  obj a := op (Q.obj (φ.obj a))
  map d := (Diagram.weight χ d • Q.diag (φ.map d)).op
  map_id a := by rw [Diagram.weight_id, one_smul, map_id, Q.diag_id]; rfl
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    simp only [Diagram.weight_comp, map_comp, Q.diag_comp, unop_comp, Quiver.Hom.unop_op,
      Linear.smul_comp, Linear.comp_smul, smul_smul, mul_comm]

@[simp] theorem toPresented_obj (a : Obj S) :
    (φ.toPresented Q χ).obj a = op (Q.obj (φ.obj a)) := rfl

@[simp] theorem toPresented_map {a b : Obj S} (d : a ⟶ b) :
    (φ.toPresented Q χ).map d = (Diagram.weight χ d • Q.diag (φ.map d)).op := rfl

theorem unop_smul {X Y : Q.Presentedᵒᵖ} (r : R) (f : X ⟶ Y) : (r • f).unop = r • f.unop := rfl

theorem op_smul {X Y : Q.Presented} (r : R) (f : X ⟶ Y) : (r • f).op = r • f.op := rfl

theorem unop_sub {X Y : Q.Presentedᵒᵖ} (f g : X ⟶ Y) : (f - g).unop = f.unop - g.unop := by
  rw [sub_eq_add_neg, unop_add, unop_neg, sub_eq_add_neg]

theorem freeLift_toPresented_of {a b : Obj S} (d : a ⟶ b) :
    (freeLift R (φ.toPresented Q χ)).map (LinDiagram.of d : LinDiagram R a b) =
      (Diagram.weight χ d • Q.diag (φ.map d)).op :=
  freeLift_map_of _ d

/-- With trivial weights, the linear extension is the class of the image. -/
theorem freeLift_toPresented_one {a b : Obj S} (f : LinDiagram R a b) :
    (freeLift R (φ.toPresented Q fun _ => 1)).map f = (Q.lin (φ.lin f)).op := by
  induction f using Finsupp.induction_linear with
  | zero => rw [Functor.map_zero, lin, Finsupp.mapDomain_zero, Q.lin_zero]; rfl
  | add f g hf hg =>
    rw [Functor.map_add, hf, hg, lin_add, Q.lin_add]; rfl
  | single d r =>
    rw [freeLift_map_single, lin, Finsupp.mapDomain_single, Q.lin_single, toPresented_map,
      Diagram.weight_one, one_smul]
    rfl

/-! ### Whiskering -/

/-- Compatibility of a family of contravariant layer maps with whiskering, on the objects and
layers reachable from `a` (see `LayerMap.WhiskerData`). -/
structure WhiskerData {ι : Type*} (φ : ι → OpLayerMap S S') where
  /-- The objects on which compatibility with whiskering is required. -/
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
    ∀ {b : Obj S}, Nonempty (a ⟶ b) →
      ((φ (idx i a u v)).obj b).WhiskerOK (left i a u v) (right i a u v)
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

variable {ι : Type*} {φ : ι → OpLayerMap S S'} (W : WhiskerData φ)

theorem map_whisker {i : ι} {a b : Obj S} (d : a ⟶ b) (u : Obj S) (v : List S.Colour)
    (ha : W.Admissible a) (hw : a.WhiskerOK u v) :
    (φ i).map (Diagram.whisker d u v hw) =
      Diagram.cast (Diagram.whisker ((φ (W.idx i a u v)).map d) (W.left i a u v)
          (W.right i a u v) (W.whiskerOK ha hw ⟨d⟩))
        (W.obj_whisker ha hw ⟨d⟩) (W.obj_whisker ha hw ⟨𝟙 a⟩) := by
  apply Diagram.ext
  simp only [layers_map, Diagram.layers_whisker, Diagram.layers_cast, List.map_map,
    List.map_reverse]
  congr 1
  refine List.map_congr_left fun L hL => ?_
  exact W.layer_whisker ha hw ((Diagram.chain d).valid_of_mem hL)
    ((Diagram.chain d).nonempty_of_mem hL)

theorem toPresented_map_whisker {i : ι} {a b : Obj S} (d : a ⟶ b) (u : Obj S)
    (v : List S.Colour) (ha : W.Admissible a) (hw : a.WhiskerOK u v) :
    ((φ i).toPresented Q χ).map (Diagram.whisker d u v hw) =
      (eqToHom (congrArg Q.obj (W.obj_whisker ha hw ⟨d⟩).symm) ≫
        Q.whisk (((φ (W.idx i a u v)).toPresented Q χ).map d).unop (W.left i a u v)
          (W.right i a u v) ≫
        eqToHom (congrArg Q.obj (W.obj_whisker ha hw ⟨𝟙 a⟩))).op := by
  rw [toPresented_map, toPresented_map, W.map_whisker _ _ _ ha, Diagram.weight_whisker, Q.diag_cast,
    Quiver.Hom.unop_op, Q.whisk_smul, Q.whisk_diag _ _ _ (W.whiskerOK ha hw ⟨d⟩),
    Linear.smul_comp, Linear.comp_smul]

theorem freeLift_whisker_eq_zero {i : ι} {a b : Obj S} (f : LinDiagram R a b) (u : Obj S)
    (v : List S.Colour) (ha : W.Admissible a) (hw : a.WhiskerOK u v)
    (hf : (freeLift R ((φ (W.idx i a u v)).toPresented Q χ)).map f = 0) :
    (freeLift R ((φ i).toPresented Q χ)).map (LinDiagram.whisker f u v hw) = 0 := by
  by_cases h0 : f = 0
  · subst h0
    rw [show LinDiagram.whisker (0 : LinDiagram R a b) u v hw = 0 from Finsupp.mapDomain_zero,
      Functor.map_zero]
  obtain ⟨d₀, -⟩ := Finsupp.ne_iff.mp h0
  have ea := congrArg Q.obj (W.obj_whisker (i := i) ha hw ⟨𝟙 a⟩)
  have eb := congrArg Q.obj (W.obj_whisker (i := i) ha hw ⟨d₀⟩).symm
  let T : (op (Q.obj ((φ (W.idx i a u v)).obj a)) ⟶ op (Q.obj ((φ (W.idx i a u v)).obj b)))
      →ₗ[R] (op (Q.obj ((φ i).obj (a.whisker u v))) ⟶ op (Q.obj ((φ i).obj (b.whisker u v)))) :=
    { toFun := fun x =>
        (eqToHom eb ≫ Q.whisk x.unop (W.left i a u v) (W.right i a u v) ≫ eqToHom ea).op
      map_add' := fun x y => by
        simp only [unop_add, Q.whisk_add, Preadditive.add_comp, Preadditive.comp_add, op_add]
      map_smul' := fun r x => by
        simp only [unop_smul, Q.whisk_smul, Linear.smul_comp, Linear.comp_smul,
          RingHom.id_apply, op_smul] }
  have := freeLift_map_mapDomain (F := (φ (W.idx i a u v)).toPresented Q χ)
    (G := (φ i).toPresented Q χ) (fun d => Diagram.whisker d u v hw) T
    (fun d => W.toPresented_map_whisker Q χ d u v ha hw) f
  exact this.trans (by rw [hf, map_zero])

end WhiskerData

/-! ### Soundness -/

variable {ι : Type*} (P : Presentation.{w, v} S R) {Q χ}

/-- **Contravariant functors from layer maps.** A family of contravariant layer maps compatible
with whiskering, with weights `χ`, respects a presentation `P` as soon as the relations of `P`
and the interchange law are respected without whiskering. -/
theorem respects {φ : ι → OpLayerMap S S'} (W : WhiskerData φ)
    (hadm : ∀ r, W.Admissible (P.dom r))
    (hrel : ∀ i r, (freeLift R ((φ i).toPresented Q χ)).map (P.rel r) = 0)
    (hint : ∀ i (x : InterchangeData S) (hx : x.Valid),
      (freeLift R ((φ i).toPresented Q χ)).map (InterchangeData.rel R hx) = 0) (i : ι) :
    P.Respects ((φ i).toPresented Q χ) :=
  P.respects_of_whisker_on (fun i => (φ i).toPresented Q χ) W.Admissible hadm
    (fun _ => W.admissible_interchange)
    (fun _ _ _ f u v ha hw hf => W.freeLift_whisker_eq_zero Q χ f u v ha hw (hf _)) hrel hint i

/-- The functor `P.Presented ⥤ Q.Presentedᵒᵖ` induced by a family of contravariant layer maps
compatible with whiskering: the class of a diagram `d` goes to `weight χ d • [φ i d]`
(`OpLayerMap.lift_diag`). -/
def lift {φ : ι → OpLayerMap S S'} (W : WhiskerData φ)
    (hadm : ∀ r, W.Admissible (P.dom r))
    (hrel : ∀ i r, (freeLift R ((φ i).toPresented Q χ)).map (P.rel r) = 0)
    (hint : ∀ i (x : InterchangeData S) (hx : x.Valid),
      (freeLift R ((φ i).toPresented Q χ)).map (InterchangeData.rel R hx) = 0) (i : ι) :
    P.Presented ⥤ Q.Presentedᵒᵖ :=
  P.lift (respects P W hadm hrel hint i)

section Lift

variable {P} {φ : ι → OpLayerMap S S'} (W : WhiskerData φ) (hadm : ∀ r, W.Admissible (P.dom r))
  (hrel : ∀ i r, (freeLift R ((φ i).toPresented Q χ)).map (P.rel r) = 0)
  (hint : ∀ i (x : InterchangeData S) (hx : x.Valid),
    (freeLift R ((φ i).toPresented Q χ)).map (InterchangeData.rel R hx) = 0) (i : ι)

instance lift_additive : (lift P W hadm hrel hint i).Additive := P.lift_additive _

instance lift_linear : (lift P W hadm hrel hint i).Linear R := P.lift_linear _

@[simp] theorem lift_obj (a : Obj S) :
    (lift P W hadm hrel hint i).obj (P.obj a) = op (Q.obj ((φ i).obj a)) := rfl

@[simp] theorem lift_diag {a b : Obj S} (d : a ⟶ b) :
    (lift P W hadm hrel hint i).map (P.diag d) = (Diagram.weight χ d • Q.diag ((φ i).map d)).op :=
  P.lift_diag _ d

theorem lift_lin {a b : Obj S} (f : LinDiagram R a b) :
    (lift P W hadm hrel hint i).map (P.lin f) = (freeLift R ((φ i).toPresented Q χ)).map f :=
  P.lift_lin _ f

end Lift

/-! ### The interchange law -/

variable (Q χ)

/-- A contravariant layer map respects the interchange law if it sends the four layers of an
instance `x` to the four layers of an instance `x'` with the same Koszul sign as a reflection
in a horizontal axis does: the image of the upper layer on either side is the lower layer on
the same side. -/
theorem toPresented_interchange_reflect {x : InterchangeData S} (hx : x.Valid)
    (x' : InterchangeData S') (h₁ : φ.layer x.gh₂ = x'.hg₁) (h₂ : φ.layer x.gh₁ = x'.hg₂)
    (h₃ : φ.layer x.hg₂ = x'.gh₁) (h₄ : φ.layer x.hg₁ = x'.gh₂) (hs : x'.sign = x.sign) :
    (freeLift R (φ.toPresented Q χ)).map (InterchangeData.rel R hx) = 0 := by
  have hx' : x'.Valid :=
    ⟨h₃ ▸ φ.valid hx.hg₂, h₄ ▸ φ.valid hx.hg₁, h₁ ▸ φ.valid hx.gh₂, h₂ ▸ φ.valid hx.gh₁⟩
  have ha : φ.obj x.cod = x'.dom := by
    rw [← x.gh₂_cod, ← φ.dom_eq hx.gh₂, h₁, x'.hg₁_dom]
  have hb : φ.obj x.dom = x'.cod := by
    rw [← x.gh₁_dom, ← φ.cod_eq hx.gh₁, h₂, x'.hg₂_cod]
  have e₁ := Q.diag_eq_of_layers_eq' (φ.map (InterchangeData.ghDiagram hx))
    (InterchangeData.hgDiagram hx') ha hb (by simp [InterchangeData.ghDiagram,
      InterchangeData.hgDiagram, h₁, h₂])
  have e₂ := Q.diag_eq_of_layers_eq' (φ.map (InterchangeData.hgDiagram hx))
    (InterchangeData.ghDiagram hx') ha hb (by simp [InterchangeData.ghDiagram,
      InterchangeData.hgDiagram, h₃, h₄])
  apply Quiver.Hom.unop_inj
  rw [InterchangeData.rel, Functor.map_sub, Functor.map_smul, freeLift_toPresented_of,
    freeLift_toPresented_of, e₁, e₂, Q.diag_ghDiagram hx', hs, InterchangeData.weight_hg]
  simp only [unop_sub, unop_smul, Quiver.Hom.unop_op, Limits.unop_zero, Linear.smul_comp,
    Linear.comp_smul, smul_smul, x.sign_cast_mul_self_assoc, sub_self]

/-- A contravariant layer map respects the interchange law if it sends the four layers of an
instance `x` to the four layers of an instance `x'` with the same Koszul sign as a rotation by a
half turn does: the image of the upper layer on either side is the lower layer on the other
side. -/
theorem toPresented_interchange_rotate {x : InterchangeData S} (hx : x.Valid)
    (x' : InterchangeData S') (h₁ : φ.layer x.gh₂ = x'.gh₁) (h₂ : φ.layer x.gh₁ = x'.gh₂)
    (h₃ : φ.layer x.hg₂ = x'.hg₁) (h₄ : φ.layer x.hg₁ = x'.hg₂) (hs : x'.sign = x.sign) :
    (freeLift R (φ.toPresented Q χ)).map (InterchangeData.rel R hx) = 0 := by
  have hx' : x'.Valid :=
    ⟨h₁ ▸ φ.valid hx.gh₂, h₂ ▸ φ.valid hx.gh₁, h₃ ▸ φ.valid hx.hg₂, h₄ ▸ φ.valid hx.hg₁⟩
  have ha : φ.obj x.cod = x'.dom := by
    rw [← x.gh₂_cod, ← φ.dom_eq hx.gh₂, h₁, x'.gh₁_dom]
  have hb : φ.obj x.dom = x'.cod := by
    rw [← x.gh₁_dom, ← φ.cod_eq hx.gh₁, h₂, x'.gh₂_cod]
  have e₁ := Q.diag_eq_of_layers_eq' (φ.map (InterchangeData.ghDiagram hx))
    (InterchangeData.ghDiagram hx') ha hb (by simp [InterchangeData.ghDiagram, h₁, h₂])
  have e₂ := Q.diag_eq_of_layers_eq' (φ.map (InterchangeData.hgDiagram hx))
    (InterchangeData.hgDiagram hx') ha hb (by simp [InterchangeData.hgDiagram, h₃, h₄])
  apply Quiver.Hom.unop_inj
  rw [InterchangeData.rel, Functor.map_sub, Functor.map_smul, freeLift_toPresented_of,
    freeLift_toPresented_of, e₁, e₂, Q.diag_ghDiagram hx', hs, InterchangeData.weight_hg]
  simp only [unop_sub, unop_smul, Quiver.Hom.unop_op, Limits.unop_zero, Linear.smul_comp,
    Linear.comp_smul, smul_comm (Diagram.weight χ _), sub_self]

/-! ### Degrees -/

section Degree

variable {A : Type*} [AddCommMonoid A] (deg : S.Gen → A) (deg' : S'.Gen → A)

/-- A contravariant layer map preserves degrees. -/
def PreservesDeg : Prop := ∀ {L : Layer S}, L.Valid → deg' (φ.layer L).gen = deg L.gen

variable {φ deg deg'}

theorem PreservesDeg.degree_map (h : φ.PreservesDeg deg deg') {a b : Obj S} (d : a ⟶ b) :
    Diagram.degree deg' (φ.map d) = Diagram.degree deg d := by
  simp only [Diagram.degree, layers_map, List.map_reverse, List.sum_reverse, List.map_map]
  congr 1
  exact List.map_congr_left fun L hL => h ((Diagram.chain d).valid_of_mem hL)

theorem preservesDeg_parityDeg
    (h : ∀ {L : Layer S}, L.Valid → S'.odd (φ.layer L).gen = S.odd L.gen) :
    φ.PreservesDeg (Presentation.parityDeg S) (Presentation.parityDeg S') := fun hv => by
  simp only [Presentation.parityDeg, h hv]

theorem PreservesDeg.toPresented_mem_homDeg (h : φ.PreservesDeg deg deg') {a b : Obj S}
    {f : LinDiagram R a b} {e : A} (hf : f ∈ LinDiagram.homDeg R deg a b e) :
    ((freeLift R (φ.toPresented Q χ)).map f).unop ∈ Q.homDeg deg' (φ.obj b) (φ.obj a) e := by
  rw [LinDiagram.homDeg, Finsupp.supported_eq_span_single] at hf
  induction hf using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨d, hd, rfl⟩ := hy
    rw [freeLift_map_single, toPresented_map, unop_smul, Quiver.Hom.unop_op, smul_smul]
    exact Submodule.smul_mem _ _ (Presentation.diag_mem_homDeg' ((h.degree_map d).trans hd))
  | zero => rw [Functor.map_zero, Limits.unop_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [Functor.map_add, unop_add]; exact Submodule.add_mem _ hy hz
  | smul r y _ hy => rw [Functor.map_smul, unop_smul]; exact Submodule.smul_mem _ r hy

variable {Q χ}

/-- **Degree-preserving contravariant layer maps induce degree-preserving functors.** -/
theorem lift_mem_homDeg {P : Presentation.{w, v} S R} {φ : ι → OpLayerMap S S'}
    (W : WhiskerData φ) (hadm : ∀ r, W.Admissible (P.dom r))
    (hrel : ∀ i r, (freeLift R ((φ i).toPresented Q χ)).map (P.rel r) = 0)
    (hint : ∀ i (x : InterchangeData S) (hx : x.Valid),
      (freeLift R ((φ i).toPresented Q χ)).map (InterchangeData.rel R hx) = 0) (i : ι)
    (h : (φ i).PreservesDeg deg deg') {a b : Obj S} {x : P.obj a ⟶ P.obj b} {e : A}
    (hx : x ∈ P.homDeg deg a b e) :
    ((lift P W hadm hrel hint i).map x).unop ∈ Q.homDeg deg' ((φ i).obj b) ((φ i).obj a) e := by
  obtain ⟨f, hf, rfl⟩ := Presentation.mem_homDeg_iff.mp hx
  rw [lift_lin]
  exact h.toPresented_mem_homDeg Q χ hf

end Degree

end Presented

end OpLayerMap

end StringDiagrams

end
