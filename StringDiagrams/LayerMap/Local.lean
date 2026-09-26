import StringDiagrams.LayerMap.Generators
import StringDiagrams.Super.Presented

/-!
# Functors from local images of layers

A `LocalMap S Q` assigns to every object of the free 2-category on `S` an object of the free
2-category on `S'` and to every well-formed layer `L` an *arbitrary* morphism of the presented
category `Q.Presented` between the images of the boundaries of `L`: a linear combination of
diagrams, a composite, a scalar multiple, … The image of a layer may depend on everything
around its generator. A local map is an `Interpretation` in `Q.Presented`, so it extends to a
functor `LocalMap.functor : Obj S ⥤ Q.Presented` (the image of a diagram is the composite of the
images of its layers).

Compatibility with whiskering (`LocalMap.WhiskerData`) asks that the image of a whiskered layer
be the whiskering, in `Q.Presented`, of the image of the layer (possibly for another member of
a family of local maps, and by objects depending on the whiskering). It extends from layers to
diagrams (`LocalMap.WhiskerData.functor_map_whisker`), so that, as for layer maps, a family of
local maps compatible with whiskering descends to functors `P.Presented ⥤ Q.Presented` as soon
as the relations of `P` and the interchange law are respected without whiskering
(`LocalMap.respects`, `LocalMap.lift`).

## Images of generators

The main source of local maps is `LocalMap.ofGen`: a relabelling `κ` of regions and strands
(`ColourMap`) and, for every generator `g`, a morphism `img g` of `Q.Presented` between the
relabelled boundaries of `g` (which may depend on `g`, hence on the regions around it). A layer
`u ⊗ g ⊗ v` goes to `κ u ⊗ img g ⊗ κ v`. Such a local map is compatible with whiskering
(`LocalMap.ofGen_whiskerData`), and it respects the interchange law as soon as every `img g` is
homogeneous of the parity of `g` (`LocalMap.ofGen_interchange`), by the super interchange law in
`Q.Presented`. Hence (`LocalMap.liftGen`) such images define a functor
`P.Presented ⥤ Q.Presented` as soon as the images of the relations of `P` vanish.

## Degrees

If the image of every layer is homogeneous of the degree of its generator
(`LocalMap.PreservesDeg`; for images of generators, `LocalMap.ofGen_preservesDeg`), the induced
functors preserve degrees (`LocalMap.lift_mem_homDeg`); for the parity gradings, parities.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory

universe w v v' u₀ u₁ u₂ u₀' u₁' u₂'

variable {S : Signature.{u₀, u₁, u₂}} {S' : Signature.{u₀', u₁', u₂'}} {R : Type w} [CommRing R]

/-- A local map from the free 2-category on `S` to the presented category of `Q`: images of
objects, and for every well-formed layer an arbitrary morphism between the images of its
boundaries. -/
structure LocalMap (S : Signature.{u₀, u₁, u₂}) (Q : Presentation.{w, v'} S' R) where
  /-- The image of an object. -/
  obj : Obj S → Obj S'
  /-- The image of a well-formed layer. -/
  layer : (L : Layer S) → L.Valid → (Q.obj (obj L.dom) ⟶ Q.obj (obj L.cod))

namespace LocalMap

variable {Q : Presentation.{w, v'} S' R} (φ : LocalMap S Q)

/-- A local map, as an interpretation in `Q.Presented`. -/
def toInterpretation : Interpretation S Q.Presented where
  obj a := Q.obj (φ.obj a)
  layer := φ.layer

@[simp] theorem toInterpretation_obj (a : Obj S) : φ.toInterpretation.obj a = Q.obj (φ.obj a) :=
  rfl

@[simp] theorem toInterpretation_layer : φ.toInterpretation.layer = φ.layer := rfl

/-- The functor induced by a local map: the image of a diagram is the composite of the images of
its layers. -/
def functor : Obj S ⥤ Q.Presented := φ.toInterpretation.functor

@[simp] theorem functor_obj (a : Obj S) : φ.functor.obj a = Q.obj (φ.obj a) := rfl

theorem functor_map_ofLayer (L : Layer S) (hv : L.Valid) :
    φ.functor.map (Diagram.ofLayer L hv) = φ.layer L hv :=
  φ.toInterpretation.functor_map_ofLayer L hv

theorem functor_map_layer (L : Layer S) (hv : L.Valid) {a b : Obj S} (ha : L.dom = a)
    (hb : L.cod = b) :
    φ.functor.map (Diagram.layer L hv ha hb) =
      eqToHom (congrArg (fun x => Q.obj (φ.obj x)) ha.symm) ≫ φ.layer L hv ≫
        eqToHom (congrArg (fun x => Q.obj (φ.obj x)) hb) := rfl

/-! ### Whiskering -/

/-- Compatibility of a family of local maps with whiskering, on the objects and layers reachable
from admissible objects `a`: the image under `φ i` of a whiskered layer `u ⊗ L ⊗ v` is the
whiskering by `left i a u v` and `right i a u v` of the image of `L` under
`φ (idx i a u v)`. -/
structure WhiskerData {ι : Type*} (φ : ι → LocalMap S Q) where
  /-- The objects on which compatibility with whiskering is required. -/
  Admissible : Obj S → Prop
  /-- The bottom boundaries of the instances of the interchange law are admissible. -/
  admissible_interchange : ∀ {x : InterchangeData S}, x.Valid → Admissible x.dom
  /-- The local map to apply before whiskering. -/
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
  layer_whisker : ∀ {i : ι} {a u : Obj S} {v : List S.Colour}, Admissible a →
    a.WhiskerOK u v → ∀ {L : Layer S} (hv : L.Valid), Nonempty (a ⟶ L.dom) →
      ∀ (hv' : (L.whisker u v).Valid)
        (e₁ : Q.obj ((φ i).obj (L.whisker u v).dom) =
          Q.obj (((φ (idx i a u v)).obj L.dom).whisker (left i a u v) (right i a u v)))
        (e₂ : Q.obj (((φ (idx i a u v)).obj L.cod).whisker (left i a u v) (right i a u v)) =
          Q.obj ((φ i).obj (L.whisker u v).cod)),
      (φ i).layer (L.whisker u v) hv' =
        eqToHom e₁ ≫ Q.whisk ((φ (idx i a u v)).layer L hv) (left i a u v) (right i a u v) ≫
          eqToHom e₂

namespace WhiskerData

variable {ι : Type*} {φ : ι → LocalMap S Q} (W : WhiskerData φ)

theorem functor_map_whisker_aux {i : ι} {a u : Obj S} {v : List S.Colour}
    (ha : W.Admissible a) (hw : a.WhiskerOK u v) :
    ∀ (ls : List (Layer S)) {c b : Obj S} (hcr : Nonempty (a ⟶ c)) (hc : Chain c ls b)
      (hwc : c.WhiskerOK u v),
      (φ i).functor.map (Diagram.whisker (Diagram.mk ls hc) u v hwc) =
        eqToHom (congrArg Q.obj (W.obj_whisker ha hw hcr).symm) ≫
          Q.whisk ((φ (W.idx i a u v)).functor.map (Diagram.mk ls hc)) (W.left i a u v)
            (W.right i a u v) ≫
          eqToHom (congrArg Q.obj (W.obj_whisker ha hw
            (hcr.map fun d => d ≫ Diagram.mk ls hc))) := by
  intro ls
  induction ls with
  | nil =>
    intro c b hcr hc hwc
    cases hc
    rw [show Diagram.mk [] (rfl : Chain c [] c) = 𝟙 c from rfl, Diagram.whisker_id,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    simp only [functor_obj]
    rw [Q.whisk_id _ _ _ (W.whiskerOK ha hw hcr), Category.id_comp, eqToHom_trans, eqToHom_refl]
  | cons L ls ih =>
    intro c b hcr hc hwc
    obtain ⟨hv, rfl, hc'⟩ := hc
    have e : Diagram.mk (L :: ls) (show Chain L.dom (L :: ls) b from ⟨hv, rfl, hc'⟩) =
        Diagram.ofLayer L hv ≫ Diagram.mk ls hc' := Diagram.ext rfl
    have hwc' : L.cod.WhiskerOK u v := Chain.whiskerOK (ls := [L]) ⟨hv, rfl, rfl⟩ hwc
    have hcr' : Nonempty (a ⟶ L.cod) := hv.nonempty_cod hcr
    have hv' : (L.whisker u v).Valid := hv.whisker hwc
    have el : Diagram.whisker (Diagram.ofLayer L hv) u v hwc =
        Diagram.layer (L.whisker u v) hv' (L.whisker_dom u v) (L.whisker_cod u v) :=
      Diagram.ext rfl
    rw [e, Diagram.whisker_comp, Functor.map_comp, el, functor_map_layer, ih hcr' hc' hwc',
      Functor.map_comp, functor_map_ofLayer, Q.whisk_comp,
      W.layer_whisker ha hw hv hcr hv'
        (by rw [L.whisker_dom]; exact congrArg Q.obj (W.obj_whisker ha hw hcr).symm)
        (by rw [L.whisker_cod]; exact congrArg Q.obj (W.obj_whisker ha hw hcr'))]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- Compatibility of the image of a diagram with whiskering. -/
theorem functor_map_whisker {i : ι} {a b : Obj S} (d : a ⟶ b) (u : Obj S) (v : List S.Colour)
    (ha : W.Admissible a) (hw : a.WhiskerOK u v) :
    (φ i).functor.map (Diagram.whisker d u v hw) =
      eqToHom (congrArg Q.obj (W.obj_whisker ha hw ⟨𝟙 a⟩).symm) ≫
        Q.whisk ((φ (W.idx i a u v)).functor.map d) (W.left i a u v) (W.right i a u v) ≫
        eqToHom (congrArg Q.obj (W.obj_whisker ha hw ⟨d⟩)) := by
  obtain ⟨ls, hc⟩ := d
  exact W.functor_map_whisker_aux ha hw ls ⟨𝟙 a⟩ hc hw

theorem freeLift_whisker_eq_zero {i : ι} {a b : Obj S} (f : LinDiagram R a b) (u : Obj S)
    (v : List S.Colour) (ha : W.Admissible a) (hw : a.WhiskerOK u v)
    (hf : (freeLift R (φ (W.idx i a u v)).functor).map f = 0) :
    (freeLift R (φ i).functor).map (LinDiagram.whisker f u v hw) = 0 := by
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
  have := freeLift_map_mapDomain (F := (φ (W.idx i a u v)).functor) (G := (φ i).functor)
    (fun d => Diagram.whisker d u v hw) T (fun d => W.functor_map_whisker d u v ha hw) f
  exact this.trans (by rw [hf, map_zero])

end WhiskerData

/-! ### Soundness -/

variable {ι : Type*} (P : Presentation.{w, v} S R)

/-- **Functors from local maps.** A family of local maps compatible with whiskering respects a
presentation `P` as soon as the relations of `P` and the interchange law are respected without
whiskering. -/
theorem respects {φ : ι → LocalMap S Q} (W : WhiskerData φ)
    (hadm : ∀ r, W.Admissible (P.dom r))
    (hrel : ∀ i r, (freeLift R (φ i).functor).map (P.rel r) = 0)
    (hint : ∀ i (x : InterchangeData S) (hx : x.Valid),
      (freeLift R (φ i).functor).map (InterchangeData.rel R hx) = 0) (i : ι) :
    P.Respects (φ i).functor :=
  P.respects_of_whisker_on (fun i => (φ i).functor) W.Admissible hadm
    (fun _ => W.admissible_interchange)
    (fun _ _ _ f u v ha hw hf => W.freeLift_whisker_eq_zero f u v ha hw (hf _)) hrel hint i

/-- The functor `P.Presented ⥤ Q.Presented` induced by a family of local maps compatible with
whiskering: the class of a diagram goes to the composite of the images of its layers. -/
def lift {φ : ι → LocalMap S Q} (W : WhiskerData φ) (hadm : ∀ r, W.Admissible (P.dom r))
    (hrel : ∀ i r, (freeLift R (φ i).functor).map (P.rel r) = 0)
    (hint : ∀ i (x : InterchangeData S) (hx : x.Valid),
      (freeLift R (φ i).functor).map (InterchangeData.rel R hx) = 0) (i : ι) :
    P.Presented ⥤ Q.Presented :=
  P.lift (respects P W hadm hrel hint i)

section Lift

variable {P} {φ : ι → LocalMap S Q} (W : WhiskerData φ) (hadm : ∀ r, W.Admissible (P.dom r))
  (hrel : ∀ i r, (freeLift R (φ i).functor).map (P.rel r) = 0)
  (hint : ∀ i (x : InterchangeData S) (hx : x.Valid),
    (freeLift R (φ i).functor).map (InterchangeData.rel R hx) = 0) (i : ι)

instance lift_additive : (lift P W hadm hrel hint i).Additive := P.lift_additive _

instance lift_linear : (lift P W hadm hrel hint i).Linear R := P.lift_linear _

@[simp] theorem lift_obj (a : Obj S) :
    (lift P W hadm hrel hint i).obj (P.obj a) = Q.obj ((φ i).obj a) := rfl

@[simp] theorem lift_diag {a b : Obj S} (d : a ⟶ b) :
    (lift P W hadm hrel hint i).map (P.diag d) = (φ i).functor.map d :=
  P.lift_diag _ d

theorem lift_lin {a b : Obj S} (f : LinDiagram R a b) :
    (lift P W hadm hrel hint i).map (P.lin f) = (freeLift R (φ i).functor).map f :=
  P.lift_lin _ f

theorem lift_layer (L : Layer S) (hv : L.Valid) :
    (lift P W hadm hrel hint i).map (P.diag (Diagram.ofLayer L hv)) = (φ i).layer L hv := by
  rw [lift_diag, functor_map_ofLayer]

/-- The induced functors commute with whiskering. -/
theorem lift_whisk {a b : Obj S} (f : P.obj a ⟶ P.obj b) {u : Obj S} {v : List S.Colour}
    (ha : W.Admissible a) (hw : a.WhiskerOK u v) (hb : Nonempty (a ⟶ b)) :
    (lift P W hadm hrel hint i).map (P.whisk f u v) =
      eqToHom (congrArg Q.obj (W.obj_whisker ha hw ⟨𝟙 a⟩).symm) ≫
        Q.whisk ((lift P W hadm hrel hint (W.idx i a u v)).map f) (W.left i a u v)
          (W.right i a u v) ≫
        eqToHom (congrArg Q.obj (W.obj_whisker ha hw hb)) := by
  obtain ⟨f, rfl⟩ := P.lin_surjective f
  rw [Presentation.whisk_lin, LinDiagram.whisk_of_ok _ hw, lift_lin, lift_lin]
  exact freeLift_map_mapDomain (F := (φ (W.idx i a u v)).functor) (G := (φ i).functor)
    (fun d => Diagram.whisker d u v hw)
    { toFun := fun x => eqToHom (congrArg Q.obj (W.obj_whisker ha hw ⟨𝟙 a⟩).symm) ≫
        Q.whisk x (W.left i a u v) (W.right i a u v) ≫
          eqToHom (congrArg Q.obj (W.obj_whisker ha hw hb))
      map_add' := fun x y => by
        simp only [Q.whisk_add, Preadditive.add_comp, Preadditive.comp_add]
      map_smul' := fun r x => by
        simp only [Q.whisk_smul, Linear.smul_comp, Linear.comp_smul, RingHom.id_apply] }
    (fun d => W.functor_map_whisker d u v ha hw) f

end Lift

/-! ### Degrees -/

section Degree

variable {A : Type*} [AddCommMonoid A] (deg : S.Gen → A) (deg' : S'.Gen → A)

/-- A local map preserves degrees: the image of every well-formed layer is homogeneous of the
degree of its generator. For the parity gradings this is parity preservation. -/
def PreservesDeg (φ : LocalMap S Q) : Prop :=
  ∀ (L : Layer S) (hv : L.Valid),
    φ.layer L hv ∈ Q.homDeg deg' (φ.obj L.dom) (φ.obj L.cod) (deg L.gen)

variable {deg deg'} {φ : LocalMap S Q}

theorem PreservesDeg.functor_map_mem (h : φ.PreservesDeg deg deg') {a b : Obj S} (d : a ⟶ b) :
    φ.functor.map d ∈ Q.homDeg deg' (φ.obj a) (φ.obj b) (Diagram.degree deg d) := by
  obtain ⟨ls, hc⟩ := d
  induction ls generalizing a with
  | nil =>
    cases hc
    change φ.functor.map (𝟙 _) ∈ Q.homDeg deg' _ _ (Diagram.degree deg (𝟙 _))
    rw [CategoryTheory.Functor.map_id, Diagram.degree_id]
    exact Presentation.id_mem_homDeg Q deg' _
  | cons L ls ih =>
    obtain ⟨hv, rfl, hc'⟩ := hc
    have e : (⟨L :: ls, hv, rfl, hc'⟩ : L.dom ⟶ b) = Diagram.ofLayer L hv ≫ ⟨ls, hc'⟩ :=
      Diagram.ext rfl
    rw [e, Functor.map_comp, functor_map_ofLayer, Diagram.degree_comp, Diagram.degree_ofLayer]
    exact Presentation.comp_mem_homDeg (h L hv) (ih hc')

theorem PreservesDeg.freeLift_mem (h : φ.PreservesDeg deg deg') {a b : Obj S}
    {f : LinDiagram R a b} {e : A} (hf : f ∈ LinDiagram.homDeg R deg a b e) :
    (freeLift R φ.functor).map f ∈ Q.homDeg deg' (φ.obj a) (φ.obj b) e := by
  rw [LinDiagram.homDeg, Finsupp.supported_eq_span_single] at hf
  induction hf using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨d, hd, rfl⟩ := hy
    rw [freeLift_map_single]
    exact Submodule.smul_mem _ _ (hd ▸ h.functor_map_mem d)
  | zero => rw [Functor.map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [Functor.map_add]; exact Submodule.add_mem _ hy hz
  | smul r y _ hy => rw [Functor.map_smul]; exact Submodule.smul_mem _ r hy

/-- **Degree-preserving local maps induce degree-preserving functors.** -/
theorem lift_mem_homDeg {P : Presentation.{w, v} S R} {φ : ι → LocalMap S Q}
    (W : WhiskerData φ) (hadm : ∀ r, W.Admissible (P.dom r))
    (hrel : ∀ i r, (freeLift R (φ i).functor).map (P.rel r) = 0)
    (hint : ∀ i (x : InterchangeData S) (hx : x.Valid),
      (freeLift R (φ i).functor).map (InterchangeData.rel R hx) = 0) (i : ι)
    (h : (φ i).PreservesDeg deg deg') {a b : Obj S} {x : P.obj a ⟶ P.obj b} {e : A}
    (hx : x ∈ P.homDeg deg a b e) :
    (lift P W hadm hrel hint i).map x ∈ Q.homDeg deg' ((φ i).obj a) ((φ i).obj b) e := by
  obtain ⟨f, hf, rfl⟩ := Presentation.mem_homDeg_iff.mp hx
  rw [lift_lin]
  exact h.freeLift_mem hf

end Degree

end LocalMap

/-! ## Images of generators -/

namespace LocalMap

variable {Q : Presentation.{w, v'} S' R}

private theorem whisk_eqToHom' {a b : Obj S'} (h : a = b) (u : Obj S') (v : List S'.Colour)
    (hw : a.WhiskerOK u v) :
    Q.whisk (eqToHom (congrArg Q.obj h)) u v =
      eqToHom (congrArg Q.obj (congrArg (Obj.whisker · u v) h)) := by
  subst h; exact Q.whisk_id a u v hw

private theorem lin_cast' {a b a' b' : Obj S'} (f : LinDiagram R a b) (ha : a = a')
    (hb : b = b') :
    Q.lin (LinDiagram.cast f ha hb) =
      eqToHom (congrArg Q.obj ha.symm) ≫ Q.lin f ≫ eqToHom (congrArg Q.obj hb) := by
  subst ha hb; simp

private theorem whisk_whisk' {a b : Obj S'} (f : Q.obj a ⟶ Q.obj b) (u' u : Obj S')
    (v' v : List S'.Colour) (h' : a.WhiskerOK u' v') (h : (a.whisker u' v').WhiskerOK u v) :
    Q.whisk (Q.whisk f u' v') u v =
      eqToHom (congrArg Q.obj (Obj.whisker_whisker a u' u v' v)) ≫
        Q.whisk f (u.tensor u') (v' ++ v) ≫
          eqToHom (congrArg Q.obj (Obj.whisker_whisker b u' u v' v).symm) := by
  obtain ⟨f, rfl⟩ := Q.lin_surjective f
  rw [Presentation.whisk_lin, Presentation.whisk_lin, Presentation.whisk_lin,
    LinDiagram.whisk_of_ok _ h', LinDiagram.whisk_of_ok _ h,
    LinDiagram.whisk_of_ok _ (h'.trans h), LinDiagram.whisker_whisker _ _ _ _ _ h' h, lin_cast']

private theorem whisk_congr' {a b : Obj S'} (f : Q.obj a ⟶ Q.obj b) {u u' : Obj S'}
    {v v' : List S'.Colour} (hu : u = u') (hv : v = v') :
    Q.whisk f u v = eqToHom (by rw [hu, hv]) ≫ Q.whisk f u' v' ≫ eqToHom (by rw [hu, hv]) := by
  subst hu hv; simp

variable (κ : ColourMap S S')

/-- The relabelled bottom boundary of a generator, read from its left region. -/
def genDom (g : S.Gen) : Obj S' := κ.obj ⟨S.left g, S.dom g⟩

/-- The relabelled top boundary of a generator, read from its left region. -/
def genCod (g : S.Gen) : Obj S' := κ.obj ⟨S.left g, S.cod g⟩

theorem whisker_genDom (L : Layer S) :
    (genDom κ L.gen).whisker (κ.obj ⟨L.start, L.left⟩) (κ.word L.right) = κ.obj L.dom := by
  simp [genDom, ColourMap.obj, Obj.whisker, Layer.dom]

theorem whisker_genCod (L : Layer S) :
    (genCod κ L.gen).whisker (κ.obj ⟨L.start, L.left⟩) (κ.word L.right) = κ.obj L.cod := by
  simp [genCod, ColourMap.obj, Obj.whisker, Layer.cod]

theorem genDom_whiskerOK {L : Layer S} (hv : L.Valid) :
    (genDom κ L.gen).WhiskerOK (κ.obj ⟨L.start, L.left⟩) (κ.word L.right) := by
  refine ⟨κ.ok_map hv.left_ok, ?_, ?_⟩
  · show S'.endR (κ.region L.start) (κ.word L.left) = κ.region (S.left L.gen)
    rw [κ.endR_map, hv.left_end]
  · show S'.ok (S'.endR (κ.region (S.left L.gen)) (κ.word (S.dom L.gen))) _
    rw [κ.endR_map, hv.dom_end]; exact κ.ok_map hv.right_ok

variable (img : (g : S.Gen) → (Q.obj (genDom κ g) ⟶ Q.obj (genCod κ g)))

/-- The local map given by images of generators: a layer `u ⊗ g ⊗ v` goes to
`κ u ⊗ img g ⊗ κ v`, where `κ` relabels regions and strands. -/
def ofGen : LocalMap S Q where
  obj := κ.obj
  layer L _ := eqToHom (congrArg Q.obj (whisker_genDom κ L)).symm ≫
    Q.whisk (img L.gen) (κ.obj ⟨L.start, L.left⟩) (κ.word L.right) ≫
      eqToHom (congrArg Q.obj (whisker_genCod κ L))

@[simp] theorem ofGen_obj (a : Obj S) : (ofGen κ img).obj a = κ.obj a := rfl

theorem ofGen_layer (L : Layer S) (hv : L.Valid) :
    (ofGen κ img).layer L hv = eqToHom (congrArg Q.obj (whisker_genDom κ L)).symm ≫
      Q.whisk (img L.gen) (κ.obj ⟨L.start, L.left⟩) (κ.word L.right) ≫
        eqToHom (congrArg Q.obj (whisker_genCod κ L)) := rfl

/-- The local map given by images of generators commutes with whiskering, on all objects. -/
def ofGen_whiskerData : WhiskerData fun _ : Unit => ofGen κ img where
  Admissible _ := True
  admissible_interchange _ := trivial
  idx _ _ _ _ := ()
  left _ _ u _ := κ.obj u
  right _ _ _ v := κ.word v
  whiskerOK _ hw _ hb := κ.whiskerOK ((Diagram.chain hb.some).whiskerOK hw)
  obj_whisker _ _ _ _ := (κ.obj_whisker _ _ _).symm
  layer_whisker := by
    intro _ a u v _ hw L hv hL hv' e₁ e₂
    have hwL : L.dom.WhiskerOK u v := (Diagram.chain hL.some).whiskerOK hw
    have hwc : L.cod.WhiskerOK u v := Chain.whiskerOK (ls := [L]) ⟨hv, rfl, rfl⟩ hwL
    have hw₀ := genDom_whiskerOK κ hv
    have hw₁ : ((genDom κ L.gen).whisker (κ.obj ⟨L.start, L.left⟩)
        (κ.word L.right)).WhiskerOK (κ.obj u) (κ.word v) := by
      rw [whisker_genDom]; exact κ.whiskerOK hwL
    rw [ofGen_layer, ofGen_layer, Q.whisk_comp, Q.whisk_comp,
      whisk_eqToHom' (whisker_genDom κ L).symm _ _ (κ.whiskerOK hwL),
      whisk_eqToHom' (whisker_genCod κ L) _ _ (by rw [whisker_genCod]; exact κ.whiskerOK hwc),
      whisk_whisk' _ _ _ _ _ hw₀ hw₁,
      whisk_congr' (img L.gen) (u := (κ.obj u).tensor (κ.obj ⟨L.start, L.left⟩))
        (v := κ.word L.right ++ κ.word v) (u' := κ.obj ⟨(L.whisker u v).start,
        (L.whisker u v).left⟩) (v' := κ.word (L.whisker u v).right)
        (by simp [ColourMap.obj, Obj.tensor, Layer.whisker]) (by simp [Layer.whisker])]
    simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
    rfl

private theorem whisk_nil_eq_wRAt {a a' : Obj S'} (f : Q.obj a ⟶ Q.obj a') {r : S'.Region}
    (b : Obj S') (ha : a.start = r) (ha' : a'.start = r) :
    Q.whisk f (Obj.nil r) b.word =
      eqToHom (congrArg Q.obj (Obj.tensor_eq_whisker_nil_of_start b ha)).symm ≫
        Q.wRAt r f b ha ha' ≫
          eqToHom (congrArg Q.obj (Obj.tensor_eq_whisker_nil_of_start b ha')) := by
  simp [Presentation.wRAt]

private theorem whisk_eq_wL {b b' : Obj S'} (g : Q.obj b ⟶ Q.obj b') (a : Obj S') :
    Q.whisk g a [] =
      eqToHom (congrArg Q.obj (Obj.tensor_eq_whisker_nil a b)).symm ≫ Q.wL a g ≫
        eqToHom (congrArg Q.obj (Obj.tensor_eq_whisker_nil a b')) := by
  simp [Presentation.wL]

/-- **Images of generators respect the interchange law** when every image `img g` is homogeneous
of the parity of `g`: this is the super interchange law in `Q.Presented`. -/
theorem ofGen_interchange
    (himg : ∀ g, img g ∈ Q.homDeg (Presentation.parityDeg S') (genDom κ g) (genCod κ g)
      (Presentation.parityDeg S g))
    {x : InterchangeData S} (hx : x.Valid) :
    (freeLift R (ofGen κ img).functor).map (InterchangeData.rel R hx) = 0 := by
  have hs : x.start = S.left x.g := hx.gh₁.left_end
  have e₀ : S.endR (S.right x.g) x.mid = S.left x.h := by
    have h₀ := hx.gh₁.left_end
    have h₁ := hx.hg₁.left_end
    have h₂ := hx.gh₁.dom_end
    simp only [InterchangeData.hg₁, InterchangeData.gh₁, Signature.endR_append,
      Signature.endR_nil] at h₀ h₁ h₂
    rwa [h₀, h₂] at h₁
  have hmok : S.ok (S.right x.g) x.mid := ((Signature.ok_append _ _ _).1 hx.gh₁.right_ok).1
  set r := κ.region (S.left x.g) with hr
  let A := genDom κ x.g
  let A' := genCod κ x.g
  let M : Obj S' := κ.obj ⟨S.right x.g, x.mid⟩
  let Dh := genDom κ x.h
  let Ch := genCod κ x.h
  have hMend : M.endR = κ.region (S.left x.h) := by
    show S'.endR (κ.region (S.right x.g)) (κ.word x.mid) = _
    rw [κ.endR_map, e₀]
  have hMD : M.Composable Dh := ⟨κ.ok_map hmok, hMend, κ.ok_map hx.hg₁.dom_ok⟩
  have hMC : M.Composable Ch := ⟨κ.ok_map hmok, hMend, κ.ok_map hx.hg₁.cod_ok⟩
  have hgd : S.endR (S.left x.g) (S.dom x.g) = S.right x.g := hx.gh₁.dom_end
  have hgc : S.endR (S.left x.g) (S.cod x.g) = S.right x.g := hx.gh₁.cod_end
  have hAM : A.Composable M := ⟨κ.ok_map hx.gh₁.dom_ok, by
    show S'.endR (κ.region (S.left x.g)) (κ.word (S.dom x.g)) = _
    rw [κ.endR_map, hgd]; rfl, κ.ok_map hmok⟩
  have hA'M : A'.Composable M := ⟨κ.ok_map hx.gh₁.cod_ok, by
    show S'.endR (κ.region (S.left x.g)) (κ.word (S.cod x.g)) = _
    rw [κ.endR_map, hgc]; rfl, κ.ok_map hmok⟩
  have hA : A.start = r := rfl
  have hA' : A'.start = r := rfl
  let G := Q.wL M (img x.h)
  have hG := Q.wL_mem (Presentation.parityDeg S') M (himg x.h)
  have key := Q.wRAt_comp_wL_super (hAM.tensor_right hMD) (himg x.g) hG hA hA'
  have hk : ((Supercategory.koszulSign (Presentation.parityDeg S x.g)
      (Presentation.parityDeg S x.h) : ℤ) : R) = ((x.sign : ℤ) : R) := by
    congr 1
    unfold InterchangeData.sign Presentation.parityDeg
    cases S.odd x.g <;> cases S.odd x.h <;> simp
  have oE₁ : κ.obj x.dom = A.tensor (M.tensor Dh) := by
    refine Obj.ext (by simp [A, InterchangeData.dom, genDom, ColourMap.obj, Obj.tensor, hs]) ?_
    simp [A, M, Dh, InterchangeData.dom, genDom, ColourMap.obj, Obj.tensor]
  have oE₂ : A'.tensor (M.tensor Ch) = κ.obj x.cod := by
    refine Obj.ext (by simp [A', InterchangeData.cod, genCod, ColourMap.obj, Obj.tensor, hs]) ?_
    simp [A', M, Ch, InterchangeData.cod, genCod, ColourMap.obj, Obj.tensor]
  have hgh : (ofGen κ img).functor.map (InterchangeData.ghDiagram hx) =
      eqToHom (congrArg Q.obj oE₁) ≫ (Q.wRAt r (img x.g) (M.tensor Dh) hA hA' ≫ Q.wL A' G) ≫
        eqToHom (congrArg Q.obj oE₂) := by
    unfold InterchangeData.ghDiagram
    show (ofGen κ img).toInterpretation.functor.map _ = _
    rw [Interpretation.functor_map_mk_cons, Interpretation.functor_map_mk_cons,
      Interpretation.functor_map_mk_nil]
    rw [toInterpretation_layer, ofGen_layer, ofGen_layer,
      whisk_congr' (img x.gh₁.gen) (u' := Obj.nil r) (v' := (M.tensor Dh).word)
        (by simp [ColourMap.obj, InterchangeData.gh₁, Obj.nil, hs, r])
        (by simp [InterchangeData.gh₁, M, Dh, genDom, ColourMap.obj, Obj.tensor]),
      whisk_nil_eq_wRAt (img x.gh₁.gen) (M.tensor Dh) hA hA',
      whisk_congr' (img x.gh₂.gen) (u' := A'.tensor M) (v' := [])
        (by simp [ColourMap.obj, InterchangeData.gh₂, A', M, genCod, Obj.tensor, hs])
        (by simp [InterchangeData.gh₂]),
      whisk_eq_wL (img x.gh₂.gen) (A'.tensor M), Q.wL_tensor hA'M hMD]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
      Category.id_comp]
    rfl
  have hhg : (ofGen κ img).functor.map (InterchangeData.hgDiagram hx) =
      eqToHom (congrArg Q.obj oE₁) ≫ (Q.wL A G ≫ Q.wRAt r (img x.g) (M.tensor Ch) hA hA') ≫
        eqToHom (congrArg Q.obj oE₂) := by
    unfold InterchangeData.hgDiagram
    show (ofGen κ img).toInterpretation.functor.map _ = _
    rw [Interpretation.functor_map_mk_cons, Interpretation.functor_map_mk_cons,
      Interpretation.functor_map_mk_nil]
    rw [toInterpretation_layer, ofGen_layer, ofGen_layer,
      whisk_congr' (img x.hg₁.gen) (u' := A.tensor M) (v' := [])
        (by simp [ColourMap.obj, InterchangeData.hg₁, A, M, genDom, Obj.tensor, hs])
        (by simp [InterchangeData.hg₁]),
      whisk_eq_wL (img x.hg₁.gen) (A.tensor M), Q.wL_tensor hAM hMD,
      whisk_congr' (img x.hg₂.gen) (u' := Obj.nil r) (v' := (M.tensor Ch).word)
        (by simp [ColourMap.obj, InterchangeData.hg₂, Obj.nil, hs, r])
        (by simp [InterchangeData.hg₂, M, Ch, genCod, ColourMap.obj, Obj.tensor]),
      whisk_nil_eq_wRAt (img x.hg₂.gen) (M.tensor Ch) hA hA']
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
      Category.id_comp]
    rfl
  have key' : Q.wRAt r (img x.g) (M.tensor Dh) hA hA' ≫ Q.wL A' G =
      ((x.sign : ℤ) : R) • (Q.wL A G ≫ Q.wRAt r (img x.g) (M.tensor Ch) hA hA') := by
    rw [← hk, Int.cast_smul_eq_zsmul]; exact key
  rw [InterchangeData.rel, Functor.map_sub, Functor.map_smul, freeLift_map_of, freeLift_map_of,
    hgh, hhg, key', Linear.smul_comp, Linear.comp_smul, sub_self]

/-- For even signatures, the images of generators are automatically homogeneous of the right
(even) parity. -/
theorem parity_of_isEven [S.IsEven] [S'.IsEven] (g : S.Gen) :
    img g ∈ Q.homDeg (Presentation.parityDeg S') (genDom κ g) (genCod κ g)
      (Presentation.parityDeg S g) := by
  obtain ⟨f, hf⟩ := Q.lin_surjective (img g)
  rw [← hf, show Presentation.parityDeg S g = 0 by
    simp [Presentation.parityDeg, Signature.IsEven.odd_eq_false]]
  exact Presentation.lin_mem_homDeg (LinDiagram.mem_homDeg_iff.mpr fun d _ => by
    rw [Diagram.degree_parityDeg, Diagram.oddCount_eq_zero, Nat.cast_zero])

/-- If every image of a generator is homogeneous of the degree of the generator, the local
map given by the images of generators preserves degrees. -/
theorem ofGen_preservesDeg {A : Type*} [AddCommMonoid A] {deg : S.Gen → A} {deg' : S'.Gen → A}
    (himg : ∀ g, img g ∈ Q.homDeg deg' (genDom κ g) (genCod κ g) (deg g)) :
    (ofGen κ img).PreservesDeg deg deg' := fun L _ => by
  have := Presentation.comp_mem_homDeg (Presentation.eqToHom_mem_homDeg (P := Q) deg'
    (congrArg Q.obj (whisker_genDom κ L)).symm) (Presentation.comp_mem_homDeg
      (Presentation.whisk_mem_homDeg (himg L.gen) (κ.obj ⟨L.start, L.left⟩) (κ.word L.right))
      (Presentation.eqToHom_mem_homDeg (P := Q) deg' (congrArg Q.obj (whisker_genCod κ L))))
  rwa [zero_add, add_zero] at this

variable (P : Presentation.{w, v} S R)

/-- **Functors from images of generators.** Let `κ` relabel regions and strands and let
`img g` be a morphism of `Q.Presented` between the relabelled boundaries of each generator `g`,
homogeneous of the parity of `g` (automatic for even signatures, `LocalMap.parity_of_isEven`).
If the images of the relations of `P` vanish, then `u ⊗ g ⊗ v ↦ κ u ⊗ img g ⊗ κ v` defines a
functor `P.Presented ⥤ Q.Presented`. -/
def liftGen
    (himg : ∀ g, img g ∈ Q.homDeg (Presentation.parityDeg S') (genDom κ g) (genCod κ g)
      (Presentation.parityDeg S g))
    (hrel : ∀ r, (freeLift R (ofGen κ img).functor).map (P.rel r) = 0) :
    P.Presented ⥤ Q.Presented :=
  lift P (ofGen_whiskerData κ img) (fun _ => trivial) (fun _ => hrel)
    (fun _ _ hx => ofGen_interchange κ img himg hx) ()

section LiftGen

variable {P}
  (himg : ∀ g, img g ∈ Q.homDeg (Presentation.parityDeg S') (genDom κ g) (genCod κ g)
    (Presentation.parityDeg S g))
  (hrel : ∀ r, (freeLift R (ofGen κ img).functor).map (P.rel r) = 0)

instance liftGen_additive : (liftGen κ img P himg hrel).Additive := lift_additive _ _ _ _ _

instance liftGen_linear : (liftGen κ img P himg hrel).Linear R := lift_linear _ _ _ _ _

@[simp] theorem liftGen_obj (a : Obj S) :
    (liftGen κ img P himg hrel).obj (P.obj a) = Q.obj (κ.obj a) := rfl

theorem liftGen_diag {a b : Obj S} (d : a ⟶ b) :
    (liftGen κ img P himg hrel).map (P.diag d) = (ofGen κ img).functor.map d :=
  lift_diag _ _ _ _ _ d

theorem liftGen_lin {a b : Obj S} (f : LinDiagram R a b) :
    (liftGen κ img P himg hrel).map (P.lin f) = (freeLift R (ofGen κ img).functor).map f :=
  lift_lin _ _ _ _ _ f

/-- A layer `u ⊗ g ⊗ v` goes to `κ u ⊗ img g ⊗ κ v`. -/
theorem liftGen_layer (L : Layer S) (hv : L.Valid) :
    (liftGen κ img P himg hrel).map (P.diag (Diagram.ofLayer L hv)) =
      eqToHom (congrArg Q.obj (whisker_genDom κ L)).symm ≫
        Q.whisk (img L.gen) (κ.obj ⟨L.start, L.left⟩) (κ.word L.right) ≫
          eqToHom (congrArg Q.obj (whisker_genCod κ L)) :=
  lift_layer _ _ _ _ _ L hv

/-- The functor commutes with whiskering. -/
theorem liftGen_whisk {a b : Obj S} (f : P.obj a ⟶ P.obj b) {u : Obj S} {v : List S.Colour}
    (hw : a.WhiskerOK u v) (hb : Nonempty (a ⟶ b)) :
    (liftGen κ img P himg hrel).map (P.whisk f u v) =
      eqToHom (congrArg Q.obj (κ.obj_whisker a u v)) ≫
        Q.whisk ((liftGen κ img P himg hrel).map f) (κ.obj u) (κ.word v) ≫
          eqToHom (congrArg Q.obj (κ.obj_whisker b u v)).symm :=
  lift_whisk (P := P) (ofGen_whiskerData κ img) (fun _ => trivial) (fun _ => hrel)
    (fun _ _ hx => ofGen_interchange κ img himg hx) () f trivial hw hb

end LiftGen

end LocalMap

end StringDiagrams

end
