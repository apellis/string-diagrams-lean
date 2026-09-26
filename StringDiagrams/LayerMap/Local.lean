import StringDiagrams.LayerMap.Generators

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

end LocalMap

end StringDiagrams

end
