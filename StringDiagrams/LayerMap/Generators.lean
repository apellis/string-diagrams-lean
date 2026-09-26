import StringDiagrams.LayerMap.Op

/-!
# Layer maps induced by maps of generators

Three kinds of maps of signatures, each given by maps of regions, strand colours and
generators compatible with all boundaries, and the layer maps they induce:

* `SigMap S S'` (covariant): a generator `g : w ⟶ w'` goes to a generator
  `κ w ⟶ κ w'`, where `κ` relabels the strands. It preserves the order of 1-morphisms and of
  2-morphisms (`SigMap.toLayerMap`). Examples: inclusions of signatures, relabellings,
  rescalings of generators (with weights).
* `SigFlip S S'` (reflection in a horizontal axis): a generator `g : w ⟶ w'` goes to a generator
  `κ w' ⟶ κ w`. It preserves the order of 1-morphisms and reverses that of 2-morphisms, and is
  a contravariant layer map (`SigFlip.toOpLayerMap`).
* `SigMirror S S'` (reflection in a vertical axis): regions `r` go to `ρ r` and a strand from
  the region `r` to the region `s` goes to a strand from `ρ s` to `ρ r`; a generator `g : w ⟶ w'`
  with regions `l`, `r` on its left and right goes to a generator `rev (κ w) ⟶ rev (κ w')` with
  regions `ρ r`, `ρ l`, where `rev (κ w)` is the relabelled word read backwards. It reverses the
  order of 1-morphisms and preserves that of 2-morphisms (`SigMirror.toLayerMap`); an object
  `a` goes to the reversed relabelled word, read from the image of the rightmost region of `a`.

Each comes with its compatibility with whiskering (`SigMap.whiskerData`, …; for the mirror,
on well-formed objects), and each respects the interchange law as soon as it preserves the
parities of generators (`SigMap.toPresented_interchange`, …). Hence (`SigMap.lift`,
`SigFlip.lift`, `SigMirror.lift`) for presentations `P` of `S` and `Q` of `S'` and weights
`χ : S.Gen → R`, the functors `P.Presented ⥤ Q.Presented` (resp. `Q.Presentedᵒᵖ`) sending the
class of a diagram `d` to `weight χ d • [φ d]` exist as soon as the images of the relations of
`P` vanish in `Q` — without whiskering.

## Signs

The three kinds of maps are well defined on presented categories without any sign beyond
the weights `χ`, also for odd generators, provided parities are preserved: the Koszul sign
`(-1)^{|g||h|}` of an instance of the interchange law is symmetric in `g` and `h`. With
respect to horizontal composition, however, reflections introduce Koszul signs. Writing
`f ⊗ g = (f ⊗ 1) ≫ (1 ⊗ g)` for the horizontal composite (the convention of
`Presentation.hcomp`, with `f` on the left), in the presented categories

* the mirror satisfies `σ (f ⊗ g) = (-1)^{|f||g|} σ g ⊗ σ f` (`SigMirror.diag_map_tensor`),
* the flip satisfies `ψ (f ⊗ g) = (-1)^{|f||g|} ψ f ⊗ ψ g` in `Q.Presented`, where `ψ f` is
  the reflected morphism in the opposite direction (`SigFlip.diag_map_tensor`),

while a covariant map of signatures commutes with horizontal composition
(`SigMap.map_tensor`). For even signatures all these signs are `1`.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Opposite

universe w v v' u₀ u₁ u₂ u₀' u₁' u₂'

variable {S : Signature.{u₀, u₁, u₂}} {S' : Signature.{u₀', u₁', u₂'}}

/-! ## Relabelling regions and strands -/

/-- A map of regions and strand colours compatible with the regions on either side of a
strand. -/
structure ColourMap (S : Signature.{u₀, u₁, u₂}) (S' : Signature.{u₀', u₁', u₂'}) where
  /-- The image of a region. -/
  region : S.Region → S'.Region
  /-- The image of a strand colour. -/
  colour : S.Colour → S'.Colour
  /-- Compatibility with the region on the left of a strand. -/
  colourSrc : ∀ c, S'.colourSrc (colour c) = region (S.colourSrc c)
  /-- Compatibility with the region on the right of a strand. -/
  colourTgt : ∀ c, S'.colourTgt (colour c) = region (S.colourTgt c)
  /-- The image of a word: by default, the word of the images of its strands. (For the identity
  relabelling one may take `id`, so that objects and diagrams keep their types.) -/
  word : List S.Colour → List S'.Colour := fun w => w.map colour
  /-- The image of a word is the word of the images of its strands. -/
  word_eq : ∀ w, word w = w.map colour := by intro; rfl

namespace ColourMap

variable (κ : ColourMap S S')

@[simp] theorem word_nil : κ.word [] = [] := by rw [κ.word_eq]; rfl

@[simp] theorem word_append (w w' : List S.Colour) : κ.word (w ++ w') = κ.word w ++ κ.word w' := by
  simp [κ.word_eq]

theorem word_cons (c : S.Colour) (w : List S.Colour) : κ.word (c :: w) = κ.colour c :: κ.word w := by
  simp [κ.word_eq]

/-- The identity relabelling, with `word := id`. -/
@[simps]
protected def id (S : Signature.{u₀, u₁, u₂}) : ColourMap S S where
  region := id
  colour := id
  colourSrc _ := rfl
  colourTgt _ := rfl
  word := id
  word_eq w := (List.map_id w).symm

theorem endR_map (r : S.Region) (w : List S.Colour) :
    S'.endR (κ.region r) (κ.word w) = κ.region (S.endR r w) := by
  rw [κ.word_eq]
  induction w generalizing r with
  | nil => rfl
  | cons c w ih => rw [List.map_cons, Signature.endR_cons, κ.colourTgt, ih]; rfl

theorem ok_map {r : S.Region} {w : List S.Colour} (h : S.ok r w) :
    S'.ok (κ.region r) (κ.word w) := by
  rw [κ.word_eq]
  induction w generalizing r with
  | nil => trivial
  | cons c w ih =>
    obtain ⟨hc, hw⟩ := h
    exact ⟨by rw [κ.colourSrc, hc], by rw [κ.colourTgt]; exact ih hw⟩

/-- The image of an object: the same word, relabelled. -/
def obj (a : Obj S) : Obj S' := ⟨κ.region a.start, κ.word a.word⟩

@[simp] theorem obj_start (a : Obj S) : (κ.obj a).start = κ.region a.start := rfl
@[simp] theorem obj_word (a : Obj S) : (κ.obj a).word = κ.word a.word := rfl

theorem obj_endR (a : Obj S) : (κ.obj a).endR = κ.region a.endR := κ.endR_map _ _

theorem obj_whisker (a u : Obj S) (v : List S.Colour) :
    κ.obj (a.whisker u v) = (κ.obj a).whisker (κ.obj u) (κ.word v) := by
  simp [obj, Obj.whisker]

theorem whiskerOK {a u : Obj S} {v : List S.Colour} (hw : a.WhiskerOK u v) :
    (κ.obj a).WhiskerOK (κ.obj u) (κ.word v) :=
  ⟨κ.ok_map hw.1, by rw [obj_endR, hw.2.1]; rfl, by rw [obj_endR]; exact κ.ok_map hw.2.2⟩

end ColourMap

/-! ## Covariant maps of signatures -/

/-- A map of signatures: regions, strand colours and generators, compatible with all
boundaries. -/
structure SigMap (S : Signature.{u₀, u₁, u₂}) (S' : Signature.{u₀', u₁', u₂'})
    extends ColourMap S S' where
  /-- The image of a generator. -/
  gen : S.Gen → S'.Gen
  /-- Bottom boundaries. -/
  dom : ∀ g, S'.dom (gen g) = word (S.dom g)
  /-- Top boundaries. -/
  cod : ∀ g, S'.cod (gen g) = word (S.cod g)
  /-- Left regions. -/
  left : ∀ g, S'.left (gen g) = region (S.left g)
  /-- Right regions. -/
  right : ∀ g, S'.right (gen g) = region (S.right g)

namespace SigMap

variable (φ : SigMap S S')

/-- The image of a layer: the same layer, relabelled. -/
def layer (L : Layer S) : Layer S' :=
  ⟨φ.region L.start, φ.word L.left, φ.gen L.gen, φ.word L.right⟩

theorem layer_valid {L : Layer S} (hv : L.Valid) : (φ.layer L).Valid where
  left_ok := φ.ok_map hv.left_ok
  left_end := by
    show S'.endR (φ.region L.start) (φ.word L.left) = S'.left (φ.gen L.gen)
    rw [φ.endR_map, hv.left_end, φ.left]
  dom_ok := by
    show S'.ok (S'.left (φ.gen L.gen)) (S'.dom (φ.gen L.gen))
    rw [φ.left, φ.dom]; exact φ.ok_map hv.dom_ok
  dom_end := by
    show S'.endR (S'.left (φ.gen L.gen)) (S'.dom (φ.gen L.gen)) = S'.right (φ.gen L.gen)
    rw [φ.left, φ.dom, φ.endR_map, hv.dom_end, φ.right]
  cod_ok := by
    show S'.ok (S'.left (φ.gen L.gen)) (S'.cod (φ.gen L.gen))
    rw [φ.left, φ.cod]; exact φ.ok_map hv.cod_ok
  cod_end := by
    show S'.endR (S'.left (φ.gen L.gen)) (S'.cod (φ.gen L.gen)) = S'.right (φ.gen L.gen)
    rw [φ.left, φ.cod, φ.endR_map, hv.cod_end, φ.right]
  right_ok := by
    show S'.ok (S'.right (φ.gen L.gen)) _
    rw [φ.right]; exact φ.ok_map hv.right_ok

/-- The layer map induced by a map of signatures. -/
@[simps]
def toLayerMap : LayerMap S S' where
  obj := φ.obj
  layer := φ.layer
  valid := φ.layer_valid
  dom_eq _ := Obj.ext rfl (by simp [layer, ColourMap.obj, Layer.dom, φ.dom])
  cod_eq _ := Obj.ext rfl (by simp [layer, ColourMap.obj, Layer.cod, φ.cod])

theorem layer_whisker (L : Layer S) (u : Obj S) (v : List S.Colour) :
    φ.layer (L.whisker u v) = (φ.layer L).whisker (φ.obj u) (φ.word v) := by
  simp [layer, Layer.whisker, ColourMap.obj]

/-- A map of signatures commutes with whiskering, on all objects. -/
def whiskerData : LayerMap.WhiskerData fun _ : Unit => φ.toLayerMap where
  Admissible _ := True
  admissible_interchange _ := trivial
  idx _ _ _ _ := ()
  left _ _ u _ := φ.obj u
  right _ _ _ v := φ.word v
  whiskerOK _ hw := φ.whiskerOK hw
  obj_whisker _ _ _ _ := (φ.obj_whisker _ _ _).symm
  layer_whisker _ _ _ _ _ := φ.layer_whisker _ _ _

variable {R : Type w} [CommRing R] (Q : Presentation.{w, v'} S' R) (χ : S.Gen → R)

/-- A parity-preserving map of signatures respects the interchange law. -/
theorem toPresented_interchange (hodd : ∀ g, S'.odd (φ.gen g) = S.odd g)
    {x : InterchangeData S} (hx : x.Valid) :
    (freeLift R (φ.toLayerMap.toPresented Q χ)).map (InterchangeData.rel R hx) = 0 :=
  φ.toLayerMap.toPresented_interchange Q χ hx ⟨φ.region x.start, φ.gen x.g,
      φ.word x.mid, φ.gen x.h⟩
    (by simp [layer, InterchangeData.gh₁, φ.dom])
    (by simp [layer, InterchangeData.gh₂, φ.cod])
    (by simp [layer, InterchangeData.hg₁, φ.dom])
    (by simp [layer, InterchangeData.hg₂, φ.cod])
    (by simp [InterchangeData.sign, hodd])

variable (P : Presentation.{w, v} S R) {Q χ}

/-- **Functors from maps of signatures.** For a parity-preserving map of signatures `φ` and
weights `χ`, if the image of every relation of `P` vanishes in `Q`, then `φ` induces a functor
`P.Presented ⥤ Q.Presented` sending the class of a diagram `d` to `weight χ d • [φ d]`. -/
def lift (hodd : ∀ g, S'.odd (φ.gen g) = S.odd g)
    (hrel : ∀ r, (freeLift R (φ.toLayerMap.toPresented Q χ)).map (P.rel r) = 0) :
    P.Presented ⥤ Q.Presented :=
  LayerMap.lift P φ.whiskerData (fun _ => trivial) (fun _ => hrel)
    (fun _ _ hx => φ.toPresented_interchange Q χ hodd hx) ()

variable {P} (hodd : ∀ g, S'.odd (φ.gen g) = S.odd g)
  (hrel : ∀ r, (freeLift R (φ.toLayerMap.toPresented Q χ)).map (P.rel r) = 0)

instance lift_additive : (φ.lift P hodd hrel).Additive := LayerMap.lift_additive _ _ _ _ _

instance lift_linear : (φ.lift P hodd hrel).Linear R := LayerMap.lift_linear _ _ _ _ _

@[simp] theorem lift_obj (a : Obj S) : (φ.lift P hodd hrel).obj (P.obj a) = Q.obj (φ.obj a) :=
  rfl

@[simp] theorem lift_diag {a b : Obj S} (d : a ⟶ b) :
    (φ.lift P hodd hrel).map (P.diag d) = Diagram.weight χ d • Q.diag (φ.toLayerMap.map d) :=
  LayerMap.lift_diag _ _ _ _ _ d

theorem lift_lin {a b : Obj S} (f : LinDiagram R a b) :
    (φ.lift P hodd hrel).map (P.lin f) = (freeLift R (φ.toLayerMap.toPresented Q χ)).map f :=
  LayerMap.lift_lin _ _ _ _ _ f

/-- A map of signatures commutes with whiskering in the presented categories. -/
theorem lift_whisk {a b : Obj S} (f : P.obj a ⟶ P.obj b) {u : Obj S} {v : List S.Colour}
    (hw : a.WhiskerOK u v) :
    (φ.lift P hodd hrel).map (P.whisk f u v) =
      eqToHom (congrArg Q.obj (φ.obj_whisker a u v)) ≫
        Q.whisk ((φ.lift P hodd hrel).map f) (φ.obj u) (φ.word v) ≫
          eqToHom (congrArg Q.obj (φ.obj_whisker b u v)).symm := by
  obtain ⟨f, rfl⟩ := P.lin_surjective f
  rw [Presentation.whisk_lin, LinDiagram.whisk_of_ok _ hw, lift_lin, lift_lin]
  exact freeLift_map_mapDomain (F := φ.toLayerMap.toPresented Q χ)
    (G := φ.toLayerMap.toPresented Q χ) (fun d => Diagram.whisker d u v hw)
    { toFun := fun x => eqToHom (congrArg Q.obj (φ.obj_whisker a u v)) ≫
        Q.whisk x (φ.obj u) (φ.word v) ≫
          eqToHom (congrArg Q.obj (φ.obj_whisker b u v)).symm
      map_add' := fun x y => by
        simp only [Q.whisk_add, Preadditive.add_comp, Preadditive.comp_add]
      map_smul' := fun r x => by
        simp only [Q.whisk_smul, Linear.smul_comp, Linear.comp_smul, RingHom.id_apply] }
    (fun d => φ.whiskerData.toPresented_map_whisker (i := ()) Q χ d u v trivial hw) f

end SigMap

/-! ## Reflections in a horizontal axis -/

/-- A map of signatures reversing 2-morphisms (a reflection in a horizontal axis, followed by a
relabelling): a generator `g : w ⟶ w'` goes to a generator `κ w' ⟶ κ w` with the same regions on
either side (relabelled). -/
structure SigFlip (S : Signature.{u₀, u₁, u₂}) (S' : Signature.{u₀', u₁', u₂'})
    extends ColourMap S S' where
  /-- The image of a generator. -/
  gen : S.Gen → S'.Gen
  /-- The bottom boundary of the image is the relabelled top boundary. -/
  dom : ∀ g, S'.dom (gen g) = word (S.cod g)
  /-- The top boundary of the image is the relabelled bottom boundary. -/
  cod : ∀ g, S'.cod (gen g) = word (S.dom g)
  /-- Left regions. -/
  left : ∀ g, S'.left (gen g) = region (S.left g)
  /-- Right regions. -/
  right : ∀ g, S'.right (gen g) = region (S.right g)

namespace SigFlip

variable (φ : SigFlip S S')

/-- The image of a layer: the reflected generator, with the same (relabelled) strands on either
side. -/
def layer (L : Layer S) : Layer S' :=
  ⟨φ.region L.start, φ.word L.left, φ.gen L.gen, φ.word L.right⟩

theorem layer_valid {L : Layer S} (hv : L.Valid) : (φ.layer L).Valid where
  left_ok := φ.ok_map hv.left_ok
  left_end := by
    show S'.endR (φ.region L.start) (φ.word L.left) = S'.left (φ.gen L.gen)
    rw [φ.endR_map, hv.left_end, φ.left]
  dom_ok := by
    show S'.ok (S'.left (φ.gen L.gen)) (S'.dom (φ.gen L.gen))
    rw [φ.left, φ.dom]; exact φ.ok_map hv.cod_ok
  dom_end := by
    show S'.endR (S'.left (φ.gen L.gen)) (S'.dom (φ.gen L.gen)) = S'.right (φ.gen L.gen)
    rw [φ.left, φ.dom, φ.endR_map, hv.cod_end, φ.right]
  cod_ok := by
    show S'.ok (S'.left (φ.gen L.gen)) (S'.cod (φ.gen L.gen))
    rw [φ.left, φ.cod]; exact φ.ok_map hv.dom_ok
  cod_end := by
    show S'.endR (S'.left (φ.gen L.gen)) (S'.cod (φ.gen L.gen)) = S'.right (φ.gen L.gen)
    rw [φ.left, φ.cod, φ.endR_map, hv.dom_end, φ.right]
  right_ok := by
    show S'.ok (S'.right (φ.gen L.gen)) _
    rw [φ.right]; exact φ.ok_map hv.right_ok

/-- The contravariant layer map induced by a reflection of generators. -/
@[simps]
def toOpLayerMap : OpLayerMap S S' where
  obj := φ.obj
  layer := φ.layer
  valid := φ.layer_valid
  dom_eq _ := Obj.ext rfl (by simp [layer, ColourMap.obj, Layer.dom, Layer.cod, φ.dom])
  cod_eq _ := Obj.ext rfl (by simp [layer, ColourMap.obj, Layer.dom, Layer.cod, φ.cod])

theorem layer_whisker (L : Layer S) (u : Obj S) (v : List S.Colour) :
    φ.layer (L.whisker u v) = (φ.layer L).whisker (φ.obj u) (φ.word v) := by
  simp [layer, Layer.whisker, ColourMap.obj]

/-- A reflection of generators commutes with whiskering, on all objects. -/
def whiskerData : OpLayerMap.WhiskerData fun _ : Unit => φ.toOpLayerMap where
  Admissible _ := True
  admissible_interchange _ := trivial
  idx _ _ _ _ := ()
  left _ _ u _ := φ.obj u
  right _ _ _ v := φ.word v
  whiskerOK _ hw _ hb := φ.whiskerOK ((Diagram.chain hb.some).whiskerOK hw)
  obj_whisker _ _ _ _ := (φ.obj_whisker _ _ _).symm
  layer_whisker _ _ _ _ _ := φ.layer_whisker _ _ _

variable {R : Type w} [CommRing R] (Q : Presentation.{w, v'} S' R) (χ : S.Gen → R)

/-- A parity-preserving reflection of generators respects the interchange law. -/
theorem toPresented_interchange (hodd : ∀ g, S'.odd (φ.gen g) = S.odd g)
    {x : InterchangeData S} (hx : x.Valid) :
    (freeLift R (φ.toOpLayerMap.toPresented Q χ)).map (InterchangeData.rel R hx) = 0 :=
  φ.toOpLayerMap.toPresented_interchange_reflect Q χ hx ⟨φ.region x.start, φ.gen x.g,
      φ.word x.mid, φ.gen x.h⟩
    (by simp [layer, InterchangeData.gh₂, InterchangeData.hg₁, φ.dom])
    (by simp [layer, InterchangeData.gh₁, InterchangeData.hg₂, φ.cod])
    (by simp [layer, InterchangeData.hg₂, InterchangeData.gh₁, φ.dom])
    (by simp [layer, InterchangeData.hg₁, InterchangeData.gh₂, φ.cod])
    (by simp [InterchangeData.sign, hodd])

variable (P : Presentation.{w, v} S R) {Q χ}

/-- **Contravariant functors from reflections of generators.** For a parity-preserving
reflection of generators `φ` and weights `χ`, if the image of every relation of `P` vanishes in
`Q`, then `φ` induces a functor `P.Presented ⥤ Q.Presentedᵒᵖ` sending the class of a diagram `d`
to `weight χ d • [φ d]`, the reflected diagram. -/
def lift (hodd : ∀ g, S'.odd (φ.gen g) = S.odd g)
    (hrel : ∀ r, (freeLift R (φ.toOpLayerMap.toPresented Q χ)).map (P.rel r) = 0) :
    P.Presented ⥤ Q.Presentedᵒᵖ :=
  OpLayerMap.lift P φ.whiskerData (fun _ => trivial) (fun _ => hrel)
    (fun _ _ hx => φ.toPresented_interchange Q χ hodd hx) ()

variable {P} (hodd : ∀ g, S'.odd (φ.gen g) = S.odd g)
  (hrel : ∀ r, (freeLift R (φ.toOpLayerMap.toPresented Q χ)).map (P.rel r) = 0)

instance lift_additive : (φ.lift P hodd hrel).Additive := OpLayerMap.lift_additive _ _ _ _ _

instance lift_linear : (φ.lift P hodd hrel).Linear R := OpLayerMap.lift_linear _ _ _ _ _

@[simp] theorem lift_obj (a : Obj S) :
    (φ.lift P hodd hrel).obj (P.obj a) = op (Q.obj (φ.obj a)) := rfl

@[simp] theorem lift_diag {a b : Obj S} (d : a ⟶ b) :
    (φ.lift P hodd hrel).map (P.diag d) =
      (Diagram.weight χ d • Q.diag (φ.toOpLayerMap.map d)).op :=
  OpLayerMap.lift_diag _ _ _ _ _ d

theorem lift_lin {a b : Obj S} (f : LinDiagram R a b) :
    (φ.lift P hodd hrel).map (P.lin f) = (freeLift R (φ.toOpLayerMap.toPresented Q χ)).map f :=
  OpLayerMap.lift_lin _ _ _ _ _ f

/-- A reflection in a horizontal axis commutes with whiskering in the presented categories. -/
theorem lift_whisk {a b : Obj S} (f : P.obj a ⟶ P.obj b) {u : Obj S} {v : List S.Colour}
    (hw : a.WhiskerOK u v) (hb : Nonempty (a ⟶ b)) :
    ((φ.lift P hodd hrel).map (P.whisk f u v)).unop =
      eqToHom (congrArg Q.obj (φ.obj_whisker b u v)) ≫
        Q.whisk ((φ.lift P hodd hrel).map f).unop (φ.obj u) (φ.word v) ≫
          eqToHom (congrArg Q.obj (φ.obj_whisker a u v)).symm :=
  OpLayerMap.lift_whisk (P := P) φ.whiskerData (fun _ => trivial) (fun _ => hrel)
    (fun _ _ hx => φ.toPresented_interchange Q χ hodd hx) () f trivial hw hb

end SigFlip

/-! ## Reflections in a vertical axis -/

/-- Regions and strand colours for a reflection in a vertical axis: a strand from the region `r`
(on its left) to the region `s` (on its right) goes to a strand from `ρ s` to `ρ r`. -/
structure MirrorColourMap (S : Signature.{u₀, u₁, u₂}) (S' : Signature.{u₀', u₁', u₂'}) where
  /-- The image of a region. -/
  region : S.Region → S'.Region
  /-- The image of a strand colour. -/
  colour : S.Colour → S'.Colour
  /-- The region on the left of the image is the image of the region on the right. -/
  colourSrc : ∀ c, S'.colourSrc (colour c) = region (S.colourTgt c)
  /-- The region on the right of the image is the image of the region on the left. -/
  colourTgt : ∀ c, S'.colourTgt (colour c) = region (S.colourSrc c)

namespace MirrorColourMap

variable (κ : MirrorColourMap S S')

/-- The reflected word: relabelled and read backwards. -/
def word (w : List S.Colour) : List S'.Colour := (w.map κ.colour).reverse

@[simp] theorem word_nil : κ.word [] = [] := rfl

theorem word_cons (c : S.Colour) (w : List S.Colour) : κ.word (c :: w) = κ.word w ++ [κ.colour c] := by
  simp [word]

theorem word_append (w w' : List S.Colour) : κ.word (w ++ w') = κ.word w' ++ κ.word w := by
  simp [word]

/-- A well-formed word read from `r` is reflected to a well-formed word read from the image of
its rightmost region, ending in the image of `r`. -/
theorem ok_word {r : S.Region} {w : List S.Colour} (h : S.ok r w) :
    S'.ok (κ.region (S.endR r w)) (κ.word w) ∧
      S'.endR (κ.region (S.endR r w)) (κ.word w) = κ.region r := by
  induction w generalizing r with
  | nil => exact ⟨trivial, rfl⟩
  | cons c w ih =>
    obtain ⟨hc, hw⟩ := h
    obtain ⟨ih₁, ih₂⟩ := ih hw
    rw [Signature.endR_cons, word_cons, Signature.ok_append, Signature.endR_append, ih₂]
    refine ⟨⟨ih₁, by rw [κ.colourSrc], trivial⟩, ?_⟩
    rw [Signature.endR_cons, Signature.endR_nil, κ.colourTgt, hc]

/-- The reflected object: the reflected word, read from the image of the rightmost region. -/
def obj (a : Obj S) : Obj S' := ⟨κ.region a.endR, κ.word a.word⟩

@[simp] theorem obj_start (a : Obj S) : (κ.obj a).start = κ.region a.endR := rfl
@[simp] theorem obj_word (a : Obj S) : (κ.obj a).word = κ.word a.word := rfl

theorem obj_endR {a : Obj S} (ha : a.WF) : (κ.obj a).endR = κ.region a.start :=
  (κ.ok_word ha).2

/-- The object by which a reflected diagram from `a` is whiskered on the left, when the diagram
is whiskered by `v` on the right. -/
def leftObj (a : Obj S) (v : List S.Colour) : Obj S' := ⟨κ.region (S.endR a.endR v), κ.word v⟩

theorem whiskerOK {a u : Obj S} {v : List S.Colour} (ha : a.WF) (hw : a.WhiskerOK u v) :
    (κ.obj a).WhiskerOK (κ.leftObj a v) (κ.word u.word) := by
  obtain ⟨hu, hue, hv⟩ := hw
  refine ⟨(κ.ok_word hv).1, (κ.ok_word hv).2, ?_⟩
  rw [κ.obj_endR ha, ← hue]
  exact (κ.ok_word hu).1

theorem obj_whisker {a u : Obj S} {v : List S.Colour} (hue : u.endR = a.start) :
    (κ.obj a).whisker (κ.leftObj a v) (κ.word u.word) = κ.obj (a.whisker u v) := by
  refine Obj.ext ?_ ?_
  · show κ.region (S.endR a.endR v) = κ.region (S.endR u.start (u.word ++ a.word ++ v))
    rw [Signature.endR_append, Signature.endR_append]
    rw [show S.endR u.start u.word = a.start from hue]
    rfl
  · simp [Obj.whisker, leftObj, word_append, List.append_assoc]

end MirrorColourMap

/-- A map of signatures reversing 1-morphisms (a reflection in a vertical axis, followed by a
relabelling): a generator `g : w ⟶ w'` with regions `l` and `r` on its left and right goes to a
generator from the reflected word of `w` to the reflected word of `w'`, with regions `ρ r` and
`ρ l` on its left and right. -/
structure SigMirror (S : Signature.{u₀, u₁, u₂}) (S' : Signature.{u₀', u₁', u₂'})
    extends MirrorColourMap S S' where
  /-- The image of a generator. -/
  gen : S.Gen → S'.Gen
  /-- Bottom boundaries. -/
  dom : ∀ g, S'.dom (gen g) = ((S.dom g).map colour).reverse
  /-- Top boundaries. -/
  cod : ∀ g, S'.cod (gen g) = ((S.cod g).map colour).reverse
  /-- The region on the left of the image is the image of the region on the right. -/
  left : ∀ g, S'.left (gen g) = region (S.right g)
  /-- The region on the right of the image is the image of the region on the left. -/
  right : ∀ g, S'.right (gen g) = region (S.left g)

namespace SigMirror

variable (φ : SigMirror S S')

theorem dom' (g : S.Gen) : S'.dom (φ.gen g) = φ.word (S.dom g) := φ.dom g

theorem cod' (g : S.Gen) : S'.cod (φ.gen g) = φ.word (S.cod g) := φ.cod g

/-- The image of a layer: the strands on the right of the generator become the reflected strands
on its left, and conversely. -/
def layer (L : Layer S) : Layer S' :=
  ⟨φ.region (S.endR (S.right L.gen) L.right), φ.word L.right, φ.gen L.gen, φ.word L.left⟩

theorem layer_valid {L : Layer S} (hv : L.Valid) : (φ.layer L).Valid := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := hv
  refine ⟨(φ.ok_word h₇).1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show S'.endR (φ.region (S.endR (S.right L.gen) L.right)) (φ.word L.right) =
      S'.left (φ.gen L.gen)
    rw [(φ.ok_word h₇).2, φ.left]
  · show S'.ok (S'.left (φ.gen L.gen)) (S'.dom (φ.gen L.gen))
    rw [φ.left, φ.dom', ← h₄]; exact (φ.ok_word h₃).1
  · show S'.endR (S'.left (φ.gen L.gen)) (S'.dom (φ.gen L.gen)) = S'.right (φ.gen L.gen)
    rw [φ.left, φ.dom', φ.right, ← h₄]; exact (φ.ok_word h₃).2
  · show S'.ok (S'.left (φ.gen L.gen)) (S'.cod (φ.gen L.gen))
    rw [φ.left, φ.cod', ← h₆]; exact (φ.ok_word h₅).1
  · show S'.endR (S'.left (φ.gen L.gen)) (S'.cod (φ.gen L.gen)) = S'.right (φ.gen L.gen)
    rw [φ.left, φ.cod', φ.right, ← h₆]; exact (φ.ok_word h₅).2
  · show S'.ok (S'.right (φ.gen L.gen)) (φ.word L.left)
    rw [φ.right, ← h₂]; exact (φ.ok_word h₁).1

theorem layer_dom {L : Layer S} (hv : L.Valid) : (φ.layer L).dom = φ.obj L.dom := by
  refine Obj.ext ?_ ?_
  · show φ.region (S.endR (S.right L.gen) L.right) = φ.region L.dom.endR
    rw [hv.endR_dom]
  · simp [layer, MirrorColourMap.obj, Layer.dom, φ.dom', MirrorColourMap.word_append,
      List.append_assoc]

theorem layer_cod {L : Layer S} (hv : L.Valid) : (φ.layer L).cod = φ.obj L.cod := by
  refine Obj.ext ?_ ?_
  · show φ.region (S.endR (S.right L.gen) L.right) = φ.region L.cod.endR
    rw [hv.endR_cod]
  · simp [layer, MirrorColourMap.obj, Layer.cod, φ.cod', MirrorColourMap.word_append,
      List.append_assoc]

/-- The layer map induced by a reflection in a vertical axis. -/
@[simps]
def toLayerMap : LayerMap S S' where
  obj := φ.obj
  layer := φ.layer
  valid := φ.layer_valid
  dom_eq := φ.layer_dom
  cod_eq := φ.layer_cod

theorem layer_whisker {L : Layer S} (hv : L.Valid) (u : Obj S) (v : List S.Colour) :
    φ.layer (L.whisker u v) = (φ.layer L).whisker (φ.leftObj L.dom v) (φ.word u.word) := by
  refine Layer.ext ?_ ?_ rfl ?_
  · show φ.region (S.endR (S.right L.gen) (L.right ++ v)) = φ.region (S.endR L.dom.endR v)
    rw [Signature.endR_append, hv.endR_dom]
  · simp [layer, Layer.whisker, MirrorColourMap.leftObj, MirrorColourMap.word_append]
  · simp [layer, Layer.whisker, MirrorColourMap.word_append]

/-- A reflection in a vertical axis commutes with whiskering, on well-formed objects: whiskering
by `u` on the left and `v` on the right becomes whiskering by the reflection of `v` on the left
and the reflection of `u` on the right. -/
def whiskerData : LayerMap.WhiskerData fun _ : Unit => φ.toLayerMap where
  Admissible := Obj.WF
  admissible_interchange hx := hx.wf_dom
  idx _ _ _ _ := ()
  left _ a _ v := φ.leftObj a v
  right _ _ u _ := φ.word u.word
  whiskerOK ha hw := φ.whiskerOK ha hw
  obj_whisker {_ a u v} _ hw b hb := by
    obtain ⟨d⟩ := hb
    have e : φ.leftObj a v = φ.leftObj b v := by
      simp only [MirrorColourMap.leftObj, (Diagram.chain d).endR_eq]
    show (φ.obj b).whisker _ _ = φ.obj _
    rw [e]
    exact φ.obj_whisker (hw.2.1.trans (Diagram.chain d).start_eq.symm)
  layer_whisker {_ a u v} _ _ L hv hL := by
    obtain ⟨d⟩ := hL
    have e : φ.leftObj a v = φ.leftObj L.dom v := by
      simp only [MirrorColourMap.leftObj, (Diagram.chain d).endR_eq]
    show φ.layer _ = (φ.layer L).whisker _ _
    rw [e]
    exact φ.layer_whisker hv u v

variable {R : Type w} [CommRing R] (Q : Presentation.{w, v'} S' R) (χ : S.Gen → R)

/-- A parity-preserving reflection in a vertical axis respects the interchange law: an instance
with `g` on the left and `h` on the right goes to the instance with the reflection of `h` on the
left and the reflection of `g` on the right. -/
theorem toPresented_interchange (hodd : ∀ g, S'.odd (φ.gen g) = S.odd g)
    {x : InterchangeData S} (hx : x.Valid) :
    (freeLift R (φ.toLayerMap.toPresented Q χ)).map (InterchangeData.rel R hx) = 0 := by
  have e₀ : S.endR (S.right x.g) x.mid = S.left x.h := by
    have h₀ := hx.gh₁.left_end
    have h₁ := hx.hg₁.left_end
    have h₂ := hx.gh₁.dom_end
    simp only [InterchangeData.hg₁, InterchangeData.gh₁, Signature.endR_append,
      Signature.endR_nil] at h₀ h₁ h₂
    rwa [h₀, h₂] at h₁
  have e₁ : S.endR (S.right x.g) (x.mid ++ S.dom x.h) = S.right x.h := by
    rw [Signature.endR_append, e₀]; exact hx.hg₁.dom_end
  have e₂ : S.endR (S.right x.g) (x.mid ++ S.cod x.h) = S.right x.h := by
    rw [Signature.endR_append, e₀]; exact hx.hg₁.cod_end
  refine φ.toLayerMap.toPresented_interchange_swap Q χ hx
    ⟨φ.region (S.right x.h), φ.gen x.h, φ.word x.mid, φ.gen x.g⟩ ?_ ?_ ?_ ?_ ?_
  · refine Layer.ext (by simp [layer, InterchangeData.gh₁, InterchangeData.hg₁, e₁]) ?_ rfl ?_
    · simp [layer, InterchangeData.gh₁, InterchangeData.hg₁, φ.dom',
        MirrorColourMap.word_append]
    · rfl
  · refine Layer.ext rfl ?_ rfl ?_
    · rfl
    · simp [layer, InterchangeData.gh₂, InterchangeData.hg₂, φ.cod',
        MirrorColourMap.word_append]
  · refine Layer.ext rfl ?_ rfl ?_
    · rfl
    · simp [layer, InterchangeData.hg₁, InterchangeData.gh₁, φ.dom',
        MirrorColourMap.word_append]
  · refine Layer.ext (by simp [layer, InterchangeData.hg₂, InterchangeData.gh₂, e₂]) ?_ rfl ?_
    · simp [layer, InterchangeData.hg₂, InterchangeData.gh₂, φ.cod',
        MirrorColourMap.word_append]
    · rfl
  · simp [InterchangeData.sign, hodd, Bool.and_comm]

variable (P : Presentation.{w, v} S R) {Q χ}

/-- **Functors from reflections in a vertical axis.** For a parity-preserving reflection `φ`
in a vertical axis and weights `χ`, if the image of every relation of `P` vanishes in `Q` and
the relations of `P` have well-formed bottom boundaries, then `φ` induces a functor
`P.Presented ⥤ Q.Presented` sending the class of a diagram `d` to `weight χ d • [φ d]`. It
reverses the order of 1-morphisms (`SigMirror.lift_whisk`). -/
def lift (hodd : ∀ g, S'.odd (φ.gen g) = S.odd g) (hwf : P.WFDom)
    (hrel : ∀ r, (freeLift R (φ.toLayerMap.toPresented Q χ)).map (P.rel r) = 0) :
    P.Presented ⥤ Q.Presented :=
  LayerMap.lift P φ.whiskerData hwf (fun _ => hrel)
    (fun _ _ hx => φ.toPresented_interchange Q χ hodd hx) ()

variable {P} (hodd : ∀ g, S'.odd (φ.gen g) = S.odd g) (hwf : P.WFDom)
  (hrel : ∀ r, (freeLift R (φ.toLayerMap.toPresented Q χ)).map (P.rel r) = 0)

instance lift_additive : (φ.lift P hodd hwf hrel).Additive := LayerMap.lift_additive _ _ _ _ _

instance lift_linear : (φ.lift P hodd hwf hrel).Linear R := LayerMap.lift_linear _ _ _ _ _

@[simp] theorem lift_obj (a : Obj S) :
    (φ.lift P hodd hwf hrel).obj (P.obj a) = Q.obj (φ.obj a) := rfl

@[simp] theorem lift_diag {a b : Obj S} (d : a ⟶ b) :
    (φ.lift P hodd hwf hrel).map (P.diag d) = Diagram.weight χ d • Q.diag (φ.toLayerMap.map d) :=
  LayerMap.lift_diag _ _ _ _ _ d

theorem lift_lin {a b : Obj S} (f : LinDiagram R a b) :
    (φ.lift P hodd hwf hrel).map (P.lin f) = (freeLift R (φ.toLayerMap.toPresented Q χ)).map f :=
  LayerMap.lift_lin _ _ _ _ _ f

/-- **A reflection in a vertical axis reverses the order of 1-morphisms**: whiskering by `u` on
the left and `v` on the right becomes whiskering by the reflection of `v` on the left and the
reflection of `u` on the right. -/
theorem lift_whisk {a b : Obj S} (f : P.obj a ⟶ P.obj b) {u : Obj S} {v : List S.Colour}
    (ha : a.WF) (hw : a.WhiskerOK u v) (hb : Nonempty (a ⟶ b)) :
    (φ.lift P hodd hwf hrel).map (P.whisk f u v) =
      eqToHom (congrArg Q.obj (φ.whiskerData.obj_whisker (i := ()) ha hw ⟨𝟙 a⟩).symm) ≫
        Q.whisk ((φ.lift P hodd hwf hrel).map f) (φ.leftObj a v) (φ.word u.word) ≫
          eqToHom (congrArg Q.obj (φ.whiskerData.obj_whisker (i := ()) ha hw hb)) :=
  LayerMap.lift_whisk (P := P) φ.whiskerData hwf (fun _ => hrel)
    (fun _ _ hx => φ.toPresented_interchange Q χ hodd hx) () f ha hw hb

end SigMirror

/-! ## Horizontal composition and Koszul signs -/

theorem Diagram.oddCountList_map {S' : Signature.{u₀', u₁', u₂'}} (f : Layer S → Layer S')
    (ls : List (Layer S)) (h : ∀ L ∈ ls, S'.odd (f L).gen = S.odd L.gen) :
    Diagram.oddCountList (ls.map f) = Diagram.oddCountList ls := by
  simp only [Diagram.oddCountList, List.filter_map, List.length_map]
  congr 1
  exact List.filter_congr fun L hL => by simp [h L hL]

theorem Diagram.oddCountList_reverse (ls : List (Layer S)) :
    Diagram.oddCountList ls.reverse = Diagram.oddCountList ls := by
  simp [Diagram.oddCountList, List.filter_reverse]

namespace Presentation

variable {R : Type w} [CommRing R] (P : Presentation.{w, v} S R)

/-- The interchange law for arbitrary diagrams and general regions, read from right to left. -/
theorem diag_interchange_of_composable_symm {a a' b b' : Obj S} (f : a ⟶ a') (g : b ⟶ b')
    (h : a.Composable b) (h₁ : a'.Composable b) (h₂ : a.Composable b') :
    P.diag (Diagram.lwhisker a g h ≫ Diagram.rwhisker f b' h₂) =
      ((-1 : ℤ) ^ (Diagram.oddCount f * Diagram.oddCount g)) •
        P.diag (Diagram.rwhisker f b h ≫ Diagram.lwhisker a' g h₁) := by
  rw [P.diag_interchange_of_composable' f g h h₁ h₂, smul_smul, ← pow_add, ← two_mul,
    pow_mul, neg_one_sq, one_pow, one_smul]

end Presentation

namespace ColourMap

variable (κ : ColourMap S S')

theorem obj_tensor (a b : Obj S) : κ.obj (a.tensor b) = (κ.obj a).tensor (κ.obj b) := by
  simp [obj, Obj.tensor]

theorem composable {a b : Obj S} (h : a.Composable b) : (κ.obj a).Composable (κ.obj b) :=
  ⟨κ.ok_map h.left_wf, by rw [obj_endR, h.endR_eq]; rfl, κ.ok_map h.right_wf⟩

end ColourMap

namespace SigMap

variable (φ : SigMap S S')

theorem map_rwhisker {a a' : Obj S} (f : a ⟶ a') (b : Obj S) (h : a.Composable b) :
    φ.toLayerMap.map (Diagram.rwhisker f b h) =
      Diagram.cast (Diagram.rwhisker (φ.toLayerMap.map f) (φ.obj b) (φ.composable h))
        (φ.obj_tensor a b).symm (φ.obj_tensor a' b).symm :=
  Diagram.ext (by simp [layer, Layer.wr, ColourMap.obj, Function.comp_def])

theorem map_lwhisker (a : Obj S) {b b' : Obj S} (g : b ⟶ b') (h : a.Composable b) :
    φ.toLayerMap.map (Diagram.lwhisker a g h) =
      Diagram.cast (Diagram.lwhisker (φ.obj a) (φ.toLayerMap.map g) (φ.composable h))
        (φ.obj_tensor a b).symm (φ.obj_tensor a b').symm :=
  Diagram.ext (by simp [layer, Layer.wl, ColourMap.obj, Function.comp_def])

/-- A map of signatures commutes with horizontal composition `f ⊗ g = (f ⊗ 1) ≫ (1 ⊗ g)`. -/
theorem map_tensor {a a' b b' : Obj S} (f : a ⟶ a') (g : b ⟶ b') (h : a.Composable b) :
    φ.toLayerMap.map (Diagram.rwhisker f b h ≫ Diagram.lwhisker a' g (h.map_left f)) =
      Diagram.cast (Diagram.rwhisker (φ.toLayerMap.map f) (φ.obj b) (φ.composable h) ≫
          Diagram.lwhisker (φ.obj a') (φ.toLayerMap.map g) (φ.composable (h.map_left f)))
        (φ.obj_tensor a b).symm (φ.obj_tensor a' b').symm :=
  Diagram.ext (by simp [layer, Layer.wl, Layer.wr, ColourMap.obj, Function.comp_def])

end SigMap

namespace SigFlip

variable (φ : SigFlip S S')

theorem map_rwhisker {a a' : Obj S} (f : a ⟶ a') (b : Obj S) (h : a.Composable b) :
    φ.toOpLayerMap.map (Diagram.rwhisker f b h) =
      Diagram.cast (Diagram.rwhisker (φ.toOpLayerMap.map f) (φ.obj b)
          (φ.composable (h.map_left f)))
        (φ.obj_tensor a' b).symm (φ.obj_tensor a b).symm :=
  Diagram.ext (by simp [layer, Layer.wr, ColourMap.obj, Function.comp_def, List.map_reverse])

theorem map_lwhisker (a : Obj S) {b b' : Obj S} (g : b ⟶ b') (h : a.Composable b) :
    φ.toOpLayerMap.map (Diagram.lwhisker a g h) =
      Diagram.cast (Diagram.lwhisker (φ.obj a) (φ.toOpLayerMap.map g)
          (φ.composable (h.map_right g)))
        (φ.obj_tensor a b').symm (φ.obj_tensor a b).symm :=
  Diagram.ext (by simp [layer, Layer.wl, ColourMap.obj, Function.comp_def, List.map_reverse])

theorem oddCount_map (hodd : ∀ g, S'.odd (φ.gen g) = S.odd g) {a b : Obj S} (d : a ⟶ b) :
    Diagram.oddCount (φ.toOpLayerMap.map d) = Diagram.oddCount d := by
  simp only [Diagram.oddCount, OpLayerMap.layers_map, Diagram.oddCountList_reverse]
  exact Diagram.oddCountList_map _ _ fun L _ => hodd L.gen

variable {R : Type w} [CommRing R] (Q : Presentation.{w, v'} S' R)

/-- **Koszul signs for reflections in a horizontal axis.** For `f : a ⟶ a'`, `g : b ⟶ b'` with
`a` composable with `b`, the reflection of `f ⊗ g = (f ⊗ 1) ≫ (1 ⊗ g)` is
`(-1)^{|f||g|} ψ f ⊗ ψ g` in the presented category, where `ψ f : ψ a' ⟶ ψ a` and
`ψ g : ψ b' ⟶ ψ b` are the reflections. -/
theorem diag_map_tensor (hodd : ∀ g, S'.odd (φ.gen g) = S.odd g) {a a' b b' : Obj S}
    (f : a ⟶ a') (g : b ⟶ b') (h : a.Composable b) :
    Q.diag (φ.toOpLayerMap.map (Diagram.rwhisker f b h ≫ Diagram.lwhisker a' g (h.map_left f))) =
      ((-1 : ℤ) ^ (Diagram.oddCount f * Diagram.oddCount g)) •
        (eqToHom (congrArg Q.obj (φ.obj_tensor a' b')) ≫
          Q.diag (Diagram.rwhisker (φ.toOpLayerMap.map f) (φ.obj b')
              (φ.composable ((h.map_left f).map_right g)) ≫
            Diagram.lwhisker (φ.obj a) (φ.toOpLayerMap.map g) (φ.composable (h.map_right g))) ≫
          eqToHom (congrArg Q.obj (φ.obj_tensor a b)).symm) := by
  have key := Q.diag_interchange_of_composable_symm (φ.toOpLayerMap.map f)
    (φ.toOpLayerMap.map g) (φ.composable ((h.map_left f).map_right g))
    (φ.composable (h.map_right g)) (φ.composable (h.map_left f))
  rw [φ.oddCount_map hodd, φ.oddCount_map hodd] at key
  simp only [toOpLayerMap_obj] at key
  rw [OpLayerMap.map_comp, φ.map_rwhisker, φ.map_lwhisker, Q.diag_comp, Q.diag_cast,
    Q.diag_cast]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Category.assoc (Q.diag _) (Q.diag _), ← Q.diag_comp, key, Linear.smul_comp,
    Linear.comp_smul]

end SigFlip

namespace MirrorColourMap

variable (κ : MirrorColourMap S S')

theorem obj_tensor {a b : Obj S} (h : a.Composable b) :
    κ.obj (a.tensor b) = (κ.obj b).tensor (κ.obj a) := by
  refine Obj.ext ?_ ?_
  · show κ.region (S.endR a.start (a.word ++ b.word)) = κ.region b.endR
    rw [Signature.endR_append]
    exact congrArg (fun r => κ.region (S.endR r b.word)) h.endR_eq
  · simp [obj, Obj.tensor, word_append]

theorem composable {a b : Obj S} (h : a.Composable b) : (κ.obj b).Composable (κ.obj a) :=
  ⟨(κ.ok_word h.right_wf).1, by rw [κ.obj_endR h.right_wf, ← h.endR_eq]; rfl,
    (κ.ok_word h.left_wf).1⟩

end MirrorColourMap

namespace SigMirror

variable (φ : SigMirror S S')

/-- The reflection of `f ⊗ 1_b` is `1_{σ b} ⊗ σ f`. -/
theorem map_rwhisker {a a' : Obj S} (f : a ⟶ a') (b : Obj S) (h : a.Composable b) :
    φ.toLayerMap.map (Diagram.rwhisker f b h) =
      Diagram.cast (Diagram.lwhisker (φ.obj b) (φ.toLayerMap.map f) (φ.composable h))
        (φ.obj_tensor h).symm (φ.obj_tensor (h.map_left f)).symm := by
  apply Diagram.ext
  simp only [LayerMap.layers_map, Diagram.layers_rwhisker, Diagram.layers_cast,
    Diagram.layers_lwhisker, List.map_map]
  refine List.map_congr_left fun L hL => ?_
  have hv := (Diagram.chain f).valid_of_mem hL
  obtain ⟨d⟩ := (Diagram.chain f).nonempty_of_mem hL
  refine Layer.ext ?_ ?_ rfl rfl
  · show φ.region (S.endR (S.right L.gen) (L.right ++ b.word)) = φ.region b.endR
    rw [Signature.endR_append, ← hv.endR_dom, (Diagram.chain d).endR_eq, h.endR_eq]
    rfl
  · simp [layer, Layer.wr, Layer.wl, MirrorColourMap.obj, MirrorColourMap.word_append]

/-- The reflection of `1_a ⊗ g` is `σ g ⊗ 1_{σ a}`. -/
theorem map_lwhisker (a : Obj S) {b b' : Obj S} (g : b ⟶ b') (h : a.Composable b) :
    φ.toLayerMap.map (Diagram.lwhisker a g h) =
      Diagram.cast (Diagram.rwhisker (φ.toLayerMap.map g) (φ.obj a) (φ.composable h))
        (φ.obj_tensor h).symm (φ.obj_tensor (h.map_right g)).symm :=
  Diagram.ext (by
    simp [layer, Layer.wr, Layer.wl, MirrorColourMap.obj, MirrorColourMap.word_append,
      Function.comp_def])

theorem oddCount_map (hodd : ∀ g, S'.odd (φ.gen g) = S.odd g) {a b : Obj S} (d : a ⟶ b) :
    Diagram.oddCount (φ.toLayerMap.map d) = Diagram.oddCount d := by
  simp only [Diagram.oddCount, LayerMap.layers_map]
  exact Diagram.oddCountList_map _ _ fun L _ => hodd L.gen

variable {R : Type w} [CommRing R] (Q : Presentation.{w, v'} S' R)

/-- **Koszul signs for reflections in a vertical axis.** For `f : a ⟶ a'`, `g : b ⟶ b'` with
`a` composable with `b`, the reflection of `f ⊗ g = (f ⊗ 1) ≫ (1 ⊗ g)` is
`(-1)^{|f||g|} σ g ⊗ σ f` in the presented category. -/
theorem diag_map_tensor (hodd : ∀ g, S'.odd (φ.gen g) = S.odd g) {a a' b b' : Obj S}
    (f : a ⟶ a') (g : b ⟶ b') (h : a.Composable b) :
    Q.diag (φ.toLayerMap.map (Diagram.rwhisker f b h ≫ Diagram.lwhisker a' g (h.map_left f))) =
      ((-1 : ℤ) ^ (Diagram.oddCount f * Diagram.oddCount g)) •
        (eqToHom (congrArg Q.obj (φ.obj_tensor h)) ≫
          Q.diag (Diagram.rwhisker (φ.toLayerMap.map g) (φ.obj a) (φ.composable h) ≫
            Diagram.lwhisker (φ.obj b') (φ.toLayerMap.map f) (φ.composable (h.map_right g))) ≫
          eqToHom (congrArg Q.obj (φ.obj_tensor ((h.map_left f).map_right g))).symm) := by
  have key := Q.diag_interchange_of_composable_symm (φ.toLayerMap.map g)
    (φ.toLayerMap.map f) (φ.composable h) (φ.composable (h.map_right g))
    (φ.composable (h.map_left f))
  rw [φ.oddCount_map hodd, φ.oddCount_map hodd, mul_comm] at key
  simp only [toLayerMap_obj] at key
  rw [LayerMap.map_comp, φ.map_rwhisker, φ.map_lwhisker, Q.diag_comp, Q.diag_cast,
    Q.diag_cast]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Category.assoc (Q.diag _) (Q.diag _), ← Q.diag_comp, key, Linear.smul_comp,
    Linear.comp_smul]

end SigMirror

end StringDiagrams

end
