import StringDiagrams.LayerMap.Local
import StringDiagrams.Super.SOp

/-!
# Contravariant superfunctors out of presented categories

A *contravariant superfunctor* from a presented category `P.Presented` to a presented category
`Q.Presented` is a functor `P.Presented ⥤ SOp R Q.Presented` into the super-opposite
(`StringDiagrams.Super.SOp`; Brundan–Ellis, *Super Kac–Moody 2-categories*, Definition 3.4): it
reverses vertical composition up to the Koszul sign,
`F(f ≫ g) = (-1)^{|f||g|} F(g) ∘ F(f)`.

This file constructs such functors from images of generators, as `LocalMap.liftGen` does for
covariant functors: a relabelling `κ` of regions and strands (`ColourMap`) and, for every
generator `g : dom → cod`, a morphism `img g : κ cod ⟶ κ dom` of `Q.Presented`, homogeneous of the
parity of `g`. A layer `u ⊗ g ⊗ v` goes to `κ u ⊗ img g ⊗ κ v` (in the opposite direction), and a
diagram to the composite of the images of its layers in `SOp R Q.Presented`. The interchange law
is respected automatically, by the super interchange law in `Q.Presented` and the sign in the
composition of `SOp` (`SOpMap.ofGen_interchange`), and the relations are respected as soon as
their images vanish without whiskering (`SOpMap.liftGen`). The resulting functor commutes with
whiskering (`SOpMap.liftGen_whisk`) and preserves parities (`SOpMap.liftGen_mem`).

The supercategory structure on `Q.Presented` is any one whose parities are those of the parity
grading (`hpar`), e.g. `Presentation.supercategory`.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory

universe w v v' u₀ u₁ u₂ u₀' u₁' u₂'

variable {S : Signature.{u₀, u₁, u₂}} {S' : Signature.{u₀', u₁', u₂'}} {R : Type w} [CommRing R]

namespace SOpMap

variable {Q : Presentation.{w, v'} S' R} [Supercategory R Q.Presented]
  (hpar : ∀ (a b : Obj S') (p : ZMod 2),
    parity (R := R) (Q.obj a) (Q.obj b) p = Q.homDeg (Presentation.parityDeg S') a b p)

include hpar in
/-- Whiskering in `Q.Presented` commutes with the parity projections. -/
theorem proj_whisk (p : ZMod 2) {a b : Obj S'} (f : Q.obj a ⟶ Q.obj b) (u : Obj S')
    (v : List S'.Colour) :
    proj R p (Q.whisk f u v) = Q.whisk (proj R p f) u v := by
  have hm : ∀ q, Q.whisk (proj R q f) u v ∈ parity (R := R) (Q.obj (a.whisker u v))
      (Q.obj (b.whisker u v)) q := fun q => by
    rw [hpar]
    exact Presentation.whisk_mem_homDeg (by rw [← hpar]; exact proj_mem q f) u v
  conv_lhs => rw [← proj_add_proj (R := R) f, Q.whisk_add]
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [map_add, proj_of_mem (hm 0), proj_of_mem_ne (hm 1) (by decide), add_zero]
  · rw [map_add, proj_of_mem (hm 1), proj_of_mem_ne (hm 0) (by decide), zero_add]

include hpar in
theorem twist_whisk (p : ZMod 2) {a b : Obj S'} (f : Q.obj a ⟶ Q.obj b) (u : Obj S')
    (v : List S'.Colour) :
    twist R p (Q.whisk f u v) = Q.whisk (twist R p f) u v := by
  rw [twist_apply, twist_apply, proj_whisk hpar, proj_whisk hpar, Q.whisk_add, Q.whisk_smul]

include hpar in
/-- Whiskering in `Q.Presented` commutes with the composition law of the super-opposite. -/
theorem whisk_compC {a b c : Obj S'} (f : Q.obj b ⟶ Q.obj a) (g : Q.obj c ⟶ Q.obj b)
    (u : Obj S') (v : List S'.Colour) :
    Q.whisk (SOp.compC (R := R) f g) u v =
      SOp.compC (R := R) (Q.whisk f u v) (Q.whisk g u v) := by
  unfold SOp.compC
  rw [Q.whisk_add, Q.whisk_comp, Q.whisk_comp, proj_whisk hpar, proj_whisk hpar, twist_whisk hpar]

omit [Supercategory R Q.Presented] in
private theorem whisk_congr' {a b : Obj S'} (f : Q.obj a ⟶ Q.obj b) {u u' : Obj S'}
    {v v' : List S'.Colour} (hu : u = u') (hv : v = v') :
    Q.whisk f u v = eqToHom (by rw [hu, hv]) ≫ Q.whisk f u' v' ≫ eqToHom (by rw [hu, hv]) := by
  subst hu hv; simp

omit [Supercategory R Q.Presented] in
private theorem whisk_nil_eq_wRAt {a a' : Obj S'} (f : Q.obj a ⟶ Q.obj a') {r : S'.Region}
    (b : Obj S') (ha : a.start = r) (ha' : a'.start = r) :
    Q.whisk f (Obj.nil r) b.word =
      eqToHom (congrArg Q.obj (Obj.tensor_eq_whisker_nil_of_start b ha)).symm ≫
        Q.wRAt r f b ha ha' ≫
          eqToHom (congrArg Q.obj (Obj.tensor_eq_whisker_nil_of_start b ha')) := by
  simp [Presentation.wRAt]

omit [Supercategory R Q.Presented] in
private theorem whisk_eq_wL {b b' : Obj S'} (g : Q.obj b ⟶ Q.obj b') (a : Obj S') :
    Q.whisk g a [] =
      eqToHom (congrArg Q.obj (Obj.tensor_eq_whisker_nil a b)).symm ≫ Q.wL a g ≫
        eqToHom (congrArg Q.obj (Obj.tensor_eq_whisker_nil a b')) := by
  simp [Presentation.wL]

variable (κ : ColourMap S S')
  (img : (g : S.Gen) → (Q.obj (LocalMap.genCod κ g) ⟶ Q.obj (LocalMap.genDom κ g)))

open LocalMap in
/-- The image of a layer `u ⊗ g ⊗ v`: `κ u ⊗ img g ⊗ κ v`, a morphism of `Q.Presented` from the
image of the top boundary to the image of the bottom boundary. -/
def layerImg (L : Layer S) : Q.obj (κ.obj L.cod) ⟶ Q.obj (κ.obj L.dom) :=
  eqToHom (congrArg Q.obj (whisker_genCod κ L)).symm ≫
    Q.whisk (img L.gen) (κ.obj ⟨L.start, L.left⟩) (κ.word L.right) ≫
      eqToHom (congrArg Q.obj (whisker_genDom κ L))

/-- The interpretation in the super-opposite given by images of generators. -/
def interp : Interpretation S (SOp R Q.Presented) where
  obj a := ⟨Q.obj (κ.obj a)⟩
  layer L _ := SOp.mk' (layerImg κ img L)

/-- The functor of the free 2-category into the super-opposite given by images of generators. -/
def functor : Obj S ⥤ SOp R Q.Presented := (interp κ img).functor

@[simp] theorem functor_obj (a : Obj S) : (functor κ img).obj a = ⟨Q.obj (κ.obj a)⟩ := rfl

theorem functor_map_ofLayer (L : Layer S) (hv : L.Valid) :
    SOp.unsop ((functor κ img).map (Diagram.ofLayer L hv)) = layerImg κ img L := by
  show SOp.unsop ((interp κ img).functor.map _) = _
  rw [Interpretation.functor_map_ofLayer]; rfl

variable {κ img}

include hpar in
open LocalMap in
theorem layerImg_mem
    (himg : ∀ g, img g ∈ Q.homDeg (Presentation.parityDeg S') (genCod κ g) (genDom κ g)
      (Presentation.parityDeg S g)) (L : Layer S) :
    layerImg κ img L ∈ parity (R := R) (Q.obj (κ.obj L.cod)) (Q.obj (κ.obj L.dom))
      (Presentation.parityDeg S L.gen) := by
  rw [hpar]
  have := Presentation.comp_mem_homDeg (Presentation.eqToHom_mem_homDeg (P := Q)
    (Presentation.parityDeg S') (congrArg Q.obj (whisker_genCod κ L)).symm)
    (Presentation.comp_mem_homDeg
      (Presentation.whisk_mem_homDeg (himg L.gen) (κ.obj ⟨L.start, L.left⟩) (κ.word L.right))
      (Presentation.eqToHom_mem_homDeg (P := Q) (Presentation.parityDeg S')
        (congrArg Q.obj (whisker_genDom κ L))))
  rwa [zero_add, add_zero] at this

/-! ### Whiskering -/

section Whisker

variable {C : Type*} [Category C] [Preadditive C] [Linear R C] [Supercategory R C]

theorem compC_eqToHom {X X' Y Y' Z Z' : C} (hY : Y = Y') (A : Y' ⟶ X') (hX : X' = X)
    (hZ : Z = Z') (B : Z' ⟶ Y') :
    SOp.compC (R := R) (eqToHom hY ≫ A ≫ eqToHom hX) (eqToHom hZ ≫ B ≫ eqToHom hY.symm) =
      eqToHom hZ ≫ SOp.compC (R := R) A B ≫ eqToHom hX := by
  subst hX hY hZ; simp

end Whisker

open LocalMap in
omit [Supercategory R Q.Presented] in
theorem genCod_whiskerOK {L : Layer S} (hv : L.Valid) :
    (genCod κ L.gen).WhiskerOK (κ.obj ⟨L.start, L.left⟩) (κ.word L.right) := by
  refine ⟨κ.ok_map hv.left_ok, ?_, ?_⟩
  · show S'.endR (κ.region L.start) (κ.word L.left) = κ.region (S.left L.gen)
    rw [κ.endR_map, hv.left_end]
  · show S'.ok (S'.endR (κ.region (S.left L.gen)) (κ.word (S.cod L.gen))) _
    rw [κ.endR_map, hv.cod_end]; exact κ.ok_map hv.right_ok

set_option backward.isDefEq.respectTransparency false in
open LocalMap in
omit [Supercategory R Q.Presented] in
/-- The image of a whiskered layer is the whiskered image of the layer. -/
theorem layerImg_whisker {u : Obj S} {v : List S.Colour} {L : Layer S} (hv : L.Valid)
    (hwL : L.dom.WhiskerOK u v) :
    layerImg κ img (L.whisker u v) =
      eqToHom (by rw [L.whisker_cod, κ.obj_whisker]) ≫
        Q.whisk (layerImg κ img L) (κ.obj u) (κ.word v) ≫
          eqToHom (by rw [L.whisker_dom, κ.obj_whisker]) := by
  have hwc : L.cod.WhiskerOK u v := Chain.whiskerOK (ls := [L]) ⟨hv, rfl, rfl⟩ hwL
  have hw₀ := genCod_whiskerOK (κ := κ) hv
  have hw₁ : ((genCod κ L.gen).whisker (κ.obj ⟨L.start, L.left⟩)
      (κ.word L.right)).WhiskerOK (κ.obj u) (κ.word v) := by
    rw [whisker_genCod]; exact κ.whiskerOK hwc
  rw [layerImg, layerImg, Q.whisk_comp, Q.whisk_comp,
    Q.whisk_eqToHom (whisker_genCod κ L).symm _ _ (κ.whiskerOK hwc),
    Q.whisk_eqToHom (whisker_genDom κ L) _ _ (by rw [whisker_genDom]; exact κ.whiskerOK hwL),
    Q.whisk_whisk _ _ _ _ _ hw₀ hw₁,
    whisk_congr' (img L.gen) (u := (κ.obj u).tensor (κ.obj ⟨L.start, L.left⟩))
      (v := κ.word L.right ++ κ.word v) (u' := κ.obj ⟨(L.whisker u v).start,
      (L.whisker u v).left⟩) (v' := κ.word (L.whisker u v).right)
      (by simp [ColourMap.obj, Obj.tensor, Layer.whisker]) (by simp [Layer.whisker])]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  rfl

omit [Supercategory R Q.Presented] in
theorem layerImg_whisker' {u : Obj S} {v : List S.Colour} {L : Layer S} (hv : L.Valid)
    (hwL : L.dom.WhiskerOK u v) {X Y : Obj S'} (hX : κ.obj (L.whisker u v).cod = X)
    (hY : κ.obj (L.whisker u v).dom = Y) :
    eqToHom (congrArg Q.obj hX).symm ≫ layerImg κ img (L.whisker u v) ≫ eqToHom (congrArg Q.obj hY) =
      eqToHom (by rw [← hX, L.whisker_cod, κ.obj_whisker]) ≫
        Q.whisk (layerImg κ img L) (κ.obj u) (κ.word v) ≫
          eqToHom (by rw [← hY, L.whisker_dom, κ.obj_whisker]) := by
  subst hX hY
  rw [layerImg_whisker hv hwL]
  simp

section SOpEq

variable {C : Type*} [Category C] [Preadditive C] [Linear R C] [Supercategory R C]

theorem unsop_eqToHom_comp {X Y Z : SOp R C} (h : X = Y) (f : Y ⟶ Z) :
    SOp.unsop (eqToHom h ≫ f) = SOp.unsop f ≫ eqToHom (congrArg SOp.unop h).symm := by
  subst h; simp

theorem unsop_comp_eqToHom {X Y Z : SOp R C} (f : X ⟶ Y) (h : Y = Z) :
    SOp.unsop (f ≫ eqToHom h) = eqToHom (congrArg SOp.unop h).symm ≫ SOp.unsop f := by
  subst h; simp

end SOpEq

include hpar in
set_option backward.isDefEq.respectTransparency false in
theorem functor_map_whisker_aux (u : Obj S) (v : List S.Colour) :
    ∀ (ls : List (Layer S)) {c b : Obj S} (hc : Chain c ls b) (hwc : c.WhiskerOK u v),
      SOp.unsop ((functor κ img).map (Diagram.whisker (Diagram.mk ls hc) u v hwc)) =
        eqToHom (congrArg Q.obj (κ.obj_whisker b u v)) ≫
          Q.whisk (SOp.unsop ((functor κ img).map (Diagram.mk ls hc))) (κ.obj u) (κ.word v) ≫
            eqToHom (congrArg Q.obj (κ.obj_whisker c u v)).symm := by
  intro ls
  induction ls with
  | nil =>
    intro c b hc hwc
    cases hc
    rw [show Diagram.mk [] (rfl : Chain c [] c) = 𝟙 c from rfl, Diagram.whisker_id,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    change (𝟙 (Q.obj (κ.obj (c.whisker u v)))) = eqToHom _ ≫
      Q.whisk (𝟙 (Q.obj (κ.obj c))) (κ.obj u) (κ.word v) ≫ eqToHom _
    rw [Q.whisk_id _ _ _ (κ.whiskerOK hwc), Category.id_comp, eqToHom_trans, eqToHom_refl]
  | cons L ls ih =>
    intro c b hc hwc
    obtain ⟨hv, rfl, hc'⟩ := hc
    have e : Diagram.mk (L :: ls) (show Chain L.dom (L :: ls) b from ⟨hv, rfl, hc'⟩) =
        Diagram.ofLayer L hv ≫ Diagram.mk ls hc' := Diagram.ext rfl
    have hwc' : L.cod.WhiskerOK u v := Chain.whiskerOK (ls := [L]) ⟨hv, rfl, rfl⟩ hwc
    have hv' : (L.whisker u v).Valid := hv.whisker hwc
    have el : Diagram.whisker (Diagram.ofLayer L hv) u v hwc =
        Diagram.layer (L.whisker u v) hv' (L.whisker_dom u v) (L.whisker_cod u v) :=
      Diagram.ext rfl
    rw [e, Diagram.whisker_comp, Functor.map_comp, el, SOp.unsop_comp, ih hc' hwc',
      Functor.map_comp, SOp.unsop_comp, functor_map_ofLayer, whisk_compC hpar]
    have hl : SOp.unsop ((functor κ img).map (Diagram.layer (L.whisker u v) hv'
        (L.whisker_dom u v) (L.whisker_cod u v))) =
        eqToHom (congrArg Q.obj (congrArg κ.obj (L.whisker_cod u v)).symm) ≫
          layerImg κ img (L.whisker u v) ≫
            eqToHom (congrArg Q.obj (congrArg κ.obj (L.whisker_dom u v))) := by
      show SOp.unsop ((interp κ img).functor.map _) = _
      rw [Interpretation.functor_map_layer, unsop_eqToHom_comp, unsop_comp_eqToHom]
      simp only [Category.assoc]
      rfl
    rw [hl, layerImg_whisker' (img := img) hv hwc (congrArg κ.obj (L.whisker_cod u v))
      (congrArg κ.obj (L.whisker_dom u v))]
    exact compC_eqToHom _ _ _ _ _

include hpar in
/-- The image of a diagram with two layers. -/
theorem functor_map_two
    (himg : ∀ g, img g ∈ Q.homDeg (Presentation.parityDeg S') (LocalMap.genCod κ g)
      (LocalMap.genDom κ g) (Presentation.parityDeg S g))
    {a b : Obj S} (L₁ L₂ : Layer S) (h : Chain a [L₁, L₂] b) :
    SOp.unsop ((functor κ img).map (Diagram.mk [L₁, L₂] h)) =
      ((Supercategory.koszulSign (Presentation.parityDeg S L₁.gen)
          (Presentation.parityDeg S L₂.gen) : ℤ) : R) •
        (eqToHom (congrArg (fun x => Q.obj (κ.obj x)) h.2.2.2.2.symm) ≫ layerImg κ img L₂ ≫
          eqToHom (congrArg (fun x => Q.obj (κ.obj x)) h.2.2.2.1) ≫ layerImg κ img L₁ ≫
            eqToHom (congrArg (fun x => Q.obj (κ.obj x)) h.2.1)) := by
  obtain ⟨hv₁, rfl, hv₂, e₁₂, rfl⟩ := h
  have m₁ := layerImg_mem hpar himg L₁
  have m₂ : layerImg κ img L₂ ≫ eqToHom (congrArg (fun x => Q.obj (κ.obj x)) e₁₂) ∈
        parity (R := R) (Q.obj (κ.obj L₂.cod)) (Q.obj (κ.obj L₁.cod))
          (Presentation.parityDeg S L₂.gen) := by
    have he : eqToHom (congrArg (fun x => Q.obj (κ.obj x)) e₁₂) ∈
        parity (R := R) (Q.obj (κ.obj L₂.dom)) (Q.obj (κ.obj L₁.cod)) 0 := by
      rw [hpar]; exact Presentation.eqToHom_mem_homDeg _ _
    simpa using comp_mem (layerImg_mem hpar himg L₂) he
  show SOp.unsop ((interp κ img).functor.map _) = _
  erw [Interpretation.functor_map_mk_cons, Interpretation.functor_map_mk_cons,
    Interpretation.functor_map_mk_nil]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  erw [Category.comp_id, SOp.unsop_comp, unsop_eqToHom_comp]
  change SOp.compC (R := R) (layerImg κ img L₁) (layerImg κ img L₂ ≫ _) = _
  refine (SOp.compC_of_mem m₁ m₂).trans ?_
  rw [Supercategory.sign_mul, Category.assoc]

open LocalMap in
include hpar in
set_option backward.isDefEq.respectTransparency false in
/-- **Images of generators respect the interchange law**: the super interchange law in
`Q.Presented` and the sign in the composition of the super-opposite. -/
theorem ofGen_interchange
    (himg : ∀ g, img g ∈ Q.homDeg (Presentation.parityDeg S') (genCod κ g) (genDom κ g)
      (Presentation.parityDeg S g))
    {x : InterchangeData S} (hx : x.Valid) :
    (freeLift R (functor κ img)).map (InterchangeData.rel R hx) = 0 := by
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
  have key := Q.wRAt_comp_wL_super (hA'M.tensor_right hMC) (himg x.g) hG hA' hA
  have hk : ((Supercategory.koszulSign (Presentation.parityDeg S x.g)
      (Presentation.parityDeg S x.h) : ℤ) : R) = ((x.sign : ℤ) : R) := by
    congr 1
    unfold InterchangeData.sign Presentation.parityDeg
    cases S.odd x.g <;> cases S.odd x.h <;> simp
  have hk' : ((Supercategory.koszulSign (Presentation.parityDeg S x.hg₁.gen)
      (Presentation.parityDeg S x.hg₂.gen) : ℤ) : R) = ((x.sign : ℤ) : R) := by
    show ((Supercategory.koszulSign (Presentation.parityDeg S x.h)
      (Presentation.parityDeg S x.g) : ℤ) : R) = _
    rw [Supercategory.koszulSign_comm]; exact hk
  have hk₂ : ((Supercategory.koszulSign (Presentation.parityDeg S x.gh₁.gen)
      (Presentation.parityDeg S x.gh₂.gen) : ℤ) : R) = ((x.sign : ℤ) : R) := hk
  have oD : A.tensor (M.tensor Dh) = κ.obj x.dom := by
    refine Obj.ext (by simp [A, InterchangeData.dom, genDom, ColourMap.obj, Obj.tensor, hs]) ?_
    simp [A, M, Dh, InterchangeData.dom, genDom, ColourMap.obj, Obj.tensor]
  have oC : κ.obj x.cod = A'.tensor (M.tensor Ch) := by
    refine Obj.ext (by simp [A', InterchangeData.cod, genCod, ColourMap.obj, Obj.tensor, hs]) ?_
    simp [A', M, Ch, InterchangeData.cod, genCod, ColourMap.obj, Obj.tensor]
  have hgh : SOp.unsop ((functor κ img).map (InterchangeData.ghDiagram hx)) =
      ((x.sign : ℤ) : R) • (eqToHom (congrArg Q.obj oC) ≫
        (Q.wL A' G ≫ Q.wRAt r (img x.g) (M.tensor Dh) hA' hA) ≫ eqToHom (congrArg Q.obj oD)) := by
    unfold InterchangeData.ghDiagram
    rw [functor_map_two hpar himg, hk₂]
    congr 1
    rw [layerImg, layerImg,
      whisk_congr' (img x.gh₁.gen) (u' := Obj.nil r) (v' := (M.tensor Dh).word)
        (by simp [ColourMap.obj, InterchangeData.gh₁, Obj.nil, hs, r])
        (by simp [InterchangeData.gh₁, M, Dh, genDom, ColourMap.obj, Obj.tensor]),
      whisk_nil_eq_wRAt (img x.gh₁.gen) (M.tensor Dh) hA' hA,
      whisk_congr' (img x.gh₂.gen) (u' := A'.tensor M) (v' := [])
        (by simp [ColourMap.obj, InterchangeData.gh₂, A', M, genCod, Obj.tensor, hs])
        (by simp [InterchangeData.gh₂]),
      whisk_eq_wL (img x.gh₂.gen) (A'.tensor M), Q.wL_tensor hA'M hMC]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
      Category.id_comp]
    rfl
  have hhg : SOp.unsop ((functor κ img).map (InterchangeData.hgDiagram hx)) =
      ((x.sign : ℤ) : R) • (eqToHom (congrArg Q.obj oC) ≫
        (Q.wRAt r (img x.g) (M.tensor Ch) hA' hA ≫ Q.wL A G) ≫ eqToHom (congrArg Q.obj oD)) := by
    unfold InterchangeData.hgDiagram
    rw [functor_map_two hpar himg, hk']
    congr 1
    rw [layerImg, layerImg,
      whisk_congr' (img x.hg₁.gen) (u' := A.tensor M) (v' := [])
        (by simp [ColourMap.obj, InterchangeData.hg₁, A, M, genDom, Obj.tensor, hs])
        (by simp [InterchangeData.hg₁]),
      whisk_eq_wL (img x.hg₁.gen) (A.tensor M), Q.wL_tensor hAM hMC,
      whisk_congr' (img x.hg₂.gen) (u' := Obj.nil r) (v' := (M.tensor Ch).word)
        (by simp [ColourMap.obj, InterchangeData.hg₂, Obj.nil, hs, r])
        (by simp [InterchangeData.hg₂, M, Ch, genCod, ColourMap.obj, Obj.tensor]),
      whisk_nil_eq_wRAt (img x.hg₂.gen) (M.tensor Ch) hA' hA]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
      Category.id_comp]
    rfl
  have key' : Q.wRAt r (img x.g) (M.tensor Ch) hA' hA ≫ Q.wL A G =
      ((x.sign : ℤ) : R) • (Q.wL A' G ≫ Q.wRAt r (img x.g) (M.tensor Dh) hA' hA) := by
    rw [← hk, Int.cast_smul_eq_zsmul]; exact key
  apply SOp.hom_ext
  rw [InterchangeData.rel, Functor.map_sub, Functor.map_smul, freeLift_map_of, freeLift_map_of,
    SOp.unsop_sub, SOp.unsop_smul, hgh, hhg, key', Linear.smul_comp, Linear.comp_smul, smul_smul,
    show ((x.sign : ℤ) : R) * ((x.sign : ℤ) : R) = 1 by
      unfold InterchangeData.sign; split_ifs <;> simp,
    one_smul, sub_self, SOp.unsop_zero]

include hpar in
/-- Compatibility of the image of a diagram with whiskering. -/
theorem functor_map_whisker {a b : Obj S} (d : a ⟶ b) (u : Obj S) (v : List S.Colour)
    (hw : a.WhiskerOK u v) :
    SOp.unsop ((functor κ img).map (Diagram.whisker d u v hw)) =
      eqToHom (congrArg Q.obj (κ.obj_whisker b u v)) ≫
        Q.whisk (SOp.unsop ((functor κ img).map d)) (κ.obj u) (κ.word v) ≫
          eqToHom (congrArg Q.obj (κ.obj_whisker a u v)).symm := by
  obtain ⟨ls, hc⟩ := d
  exact functor_map_whisker_aux hpar u v ls hc hw

variable (κ) in
/-- Whiskering of morphisms of the super-opposite, as a linear map. -/
def whiskT (a b u : Obj S) (v : List S.Colour) :
    ((⟨Q.obj (κ.obj a)⟩ : SOp R Q.Presented) ⟶ ⟨Q.obj (κ.obj b)⟩) →ₗ[R]
      ((⟨Q.obj (κ.obj (a.whisker u v))⟩ : SOp R Q.Presented) ⟶
        ⟨Q.obj (κ.obj (b.whisker u v))⟩) where
  toFun x := SOp.mk' (eqToHom (congrArg Q.obj (κ.obj_whisker b u v)) ≫
    Q.whisk (SOp.unsop x) (κ.obj u) (κ.word v) ≫
      eqToHom (congrArg Q.obj (κ.obj_whisker a u v)).symm)
  map_add' x y := by
    apply SOp.hom_ext
    change eqToHom _ ≫ Q.whisk (SOp.unsop x + SOp.unsop y) _ _ ≫ eqToHom _ =
      eqToHom _ ≫ Q.whisk (SOp.unsop x) _ _ ≫ eqToHom _ +
        eqToHom _ ≫ Q.whisk (SOp.unsop y) _ _ ≫ eqToHom _
    rw [Q.whisk_add, Preadditive.add_comp, Preadditive.comp_add]
    rfl
  map_smul' r x := by
    apply SOp.hom_ext
    change eqToHom _ ≫ Q.whisk (r • SOp.unsop x) _ _ ≫ eqToHom _ =
      r • (eqToHom _ ≫ Q.whisk (SOp.unsop x) _ _ ≫ eqToHom _)
    rw [Q.whisk_smul, Linear.smul_comp, Linear.comp_smul]
    rfl

include hpar in
set_option backward.isDefEq.respectTransparency false in
theorem freeLift_whisker_eq_zero {a b : Obj S} (f : LinDiagram R a b) (u : Obj S)
    (v : List S.Colour) (hw : a.WhiskerOK u v) (hf : (freeLift R (functor κ img)).map f = 0) :
    (freeLift R (functor κ img)).map (LinDiagram.whisker f u v hw) = 0 := by
  have := freeLift_map_mapDomain (F := functor κ img) (G := functor κ img)
    (fun d => Diagram.whisker d u v hw) (whiskT κ a b u v)
    (fun d => SOp.hom_ext (functor_map_whisker hpar d u v hw)) f
  exact this.trans (by rw [hf, map_zero])

variable (P : Presentation.{w, v} S R)

include hpar in
/-- **Contravariant superfunctors from images of generators**: the functor into the
super-opposite respects `P` as soon as the images of the relations of `P` vanish. -/
theorem respects
    (himg : ∀ g, img g ∈ Q.homDeg (Presentation.parityDeg S') (LocalMap.genCod κ g)
      (LocalMap.genDom κ g) (Presentation.parityDeg S g))
    (hrel : ∀ r, (freeLift R (functor κ img)).map (P.rel r) = 0) :
    P.Respects (functor κ img) :=
  P.respects_of_whisker_on (fun _ : Unit => functor κ img) (fun _ => True) (fun _ => trivial)
    (fun _ _ => trivial)
    (fun _ _ _ f u v _ hw hf => freeLift_whisker_eq_zero hpar f u v hw (hf ()))
    (fun _ r => hrel r) (fun _ _ hx => ofGen_interchange hpar himg hx) ()

variable (κ img) in
/-- The contravariant superfunctor `P.Presented ⥤ SOp R Q.Presented` given by images of
generators. -/
def liftGen
    (himg : ∀ g, img g ∈ Q.homDeg (Presentation.parityDeg S') (LocalMap.genCod κ g)
      (LocalMap.genDom κ g) (Presentation.parityDeg S g))
    (hrel : ∀ r, (freeLift R (functor κ img)).map (P.rel r) = 0) :
    P.Presented ⥤ SOp R Q.Presented :=
  P.lift (respects hpar P himg hrel)

section LiftGen

variable {P}
  (himg : ∀ g, img g ∈ Q.homDeg (Presentation.parityDeg S') (LocalMap.genCod κ g)
    (LocalMap.genDom κ g) (Presentation.parityDeg S g))
  (hrel : ∀ r, (freeLift R (functor κ img)).map (P.rel r) = 0)

instance liftGen_additive : (liftGen hpar κ img P himg hrel).Additive := P.lift_additive _

instance liftGen_linear : (liftGen hpar κ img P himg hrel).Linear R := P.lift_linear _

@[simp] theorem liftGen_obj (a : Obj S) :
    (liftGen hpar κ img P himg hrel).obj (P.obj a) = ⟨Q.obj (κ.obj a)⟩ := rfl

theorem liftGen_diag {a b : Obj S} (d : a ⟶ b) :
    (liftGen hpar κ img P himg hrel).map (P.diag d) = (functor κ img).map d :=
  P.lift_diag _ d

theorem liftGen_lin {a b : Obj S} (f : LinDiagram R a b) :
    (liftGen hpar κ img P himg hrel).map (P.lin f) = (freeLift R (functor κ img)).map f :=
  P.lift_lin _ f

/-- A layer `u ⊗ g ⊗ v` goes to `κ u ⊗ img g ⊗ κ v` (reversed). -/
theorem liftGen_layer (L : Layer S) (hv : L.Valid) :
    SOp.unsop ((liftGen hpar κ img P himg hrel).map (P.diag (Diagram.ofLayer L hv))) =
      layerImg κ img L := by
  rw [liftGen_diag]; exact functor_map_ofLayer κ img L hv

set_option backward.isDefEq.respectTransparency false in
/-- The contravariant superfunctor commutes with whiskering. -/
theorem liftGen_whisk {a b : Obj S} (f : P.obj a ⟶ P.obj b) {u : Obj S} {v : List S.Colour}
    (hw : a.WhiskerOK u v) :
    SOp.unsop ((liftGen hpar κ img P himg hrel).map (P.whisk f u v)) =
      eqToHom (congrArg Q.obj (κ.obj_whisker b u v)) ≫
        Q.whisk (SOp.unsop ((liftGen hpar κ img P himg hrel).map f)) (κ.obj u) (κ.word v) ≫
          eqToHom (congrArg Q.obj (κ.obj_whisker a u v)).symm := by
  obtain ⟨f, rfl⟩ := P.lin_surjective f
  rw [Presentation.whisk_lin, LinDiagram.whisk_of_ok _ hw, liftGen_lin, liftGen_lin]
  have := freeLift_map_mapDomain (F := functor κ img) (G := functor κ img)
    (fun d => Diagram.whisker d u v hw) (whiskT κ a b u v)
    (fun d => SOp.hom_ext (functor_map_whisker hpar d u v hw)) f
  exact congrArg SOp.unsop this

include hpar himg in
set_option backward.isDefEq.respectTransparency false in
/-- The image of a diagram is homogeneous of its parity. -/
theorem functor_map_mem {a b : Obj S} (d : a ⟶ b) :
    (functor κ img).map d ∈ parity (R := R) ((functor κ img).obj a) ((functor κ img).obj b)
      (Diagram.degree (Presentation.parityDeg S) d) := by
  obtain ⟨ls, hc⟩ := d
  induction ls generalizing a with
  | nil =>
    cases hc
    change (functor κ img).map (𝟙 _) ∈ _
    rw [CategoryTheory.Functor.map_id]
    exact Supercategory.id_mem _
  | cons L ls ih =>
    obtain ⟨hv, rfl, hc'⟩ := hc
    have e : (⟨L :: ls, hv, rfl, hc'⟩ : L.dom ⟶ b) = Diagram.ofLayer L hv ≫ ⟨ls, hc'⟩ :=
      Diagram.ext rfl
    rw [e, Functor.map_comp, Diagram.degree_comp, Diagram.degree_ofLayer]
    refine Supercategory.comp_mem ?_ (ih hc')
    rw [SOp.mem_parity_iff, functor_map_ofLayer]
    exact layerImg_mem hpar himg L

include hpar himg in
set_option backward.isDefEq.respectTransparency false in
/-- **The contravariant superfunctor preserves parities.** -/
theorem liftGen_mem {a b : Obj S} {x : P.obj a ⟶ P.obj b} {p : ZMod 2}
    (hx : x ∈ P.homDeg (Presentation.parityDeg S) a b p) :
    (liftGen hpar κ img P himg hrel).map x ∈
      parity (R := R) ((functor κ img).obj a) ((functor κ img).obj b) p := by
  obtain ⟨f, hf, rfl⟩ := Presentation.mem_homDeg_iff.mp hx
  clear hx
  rw [liftGen_lin]
  rw [LinDiagram.homDeg, Finsupp.supported_eq_span_single] at hf
  induction hf using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨d, hd, rfl⟩ := hy
    rw [freeLift_map_single]
    exact Submodule.smul_mem _ _ (hd ▸ functor_map_mem hpar himg d)
  | zero => rw [Functor.map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [Functor.map_add]; exact Submodule.add_mem _ hy hz
  | smul r y _ hy => rw [Functor.map_smul]; exact Submodule.smul_mem _ r hy

end LiftGen

end SOpMap

end StringDiagrams

end
