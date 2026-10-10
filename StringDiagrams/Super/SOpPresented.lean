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

end SOpMap

end StringDiagrams

end
