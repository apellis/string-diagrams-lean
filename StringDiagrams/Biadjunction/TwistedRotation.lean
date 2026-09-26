import StringDiagrams.Biadjunction.MateCalculus

/-!
# Rotation of diagrams without cyclicity

Let `P` be a presentation of an even signature with chosen cups and caps `Q : ColourCupsCaps P D`
satisfying the zigzag identities (for instance a presentation of the pivotal extension in which
the zigzag relations hold, `Presentation.pivotalCupsCaps`). No cyclicity is assumed: the right and
left mates of a 2-morphism need not agree, and the rotation below is the right mate.

## Rotation as a linear map

For words `u`, `u'` read from the region `r` and ending in the region `s`,
`Presentation.rotMate Q hu hu' hs hs' ev ev'` is the rotation by a half turn

  `(P.obj ⟨r, u⟩ ⟶ P.obj ⟨r, u'⟩) →ₗ[R] (P.obj ⟨s, v'⟩ ⟶ P.obj ⟨s, v⟩)`,

the right mate for the biadjunctions of words given by the nested cups and caps
(`StringDiagrams.Biadjunction.NestedCups`), where `v = u*` and `v' = u'*` are the dual words
(`ev : D.dualWord u = v`, `ev' : D.dualWord u' = v'`; they are parameters so that no transport is
needed when the dual words are known in another form). It is `R`-linear and contravariant
(`rotMate_comp`, `rotMate_id`).

## Rotation data

A rotation datum `ρ : Presentation.RotationDatum Q` consists of a family of generators
(`ρ.Rotates`), and for each generator `g` of the family a generator `ρ.rot g` (its rotation) and a
scalar `ρ.scalar g`, such that the right rotation of `g` by the nested cups and caps
(`ColourCupCapDiagrams.genRotR`) is `ρ.scalar g` times the diagram consisting of the generator
`ρ.rot g` alone (`ρ.genRotR_eq`). Equivalently, the right mate of `g` is `ρ.scalar g • ρ.rot g`
(`RotationDatum.rightMate_gen2`). The scalars are arbitrary elements of `R`; in a cyclic situation
they are all `1`, in a twisted pivotal situation they are units.

The rotation of a layer `(u, g, v)` (the generator `g` with the strands `u` on its left and `v`
on its right) is the layer `(v*, ρ.rot g, u*)` (`Layer.rotate`).

## Main results

* `RotationDatum.rightMate_layer`: the mate of a layer whose generator is in the family is
  `ρ.scalar g` times the rotated layer;
* `RotationDatum.rightMate_diag`, `RotationDatum.rotMate_diag`: **the rotation of a diagram all of
  whose generators are in the family is the product of the scalars of its generators times the
  diagram of the rotated layers in reverse order**.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Bicategory Biadjunction

universe w v u₀ u₁ u₂

variable {S : Signature.{u₀, u₁, u₂}} {R : Type w} [CommRing R]

/-- The rotation of a layer by a half turn: the layer `(u, g, v)` becomes `(v*, ρ g, u*)`, read
from the region at the right end of the original layer. -/
def Layer.rotate (D : S.ColourDuality) (ρ : S.Gen → S.Gen) (L : Layer S) : Layer S :=
  ⟨S.endR (S.right L.gen) L.right, D.dualWord L.right, ρ L.gen, D.dualWord L.left⟩

@[simp] theorem Layer.rotate_start (D : S.ColourDuality) (ρ : S.Gen → S.Gen) (L : Layer S) :
    (L.rotate D ρ).start = S.endR (S.right L.gen) L.right := rfl

@[simp] theorem Layer.rotate_left (D : S.ColourDuality) (ρ : S.Gen → S.Gen) (L : Layer S) :
    (L.rotate D ρ).left = D.dualWord L.right := rfl

@[simp] theorem Layer.rotate_gen (D : S.ColourDuality) (ρ : S.Gen → S.Gen) (L : Layer S) :
    (L.rotate D ρ).gen = ρ L.gen := rfl

@[simp] theorem Layer.rotate_right (D : S.ColourDuality) (ρ : S.Gen → S.Gen) (L : Layer S) :
    (L.rotate D ρ).right = D.dualWord L.left := rfl

namespace Presentation

variable {P : Presentation.{w, v} S R} {D : S.ColourDuality}

/-- A well-formed word read from the region `r` and ending in the region `s`, as a 1-morphism
`⟨r⟩ ⟶ ⟨s⟩` of `P.Bicat`. -/
def wordHomTo (P : Presentation.{w, v} S R) (r s : S.Region) (u : List S.Colour) (hu : S.ok r u)
    (hs : S.endR r u = s) : (⟨r⟩ : P.Bicat) ⟶ ⟨s⟩ :=
  ⟨⟨r, u⟩, rfl, hu, hs⟩

@[simp] theorem wordHomTo_obj (r s : S.Region) (u : List S.Colour) (hu : S.ok r u)
    (hs : S.endR r u = s) : (P.wordHomTo r s u hu hs).obj = ⟨r, u⟩ := rfl

theorem dualHom_wordHomTo_obj (r s : S.Region) (u : List S.Colour) (hu : S.ok r u)
    (hs : S.endR r u = s) : (P.dualHom D (P.wordHomTo r s u hu hs)).obj = ⟨s, D.dualWord u⟩ :=
  rfl

variable [S.IsEven] (Q : ColourCupsCaps P D)

/-! ## The mate as a linear map -/

/-- The right mate for the biadjunctions of words, as an `R`-linear map between the `Hom`-spaces of
the presented category. -/
def wordMate {l m : P.Bicat} (x x' : l ⟶ m) :
    (P.obj x.obj ⟶ P.obj x'.obj) →ₗ[R]
      (P.obj (P.dualHom D x').obj ⟶ P.obj (P.dualHom D x).obj) where
  toFun f := Biadjunction.rightMate (biadj Q.biadjunctions x) (biadj Q.biadjunctions x')
    (show x ⟶ x' from f)
  map_add' f g := Biadjunction.rightMate_add (biadj Q.biadjunctions x) (biadj Q.biadjunctions x')
    (show x ⟶ x' from f) g
  map_smul' r f := Biadjunction.rightMate_smul (biadj Q.biadjunctions x)
    (biadj Q.biadjunctions x') r (show x ⟶ x' from f)

theorem wordMate_apply {l m : P.Bicat} (x x' : l ⟶ m) (f : P.obj x.obj ⟶ P.obj x'.obj) :
    wordMate Q x x' f =
      Biadjunction.rightMate (biadj Q.biadjunctions x) (biadj Q.biadjunctions x')
        (show x ⟶ x' from f) := rfl

theorem wordMate_comp {l m : P.Bicat} (x x' x'' : l ⟶ m) (f : P.obj x.obj ⟶ P.obj x'.obj)
    (g : P.obj x'.obj ⟶ P.obj x''.obj) :
    wordMate Q x x'' (f ≫ g) = wordMate Q x' x'' g ≫ wordMate Q x x' f :=
  Biadjunction.rightMate_comp (biadj Q.biadjunctions x) (biadj Q.biadjunctions x')
    (biadj Q.biadjunctions x'') (f : x ⟶ x') (g : x' ⟶ x'')

theorem wordMate_id {l m : P.Bicat} (x : l ⟶ m) : wordMate Q x x (𝟙 _) = 𝟙 _ :=
  Biadjunction.rightMate_id (biadj Q.biadjunctions x)

section RotMate

variable {r s : S.Region} {u u' u'' v v' v'' : List S.Colour}

omit [S.IsEven] in
theorem rotMate_obj_eq (hu : S.ok r u) (hs : S.endR r u = s) (ev : D.dualWord u = v) :
    P.obj ⟨s, v⟩ = P.obj (P.dualHom D (P.wordHomTo r s u hu hs)).obj := by
  rw [dualHom_wordHomTo_obj, ev]

/-- **Rotation by a half turn** of morphisms `⟨r, u⟩ ⟶ ⟨r, u'⟩` of the presented category between
words from the region `r` to the region `s`: the right mate `⟨s, u'*⟩ ⟶ ⟨s, u*⟩` for the
biadjunctions of words given by the nested cups and caps, with the dual words written as
`v = u*`, `v' = u'*`. -/
def rotMate (hu : S.ok r u) (hu' : S.ok r u') (hs : S.endR r u = s) (hs' : S.endR r u' = s)
    (ev : D.dualWord u = v) (ev' : D.dualWord u' = v') :
    (P.obj ⟨r, u⟩ ⟶ P.obj ⟨r, u'⟩) →ₗ[R] (P.obj ⟨s, v'⟩ ⟶ P.obj ⟨s, v⟩) where
  toFun f := eqToHom (rotMate_obj_eq hu' hs' ev') ≫
      wordMate Q (P.wordHomTo r s u hu hs) (P.wordHomTo r s u' hu' hs') f ≫
        eqToHom (rotMate_obj_eq hu hs ev).symm
  map_add' f g := by
    rw [map_add, Preadditive.add_comp, Preadditive.comp_add]
  map_smul' c f := by
    rw [map_smul, Linear.smul_comp, Linear.comp_smul]
    rfl

theorem rotMate_apply (hu : S.ok r u) (hu' : S.ok r u') (hs : S.endR r u = s)
    (hs' : S.endR r u' = s) (ev : D.dualWord u = v) (ev' : D.dualWord u' = v')
    (f : P.obj ⟨r, u⟩ ⟶ P.obj ⟨r, u'⟩) :
    rotMate Q hu hu' hs hs' ev ev' f = eqToHom (rotMate_obj_eq hu' hs' ev') ≫
      wordMate Q (P.wordHomTo r s u hu hs) (P.wordHomTo r s u' hu' hs') f ≫
        eqToHom (rotMate_obj_eq hu hs ev).symm := rfl

/-- With the canonical dual words, the rotation is the right mate. -/
theorem rotMate_rfl_apply (hu : S.ok r u) (hu' : S.ok r u') (hs : S.endR r u = s)
    (hs' : S.endR r u' = s) (f : P.obj ⟨r, u⟩ ⟶ P.obj ⟨r, u'⟩) :
    rotMate Q hu hu' hs hs' rfl rfl f =
      Biadjunction.rightMate (biadj Q.biadjunctions (P.wordHomTo r s u hu hs))
        (biadj Q.biadjunctions (P.wordHomTo r s u' hu' hs')) f := by
  rw [rotMate_apply, wordMate_apply]
  simp

/-- The rotation is contravariant. -/
theorem rotMate_comp (hu : S.ok r u) (hu' : S.ok r u') (hu'' : S.ok r u'') (hs : S.endR r u = s)
    (hs' : S.endR r u' = s) (hs'' : S.endR r u'' = s) (ev : D.dualWord u = v)
    (ev' : D.dualWord u' = v') (ev'' : D.dualWord u'' = v'')
    (f : P.obj ⟨r, u⟩ ⟶ P.obj ⟨r, u'⟩) (g : P.obj ⟨r, u'⟩ ⟶ P.obj ⟨r, u''⟩) :
    rotMate Q hu hu'' hs hs'' ev ev'' (f ≫ g) =
      rotMate Q hu' hu'' hs' hs'' ev' ev'' g ≫ rotMate Q hu hu' hs hs' ev ev' f := by
  have h := wordMate_comp Q (P.wordHomTo r s u hu hs) (P.wordHomTo r s u' hu' hs')
    (P.wordHomTo r s u'' hu'' hs'') f g
  simp only [rotMate_apply]
  rw [h]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- The rotation of an identity is an identity. -/
theorem rotMate_id (hu : S.ok r u) (hs : S.endR r u = s) (ev : D.dualWord u = v) :
    rotMate Q hu hu hs hs ev ev (𝟙 _) = 𝟙 _ := by
  rw [rotMate_apply]
  erw [wordMate_id]
  simp

end RotMate

/-! ## Rotation data -/

/-- The right mate of a generator for the biadjunctions of its boundary words is the class of its
right rotation by the nested cups and caps. -/
theorem rightMate_gen2_eq_genRotR (g : S.Gen) (hg : S.GenValid g) :
    Biadjunction.rightMate (biadj Q.biadjunctions (P.genDom g hg))
        (biadj Q.biadjunctions (P.genCod g hg)) (P.gen2 g hg) =
      P.diag (Q.toDiagrams.genRotR g hg) := by
  rw [gen2, rightMate_biadj_diag]
  exact P.diag_eq_of_layers_eq (by
    simp only [ColourCupCapDiagrams.rotateR, ColourCupCapDiagrams.genRotR,
      ColourCupCapDiagrams.layers_rotR, Diagram.layers_cast]
    rfl)

/-- A rotation datum for chosen cups and caps `Q`: a family of generators (`Rotates`), and for
each generator `g` of the family a generator `rot g` and a scalar `scalar g` such that the right
rotation of `g` by the nested cups and caps of its boundary words is `scalar g` times the
generator `rot g` (as a one-layer diagram). -/
structure RotationDatum where
  /-- The generators to which the datum applies. -/
  Rotates : S.Gen → Prop
  /-- The rotated generator. -/
  rot : S.Gen → S.Gen
  /-- The scalar acquired by a generator under rotation. -/
  scalar : S.Gen → R
  /-- The right rotation of `g` is `scalar g` times the generator `rot g`. -/
  genRotR_eq : ∀ g, Rotates g → ∀ hg : S.GenValid g,
    ∃ d : (⟨S.right g, D.dualWord (S.cod g)⟩ : Obj S) ⟶ ⟨S.right g, D.dualWord (S.dom g)⟩,
      Diagram.layers d = [⟨S.right g, [], rot g, []⟩] ∧
        P.diag (Q.toDiagrams.genRotR g hg) = scalar g • P.diag d

namespace RotationDatum

variable {Q} (ρ : RotationDatum Q)

/-- The right mate of a generator of the family is its scalar times the rotated generator. -/
theorem rightMate_gen2 (g : S.Gen) (hρ : ρ.Rotates g) (hg : S.GenValid g) :
    ∃ X : P.dualHom D (P.genCod g hg) ⟶ P.dualHom D (P.genDom g hg),
      Biadjunction.rightMate (biadj Q.biadjunctions (P.genDom g hg))
          (biadj Q.biadjunctions (P.genCod g hg)) (P.gen2 g hg) = ρ.scalar g • X ∧
        IsDiag P X [⟨S.right g, [], ρ.rot g, []⟩] := by
  obtain ⟨d, hd, he⟩ := ρ.genRotR_eq g hρ hg
  exact ⟨P.diag d, (rightMate_gen2_eq_genRotR Q g hg).trans he, ⟨d, rfl, hd⟩⟩

/-- **The rotation of a layer**: the right mate of a layer `(u, g, v)` whose generator is in the
family is `ρ.scalar g` times the rotated layer `(v*, ρ.rot g, u*)`. -/
theorem rightMate_layer {l m : P.Bicat} (x x' : l ⟶ m) (L : Layer S) (hv : L.Valid)
    (hdom : L.dom = x.obj) (hcod : L.cod = x'.obj) (hρ : ρ.Rotates L.gen) :
    ∃ e : (P.dualHom D x').obj ⟶ (P.dualHom D x).obj,
      Diagram.layers e = [L.rotate D ρ.rot] ∧
        Biadjunction.rightMate (biadj Q.biadjunctions x) (biadj Q.biadjunctions x')
            (P.diag (Diagram.layer L hv hdom hcod)) = ρ.scalar L.gen • P.diag e := by
  have hr : L.start = l.region := (congrArg Obj.start hdom).trans x.start_eq
  have he : S.endR (S.right L.gen) L.right = m.region := by
    rw [← hv.endR_dom, hdom]; exact x.endR_eq
  let uu : l ⟶ ⟨S.left L.gen⟩ :=
    ⟨⟨l.region, L.left⟩, rfl, by rw [← hr]; exact hv.left_ok,
      by show S.endR l.region L.left = _; rw [← hr]; exact hv.left_end⟩
  let vv : (⟨S.right L.gen⟩ : P.Bicat) ⟶ m := ⟨⟨S.right L.gen, L.right⟩, rfl, hv.right_ok, he⟩
  let G := P.genDom L.gen hv.genValid
  let G' := P.genCod L.gen hv.genValid
  have e : x = uu ≫ (G ≫ vv) :=
    Bicat.Hom.ext (hdom.symm.trans (Obj.ext hr (by
      simp only [Layer.dom_word, List.append_assoc]; rfl)))
  have e' : x' = uu ≫ (G' ≫ vv) :=
    Bicat.Hom.ext (hcod.symm.trans (Obj.ext hr (by
      simp only [Layer.cod_word, List.append_assoc]; rfl)))
  obtain ⟨X, hX, hXl⟩ := ρ.rightMate_gen2 L.gen hρ hv.genValid
  -- the generator is `scalar • θ'` where `θ'` has mate `X`
  let θ' : G ⟶ G' := (Biadjunction.rightMateLinearEquiv R (biadj Q.biadjunctions G)
    (biadj Q.biadjunctions G')).symm X
  have hθ'm : Biadjunction.rightMate (biadj Q.biadjunctions G) (biadj Q.biadjunctions G') θ' = X :=
    (Biadjunction.rightMateLinearEquiv R (biadj Q.biadjunctions G)
      (biadj Q.biadjunctions G')).apply_symm_apply X
  have hθθ' : P.gen2 L.gen hv.genValid = ρ.scalar L.gen • θ' := by
    apply (Biadjunction.rightMateLinearEquiv R (biadj Q.biadjunctions G)
      (biadj Q.biadjunctions G')).injective
    rw [map_smul]
    exact hX.trans (congrArg (ρ.scalar L.gen • ·) hθ'm.symm)
  -- the layer is the whiskered generator
  have hlay : IsDiag P (P.diag (Diagram.layer L hv hdom hcod) : x ⟶ x') [L] :=
    ⟨_, rfl, Diagram.layers_layer _ _ _ _⟩
  have hwh : IsDiag P (uu ◁ (P.gen2 L.gen hv.genValid ▷ vv)) [L] := by
    refine (((isDiag_diag (P := P) (x := G) (y := G') (genDiag L.gen hv.genValid)).whiskerRight
      vv).whiskerLeft uu).congr ?_
    simp only [genDiag, Diagram.layers_layer, List.map_cons, List.map_nil]
    congr 1
    exact Layer.ext hr.symm (by simp [Layer.wl, Layer.wr, uu]) rfl
      (by simp [Layer.wl, Layer.wr, vv])
  have heq := hlay.eq_eqToHom hwh e e'
  -- the mate of the whiskered generator
  have hbase : IsDiag P (Biadjunction.rightMate (biadj Q.biadjunctions G)
      (biadj Q.biadjunctions G') θ') [⟨S.right L.gen, [], ρ.rot L.gen, []⟩] := by
    rw [hθ'm]; exact hXl
  have hW := (hbase.rightMate_biadj_whiskerRight Q vv).rightMate_biadj_whiskerLeft Q uu
  have hsm : uu ◁ (P.gen2 L.gen hv.genValid ▷ vv) = ρ.scalar L.gen • (uu ◁ (θ' ▷ vv)) := by
    rw [hθθ', LocallyLinear.smul_whiskerRight, LocallyLinear.whiskerLeft_smul]
  have hY : IsDiag P (eqToHom (congrArg (P.dualHom D) e') ≫
      Biadjunction.rightMate (biadj Q.biadjunctions (uu ≫ (G ≫ vv)))
        (biadj Q.biadjunctions (uu ≫ (G' ≫ vv))) (uu ◁ (θ' ▷ vv)) ≫
          eqToHom (congrArg (P.dualHom D) e).symm) [L.rotate D ρ.rot] := by
    refine ((hW.comp_eqToHom _).eqToHom_comp _).congr ?_
    simp only [List.map_cons, List.map_nil]
    congr 1
    exact Layer.ext he.symm (by simp [Layer.wl, Layer.wr, vv]) rfl
      (by simp [Layer.wl, Layer.wr, uu])
  obtain ⟨d, hd, hdl⟩ := hY
  refine ⟨d, hdl, ?_⟩
  change Biadjunction.rightMate (biadj Q.biadjunctions x) (biadj Q.biadjunctions x')
    (P.diag (Diagram.layer L hv hdom hcod) : x ⟶ x') = _
  rw [heq, rightMate_biadj_eqToHom_conj Q e e', hsm, Biadjunction.rightMate_smul, Linear.smul_comp,
    Linear.comp_smul]
  exact congrArg (ρ.scalar L.gen • ·) hd

/-- **The rotation of a diagram** all of whose generators are in the family: its right mate for the
biadjunctions of words is the product of the scalars of its generators times the diagram of the
rotated layers in reverse order. -/
theorem rightMate_diag : ∀ (ls : List (Layer S)) {l m : P.Bicat} (x x' : l ⟶ m)
    (hc : Chain x.obj ls x'.obj), (∀ L ∈ ls, ρ.Rotates L.gen) →
    ∃ e : (P.dualHom D x').obj ⟶ (P.dualHom D x).obj,
      Diagram.layers e = (ls.map (Layer.rotate D ρ.rot)).reverse ∧
        Biadjunction.rightMate (biadj Q.biadjunctions x) (biadj Q.biadjunctions x')
            (P.diag (Diagram.mk ls hc)) = (ls.map fun L => ρ.scalar L.gen).prod • P.diag e
  | [], l, m, x, x', hc, _ => by
    obtain rfl : x = x' := Bicat.Hom.ext hc
    refine ⟨𝟙 _, rfl, ?_⟩
    have h₁ : (P.diag (Diagram.mk [] hc) : x ⟶ x) = 𝟙 x :=
      (P.diag_eq_of_layers_eq rfl).trans (P.diag_id _)
    rw [h₁, Biadjunction.rightMate_id, List.map_nil, List.prod_nil, one_smul, P.diag_id]
    rfl
  | L :: ls, l, m, x, x', hc, hrot => by
    obtain ⟨hv, hdom, hc'⟩ := hc
    let x₁ : l ⟶ m :=
      ⟨L.cod, (congrArg Obj.start hdom).trans x.start_eq,
        hv.wf_cod,
        by rw [hv.endR_eq, hdom]; exact x.endR_eq⟩
    obtain ⟨e₁, he₁l, he₁⟩ := ρ.rightMate_layer x x₁ L hv hdom rfl
      (hrot L List.mem_cons_self)
    obtain ⟨e₂, he₂l, he₂⟩ := rightMate_diag ls x₁ x' hc'
      (fun L' hL' => hrot L' (List.mem_cons_of_mem L hL'))
    refine ⟨e₂ ≫ e₁, by simp [he₁l, he₂l], ?_⟩
    have hsplit : (P.diag (Diagram.mk (L :: ls) ⟨hv, hdom, hc'⟩) : x ⟶ x') =
        (P.diag (Diagram.layer L hv hdom rfl) : x ⟶ x₁) ≫
          (P.diag (Diagram.mk ls hc') : x₁ ⟶ x') :=
      (P.diag_eq_of_layers_eq (g := Diagram.layer L hv hdom rfl ≫ Diagram.mk ls hc')
        rfl).trans (P.diag_comp _ _)
    rw [hsplit]
    refine (Biadjunction.rightMate_comp (biadj Q.biadjunctions x) (biadj Q.biadjunctions x₁)
      (biadj Q.biadjunctions x') (P.diag (Diagram.layer L hv hdom rfl) : x ⟶ x₁)
      (P.diag (Diagram.mk ls hc') : x₁ ⟶ x')).trans ?_
    rw [he₁, he₂,
      Linear.smul_comp, Linear.comp_smul, smul_smul, List.map_cons, List.prod_cons, mul_comm]
    exact congrArg (_ • ·) (P.diag_comp e₂ e₁).symm

/-- **The rotation of a diagram** `d : ⟨r, u⟩ ⟶ ⟨r, u'⟩` all of whose generators are in the
family, as the linear map `rotMate`: the product of the scalars of its generators times the
diagram of the rotated layers in reverse order. -/
theorem rotMate_diag {r s : S.Region} {u u' : List S.Colour} (hu : S.ok r u) (hu' : S.ok r u')
    (hs : S.endR r u = s) (hs' : S.endR r u' = s) (d : (⟨r, u⟩ : Obj S) ⟶ ⟨r, u'⟩)
    (hrot : ∀ L ∈ Diagram.layers d, ρ.Rotates L.gen) :
    ∃ e : (⟨s, D.dualWord u'⟩ : Obj S) ⟶ ⟨s, D.dualWord u⟩,
      Diagram.layers e = ((Diagram.layers d).map (Layer.rotate D ρ.rot)).reverse ∧
        rotMate Q hu hu' hs hs' rfl rfl (P.diag d) =
          ((Diagram.layers d).map fun L => ρ.scalar L.gen).prod • P.diag e := by
  obtain ⟨e, hel, he⟩ := RotationDatum.rightMate_diag ρ (Diagram.layers d) (P.wordHomTo r s u hu hs)
    (P.wordHomTo r s u' hu' hs') (Diagram.chain d) hrot
  exact ⟨e, hel, (rotMate_rfl_apply Q hu hu' hs hs' _).trans he⟩

/-- `rotMate_diag` with the dual boundary words given as `v = u*`, `v' = u'*`. -/
theorem rotMate_diag' {r s : S.Region} {u u' v v' : List S.Colour} (hu : S.ok r u)
    (hu' : S.ok r u') (hs : S.endR r u = s) (hs' : S.endR r u' = s) (ev : D.dualWord u = v)
    (ev' : D.dualWord u' = v') (d : (⟨r, u⟩ : Obj S) ⟶ ⟨r, u'⟩)
    (hrot : ∀ L ∈ Diagram.layers d, ρ.Rotates L.gen) :
    ∃ e : (⟨s, v'⟩ : Obj S) ⟶ ⟨s, v⟩,
      Diagram.layers e = ((Diagram.layers d).map (Layer.rotate D ρ.rot)).reverse ∧
        rotMate Q hu hu' hs hs' ev ev' (P.diag d) =
          ((Diagram.layers d).map fun L => ρ.scalar L.gen).prod • P.diag e := by
  subst ev ev'
  exact ρ.rotMate_diag hu hu' hs hs' d hrot

end RotationDatum

end Presentation

end StringDiagrams
