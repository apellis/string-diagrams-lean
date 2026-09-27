import StringDiagrams.Biadjunction.NestedCups
import StringDiagrams.Biadjunction.IsDiag

/-!
# Mate calculus for the biadjunctions of words

Let `P` be a presentation of an even signature with chosen cups and caps `Q : ColourCupsCaps P D`
for a duality `D` on colours, so that every 1-morphism `x` of `P.Bicat` is biadjoint to its dual
word `x*` by nested cups and caps (`biadj Q.biadjunctions x`,
`StringDiagrams.Biadjunction.NestedCups`). This file computes mates (rotations) of whiskered
2-morphisms and of mates, without any cyclicity hypothesis unless stated.

## Units and counits as lists of layers

* `IsDiag.comp_left_unit`, `IsDiag.comp_left_counit`, `IsDiag.comp_right_unit`,
  `IsDiag.comp_right_counit`: the units and counits of a composite of biadjunctions in `P.Bicat`
  are classes of the evident nested diagrams.
* `isDiag_biadj_left_unit`, …: the units and counits of the biadjunctions of words have the
  layers of the nested cups and caps `cupW`, `capW`, `cup'W`, `cap'W`.
* `IsDiag.rightMate`, `IsDiag.leftMate`: layers of mates.
* `rightMate_id_eq_eqToHom`: two biadjunctions `x ⊣⊢ y`, `x ⊣⊢ y'` whose counits (of the
  adjunctions in which `x` is the left adjoint) have the same layers induce the trivial comparison
  `y' ⟶ y`.

## Composites and whiskering

* `rightMate_biadj_comp_id`, `rightMate_comp_biadj_id`: **the comparison between the
  biadjunction of a concatenated word and the composite of the biadjunctions is trivial**,
  `rightMate (biadj (x ≫ y)) ((biadj x).comp (biadj y)) (𝟙 _) = eqToHom _`.
* `rightMate_biadj_comp`: the mate for the biadjunction of a concatenated word is the mate for
  the composite biadjunction.
* `rightMate_biadj_whiskerLeft`, `rightMate_biadj_whiskerRight`: **the mate of a whiskered
  2-morphism is the oppositely whiskered mate**, `(h ◁ θ)^* = θ^* ▷ h*` and
  `(θ ▷ h)^* = h* ◁ θ^*`, up to the identifications `(h x)* = x* h*`.
* For the pivotal structure on `P.Bicat` given by the nested cups and caps when all generators
  are cyclic (`Presentation.pivotalOfGenerators`), the comparisons `Pivotal.dualCompIso` are
  identities (`pivotalOfGenerators_dualCompIso_hom`), so rotation is a strict 2-functor
  (`pivotalOfGenerators_rotate_whiskerLeft`, `pivotalOfGenerators_rotate_whiskerRight`).

## Double rotation

For an involutive duality (`D.dual (D.dual c) = c`) and cups and caps such that the cap of `c*`
has the layers of the cap `c c* ⟶ 1` (`Q.cap (D.dual c)` versus `Q.cap' c`; this holds for the
pivotal extension, `Presentation.pivotalCupsCaps`), the nested caps of the dual word `w*` are
the nested caps `cap'W` of `w` (`ColourCupCapDiagrams.layers_capW_dualWord`), and

* `rightMate_rightMate`: **rotating a cyclic 2-morphism twice gives it back**, up to the
  identifications `x** = x`;
* `pivotalOfGenerators_pivotalIso_hom`: the canonical comparison `x ≅ x**` of the pivotal
  structure is an identity, so double rotation is the identity.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Bicategory Biadjunction

universe w v u₀ u₁ u₂

variable {S : Signature.{u₀, u₁, u₂}} {R : Type w} [CommRing R]

namespace Presentation

/-! ## Units and counits of composite biadjunctions -/

section Comp

variable {P : Presentation.{w, v} S R} [S.IsEven] {l m n : P.Bicat}

theorem IsDiag.comp_left_unit {f₁ : l ⟶ m} {g₁ : m ⟶ l} {f₂ : m ⟶ n} {g₂ : n ⟶ m}
    (P₁ : f₁ ⊣⊢ g₁) (P₂ : f₂ ⊣⊢ g₂) {ls ms : List (Layer S)}
    (h₁ : IsDiag P P₁.left.unit ls) (h₂ : IsDiag P P₂.left.unit ms) :
    IsDiag P (P₁.comp P₂).left.unit
      (ls ++ (ms.map (·.wr g₁.obj.word)).map (·.wl f₁.obj)) := by
  simp only [Biadjunction.comp_left, Bicategory.Adjunction.comp_unit,
    Bicategory.Adjunction.compUnit, bicategoricalComp]
  refine IsDiag.congr (IsDiag.comp h₁ (IsDiag.comp (ls := []) ?_
      (IsDiag.comp (IsDiag.whiskerLeft _ (IsDiag.whiskerRight _ h₂)) (IsDiag.comp (ls := []) ?_
      (isDiag_id _))))) ?_
  · isdiag_triv
  · isdiag_triv
  · simp

theorem IsDiag.comp_left_counit {f₁ : l ⟶ m} {g₁ : m ⟶ l} {f₂ : m ⟶ n} {g₂ : n ⟶ m}
    (P₁ : f₁ ⊣⊢ g₁) (P₂ : f₂ ⊣⊢ g₂) {ls ms : List (Layer S)}
    (h₁ : IsDiag P P₁.left.counit ls) (h₂ : IsDiag P P₂.left.counit ms) :
    IsDiag P (P₁.comp P₂).left.counit
      ((ls.map (·.wr f₂.obj.word)).map (·.wl g₂.obj) ++ ms) := by
  simp only [Biadjunction.comp_left, Bicategory.Adjunction.comp_counit,
    Bicategory.Adjunction.compCounit, bicategoricalComp]
  refine IsDiag.congr (IsDiag.comp (isDiag_id _) (IsDiag.comp (ls := []) ?_
      (IsDiag.comp (IsDiag.whiskerLeft _ (IsDiag.whiskerRight _ h₁)) (IsDiag.comp (ls := []) ?_
      h₂)))) ?_
  · isdiag_triv
  · isdiag_triv
  · simp

theorem IsDiag.comp_right_unit {f₁ : l ⟶ m} {g₁ : m ⟶ l} {f₂ : m ⟶ n} {g₂ : n ⟶ m}
    (P₁ : f₁ ⊣⊢ g₁) (P₂ : f₂ ⊣⊢ g₂) {ls ms : List (Layer S)}
    (h₁ : IsDiag P P₁.right.unit ls) (h₂ : IsDiag P P₂.right.unit ms) :
    IsDiag P (P₁.comp P₂).right.unit
      (ms ++ (ls.map (·.wr f₂.obj.word)).map (·.wl g₂.obj)) :=
  IsDiag.comp_left_unit (f₁ := g₂) (g₁ := f₂) (f₂ := g₁) (g₂ := f₁) P₂.symm P₁.symm h₂ h₁

theorem IsDiag.comp_right_counit {f₁ : l ⟶ m} {g₁ : m ⟶ l} {f₂ : m ⟶ n} {g₂ : n ⟶ m}
    (P₁ : f₁ ⊣⊢ g₁) (P₂ : f₂ ⊣⊢ g₂) {ls ms : List (Layer S)}
    (h₁ : IsDiag P P₁.right.counit ls) (h₂ : IsDiag P P₂.right.counit ms) :
    IsDiag P (P₁.comp P₂).right.counit
      ((ms.map (·.wr g₁.obj.word)).map (·.wl f₁.obj) ++ ls) :=
  IsDiag.comp_left_counit (f₁ := g₂) (g₁ := f₂) (f₂ := g₁) (g₂ := f₁) P₂.symm P₁.symm h₂ h₁

/-- The layers of the right mate of the class of a diagram, for biadjunctions whose units and
counits are classes of diagrams with given layers. -/
theorem IsDiag.rightMate {x x' : l ⟶ m} {y y' : m ⟶ l} (Q₁ : x ⊣⊢ y) (Q₂ : x' ⊣⊢ y')
    {cl al ls : List (Layer S)} (hcup : IsDiag P Q₁.left.unit cl)
    (hcap : IsDiag P Q₂.left.counit al) {θ : x ⟶ x'} (hθ : IsDiag P θ ls) :
    IsDiag P (Biadjunction.rightMate Q₁ Q₂ θ)
      (cl.map (·.wl y'.obj) ++ (ls.map (·.wr y.obj.word)).map (·.wl y'.obj) ++
        al.map (·.wr y.obj.word)) := by
  obtain ⟨cup, hcup, rfl⟩ := hcup
  obtain ⟨cap', hcap, rfl⟩ := hcap
  obtain ⟨d, rfl, rfl⟩ := hθ
  exact ⟨_, rightMate_diag Q₁ Q₂ cup hcup cap' hcap d, layers_rightRotateD _ _ _ _ _ _ _⟩

/-- The layers of the left mate of the class of a diagram, for biadjunctions whose units and
counits are classes of diagrams with given layers. -/
theorem IsDiag.leftMate {x x' : l ⟶ m} {y y' : m ⟶ l} (Q₁ : x ⊣⊢ y) (Q₂ : x' ⊣⊢ y')
    {cl al ls : List (Layer S)} (hcup : IsDiag P Q₁.right.unit cl)
    (hcap : IsDiag P Q₂.right.counit al) {θ : x ⟶ x'} (hθ : IsDiag P θ ls) :
    IsDiag P (Biadjunction.leftMate Q₁ Q₂ θ)
      (cl.map (·.wr y'.obj.word) ++ (ls.map (·.wr y'.obj.word)).map (·.wl y.obj) ++
        al.map (·.wl y.obj)) := by
  obtain ⟨cup, hcup, rfl⟩ := hcup
  obtain ⟨cap', hcap, rfl⟩ := hcap
  obtain ⟨d, rfl, rfl⟩ := hθ
  exact ⟨_, leftMate_diag Q₁ Q₂ cup hcup cap' hcap d, layers_leftRotateD _ _ _ _ _ _ _⟩

/-- **Comparison of biadjunctions.** Two biadjunctions `x ⊣⊢ y` and `x ⊣⊢ y'` (with `y = y'`)
whose counits `y x ⟶ 1`, `y' x ⟶ 1` are classes of diagrams with the same layers, the first with
a unit that is the class of a diagram, induce the trivial comparison `y' ⟶ y`. -/
theorem rightMate_id_eq_eqToHom {x : l ⟶ m} {y y' : m ⟶ l} (Q₁ : x ⊣⊢ y) (Q₂ : x ⊣⊢ y')
    (h : y = y') {cl al : List (Layer S)} (hcup : IsDiag P Q₁.left.unit cl)
    (hcap : IsDiag P Q₁.left.counit al) (hcap' : IsDiag P Q₂.left.counit al) :
    Biadjunction.rightMate Q₁ Q₂ (𝟙 x) = eqToHom h.symm := by
  subst h
  rw [eqToHom_refl, ← Biadjunction.rightMate_id Q₁]
  exact (IsDiag.rightMate Q₁ Q₂ hcup hcap' (isDiag_id x)).eq
    (IsDiag.rightMate Q₁ Q₁ hcup hcap (isDiag_id x))

end Comp

/-! ## The biadjunctions of words -/

section Words

variable {P : Presentation.{w, v} S R} {D : S.ColourDuality}

theorem _root_.StringDiagrams.ColourCupCapDiagrams.layers_cupW_congr' (K : ColourCupCapDiagrams S D)
    {r r' : S.Region} {w w' : List S.Colour} (er : r = r') (ew : w = w') (h : S.ok r w)
    (h' : S.ok r' w') : Diagram.layers (K.cupW r w h) = Diagram.layers (K.cupW r' w' h') := by
  subst er ew; rfl

theorem _root_.StringDiagrams.ColourCupCapDiagrams.layers_capW_congr' (K : ColourCupCapDiagrams S D)
    {r r' : S.Region} {w w' : List S.Colour} (er : r = r') (ew : w = w') (h : S.ok r w)
    (h' : S.ok r' w') : Diagram.layers (K.capW r w h) = Diagram.layers (K.capW r' w' h') := by
  subst er ew; rfl

theorem _root_.StringDiagrams.ColourCupCapDiagrams.layers_cup'W_congr'
    (K : ColourCupCapDiagrams S D) {r r' : S.Region} {w w' : List S.Colour} (er : r = r')
    (ew : w = w') (h : S.ok r w) (h' : S.ok r' w') :
    Diagram.layers (K.cup'W r w h) = Diagram.layers (K.cup'W r' w' h') := by
  subst er ew; rfl

theorem _root_.StringDiagrams.ColourCupCapDiagrams.layers_cap'W_congr'
    (K : ColourCupCapDiagrams S D) {r r' : S.Region} {w w' : List S.Colour} (er : r = r')
    (ew : w = w') (h : S.ok r w) (h' : S.ok r' w') :
    Diagram.layers (K.cap'W r w h) = Diagram.layers (K.cap'W r' w' h') := by
  subst er ew; rfl

variable [S.IsEven] (Q : ColourCupsCaps P D) {l m n : P.Bicat}

/-- The unit of `x ⊣ x*` has the layers of the nested cups `cupW` of `x`. -/
theorem isDiag_biadj_left_unit (x : l ⟶ m) :
    IsDiag P (biadj Q.biadjunctions x).left.unit
      (Diagram.layers (Q.toDiagrams.cupW l.region x.obj.word (Bicat.Hom.ok_region x))) :=
  ⟨_, biadj_left_unit_eq_wordCup Q x, rfl⟩

/-- The counit of `x ⊣ x*` has the layers of the nested caps `capW` of `x`. -/
theorem isDiag_biadj_left_counit (x : l ⟶ m) :
    IsDiag P (biadj Q.biadjunctions x).left.counit
      (Diagram.layers (Q.toDiagrams.capW l.region x.obj.word (Bicat.Hom.ok_region x))) :=
  ⟨_, biadj_left_counit_eq_wordCap Q x, rfl⟩

/-- The unit of `x* ⊣ x` has the layers of the nested cups `cup'W` of `x`. -/
theorem isDiag_biadj_right_unit (x : l ⟶ m) :
    IsDiag P (biadj Q.biadjunctions x).right.unit
      (Diagram.layers (Q.toDiagrams.cup'W l.region x.obj.word (Bicat.Hom.ok_region x))) :=
  ⟨_, biadj_right_unit_eq_wordCup' Q x, rfl⟩

/-- The counit of `x* ⊣ x` has the layers of the nested caps `cap'W` of `x`. -/
theorem isDiag_biadj_right_counit (x : l ⟶ m) :
    IsDiag P (biadj Q.biadjunctions x).right.counit
      (Diagram.layers (Q.toDiagrams.cap'W l.region x.obj.word (Bicat.Hom.ok_region x))) :=
  ⟨_, biadj_right_counit_eq_wordCap' Q x, rfl⟩

omit [S.IsEven] in
theorem Bicat.Hom.comp_word (x : l ⟶ m) (y : m ⟶ n) :
    (x ≫ y).obj.word = x.obj.word ++ y.obj.word := rfl

/-- The counit of the composite `(biadj x).comp (biadj y)` has the layers of the nested caps of
the concatenated word. -/
theorem isDiag_biadj_comp_left_counit (x : l ⟶ m) (y : m ⟶ n) :
    IsDiag P ((biadj Q.biadjunctions x).comp (biadj Q.biadjunctions y)).left.counit
      (Diagram.layers (Q.toDiagrams.capW l.region (x ≫ y).obj.word
        (Bicat.Hom.ok_region (x ≫ y)))) := by
  refine (IsDiag.comp_left_counit _ _ (isDiag_biadj_left_counit Q x)
    (isDiag_biadj_left_counit Q y)).congr ?_
  have hok : S.ok l.region (x.obj.word ++ y.obj.word) := Bicat.Hom.ok_region (x ≫ y)
  rw [ColourCupCapDiagrams.layers_capW_congr' _ rfl (Bicat.Hom.comp_word x y) _ hok,
    ColourCupCapDiagrams.layers_capW_append _ _ _ hok,
    ColourCupCapDiagrams.layers_capW_congr' _ (Bicat.Hom.endR_region x) rfl _
      (Bicat.Hom.ok_region y), List.map_map]
  congr 1
  refine List.map_congr_left fun L _ => ?_
  have hn : S.endR l.region (x.obj.word ++ y.obj.word) = n.region := Bicat.Hom.endR_region (x ≫ y)
  simp only [Function.comp_apply, Layer.wl, Layer.wr, Layer.whisker, dualHom_obj, hn]

/-- **The biadjunction of a concatenated word is the composite biadjunction**: the comparison
`(x ≫ y)* ⟶ y* ≫ x*` of right adjoints of `x ≫ y` is the identity. -/
theorem rightMate_comp_biadj_id (x : l ⟶ m) (y : m ⟶ n) :
    Biadjunction.rightMate ((biadj Q.biadjunctions x).comp (biadj Q.biadjunctions y))
        (biadj Q.biadjunctions (x ≫ y)) (𝟙 _) = eqToHom (P.dualHom_comp D x y) := by
  refine rightMate_id_eq_eqToHom _ _ (P.dualHom_comp D x y).symm
    (IsDiag.comp_left_unit _ _ (isDiag_biadj_left_unit Q x) (isDiag_biadj_left_unit Q y))
    (isDiag_biadj_comp_left_counit Q x y) (isDiag_biadj_left_counit Q (x ≫ y))

/-- **The biadjunction of a concatenated word is the composite biadjunction**: the comparison
`y* ≫ x* ⟶ (x ≫ y)*` of right adjoints of `x ≫ y` is the identity. -/
theorem rightMate_biadj_comp_id (x : l ⟶ m) (y : m ⟶ n) :
    Biadjunction.rightMate (biadj Q.biadjunctions (x ≫ y))
        ((biadj Q.biadjunctions x).comp (biadj Q.biadjunctions y)) (𝟙 _) =
      eqToHom (P.dualHom_comp D x y).symm := by
  refine rightMate_id_eq_eqToHom _ _ (P.dualHom_comp D x y) (isDiag_biadj_left_unit Q (x ≫ y))
    (isDiag_biadj_left_counit Q (x ≫ y)) (isDiag_biadj_comp_left_counit Q x y)

/-- The mate for the biadjunction of a concatenated word is the mate for the composite
biadjunction, up to the identifications `(x y)* = y* x*`. -/
theorem rightMate_biadj_comp {x x' : l ⟶ m} {y y' : m ⟶ n} (α : x ≫ y ⟶ x' ≫ y') :
    Biadjunction.rightMate (biadj Q.biadjunctions (x ≫ y)) (biadj Q.biadjunctions (x' ≫ y')) α =
      eqToHom (P.dualHom_comp D x' y') ≫
        Biadjunction.rightMate ((biadj Q.biadjunctions x).comp (biadj Q.biadjunctions y))
          ((biadj Q.biadjunctions x').comp (biadj Q.biadjunctions y')) α ≫
          eqToHom (P.dualHom_comp D x y).symm := by
  rw [rightMate_eq_comp' _ ((biadj Q.biadjunctions x).comp (biadj Q.biadjunctions y)) _
    ((biadj Q.biadjunctions x').comp (biadj Q.biadjunctions y')),
    rightMate_comp_biadj_id, rightMate_biadj_comp_id]

/-- **The mate of a left-whiskered 2-morphism is the right-whiskered mate**:
`(h ◁ θ)^* = θ^* ▷ h*`, up to the identifications `(h x)* = x* h*`. -/
theorem rightMate_biadj_whiskerLeft (h : n ⟶ l) {x x' : l ⟶ m} (θ : x ⟶ x') :
    Biadjunction.rightMate (biadj Q.biadjunctions (h ≫ x)) (biadj Q.biadjunctions (h ≫ x'))
        (h ◁ θ) =
      eqToHom (P.dualHom_comp D h x') ≫
        Biadjunction.rightMate (biadj Q.biadjunctions x) (biadj Q.biadjunctions x') θ ▷
          P.dualHom D h ≫ eqToHom (P.dualHom_comp D h x).symm := by
  rw [rightMate_biadj_comp, Biadjunction.rightMate_whiskerLeft]

/-- **The mate of a right-whiskered 2-morphism is the left-whiskered mate**:
`(θ ▷ h)^* = h* ◁ θ^*`, up to the identifications `(x h)* = h* x*`. -/
theorem rightMate_biadj_whiskerRight (h : m ⟶ n) {x x' : l ⟶ m} (θ : x ⟶ x') :
    Biadjunction.rightMate (biadj Q.biadjunctions (x ≫ h)) (biadj Q.biadjunctions (x' ≫ h))
        (θ ▷ h) =
      eqToHom (P.dualHom_comp D x' h) ≫
        P.dualHom D h ◁ Biadjunction.rightMate (biadj Q.biadjunctions x)
          (biadj Q.biadjunctions x') θ ≫ eqToHom (P.dualHom_comp D x h).symm := by
  rw [rightMate_biadj_comp, Biadjunction.rightMate_whiskerRight]

/-- Mates along equalities of 1-morphisms. -/
theorem rightMate_biadj_eqToHom_conj {A A₁ A' A₁' : l ⟶ m} (e : A = A₁) (e' : A' = A₁')
    (θ : A₁ ⟶ A₁') :
    Biadjunction.rightMate (biadj Q.biadjunctions A) (biadj Q.biadjunctions A')
        (eqToHom e ≫ θ ≫ eqToHom e'.symm) =
      eqToHom (congrArg (P.dualHom D) e') ≫
        Biadjunction.rightMate (biadj Q.biadjunctions A₁) (biadj Q.biadjunctions A₁') θ ≫
          eqToHom (congrArg (P.dualHom D) e).symm := by
  subst e e'; simp

/-- The layers of the right mate of the class of a diagram, for the biadjunctions of words. -/
theorem IsDiag.rightMate_biadj {x x' : l ⟶ m} {θ : x ⟶ x'} {ls : List (Layer S)}
    (hθ : IsDiag P θ ls) :
    IsDiag P (Biadjunction.rightMate (biadj Q.biadjunctions x) (biadj Q.biadjunctions x') θ)
      ((Diagram.layers (Q.toDiagrams.cupW l.region x.obj.word (Bicat.Hom.ok_region x))).map
          (·.wl (P.dualHom D x').obj) ++
        (ls.map (·.wr (P.dualHom D x).obj.word)).map (·.wl (P.dualHom D x').obj) ++
        (Diagram.layers (Q.toDiagrams.capW l.region x'.obj.word (Bicat.Hom.ok_region x'))).map
          (·.wr (P.dualHom D x).obj.word)) :=
  IsDiag.rightMate _ _ (isDiag_biadj_left_unit Q x) (isDiag_biadj_left_counit Q x') hθ

/-- `(h ◁ θ)^* = θ^* ▷ h*`, at the level of layers. -/
theorem IsDiag.rightMate_biadj_whiskerLeft (h : n ⟶ l) {x x' : l ⟶ m} {θ : x ⟶ x'}
    {ms : List (Layer S)}
    (hθ : IsDiag P (Biadjunction.rightMate (biadj Q.biadjunctions x) (biadj Q.biadjunctions x') θ)
      ms) :
    IsDiag P (Biadjunction.rightMate (biadj Q.biadjunctions (h ≫ x))
        (biadj Q.biadjunctions (h ≫ x')) (h ◁ θ)) (ms.map (·.wr (P.dualHom D h).obj.word)) := by
  rw [Presentation.rightMate_biadj_whiskerLeft]
  exact ((hθ.whiskerRight _).comp_eqToHom _).eqToHom_comp _

/-- `(θ ▷ h)^* = h* ◁ θ^*`, at the level of layers. -/
theorem IsDiag.rightMate_biadj_whiskerRight (h : m ⟶ n) {x x' : l ⟶ m} {θ : x ⟶ x'}
    {ms : List (Layer S)}
    (hθ : IsDiag P (Biadjunction.rightMate (biadj Q.biadjunctions x) (biadj Q.biadjunctions x') θ)
      ms) :
    IsDiag P (Biadjunction.rightMate (biadj Q.biadjunctions (x ≫ h))
        (biadj Q.biadjunctions (x' ≫ h)) (θ ▷ h)) (ms.map (·.wl (P.dualHom D h).obj)) := by
  rw [Presentation.rightMate_biadj_whiskerRight]
  exact ((hθ.whiskerLeft _).comp_eqToHom _).eqToHom_comp _

/-! ### Rotation is a strict 2-functor -/

variable (hgen : ∀ (g : S.Gen) (hg : S.GenValid g),
  Biadjunction.IsCyclic (biadj Q.biadjunctions (P.genDom g hg))
    (biadj Q.biadjunctions (P.genCod g hg)) (P.gen2 g hg))

/-- For the pivotal structure given by the nested cups and caps, the canonical comparison
`(x ≫ y)* ≅ y* ≫ x*` is the identity. -/
theorem pivotalOfGenerators_dualCompIso_hom (x : l ⟶ m) (y : m ⟶ n) :
    letI := pivotalOfGenerators Q.biadjunctions hgen
    (Pivotal.dualCompIso x y).hom = eqToHom (P.dualHom_comp D x y) :=
  rightMate_comp_biadj_id Q x y

/-- For the pivotal structure given by the nested cups and caps, rotation commutes strictly with
left whiskering. -/
theorem pivotalOfGenerators_rotate_whiskerLeft (h : n ⟶ l) {x x' : l ⟶ m} (θ : x ⟶ x') :
    letI := pivotalOfGenerators Q.biadjunctions hgen
    Pivotal.rotate (h ◁ θ) =
      eqToHom (P.dualHom_comp D h x') ≫ Pivotal.rotate θ ▷ P.dualHom D h ≫
        eqToHom (P.dualHom_comp D h x).symm :=
  rightMate_biadj_whiskerLeft Q h θ

/-- For the pivotal structure given by the nested cups and caps, rotation commutes strictly with
right whiskering. -/
theorem pivotalOfGenerators_rotate_whiskerRight (h : m ⟶ n) {x x' : l ⟶ m} (θ : x ⟶ x') :
    letI := pivotalOfGenerators Q.biadjunctions hgen
    Pivotal.rotate (θ ▷ h) =
      eqToHom (P.dualHom_comp D x' h) ≫ P.dualHom D h ◁ Pivotal.rotate θ ≫
        eqToHom (P.dualHom_comp D x h).symm :=
  rightMate_biadj_whiskerRight Q h θ

end Words

/-! ## Double rotation -/

section Double

variable {D : S.ColourDuality}

theorem _root_.StringDiagrams.Signature.ColourDuality.dualWord_dualWord_of
    (hD : ∀ c, D.dual (D.dual c) = c) (w : List S.Colour) : D.dualWord (D.dualWord w) = w := by
  simp [Signature.ColourDuality.dualWord_eq, List.map_reverse, List.map_map, Function.comp_def,
    hD]

set_option backward.isDefEq.respectTransparency false in
/-- For an involutive duality whose chosen caps of `c*` have the layers of the caps `c c* ⟶ 1`,
the nested caps of the dual word `w*` are the nested caps `cap'W` of `w`. -/
theorem _root_.StringDiagrams.ColourCupCapDiagrams.layers_capW_dualWord
    (K : ColourCupCapDiagrams S D) (hD : ∀ c, D.dual (D.dual c) = c)
    (hcap : ∀ c, Diagram.layers (K.cap (D.dual c)) = Diagram.layers (K.cap' c)) :
    ∀ (r : S.Region) (w : List S.Colour) (h : S.ok r w) (h' : S.ok (S.endR r w) (D.dualWord w)),
      Diagram.layers (K.capW (S.endR r w) (D.dualWord w) h') =
        Diagram.layers (K.cap'W r w h)
  | _, [], _, _ => by simp
  | r, c :: w, h, h' => by
    have hw' : S.ok (S.endR (S.colourTgt c) w) (D.dualWord w) :=
      (D.ok_dualWord _ w h.2).1
    have ih := ColourCupCapDiagrams.layers_capW_dualWord K hD hcap (S.colourTgt c) w h.2 hw'
    have h'' : S.ok (S.endR (S.colourTgt c) w) (D.dualWord w ++ [D.dual c]) := by
      simpa using h'
    rw [ColourCupCapDiagrams.layers_capW_congr' K rfl (D.dualWord_cons c w) h' h'',
      ColourCupCapDiagrams.layers_capW_append,
      ColourCupCapDiagrams.layers_capW_congr' K
        (show S.endR r (c :: w) = S.endR (S.colourTgt c) w from rfl) rfl _ hw', ih,
      ColourCupCapDiagrams.layers_cap'W_cons]
    have hr : S.endR (S.endR (S.colourTgt c) w) (D.dualWord w) = S.colourTgt c :=
      (D.ok_dualWord _ w h.2).2
    congr 1
    · refine List.map_congr_left fun L _ => ?_
      simp only [Layer.whisker, Signature.endR_append, hr, Signature.endR_cons,
        Signature.endR_nil, D.tgt_dual, h.1, Signature.ColourDuality.dualWord_cons,
        Signature.ColourDuality.dualWord_nil, List.nil_append, hD]
    · rw [ColourCupCapDiagrams.layers_capW_congr' K
        (show S.endR (S.endR r (c :: w)) (D.dualWord w) = S.colourTgt c from hr) rfl _
        (show S.ok (S.colourTgt c) [D.dual c] from ⟨D.src_dual c, trivial⟩),
        ColourCupCapDiagrams.layers_capW_cons,
        ColourCupCapDiagrams.layers_capW_nil, List.append_nil, ← hcap c]
      exact ColourCupCapDiagrams.layers_whisker_nil_of_start (K.cap (D.dual c))

variable {P : Presentation.{w, v} S R} {l m : P.Bicat}

theorem dualHom_dualHom_of (hD : ∀ c, D.dual (D.dual c) = c) (x : l ⟶ m) :
    P.dualHom D (P.dualHom D x) = x :=
  Bicat.Hom.ext (Obj.ext x.start_eq.symm (D.dualWord_dualWord_of hD _))

variable [S.IsEven] (Q : ColourCupsCaps P D) (hD : ∀ c, D.dual (D.dual c) = c)
  (hcap : ∀ c, Diagram.layers (Q.cap (D.dual c)) = Diagram.layers (Q.cap' c))
include hD hcap

/-- The counit of `x** ⊣ x*` (the biadjunction of the dual word) has the layers of the counit
of `x ⊣ x*` read the other way, the nested caps `cap'W` of `x`. -/
theorem isDiag_biadj_dualHom_left_counit (x : l ⟶ m) :
    IsDiag P (biadj Q.biadjunctions (P.dualHom D x)).left.counit
      (Diagram.layers (Q.toDiagrams.cap'W l.region x.obj.word (Bicat.Hom.ok_region x))) := by
  refine (isDiag_biadj_left_counit Q (P.dualHom D x)).congr ?_
  have h' : S.ok (S.endR l.region x.obj.word) (D.dualWord x.obj.word) := by
    rw [Bicat.Hom.endR_region x]; exact Bicat.Hom.ok_region (P.dualHom D x)
  rw [ColourCupCapDiagrams.layers_capW_congr' _ (Bicat.Hom.endR_region x).symm
    (rfl : (P.dualHom D x).obj.word = D.dualWord x.obj.word) _ h']
  exact Q.toDiagrams.layers_capW_dualWord hD hcap _ _ _ _

/-- The comparison `x ⟶ x**` of the right adjoints of `x*` given by the biadjunctions of `x*`
and of `x` is the identity. -/
theorem rightMate_biadj_dualHom_symm_id (x : l ⟶ m) :
    Biadjunction.rightMate (biadj Q.biadjunctions (P.dualHom D x)) (biadj Q.biadjunctions x).symm
        (𝟙 _) = eqToHom (dualHom_dualHom_of hD x).symm :=
  rightMate_id_eq_eqToHom _ _ (dualHom_dualHom_of hD x) (isDiag_biadj_left_unit Q _)
    (isDiag_biadj_dualHom_left_counit Q hD hcap x) (isDiag_biadj_right_counit Q x)

/-- The comparison `x** ⟶ x` of the right adjoints of `x*` given by the biadjunctions of `x`
and of `x*` is the identity. -/
theorem rightMate_biadj_symm_dualHom_id (x : l ⟶ m) :
    Biadjunction.rightMate (biadj Q.biadjunctions x).symm (biadj Q.biadjunctions (P.dualHom D x))
        (𝟙 _) = eqToHom (dualHom_dualHom_of hD x) :=
  rightMate_id_eq_eqToHom _ _ (dualHom_dualHom_of hD x).symm (isDiag_biadj_right_unit Q x)
    (isDiag_biadj_right_counit Q x) (isDiag_biadj_dualHom_left_counit Q hD hcap x)

/-- **Rotating a cyclic 2-morphism twice gives it back**, up to the identifications `x** = x`. -/
theorem rightMate_rightMate {x x' : l ⟶ m} (α : x ⟶ x')
    (hα : Biadjunction.IsCyclic (biadj Q.biadjunctions x) (biadj Q.biadjunctions x') α) :
    Biadjunction.rightMate (biadj Q.biadjunctions (P.dualHom D x'))
        (biadj Q.biadjunctions (P.dualHom D x))
        (Biadjunction.rightMate (biadj Q.biadjunctions x) (biadj Q.biadjunctions x') α) =
      eqToHom (dualHom_dualHom_of hD x) ≫ α ≫ eqToHom (dualHom_dualHom_of hD x').symm := by
  rw [rightMate_eq_comp' _ (biadj Q.biadjunctions x').symm _ (biadj Q.biadjunctions x).symm,
    show Biadjunction.rightMate (biadj Q.biadjunctions x) (biadj Q.biadjunctions x') α =
      Biadjunction.leftMate (biadj Q.biadjunctions x) (biadj Q.biadjunctions x') α from hα,
    rightMate_symm_leftMate, rightMate_biadj_symm_dualHom_id Q hD hcap,
    rightMate_biadj_dualHom_symm_id Q hD hcap]

/-- Rotating back: if `β` is the rotation of a cyclic `α`, then the rotation of `β` has the
layers of `α`. -/
theorem IsDiag.rightMate_rotate_back {A A' : l ⟶ m} {B B' : m ⟶ l}
    (eB : B = P.dualHom D A') (eB' : B' = P.dualHom D A) {α : A ⟶ A'} {β : B ⟶ B'}
    (hα : Biadjunction.IsCyclic (biadj Q.biadjunctions A) (biadj Q.biadjunctions A') α)
    (hβ : β = eqToHom eB ≫ Biadjunction.rightMate (biadj Q.biadjunctions A)
      (biadj Q.biadjunctions A') α ≫ eqToHom eB'.symm)
    {ls : List (Layer S)} (hl : IsDiag P α ls) :
    IsDiag P (Biadjunction.rightMate (biadj Q.biadjunctions B) (biadj Q.biadjunctions B') β) ls := by
  subst eB eB' hβ
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [rightMate_rightMate Q hD hcap α hα]
  exact (hl.comp_eqToHom _).eqToHom_comp _

variable (hgen : ∀ (g : S.Gen) (hg : S.GenValid g),
  Biadjunction.IsCyclic (biadj Q.biadjunctions (P.genDom g hg))
    (biadj Q.biadjunctions (P.genCod g hg)) (P.gen2 g hg))

/-- For the pivotal structure given by the nested cups and caps of an involutive duality, the
canonical comparison `x ≅ x**` is the identity. -/
theorem pivotalOfGenerators_pivotalIso_hom (x : l ⟶ m) :
    letI := pivotalOfGenerators Q.biadjunctions hgen
    (Pivotal.pivotalIso x).hom = eqToHom (dualHom_dualHom_of hD x).symm :=
  rightMate_biadj_dualHom_symm_id Q hD hcap x

/-- For the pivotal structure given by the nested cups and caps of an involutive duality,
rotating twice is the identity, up to the identifications `x** = x`. -/
theorem pivotalOfGenerators_rotate_rotate {x x' : l ⟶ m} (α : x ⟶ x') :
    letI := pivotalOfGenerators Q.biadjunctions hgen
    Pivotal.rotate (Pivotal.rotate α) =
      eqToHom (dualHom_dualHom_of hD x) ≫ α ≫ eqToHom (dualHom_dualHom_of hD x').symm :=
  rightMate_rightMate Q hD hcap α (isCyclic_of_generators _ hgen α)

end Double

/-- The cups and caps of the pivotal extension satisfy the hypothesis of `rightMate_rightMate`:
the cap of `c*` is the cap `c c* ⟶ 1`. -/
theorem pivotalCupsCaps_cap_dual [S.IsEven]
    (E : S.ColourInvolution) (Q : Presentation.{w, v} (S.pivotal E.toColourDuality) R)
    (hz : Q.PivotalZigzags E.toColourDuality) (c : S.Colour) :
    Diagram.layers ((Q.pivotalCupsCaps E hz).cap (E.dual c)) =
      Diagram.layers ((Q.pivotalCupsCaps E hz).cap' c) := rfl

/-- **Rotating a cyclic 2-morphism twice gives it back**, for a presentation of the pivotal
extension along an involution, up to the identifications `x** = x`. -/
theorem pivotal_rightMate_rightMate [S.IsEven] (E : S.ColourInvolution)
    (Q : Presentation.{w, v} (S.pivotal E.toColourDuality) R)
    (hz : Q.PivotalZigzags E.toColourDuality) {l m : Q.Bicat} {x x' : l ⟶ m} (α : x ⟶ x')
    (hα : Biadjunction.IsCyclic (biadj (pivotalBiadj E Q hz) x) (biadj (pivotalBiadj E Q hz) x')
      α) :
    Biadjunction.rightMate (biadj (pivotalBiadj E Q hz) (Q.dualHom E.toColourDuality.pivotal x'))
        (biadj (pivotalBiadj E Q hz) (Q.dualHom E.toColourDuality.pivotal x))
        (Biadjunction.rightMate (biadj (pivotalBiadj E Q hz) x) (biadj (pivotalBiadj E Q hz) x')
          α) =
      eqToHom (dualHom_dualHom_of (D := E.toColourDuality.pivotal) E.dual_dual x) ≫ α ≫
        eqToHom (dualHom_dualHom_of (D := E.toColourDuality.pivotal) E.dual_dual x').symm :=
  rightMate_rightMate (Q.pivotalCupsCaps E hz) E.dual_dual (pivotalCupsCaps_cap_dual E Q hz) α hα

end Presentation

end StringDiagrams
