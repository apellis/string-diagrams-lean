import StringDiagrams.Bicategory
import StringDiagrams.Generation
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# Adjunctions in presented 2-categories from zigzag relations

Let `P` be a presentation of an even signature. A pair of well-formed words `x : l ⟶ m` and
`y : m ⟶ l` of the presented bicategory `P.Bicat`, together with a *cup* diagram
`cup : 1_l ⟶ x ⊗ y` and a *cap* diagram `cap : y ⊗ x ⟶ 1_m` whose two zigzag composites

* `(cup ⊗ 1_x) ≫ (1_x ⊗ cap)`  (`Diagram.leftZigzag`, a diagram `x ⟶ x`), and
* `(1_y ⊗ cup) ≫ (cap ⊗ 1_y)`  (`Diagram.rightZigzag`, a diagram `y ⟶ y`)

have the class of the identity, gives a Mathlib adjunction `x ⊣ y` in `P.Bicat` with unit and
counit the classes of `cup` and `cap` (`Presentation.adjunctionOfZigzag`). The same data for a
monoidal signature gives an `ExactPairing (P.obj x) (P.obj y)` in the monoidal category
`P.Presented` (`Presentation.exactPairingOfZigzag`); this generalizes the self-duality of one
Temperley–Lieb strand.

The zigzag hypotheses are equalities in the presented category of the classes of two explicit
diagrams. In practice they are imposed as relations of `P`. A relation `rel i = d₁ - d₂` gives
`P.diag d₁ = P.diag d₂` (`Presentation.diag_eq_of_rel`), and a diagram with the same layers as a
zigzag has the same class (`Presentation.diag_eq_of_layers_eq'`). The variants
`Presentation.adjunctionOfRels` and `Presentation.exactPairingOfRels` take the indices of two
relations of the form `z - e` (with `e` a diagram with no layers, such as an identity) and
the equalities of layers of `z` with the zigzags; everything else is automatic.

## Main definitions and results

* `Presentation.lin_rel_self`, `Presentation.diag_eq_of_rel`, `Presentation.diag_eq_eqToHom_of_rel`:
  an unwhiskered relation holds in the presented category.
* `Diagram.leftZigzag`, `Diagram.rightZigzag` (bicategorical) and `Diagram.leftZigzagM`,
  `Diagram.rightZigzagM` (monoidal), with their layers.
* `Presentation.leftZigzag_diag`, `Presentation.rightZigzag_diag`: Mathlib's zigzag 2-morphisms
  `leftZigzag`, `rightZigzag` of the classes of `cup` and `cap` are the classes of the zigzag
  diagrams, up to unitors.
* `Presentation.adjunctionOfZigzag`, `Presentation.adjunctionOfRels`.
* `Presentation.exactPairingOfZigzag`, `Presentation.exactPairingOfRels`.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Bicategory

universe w v u₀ u₁ u₂

variable {S : Signature.{u₀, u₁, u₂}} {R : Type w} [CommRing R]

/-! ## Unwhiskered relations -/

namespace Diagram

variable {a b : Obj S}

/-- A diagram without layers is between equal objects. -/
theorem eq_of_layers_eq_nil (e : a ⟶ b) (he : layers e = []) : a = b := by
  have := chain e
  rw [he] at this
  exact this

theorem whisker_nil_start_eq_cast (d : a ⟶ b) (hw : a.WhiskerOK (Obj.nil a.start) [])
    (ha : a = a.whisker (Obj.nil a.start) []) (hb : b = b.whisker (Obj.nil a.start) []) :
    whisker d (Obj.nil a.start) [] hw = cast d ha hb := by
  apply Diagram.ext
  simp only [layers_whisker, layers_cast]
  conv_rhs => rw [← List.map_id (layers d)]
  exact List.map_congr_left fun L hL =>
    show L.whisker (Obj.nil a.start) [] = id L from
      Layer.ext ((chain d).start_of_mem hL).symm (by simp [Layer.whisker]) rfl
        (by simp [Layer.whisker])

end Diagram

namespace Presentation

variable (P : Presentation.{w, v} S R)

theorem lin_cast {a b a' b' : Obj S} (f : LinDiagram R a b) (ha : a = a') (hb : b = b') :
    P.lin (LinDiagram.cast f ha hb) =
      eqToHom (congrArg P.obj ha.symm) ≫ P.lin f ≫ eqToHom (congrArg P.obj hb) := by
  subst ha hb; simp

/-- Every relation holds in the presented category, without whiskering. -/
theorem lin_rel_self (i : P.Rel) : P.lin (P.rel i) = 0 := by
  by_cases h0 : P.rel i = 0
  · rw [h0, lin_zero]
  obtain ⟨d, -⟩ := Finsupp.ne_iff.mp h0
  have hw : (P.dom i).WhiskerOK (Obj.nil (P.dom i).start) [] := ⟨trivial, rfl, trivial⟩
  have ha : P.dom i = (P.dom i).whisker (Obj.nil (P.dom i).start) [] :=
    Obj.ext rfl (by simp [Obj.whisker])
  have hb : P.cod i = (P.cod i).whisker (Obj.nil (P.dom i).start) [] :=
    Obj.ext (Diagram.chain (d : P.dom i ⟶ P.cod i)).start_eq (by simp [Obj.whisker])
  have key := P.lin_rel i _ [] hw
  have e : LinDiagram.whisker (P.rel i) (Obj.nil (P.dom i).start) [] hw =
      LinDiagram.cast (P.rel i) ha hb := by
    unfold LinDiagram.whisker LinDiagram.cast
    congr 1
    funext d'
    exact Diagram.whisker_nil_start_eq_cast d' hw ha hb
  rw [e, lin_cast] at key
  have := congrArg (fun t => eqToHom (congrArg P.obj ha) ≫ t ≫ eqToHom (congrArg P.obj hb.symm))
    key
  simpa using this

/-- A relation `rel i = d₁ - d₂` identifies the classes of `d₁` and `d₂`. -/
theorem diag_eq_of_rel (i : P.Rel) {d₁ d₂ : P.dom i ⟶ P.cod i}
    (h : P.rel i = LinDiagram.of d₁ - LinDiagram.of d₂) : P.diag d₁ = P.diag d₂ := by
  have := P.lin_rel_self i
  rwa [h, lin_sub, lin_of, lin_of, sub_eq_zero] at this

/-- A relation `rel i = z - e`, where `e` has no layers (for example an identity), says that the
class of `z` is an identity, up to retyping. -/
theorem diag_eq_eqToHom_of_rel (i : P.Rel) {z e : P.dom i ⟶ P.cod i}
    (he : Diagram.layers e = []) (h : P.rel i = LinDiagram.of z - LinDiagram.of e) :
    P.diag z = eqToHom (congrArg P.obj (Diagram.eq_of_layers_eq_nil e he)) := by
  rw [P.diag_eq_of_rel i h, ← P.diag_eqToHom (Diagram.eq_of_layers_eq_nil e he)]
  exact P.diag_eq_of_layers_eq (by simp [he])

end Presentation

/-! ## Zigzag diagrams -/

namespace Diagram

variable {x y : Obj S} {l m : S.Region}

/-- The left zigzag `(cup ⊗ 1_x) ≫ (1_x ⊗ cap) : x ⟶ x` of a cup `1_l ⟶ x ⊗ y` and a cap
`y ⊗ x ⟶ 1_m`, for general regions. -/
def leftZigzag (cup : Obj.nil l ⟶ x.tensor y) (cap : y.tensor x ⟶ Obj.nil m)
    (h₁ : (Obj.nil l).Composable x) (h₂ : x.Composable (y.tensor x)) (hx : x.start = l) :
    x ⟶ x :=
  cast (rwhisker cup x h₁ ≫ eqToHom (Obj.tensor_assoc x y x) ≫ lwhisker x cap h₂)
    (Obj.nil_tensor hx) (Obj.tensor_nil x m)

/-- The right zigzag `(1_y ⊗ cup) ≫ (cap ⊗ 1_y) : y ⟶ y` of a cup `1_l ⟶ x ⊗ y` and a cap
`y ⊗ x ⟶ 1_m`, for general regions. -/
def rightZigzag (cup : Obj.nil l ⟶ x.tensor y) (cap : y.tensor x ⟶ Obj.nil m)
    (h₁ : y.Composable (Obj.nil l)) (h₂ : (y.tensor x).Composable y) (hy : y.start = m) :
    y ⟶ y :=
  cast (lwhisker y cup h₁ ≫ eqToHom (Obj.tensor_assoc y x y).symm ≫ rwhisker cap y h₂)
    (Obj.tensor_nil y l) (Obj.nil_tensor hy)

@[simp] theorem layers_leftZigzag (cup : Obj.nil l ⟶ x.tensor y) (cap : y.tensor x ⟶ Obj.nil m)
    (h₁ : (Obj.nil l).Composable x) (h₂ : x.Composable (y.tensor x)) (hx : x.start = l) :
    layers (leftZigzag cup cap h₁ h₂ hx) =
      (layers cup).map (·.wr x.word) ++ (layers cap).map (·.wl x) := by
  simp [leftZigzag]

@[simp] theorem layers_rightZigzag (cup : Obj.nil l ⟶ x.tensor y) (cap : y.tensor x ⟶ Obj.nil m)
    (h₁ : y.Composable (Obj.nil l)) (h₂ : (y.tensor x).Composable y) (hy : y.start = m) :
    layers (rightZigzag cup cap h₁ h₂ hy) =
      (layers cup).map (·.wl y) ++ (layers cap).map (·.wr y.word) := by
  simp [rightZigzag]

end Diagram

/-! ## Adjunctions in the presented bicategory -/

namespace Presentation

variable (P : Presentation.{w, v} S R) [S.IsEven] {l m : P.Bicat}

/-- The left zigzag diagram of a cup and a cap for 1-morphisms `x : l ⟶ m`, `y : m ⟶ l` of
`P.Bicat`. -/
abbrev leftZigzagD (x : l ⟶ m) (y : m ⟶ l) (cup : Obj.nil l.region ⟶ x.obj.tensor y.obj)
    (cap : y.obj.tensor x.obj ⟶ Obj.nil m.region) : x.obj ⟶ x.obj :=
  Diagram.leftZigzag cup cap (Bicat.Hom.composable (𝟙 l) x) (Bicat.Hom.composable x (y ≫ x))
    x.start_eq

/-- The right zigzag diagram of a cup and a cap for 1-morphisms `x : l ⟶ m`, `y : m ⟶ l` of
`P.Bicat`. -/
abbrev rightZigzagD (x : l ⟶ m) (y : m ⟶ l) (cup : Obj.nil l.region ⟶ x.obj.tensor y.obj)
    (cap : y.obj.tensor x.obj ⟶ Obj.nil m.region) : y.obj ⟶ y.obj :=
  Diagram.rightZigzag cup cap (Bicat.Hom.composable y (𝟙 l)) (Bicat.Hom.composable (y ≫ x) y)
    y.start_eq

variable {P}

theorem Bicat.associator_hom_eq {n k : P.Bicat} (x : l ⟶ m) (y : m ⟶ n) (z : n ⟶ k) :
    ((α_ x y z).hom : P.obj _ ⟶ P.obj _) =
      eqToHom (congrArg P.obj (Obj.tensor_assoc x.obj y.obj z.obj)) := rfl

theorem Bicat.associator_inv_eq {n k : P.Bicat} (x : l ⟶ m) (y : m ⟶ n) (z : n ⟶ k) :
    ((α_ x y z).inv : P.obj _ ⟶ P.obj _) =
      eqToHom (congrArg P.obj (Obj.tensor_assoc x.obj y.obj z.obj).symm) := rfl

theorem Bicat.leftUnitor_hom_eq (x : l ⟶ m) :
    ((λ_ x).hom : P.obj _ ⟶ P.obj _) = eqToHom (congrArg P.obj (Obj.nil_tensor x.start_eq)) :=
  rfl

theorem Bicat.leftUnitor_inv_eq (x : l ⟶ m) :
    ((λ_ x).inv : P.obj _ ⟶ P.obj _) =
      eqToHom (congrArg P.obj (Obj.nil_tensor x.start_eq).symm) := rfl

theorem Bicat.rightUnitor_hom_eq (x : l ⟶ m) :
    ((ρ_ x).hom : P.obj _ ⟶ P.obj _) = eqToHom (congrArg P.obj (Obj.tensor_nil x.obj m.region)) :=
  rfl

theorem Bicat.rightUnitor_inv_eq (x : l ⟶ m) :
    ((ρ_ x).inv : P.obj _ ⟶ P.obj _) =
      eqToHom (congrArg P.obj (Obj.tensor_nil x.obj m.region).symm) := rfl

theorem leftZigzag_eq (x : l ⟶ m) (y : m ⟶ l) (η : 𝟙 l ⟶ x ≫ y) (ε : y ≫ x ⟶ 𝟙 m) :
    leftZigzag η ε = η ▷ x ≫ (α_ x y x).hom ≫ x ◁ ε := by
  bicategory

theorem rightZigzag_eq (x : l ⟶ m) (y : m ⟶ l) (η : 𝟙 l ⟶ x ≫ y) (ε : y ≫ x ⟶ 𝟙 m) :
    rightZigzag η ε = y ◁ η ≫ (α_ y x y).inv ≫ ε ▷ y := by
  bicategory

/-- Mathlib's left zigzag of the classes of a cup and a cap is the class of the left zigzag
diagram, up to unitors. -/
theorem leftZigzag_diag (x : l ⟶ m) (y : m ⟶ l) (cup : Obj.nil l.region ⟶ x.obj.tensor y.obj)
    (cap : y.obj.tensor x.obj ⟶ Obj.nil m.region) :
    leftZigzag (P.diag cup : 𝟙 l ⟶ x ≫ y) (P.diag cap : y ≫ x ⟶ 𝟙 m) =
      (λ_ x).hom ≫ (P.diag (P.leftZigzagD x y cup cap) : x ⟶ x) ≫ (ρ_ x).inv := by
  rw [leftZigzag_eq]
  change P.wRAt l.region (P.diag cup) x.obj rfl x.start_eq ≫
      eqToHom (congrArg P.obj (Obj.tensor_assoc x.obj y.obj x.obj)) ≫ P.wL x.obj (P.diag cap) =
    eqToHom (congrArg P.obj (Obj.nil_tensor x.start_eq)) ≫ P.diag (P.leftZigzagD x y cup cap) ≫
      eqToHom (congrArg P.obj (Obj.tensor_nil x.obj m.region).symm)
  rw [P.wRAt_diag cup _ (Bicat.Hom.composable (𝟙 l) x),
    P.wL_diag_of_composable _ cap (Bicat.Hom.composable x (y ≫ x))]
  simp [Diagram.leftZigzag, Diagram.cast_eq, P.diag_eqToHom]

/-- Mathlib's right zigzag of the classes of a cup and a cap is the class of the right zigzag
diagram, up to unitors. -/
theorem rightZigzag_diag (x : l ⟶ m) (y : m ⟶ l) (cup : Obj.nil l.region ⟶ x.obj.tensor y.obj)
    (cap : y.obj.tensor x.obj ⟶ Obj.nil m.region) :
    rightZigzag (P.diag cup : 𝟙 l ⟶ x ≫ y) (P.diag cap : y ≫ x ⟶ 𝟙 m) =
      (ρ_ y).hom ≫ (P.diag (P.rightZigzagD x y cup cap) : y ⟶ y) ≫ (λ_ y).inv := by
  rw [rightZigzag_eq]
  change P.wL y.obj (P.diag cup) ≫
      eqToHom (congrArg P.obj (Obj.tensor_assoc y.obj x.obj y.obj).symm) ≫
        P.wRAt m.region (P.diag cap) y.obj (y ≫ x).start_eq rfl =
    eqToHom (congrArg P.obj (Obj.tensor_nil y.obj l.region)) ≫
      P.diag (P.rightZigzagD x y cup cap) ≫
        eqToHom (congrArg P.obj (Obj.nil_tensor y.start_eq).symm)
  rw [P.wRAt_diag cap _ (Bicat.Hom.composable (y ≫ x) y),
    P.wL_diag_of_composable _ cup (Bicat.Hom.composable y (𝟙 l))]
  simp [Diagram.rightZigzag, Diagram.cast_eq, P.diag_eqToHom]

omit [S.IsEven] in
/-- A relation `rel i = z - e` (with `e` without layers) at the object `a` shows that every
diagram `a ⟶ a` with the same layers as `z` has the class of the identity. -/
theorem diag_eq_id_of_rel {a : Obj S} (i : P.Rel) {z e : P.dom i ⟶ P.cod i}
    (he : Diagram.layers e = []) (hi : P.rel i = LinDiagram.of z - LinDiagram.of e)
    (hdom : P.dom i = a) (Z : a ⟶ a) (hz : Diagram.layers z = Diagram.layers Z) :
    P.diag Z = 𝟙 _ := by
  have hcod : P.cod i = a := (Diagram.eq_of_layers_eq_nil e he).symm.trans hdom
  rw [P.diag_eq_of_layers_eq' Z z hdom.symm hcod.symm hz.symm, P.diag_eq_eqToHom_of_rel i he hi]
  simp

/-- The adjunction `x ⊣ y` in `P.Bicat` given by a cup and a cap satisfying the two zigzag
identities. Its unit and counit are the classes of the cup and the cap. -/
@[simps]
def adjunctionOfZigzag (x : l ⟶ m) (y : m ⟶ l) (cup : Obj.nil l.region ⟶ x.obj.tensor y.obj)
    (cap : y.obj.tensor x.obj ⟶ Obj.nil m.region)
    (hl : P.diag (P.leftZigzagD x y cup cap) = 𝟙 _)
    (hr : P.diag (P.rightZigzagD x y cup cap) = 𝟙 _) : x ⊣ y where
  unit := P.diag cup
  counit := P.diag cap
  left_triangle := by
    rw [leftZigzag_diag, hl]
    exact congrArg ((λ_ x).hom ≫ ·) (Category.id_comp ((ρ_ x).inv))
  right_triangle := by
    rw [rightZigzag_diag, hr]
    exact congrArg ((ρ_ y).hom ≫ ·) (Category.id_comp ((λ_ y).inv))

/-- The adjunction `x ⊣ y` in `P.Bicat` given by a cup and a cap whose zigzag identities are
relations `i` and `j` of `P`, of the form `z - e` with `e` without layers and `z` with the
layers of the zigzag diagram. -/
def adjunctionOfRels (x : l ⟶ m) (y : m ⟶ l) (cup : Obj.nil l.region ⟶ x.obj.tensor y.obj)
    (cap : y.obj.tensor x.obj ⟶ Obj.nil m.region)
    (i : P.Rel) {z e : P.dom i ⟶ P.cod i} (he : Diagram.layers e = [])
    (hi : P.rel i = LinDiagram.of z - LinDiagram.of e) (hidom : P.dom i = x.obj)
    (hz : Diagram.layers z = Diagram.layers (P.leftZigzagD x y cup cap))
    (j : P.Rel) {z' e' : P.dom j ⟶ P.cod j} (he' : Diagram.layers e' = [])
    (hj : P.rel j = LinDiagram.of z' - LinDiagram.of e') (hjdom : P.dom j = y.obj)
    (hz' : Diagram.layers z' = Diagram.layers (P.rightZigzagD x y cup cap)) : x ⊣ y :=
  adjunctionOfZigzag x y cup cap (P.diag_eq_id_of_rel i he hi hidom _ hz)
    (P.diag_eq_id_of_rel j he' hj hjdom _ hz')

@[simp] theorem adjunctionOfRels_unit (x : l ⟶ m) (y : m ⟶ l)
    (cup : Obj.nil l.region ⟶ x.obj.tensor y.obj) (cap : y.obj.tensor x.obj ⟶ Obj.nil m.region)
    (i : P.Rel) {z e : P.dom i ⟶ P.cod i} (he : Diagram.layers e = [])
    (hi : P.rel i = LinDiagram.of z - LinDiagram.of e) (hidom : P.dom i = x.obj)
    (hz : Diagram.layers z = Diagram.layers (P.leftZigzagD x y cup cap))
    (j : P.Rel) {z' e' : P.dom j ⟶ P.cod j} (he' : Diagram.layers e' = [])
    (hj : P.rel j = LinDiagram.of z' - LinDiagram.of e') (hjdom : P.dom j = y.obj)
    (hz' : Diagram.layers z' = Diagram.layers (P.rightZigzagD x y cup cap)) :
    (adjunctionOfRels x y cup cap i he hi hidom hz j he' hj hjdom hz').unit = P.diag cup := rfl

@[simp] theorem adjunctionOfRels_counit (x : l ⟶ m) (y : m ⟶ l)
    (cup : Obj.nil l.region ⟶ x.obj.tensor y.obj) (cap : y.obj.tensor x.obj ⟶ Obj.nil m.region)
    (i : P.Rel) {z e : P.dom i ⟶ P.cod i} (he : Diagram.layers e = [])
    (hi : P.rel i = LinDiagram.of z - LinDiagram.of e) (hidom : P.dom i = x.obj)
    (hz : Diagram.layers z = Diagram.layers (P.leftZigzagD x y cup cap))
    (j : P.Rel) {z' e' : P.dom j ⟶ P.cod j} (he' : Diagram.layers e' = [])
    (hj : P.rel j = LinDiagram.of z' - LinDiagram.of e') (hjdom : P.dom j = y.obj)
    (hz' : Diagram.layers z' = Diagram.layers (P.rightZigzagD x y cup cap)) :
    (adjunctionOfRels x y cup cap i he hi hidom hz j he' hj hjdom hz').counit = P.diag cap := rfl

end Presentation

/-! ## Exact pairings in presented monoidal categories -/

namespace Diagram

variable [Subsingleton S.Region] [Inhabited S.Region] {x y : Obj S}

/-- The left zigzag `(cup ⊗ 1_x) ≫ (1_x ⊗ cap) : x ⟶ x`, for a monoidal signature. -/
def leftZigzagM (cup : Obj.unit ⟶ x.tensor y) (cap : y.tensor x ⟶ Obj.unit) : x ⟶ x :=
  cast (whiskerR cup x ≫ eqToHom (Obj.tensor_assoc x y x) ≫ whiskerL x cap)
    (Obj.unit_tensor x) (Obj.tensor_unit x)

/-- The right zigzag `(1_y ⊗ cup) ≫ (cap ⊗ 1_y) : y ⟶ y`, for a monoidal signature. -/
def rightZigzagM (cup : Obj.unit ⟶ x.tensor y) (cap : y.tensor x ⟶ Obj.unit) : y ⟶ y :=
  cast (whiskerL y cup ≫ eqToHom (Obj.tensor_assoc y x y).symm ≫ whiskerR cap y)
    (Obj.tensor_unit y) (Obj.unit_tensor y)

@[simp] theorem layers_leftZigzagM (cup : Obj.unit ⟶ x.tensor y) (cap : y.tensor x ⟶ Obj.unit) :
    layers (leftZigzagM cup cap) = (layers cup).map (·.wr x.word) ++ (layers cap).map (·.wl x) := by
  simp [leftZigzagM]

@[simp] theorem layers_rightZigzagM (cup : Obj.unit ⟶ x.tensor y) (cap : y.tensor x ⟶ Obj.unit) :
    layers (rightZigzagM cup cap) = (layers cup).map (·.wl y) ++ (layers cap).map (·.wr y.word) := by
  simp [rightZigzagM]

end Diagram

namespace Presentation

open MonoidalCategory

variable {P : Presentation.{w, v} S R} [S.IsEven] [Subsingleton S.Region] [Inhabited S.Region]
  {x y : Obj S}

omit [S.IsEven] in
theorem evaluation_coevaluation_diag (cup : Obj.unit ⟶ x.tensor y) (cap : y.tensor x ⟶ Obj.unit) :
    (P.diag cup : 𝟙_ P.Presented ⟶ P.obj x ⊗ P.obj y) ▷ P.obj x ≫ (MonoidalCategory.associator _ _ _).hom ≫
        P.obj x ◁ (P.diag cap : P.obj y ⊗ P.obj x ⟶ 𝟙_ P.Presented) =
      (λ_ (P.obj x)).hom ≫ P.diag (Diagram.leftZigzagM cup cap) ≫ (ρ_ (P.obj x)).inv := by
  change P.wR (P.diag cup) x ≫ _ ≫ P.wL x (P.diag cap) = _
  simp [wR_diag, wL_diag, associator_eq, leftUnitor_eq, rightUnitor_eq, Diagram.leftZigzagM,
    Diagram.cast_eq, P.diag_eqToHom]

omit [S.IsEven] in
theorem coevaluation_evaluation_diag (cup : Obj.unit ⟶ x.tensor y) (cap : y.tensor x ⟶ Obj.unit) :
    P.obj y ◁ (P.diag cup : 𝟙_ P.Presented ⟶ P.obj x ⊗ P.obj y) ≫ (MonoidalCategory.associator _ _ _).inv ≫
        (P.diag cap : P.obj y ⊗ P.obj x ⟶ 𝟙_ P.Presented) ▷ P.obj y =
      (ρ_ (P.obj y)).hom ≫ P.diag (Diagram.rightZigzagM cup cap) ≫ (λ_ (P.obj y)).inv := by
  change P.wL y (P.diag cup) ≫ _ ≫ P.wR (P.diag cap) y = _
  simp [wR_diag, wL_diag, associator_eq, leftUnitor_eq, rightUnitor_eq, Diagram.rightZigzagM,
    Diagram.cast_eq, P.diag_eqToHom]

variable (P)

/-- The exact pairing between `P.obj x` and `P.obj y` given by a cup and a cap satisfying the two
zigzag identities, for an even monoidal signature. Its coevaluation and evaluation are the classes
of the cup and the cap. -/
def exactPairingOfZigzag (cup : Obj.unit ⟶ x.tensor y) (cap : y.tensor x ⟶ Obj.unit)
    (hl : P.diag (Diagram.leftZigzagM cup cap) = 𝟙 _)
    (hr : P.diag (Diagram.rightZigzagM cup cap) = 𝟙 _) : ExactPairing (P.obj x) (P.obj y) where
  coevaluation' := P.diag cup
  evaluation' := P.diag cap
  coevaluation_evaluation' := by rw [coevaluation_evaluation_diag, hr, Category.id_comp]
  evaluation_coevaluation' := by rw [evaluation_coevaluation_diag, hl, Category.id_comp]

theorem exactPairingOfZigzag_coevaluation (cup : Obj.unit ⟶ x.tensor y)
    (cap : y.tensor x ⟶ Obj.unit) (hl : P.diag (Diagram.leftZigzagM cup cap) = 𝟙 _)
    (hr : P.diag (Diagram.rightZigzagM cup cap) = 𝟙 _) :
    @ExactPairing.coevaluation _ _ _ _ _ (P.exactPairingOfZigzag cup cap hl hr) = P.diag cup :=
  rfl

theorem exactPairingOfZigzag_evaluation (cup : Obj.unit ⟶ x.tensor y)
    (cap : y.tensor x ⟶ Obj.unit) (hl : P.diag (Diagram.leftZigzagM cup cap) = 𝟙 _)
    (hr : P.diag (Diagram.rightZigzagM cup cap) = 𝟙 _) :
    @ExactPairing.evaluation _ _ _ _ _ (P.exactPairingOfZigzag cup cap hl hr) = P.diag cap :=
  rfl

/-- The exact pairing between `P.obj x` and `P.obj y` given by a cup and a cap whose zigzag
identities are relations `i` and `j` of `P` of the form `z - e`, with `e` without layers and `z`
with the layers of the zigzag diagram. -/
def exactPairingOfRels (cup : Obj.unit ⟶ x.tensor y) (cap : y.tensor x ⟶ Obj.unit)
    (i : P.Rel) {z e : P.dom i ⟶ P.cod i} (he : Diagram.layers e = [])
    (hi : P.rel i = LinDiagram.of z - LinDiagram.of e) (hidom : P.dom i = x)
    (hz : Diagram.layers z = Diagram.layers (Diagram.leftZigzagM cup cap))
    (j : P.Rel) {z' e' : P.dom j ⟶ P.cod j} (he' : Diagram.layers e' = [])
    (hj : P.rel j = LinDiagram.of z' - LinDiagram.of e') (hjdom : P.dom j = y)
    (hz' : Diagram.layers z' = Diagram.layers (Diagram.rightZigzagM cup cap)) :
    ExactPairing (P.obj x) (P.obj y) :=
  P.exactPairingOfZigzag cup cap (P.diag_eq_id_of_rel i he hi hidom _ hz)
    (P.diag_eq_id_of_rel j he' hj hjdom _ hz')

end Presentation

end StringDiagrams
