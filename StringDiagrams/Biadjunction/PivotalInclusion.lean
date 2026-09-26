import StringDiagrams.Biadjunction.NestedCups
import StringDiagrams.Interpretation

/-!
# The inclusion of a presented category into its pivotal extension

Let `P` be a presentation of a signature `S` with a duality `D` on its colours, and let `Q` be a
presentation of the pivotal extension `S.pivotal D` in which the relations of `P` hold, i.e. the
images `(P.rel i).toPivotal D` of the relations of `P` have class zero (`ContainsRels`). This is the
case for the pivotal extension `P.pivotal D` itself (`pivotal_containsRels`), for any extension of
it by further relations (`addRels_pivotal_containsRels`), and for the cyclic pivotal extension
(`pivotalCyclic_containsRels`).

The inclusion of diagrams `Diagram.toPivotal` (every generator `g` goes to `.gen g`) is a functor
of free 2-categories (`Diagram.toPivotalFunctor`), which respects the relations of `P` and the
interchange law. By soundness (`Presentation.lift`) it descends to an `R`-linear functor
`Presentation.toPivotalLift : P.Presented ⥤ Q.Presented` sending the class of a diagram `d` to the
class of `d.toPivotal D` (`toPivotalLift_diag`), in particular a generator to the corresponding
generator of the pivotal extension (`toPivotalLift_genDiag`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory

universe w v v' u₀ u₁ u₂

variable {S : Signature.{u₀, u₁, u₂}} (D : S.ColourDuality)

/-! ## The inclusion of diagrams -/

theorem Obj.WhiskerOK.toPivotal {a u : Obj S} {v : List S.Colour} (h : a.WhiskerOK u v) :
    (a.toPivotal D).WhiskerOK (u.toPivotal D) v :=
  ⟨(Signature.pivotal_ok D _ _).2 h.1, (Signature.pivotal_endR D _ _).trans h.2.1, by
    show (S.pivotal D).ok ((S.pivotal D).endR a.start a.word) v
    rw [Signature.pivotal_endR, Signature.pivotal_ok]
    exact h.2.2⟩

@[simp] theorem Diagram.layers_toPivotal {a b : Obj S} (d : a ⟶ b) :
    Diagram.layers (Diagram.toPivotal D d) = (Diagram.layers d).map (Layer.toPivotal D) := rfl

/-- The inclusion of diagrams of `S` into the pivotal extension, as a functor of free
2-categories. -/
@[simps]
def Diagram.toPivotalFunctor : Obj S ⥤ Obj (S.pivotal D) where
  obj := Obj.toPivotal D
  map := Diagram.toPivotal D
  map_id _ := rfl
  map_comp _ _ := Diagram.ext List.map_append

theorem Diagram.toPivotal_whisker {a b : Obj S} (d : a ⟶ b) (u : Obj S) (v : List S.Colour)
    (hw : a.WhiskerOK u v) :
    Diagram.toPivotal D (Diagram.whisker d u v hw) =
      Diagram.whisker (Diagram.toPivotal D d) (u.toPivotal D) v (hw.toPivotal D) :=
  Diagram.ext (by simp only [Diagram.layers_toPivotal, Diagram.layers_whisker, List.map_map]; rfl)

theorem LinDiagram.toPivotal_whisker {R : Type w} [CommRing R] {a b : Obj S}
    (f : LinDiagram R a b) (u : Obj S) (v : List S.Colour) (hw : a.WhiskerOK u v) :
    (LinDiagram.whisker f u v hw).toPivotal D =
      LinDiagram.whisker (f.toPivotal D) (u.toPivotal D) v (hw.toPivotal D) := by
  unfold LinDiagram.toPivotal LinDiagram.whisker
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  congr 1
  funext d
  exact Diagram.toPivotal_whisker D d u v hw

/-- An instance of the interchange law of `S`, as one of the pivotal extension. -/
def InterchangeData.toPivotal (x : InterchangeData S) : InterchangeData (S.pivotal D) :=
  ⟨x.start, .gen x.g, x.mid, .gen x.h⟩

theorem InterchangeData.Valid.toPivotal {x : InterchangeData S} (hx : x.Valid) :
    (x.toPivotal D).Valid :=
  ⟨hx.gh₁.toPivotal, hx.gh₂.toPivotal, hx.hg₁.toPivotal, hx.hg₂.toPivotal⟩

section LinToPivotal

variable {R : Type w} [CommRing R] {a b : Obj S}

theorem LinDiagram.toPivotal_sub (f g : LinDiagram R a b) :
    (f - g).toPivotal D = f.toPivotal D - g.toPivotal D :=
  (Finsupp.lmapDomain R R (Diagram.toPivotal D (a := a) (b := b))).map_sub f g

theorem LinDiagram.toPivotal_smul (r : R) (f : LinDiagram R a b) :
    (r • f).toPivotal D = r • f.toPivotal D :=
  Finsupp.mapDomain_smul _ _

theorem LinDiagram.toPivotal_of (d : a ⟶ b) :
    (LinDiagram.of d : LinDiagram R a b).toPivotal D = LinDiagram.of (Diagram.toPivotal D d) :=
  Finsupp.mapDomain_single

end LinToPivotal

theorem InterchangeData.toPivotal_rel {R : Type w} [CommRing R] {x : InterchangeData S}
    (hx : x.Valid) :
    (InterchangeData.rel R hx).toPivotal D = InterchangeData.rel R (hx.toPivotal D) := by
  unfold InterchangeData.rel
  rw [LinDiagram.toPivotal_sub, LinDiagram.toPivotal_smul, LinDiagram.toPivotal_of,
    LinDiagram.toPivotal_of]
  rfl

/-! ## The inclusion functor -/

namespace Presentation

variable {R : Type w} [CommRing R]

/-- The class of diagrams, as a functor out of the free 2-category. -/
@[simps]
def diagFunctor {S' : Signature.{u₀, u₁, u₂}} (Q : Presentation.{w, v} S' R) :
    Obj S' ⥤ Q.Presented where
  obj := Q.obj
  map := Q.diag
  map_id := Q.diag_id
  map_comp := Q.diag_comp

variable (P : Presentation.{w, v} S R) (Q : Presentation.{w, v'} (S.pivotal D) R)

/-- The relations of `P`, included in the pivotal extension, hold in `Q`. -/
def ContainsRels : Prop := ∀ i : P.Rel, Q.lin ((P.rel i).toPivotal D) = 0

theorem lin_whisker_eq_zero {S' : Signature.{u₀, u₁, u₂}} (Q : Presentation.{w, v'} S' R)
    {a b : Obj S'} {f : LinDiagram R a b} (hf : Q.lin f = 0) (u : Obj S') (v : List S'.Colour)
    (hw : a.WhiskerOK u v) : Q.lin (LinDiagram.whisker f u v hw) = 0 := by
  rw [← LinDiagram.whisk_of_ok f hw, ← whisk_lin, hf, whisk_zero]

theorem freeLift_toPivotal_map {a b : Obj S} (f : LinDiagram R a b) :
    (freeLift R (Diagram.toPivotalFunctor D ⋙ Q.diagFunctor)).map f = Q.lin (f.toPivotal D) := by
  induction f using Finsupp.induction_linear with
  | zero => simp [LinDiagram.toPivotal]
  | add f g hf hg =>
    rw [Functor.map_add, hf, hg, LinDiagram.toPivotal, LinDiagram.toPivotal,
      LinDiagram.toPivotal, Finsupp.mapDomain_add, lin_add]
  | single d r =>
    rw [freeLift_map_single, LinDiagram.toPivotal, Finsupp.mapDomain_single, lin_single]
    rfl

variable {P Q D}

theorem respects_toPivotal (hQ : P.ContainsRels D Q) :
    P.Respects (Diagram.toPivotalFunctor D ⋙ Q.diagFunctor) where
  rel i u v hw := by
    rw [freeLift_toPivotal_map, LinDiagram.toPivotal_whisker]
    exact Q.lin_whisker_eq_zero (hQ i) _ _ _
  interchange x hx u v hw := by
    rw [freeLift_toPivotal_map, LinDiagram.toPivotal_whisker]
    have h := Q.lin_interchange (x.toPivotal D) (hx.toPivotal D) (u.toPivotal D) v
      (hw.toPivotal D)
    rw [← InterchangeData.toPivotal_rel] at h
    exact h

variable (P Q D)

/-- **The inclusion functor** `P.Presented ⥤ Q.Presented` into a presentation `Q` of the pivotal
extension in which the relations of `P` hold (for example `P.pivotal D`, or any extension of it by
further relations): the class of a diagram `d` goes to the class of `d.toPivotal D`. -/
def toPivotalLift (hQ : P.ContainsRels D Q) : P.Presented ⥤ Q.Presented :=
  P.lift (respects_toPivotal hQ)

variable {P Q D}

instance toPivotalLift_linear (hQ : P.ContainsRels D Q) : (P.toPivotalLift D Q hQ).Linear R :=
  P.lift_linear _

instance toPivotalLift_additive (hQ : P.ContainsRels D Q) : (P.toPivotalLift D Q hQ).Additive :=
  P.lift_additive _

@[simp] theorem toPivotalLift_obj (hQ : P.ContainsRels D Q) (a : Obj S) :
    (P.toPivotalLift D Q hQ).obj (P.obj a) = Q.obj (a.toPivotal D) := rfl

@[simp] theorem toPivotalLift_diag (hQ : P.ContainsRels D Q) {a b : Obj S} (d : a ⟶ b) :
    (P.toPivotalLift D Q hQ).map (P.diag d) = Q.diag (Diagram.toPivotal D d) :=
  P.lift_diag _ d

theorem toPivotalLift_lin (hQ : P.ContainsRels D Q) {a b : Obj S} (f : LinDiagram R a b) :
    (P.toPivotalLift D Q hQ).map (P.lin f) = Q.lin (f.toPivotal D) :=
  (P.lift_lin _ f).trans (freeLift_toPivotal_map D Q f)

/-- A single layer goes to the same layer, with the generator `g` replaced by `.gen g`. -/
theorem toPivotalLift_layer (hQ : P.ContainsRels D Q) (L : Layer S) (hv : L.Valid) :
    (P.toPivotalLift D Q hQ).map (P.diag (Diagram.ofLayer L hv)) =
      Q.diag (Diagram.ofLayer (L.toPivotal D) hv.toPivotal) :=
  toPivotalLift_diag hQ _

/-- A generator goes to the corresponding generator `.gen g` of the pivotal extension. -/
theorem toPivotalLift_genDiag [S.IsEven] (hQ : P.ContainsRels D Q) (g : S.Gen)
    (hg : S.GenValid g) (hg' : (S.pivotal D).GenValid (.gen g)) :
    (P.toPivotalLift D Q hQ).map (P.diag (genDiag g hg)) =
      Q.diag (genDiag (S := S.pivotal D) (.gen g) hg') :=
  (toPivotalLift_diag hQ _).trans (Q.diag_eq_of_layers_eq rfl)

/-! ### Presentations containing the relations of `P` -/

variable (P D)

theorem pivotal_containsRels : P.ContainsRels D (P.pivotal D) :=
  fun i => (P.pivotal D).lin_rel_self (Sum.inl i)

theorem addRels_pivotal_containsRels (ι : Type (max u₁ v)) (dom cod : ι → Obj (S.pivotal D))
    (rel : ∀ i, LinDiagram R (dom i) (cod i)) :
    P.ContainsRels D ((P.pivotal D).addRels ι dom cod rel) :=
  fun i => ((P.pivotal D).addRels ι dom cod rel).lin_rel_self (Sum.inl (Sum.inl i))

theorem pivotalCyclic_containsRels [S.IsEven] (E : S.ColourInvolution) :
    P.ContainsRels E.toColourDuality (P.pivotalCyclic E) :=
  fun i => (P.pivotalCyclic E).lin_rel_self (Sum.inl (Sum.inl i))

/-- The inclusion functor into the pivotal extension. -/
abbrev toPivotalExtension : P.Presented ⥤ (P.pivotal D).Presented :=
  P.toPivotalLift D (P.pivotal D) (P.pivotal_containsRels D)

end Presentation

end StringDiagrams
