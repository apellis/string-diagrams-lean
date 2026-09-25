import StringDiagrams.Presentation

/-!
# Interpretations and soundness

An *interpretation* of the free 2-category on a signature `S` in a category `D` assigns an
object of `D` to every object and a morphism to every well-formed layer
(`StringDiagrams.Interpretation`); it extends uniquely to a functor
(`Interpretation.functor`), computed on a diagram by composing the images of its layers.

If `D` is `R`-linear, such a functor extends linearly to linear combinations of diagrams
(`StringDiagrams.freeLift`, a universe-polymorphic version of `CategoryTheory.Free.lift`),
and it descends to the presented category of a presentation `P` as soon as it kills every
whiskered relation and every whiskered instance of the interchange law
(`Presentation.lift`, soundness). The descended functor is `R`-linear
(`Presentation.lift_linear`) and sends the class of a diagram to its image
(`Presentation.lift_diag`).

Faithfulness of an interpretation is a separate question, not addressed here.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory

universe w v u₀ u₁ u₂ w₁ w₂

variable {S : Signature.{u₀, u₁, u₂}}

/-! ## Interpretations by layers -/

/-- An interpretation of the free 2-category on `S` in a category `D`: images of objects and
of well-formed layers. -/
structure Interpretation (S : Signature.{u₀, u₁, u₂}) (D : Type w₁) [Category.{w₂} D] where
  /-- Image of an object. -/
  obj : Obj S → D
  /-- Image of a well-formed layer. -/
  layer : (L : Layer S) → L.Valid → (obj L.dom ⟶ obj L.cod)

namespace Interpretation

variable {D : Type w₁} [Category.{w₂} D] (I : Interpretation S D)

/-- The image of a chain of layers. -/
def mapChain : (a : Obj S) → (ls : List (Layer S)) → (b : Obj S) → Chain a ls b →
    (I.obj a ⟶ I.obj b)
  | _, [], _, h => eqToHom (congrArg I.obj h)
  | _, L :: ls, b, h => eqToHom (congrArg I.obj h.2.1.symm) ≫ I.layer L h.1 ≫
      mapChain L.cod ls b h.2.2

theorem mapChain_append {a b c : Obj S} {ls ms : List (Layer S)} (h₁ : Chain a ls b)
    (h₂ : Chain b ms c) :
    I.mapChain a (ls ++ ms) c (h₁.append h₂) = I.mapChain a ls b h₁ ≫ I.mapChain b ms c h₂ := by
  induction ls generalizing a with
  | nil => cases h₁; simp [mapChain]
  | cons L ls ih => simp only [List.cons_append, mapChain, Category.assoc, ← ih]

/-- The functor determined by an interpretation. -/
def functor : Obj S ⥤ D where
  obj := I.obj
  map f := I.mapChain _ (Diagram.layers f) _ (Diagram.chain f)
  map_id _ := by simp [mapChain]
  map_comp f g := I.mapChain_append (Diagram.chain f) (Diagram.chain g)

@[simp] theorem functor_obj (a : Obj S) : I.functor.obj a = I.obj a := rfl

theorem functor_map (f : a ⟶ b) :
    I.functor.map f = I.mapChain a (Diagram.layers f) b (Diagram.chain f) := rfl

@[simp] theorem functor_map_layer (L : Layer S) (hv : L.Valid) {a b : Obj S} (ha : L.dom = a)
    (hb : L.cod = b) :
    I.functor.map (Diagram.layer L hv ha hb) =
      eqToHom (congrArg I.obj ha.symm) ≫ I.layer L hv ≫ eqToHom (congrArg I.obj hb) := rfl

theorem functor_map_ofLayer (L : Layer S) (hv : L.Valid) :
    I.functor.map (Diagram.ofLayer L hv) = I.layer L hv := by
  show eqToHom (congrArg I.obj rfl) ≫ I.layer L hv ≫ eqToHom (congrArg I.obj rfl) = _
  simp

/-- The image of a diagram given by an explicit list of layers. -/
theorem functor_map_mk_cons {a b : Obj S} (L : Layer S) (ls : List (Layer S))
    (h : Chain a (L :: ls) b) :
    I.functor.map (Diagram.mk (L :: ls) h) =
      eqToHom (congrArg I.obj h.2.1.symm) ≫ I.layer L h.1 ≫
        I.functor.map (Diagram.mk ls h.2.2) := rfl

theorem functor_map_mk_nil {a b : Obj S} (h : Chain a [] b) :
    I.functor.map (Diagram.mk [] h) = eqToHom (congrArg I.obj h) := rfl

end Interpretation

/-! ## Linear extension and descent -/

section Linear

variable (R : Type w) [CommRing R] {D : Type w₁} [Category.{w₂} D] [Preadditive D] [Linear R D]

open Preadditive Linear

/-- The `R`-linear extension of a functor out of the free 2-category. -/
@[simps]
def freeLift (F : Obj S ⥤ D) : Free R (Obj S) ⥤ D where
  obj a := F.obj a
  map {_ _} f := f.sum fun f' r => r • F.map f'
  map_id := by dsimp [CategoryTheory.categoryFree]; simp
  map_comp {X Y Z} f g := by
    induction f using Finsupp.induction_linear with
    | zero => simp
    | add f₁ f₂ w₁ w₂ =>
      rw [add_comp]
      rw [Finsupp.sum_add_index', Finsupp.sum_add_index']
      · simp only [w₁, w₂, add_comp]
      · intros; rw [zero_smul]
      · intros; simp only [add_smul]
      · intros; rw [zero_smul]
      · intros; simp only [add_smul]
    | single f' r =>
      induction g using Finsupp.induction_linear with
      | zero => simp
      | add f₁ f₂ w₁ w₂ =>
        rw [comp_add]
        rw [Finsupp.sum_add_index', Finsupp.sum_add_index']
        · simp only [w₁, w₂, comp_add]
        · intros; rw [zero_smul]
        · intros; simp only [add_smul]
        · intros; rw [zero_smul]
        · intros; simp only [add_smul]
      | single g' s =>
        rw [Free.single_comp_single _ _ f' g' r s]
        simp [mul_comm r s, mul_smul]

variable {R}

theorem freeLift_map_single (F : Obj S ⥤ D) {a b : Obj S} (f : a ⟶ b) (r : R) :
    (freeLift R F).map (Finsupp.single f r : LinDiagram R a b) = r • F.map f := by simp

@[simp] theorem freeLift_map_of (F : Obj S ⥤ D) {a b : Obj S} (f : a ⟶ b) :
    (freeLift R F).map (LinDiagram.of f : LinDiagram R a b) = F.map f := by simp

instance freeLift_additive (F : Obj S ⥤ D) : (freeLift R F).Additive where
  map_add {X Y} f g := by
    dsimp
    rw [Finsupp.sum_add_index'] <;> simp [add_smul]

instance freeLift_linear (F : Obj S ⥤ D) : (freeLift R F).Linear R where
  map_smul {X Y} f r := by
    dsimp
    rw [Finsupp.sum_smul_index] <;> simp [Finsupp.smul_sum, mul_smul]

namespace Presentation

variable (P : Presentation.{w, v} S R) (F : Obj S ⥤ D)

/-- The hypotheses of soundness: `F` kills every whiskered relation of `P` and every
whiskered instance of the interchange law. -/
structure Respects : Prop where
  rel : ∀ (i : P.Rel) (u : Obj S) (v : List S.Colour) (hw : (P.dom i).WhiskerOK u v),
    (freeLift R F).map (LinDiagram.whisker (P.rel i) u v hw) = 0
  interchange : ∀ (x : InterchangeData S) (hx : x.Valid) (u : Obj S) (v : List S.Colour)
    (hw : x.dom.WhiskerOK u v),
    (freeLift R F).map (LinDiagram.whisker (InterchangeData.rel R hx) u v hw) = 0

variable {P F}

theorem Respects.allRel (hF : P.Respects F) (k : P.AllRel) (u : Obj S) (v : List S.Colour)
    (hw : k.dom.WhiskerOK u v) : (freeLift R F).map (LinDiagram.whisker k.rel u v hw) = 0 := by
  cases k with
  | user i => exact hF.rel i u v hw
  | interchange x hx => exact hF.interchange x hx u v hw

theorem Respects.map_eq_zero (hF : P.Respects F) {a b : Obj S} {f : LinDiagram R a b}
    (hf : f ∈ P.ideal a b) : (freeLift R F).map f = 0 := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, u, v, hw, pre, post⟩ := hx
    rw [Functor.map_comp, Functor.map_comp, hF.allRel k u v hw, Limits.zero_comp, Limits.comp_zero]
  | zero => exact Functor.map_zero _ _ _
  | add x y _ _ hx hy => rw [Functor.map_add, hx, hy, add_zero]
  | smul r x _ hx => rw [Functor.map_smul, hx, smul_zero]

/-- Soundness: a functor out of the free 2-category that respects the relations and the
interchange law descends to the presented category. -/
def lift (hF : P.Respects F) : P.Presented ⥤ D :=
  CategoryTheory.Quotient.lift P.homRel (freeLift R F) fun _ _ f₁ f₂ h => by
    rw [← sub_eq_zero, ← Functor.map_sub]; exact hF.map_eq_zero h

@[simp] theorem lift_obj (hF : P.Respects F) (a : Obj S) : (P.lift hF).obj (P.obj a) = F.obj a :=
  rfl

@[simp] theorem lift_lin (hF : P.Respects F) {a b : Obj S} (f : LinDiagram R a b) :
    (P.lift hF).map (P.lin f) = (freeLift R F).map f := rfl

@[simp] theorem lift_diag (hF : P.Respects F) {a b : Obj S} (f : a ⟶ b) :
    (P.lift hF).map (P.diag f) = F.map f := by
  rw [diag, lift_lin, freeLift_map_of]

instance lift_additive (hF : P.Respects F) : (P.lift hF).Additive where
  map_add {X Y} f g := by
    obtain ⟨f, rfl⟩ := P.linFunctor.map_surjective f
    obtain ⟨g, rfl⟩ := P.linFunctor.map_surjective g
    rw [← Functor.map_add]
    exact (freeLift R F).map_add

instance lift_linear (hF : P.Respects F) : (P.lift hF).Linear R where
  map_smul {X Y} f r := by
    obtain ⟨f, rfl⟩ := P.linFunctor.map_surjective f
    rw [← Functor.map_smul]
    exact (freeLift R F).map_smul r f

end Presentation

end Linear

end StringDiagrams

end
