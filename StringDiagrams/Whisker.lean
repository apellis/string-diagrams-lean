import StringDiagrams.Presentation

/-!
# Whiskering in presented 2-categories

Whiskering `f ↦ u ⊗ f ⊗ v` by an object `u` on the left and a word `v` on the right
descends to the presented category of any presentation (`Presentation.whisk`), because the
tensor ideal is closed under whiskering. It is `R`-linear, compatible with composition and
identities, sends the class of a diagram to the class of the whiskered diagram, and
whiskering twice is whiskering once by the composite objects.

Whiskering is only meaningful when the regions match (`Obj.WhiskerOK`); to keep the
operations total, `LinDiagram.whisk` and `Presentation.whisk` are defined to be `0` when
the source object cannot be whiskered. For monoidal signatures (`Region` a subsingleton)
this never happens.

## Main definitions and results

* `Obj.tensor`: horizontal composite of objects; `Obj.whisker_whisker`.
* `LinDiagram.whisk`: total whiskering of linear combinations of diagrams;
  `LinDiagram.whisk_comp` (functoriality, unconditional).
* `Presentation.whisk_mem_ideal`: the tensor ideal is closed under whiskering.
* `Presentation.whisk` with `whisk_lin`, `whisk_diag`, `whisk_comp`, `whisk_id`,
  `whisk_add`, `whisk_smul`, `whisk_whisk`.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory

universe w v u₀ u₁ u₂

variable {S : Signature.{u₀, u₁, u₂}}

/-! ## Objects, layers and diagrams -/

namespace Obj

/-- Horizontal composite `u ⊗ u'` of objects (the start of `u` is kept). -/
def tensor (u u' : Obj S) : Obj S := ⟨u.start, u.word ++ u'.word⟩

@[simp] theorem tensor_start (u u' : Obj S) : (u.tensor u').start = u.start := rfl
@[simp] theorem tensor_word (u u' : Obj S) : (u.tensor u').word = u.word ++ u'.word := rfl

theorem whisker_whisker (a u' u : Obj S) (v' v : List S.Colour) :
    (a.whisker u' v').whisker u v = a.whisker (u.tensor u') (v' ++ v) := by
  ext <;> simp [whisker, tensor, List.append_assoc]

theorem WhiskerOK.trans {a u' u : Obj S} {v' v : List S.Colour} (h' : a.WhiskerOK u' v')
    (h : (a.whisker u' v').WhiskerOK u v) : a.WhiskerOK (u.tensor u') (v' ++ v) := by
  obtain ⟨hu', hue', hv'⟩ := h'
  obtain ⟨hu, hue, hv⟩ := h
  have hue₀ : S.endR u.start u.word = u'.start := hue
  have hue'₀ : S.endR u'.start u'.word = a.start := hue'
  have hend : (a.whisker u' v').endR = S.endR a.endR v' := by
    simp [endR, whisker, hue'₀]
  refine ⟨?_, ?_, ?_⟩
  · simp only [tensor, Signature.ok_append, hue₀]; exact ⟨hu, hu'⟩
  · simp [endR, tensor, hue₀, hue'₀]
  · rw [Signature.ok_append]; exact ⟨hv', hend ▸ hv⟩

end Obj

theorem Layer.whisker_whisker (L : Layer S) (u' u : Obj S) (v' v : List S.Colour) :
    (L.whisker u' v').whisker u v = L.whisker (u.tensor u') (v' ++ v) := by
  simp [Layer.whisker, Obj.tensor, List.append_assoc]

namespace Diagram

variable {a b : Obj S}

theorem whisker_whisker (f : a ⟶ b) (u' u : Obj S) (v' v : List S.Colour)
    (h' : a.WhiskerOK u' v') (h : (a.whisker u' v').WhiskerOK u v) :
    whisker (whisker f u' v' h') u v h =
      cast (whisker f (u.tensor u') (v' ++ v) (h'.trans h)) (Obj.whisker_whisker _ _ _ _ _).symm
        (Obj.whisker_whisker _ _ _ _ _).symm := by
  ext; simp [Function.comp_def, Layer.whisker_whisker]

theorem whisker_cast {a' b' : Obj S} (f : a ⟶ b) (ha : a = a') (hb : b = b') (u : Obj S)
    (v : List S.Colour) (hw : a'.WhiskerOK u v) :
    whisker (cast f ha hb) u v hw =
      cast (whisker f u v (ha ▸ hw)) (by rw [ha]) (by rw [hb]) := by
  ext; simp

end Diagram

/-! ## Linear combinations -/

namespace LinDiagram

variable {R : Type w} [CommRing R] {a b c : Obj S}

open Classical in
/-- Total whiskering of linear combinations of diagrams: `whisker` when the source object can
be whiskered by `u` and `v`, and `0` otherwise. -/
def whisk (f : LinDiagram R a b) (u : Obj S) (v : List S.Colour) :
    LinDiagram R (a.whisker u v) (b.whisker u v) :=
  if h : a.WhiskerOK u v then whisker f u v h else 0

theorem whisk_of_ok (f : LinDiagram R a b) {u : Obj S} {v : List S.Colour}
    (h : a.WhiskerOK u v) : whisk f u v = whisker f u v h := dif_pos h

theorem whisk_of_not_ok (f : LinDiagram R a b) {u : Obj S} {v : List S.Colour}
    (h : ¬ a.WhiskerOK u v) : whisk f u v = 0 := dif_neg h

theorem whisk_add (f g : LinDiagram R a b) (u : Obj S) (v : List S.Colour) :
    whisk (f + g) u v = whisk f u v + whisk g u v := by
  by_cases h : a.WhiskerOK u v
  · simp only [whisk_of_ok _ h, whisker_add]
  · simp only [whisk_of_not_ok _ h, add_zero]

theorem whisk_smul (r : R) (f : LinDiagram R a b) (u : Obj S) (v : List S.Colour) :
    whisk (r • f) u v = r • whisk f u v := by
  by_cases h : a.WhiskerOK u v
  · simp only [whisk_of_ok _ h, whisker_smul]
  · simp only [whisk_of_not_ok _ h, smul_zero]

theorem whisk_sub (f g : LinDiagram R a b) (u : Obj S) (v : List S.Colour) :
    whisk (f - g) u v = whisk f u v - whisk g u v := by
  by_cases h : a.WhiskerOK u v
  · simp only [whisk_of_ok _ h, whisker_sub]
  · simp only [whisk_of_not_ok _ h, sub_zero]

theorem whisk_zero (u : Obj S) (v : List S.Colour) : whisk (0 : LinDiagram R a b) u v = 0 := by
  simpa using whisk_smul (0 : R) (0 : LinDiagram R a b) u v

/-- A nonzero linear combination of diagrams from `a` to `b` transfers whiskerability from
`a` to `b`. -/
theorem whiskerOK_of_ne_zero {f : LinDiagram R a b} (hf : f ≠ 0) {u : Obj S}
    {v : List S.Colour} (h : a.WhiskerOK u v) : b.WhiskerOK u v := by
  obtain ⟨d, -⟩ := Finsupp.ne_iff.mp hf
  exact (Diagram.chain d).whiskerOK h

theorem whisker_comp (f : LinDiagram R a b) (g : LinDiagram R b c) (u : Obj S)
    (v : List S.Colour) (ha : a.WhiskerOK u v) (hb : b.WhiskerOK u v) :
    whisker (f ≫ g) u v ha = whisker f u v ha ≫ whisker g u v hb := by
  induction f using Finsupp.induction_linear with
  | zero => simp [whisker, Finsupp.mapDomain_zero]
  | add f₁ f₂ h₁ h₂ => rw [Preadditive.add_comp, whisker_add, h₁, h₂, whisker_add,
      Preadditive.add_comp]
  | single d r =>
    induction g using Finsupp.induction_linear with
    | zero => simp [whisker, Finsupp.mapDomain_zero]
    | add g₁ g₂ h₁ h₂ => rw [Preadditive.comp_add, whisker_add, h₁, h₂, whisker_add,
        Preadditive.comp_add]
    | single e s =>
      have h₁ := Free.single_comp_single R (Obj S) d e r s
      have h₂ := Free.single_comp_single R (Obj S) (Diagram.whisker d u v ha)
        (Diagram.whisker e u v hb) r s
      erw [h₁, whisker_single, whisker_single, whisker_single, h₂, Diagram.whisker_comp]

theorem whisk_comp (f : LinDiagram R a b) (g : LinDiagram R b c) (u : Obj S)
    (v : List S.Colour) : whisk (f ≫ g) u v = whisk f u v ≫ whisk g u v := by
  by_cases ha : a.WhiskerOK u v
  · by_cases hf : f = 0
    · subst hf; simp [whisk_zero]
    · have hb := whiskerOK_of_ne_zero hf ha
      rw [whisk_of_ok _ ha, whisk_of_ok _ ha, whisk_of_ok _ hb, whisker_comp _ _ _ _ ha hb]
  · rw [whisk_of_not_ok _ ha, whisk_of_not_ok _ ha, Limits.zero_comp]

theorem whisk_id (a : Obj S) (u : Obj S) (v : List S.Colour) (h : a.WhiskerOK u v) :
    whisk (𝟙 (Free.of R a)) u v = 𝟙 (Free.of R (a.whisker u v)) := by
  rw [whisk_of_ok _ h]
  exact whisker_single _ _ _ _ _

theorem cast_eq_comp {a' b' : Obj S} (f : LinDiagram R a b) (ha : a = a') (hb : b = b') :
    cast f ha hb = eqToHom (by rw [ha]) ≫ f ≫ eqToHom (by rw [hb]) := by
  subst ha hb; simp

theorem whisker_whisker (f : LinDiagram R a b) (u' u : Obj S) (v' v : List S.Colour)
    (h' : a.WhiskerOK u' v') (h : (a.whisker u' v').WhiskerOK u v) :
    whisker (whisker f u' v' h') u v h =
      cast (whisker f (u.tensor u') (v' ++ v) (h'.trans h)) (Obj.whisker_whisker _ _ _ _ _).symm
        (Obj.whisker_whisker _ _ _ _ _).symm := by
  simp only [whisker, cast, ← Finsupp.mapDomain_comp]
  congr 1
  funext d
  exact Diagram.whisker_whisker d u' u v' v h' h

end LinDiagram

/-! ## The presented category -/

namespace Presentation

variable {R : Type w} [CommRing R] (P : Presentation.{w, v} S R)

theorem whisk_mem_ideal {a b : Obj S} {f : LinDiagram R a b} (hf : f ∈ P.ideal a b)
    (u : Obj S) (v : List S.Colour) : LinDiagram.whisk f u v ∈ P.ideal _ _ := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, u', v', hw', pre, post⟩ := hx
    rw [LinDiagram.whisk_comp, LinDiagram.whisk_comp]
    by_cases hk : (k.dom.whisker u' v').WhiskerOK u v
    · rw [LinDiagram.whisk_of_ok _ hk, LinDiagram.whisker_whisker _ _ _ _ _ hw' hk,
        LinDiagram.cast_eq_comp]
      apply Submodule.subset_span
      have := IdealGen.intro (P := P) k (u.tensor u') (v' ++ v) (hw'.trans hk)
        (LinDiagram.whisk pre u v ≫ eqToHom (by rw [Obj.whisker_whisker]))
        (eqToHom (by rw [Obj.whisker_whisker]) ≫ LinDiagram.whisk post u v)
      simpa only [Category.assoc] using this
    · rw [LinDiagram.whisk_of_not_ok _ hk, Limits.zero_comp, Limits.comp_zero]
      exact Submodule.zero_mem _
  | zero => rw [LinDiagram.whisk_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [LinDiagram.whisk_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [LinDiagram.whisk_smul]; exact Submodule.smul_mem _ r hx

/-- Whiskering `u ⊗ f ⊗ v` in the presented category (`0` if `a` cannot be whiskered). -/
def whisk {a b : Obj S} (f : P.obj a ⟶ P.obj b) (u : Obj S) (v : List S.Colour) :
    P.obj (a.whisker u v) ⟶ P.obj (b.whisker u v) :=
  Quot.lift (fun g : LinDiagram R a b => P.lin (LinDiagram.whisk g u v))
    (fun g₁ g₂ h => by
      have h' : P.homRel g₁ g₂ := by
        rwa [CategoryTheory.Quotient.compClosure_eq_self] at h
      rw [lin_eq_iff, ← LinDiagram.whisk_sub]
      exact P.whisk_mem_ideal h' u v) f

@[simp] theorem whisk_lin {a b : Obj S} (f : LinDiagram R a b) (u : Obj S) (v : List S.Colour) :
    P.whisk (P.lin f) u v = P.lin (LinDiagram.whisk f u v) := rfl

theorem whisk_diag {a b : Obj S} (f : a ⟶ b) (u : Obj S) (v : List S.Colour)
    (h : a.WhiskerOK u v) : P.whisk (P.diag f) u v = P.diag (Diagram.whisker f u v h) := by
  rw [diag, whisk_lin, LinDiagram.whisk_of_ok _ h, LinDiagram.whisker_of, lin_of]

theorem lin_surjective {a b : Obj S} (f : P.obj a ⟶ P.obj b) : ∃ g, P.lin g = f :=
  P.linFunctor.map_surjective f

theorem whisk_comp {a b c : Obj S} (f : P.obj a ⟶ P.obj b) (g : P.obj b ⟶ P.obj c) (u : Obj S)
    (v : List S.Colour) : P.whisk (f ≫ g) u v = P.whisk f u v ≫ P.whisk g u v := by
  obtain ⟨f, rfl⟩ := P.lin_surjective f
  obtain ⟨g, rfl⟩ := P.lin_surjective g
  rw [← lin_comp, whisk_lin, whisk_lin, whisk_lin, LinDiagram.whisk_comp, lin_comp]

theorem whisk_id (a : Obj S) (u : Obj S) (v : List S.Colour) (h : a.WhiskerOK u v) :
    P.whisk (𝟙 (P.obj a)) u v = 𝟙 _ := by
  rw [← lin_id, whisk_lin, LinDiagram.whisk_id a u v h, lin_id]

theorem whisk_add {a b : Obj S} (f g : P.obj a ⟶ P.obj b) (u : Obj S) (v : List S.Colour) :
    P.whisk (f + g) u v = P.whisk f u v + P.whisk g u v := by
  obtain ⟨f, rfl⟩ := P.lin_surjective f
  obtain ⟨g, rfl⟩ := P.lin_surjective g
  rw [← lin_add, whisk_lin, whisk_lin, whisk_lin, LinDiagram.whisk_add, lin_add]

theorem whisk_smul {a b : Obj S} (r : R) (f : P.obj a ⟶ P.obj b) (u : Obj S)
    (v : List S.Colour) : P.whisk (r • f) u v = r • P.whisk f u v := by
  obtain ⟨f, rfl⟩ := P.lin_surjective f
  rw [← lin_smul, whisk_lin, whisk_lin, LinDiagram.whisk_smul, lin_smul]

theorem whisk_sub {a b : Obj S} (f g : P.obj a ⟶ P.obj b) (u : Obj S) (v : List S.Colour) :
    P.whisk (f - g) u v = P.whisk f u v - P.whisk g u v := by
  obtain ⟨f, rfl⟩ := P.lin_surjective f
  obtain ⟨g, rfl⟩ := P.lin_surjective g
  rw [← lin_sub, whisk_lin, whisk_lin, whisk_lin, LinDiagram.whisk_sub, lin_sub]

theorem whisk_zero {a b : Obj S} (u : Obj S) (v : List S.Colour) :
    P.whisk (0 : P.obj a ⟶ P.obj b) u v = 0 := by
  rw [← P.lin_zero, whisk_lin, LinDiagram.whisk_zero, lin_zero]

/-- Whiskering as an `R`-linear map. -/
def whiskLinearMap (a b : Obj S) (u : Obj S) (v : List S.Colour) :
    (P.obj a ⟶ P.obj b) →ₗ[R] (P.obj (a.whisker u v) ⟶ P.obj (b.whisker u v)) where
  toFun f := P.whisk f u v
  map_add' f g := P.whisk_add f g u v
  map_smul' r f := P.whisk_smul r f u v

end Presentation

end StringDiagrams

end
