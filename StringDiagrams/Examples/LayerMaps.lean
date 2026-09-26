import StringDiagrams.Examples.TemperleyLieb
import StringDiagrams.Examples.Exterior
import StringDiagrams.LayerMap.Local

/-!
# Examples of functors from layer maps

Tests of `StringDiagrams.LayerMap` on the Temperley–Lieb category `TL(δ)`
(`StringDiagrams.TemperleyLieb`) and on the odd dots of `StringDiagrams.Exterior`.

* `TemperleyLieb.flipFunctor`: the reflection in a horizontal axis exchanges cups and caps. It
  is a contravariant functor `TL(δ) ⥤ TL(δ)ᵒᵖ` (`SigFlip.lift`); only the three defining
  relations need to be checked, without whiskering: the loop relation is fixed and the two
  zigzag relations are exchanged. On the Temperley–Lieb generators, `e_i ↦ e_i`
  (`flipFunctor_e`).
* `TemperleyLieb.mirrorFunctor`: the reflection in a vertical axis fixes cups and caps and
  reverses the order of the strands (`SigMirror.lift`). It exchanges the two zigzag relations.
* `TemperleyLieb.loopFunctor`: the free category on a closed generator `○` maps to `TL(δ)` by
  sending `○` to the composite `cap ∘ cup` (`LocalMap.liftGen`); hence `○ ↦ δ`
  (`loopFunctor_loop`).
* `Exterior.mirrorFunctor`: the reflection in a vertical axis of the odd dots. It is well defined
  without signs, and it satisfies the Koszul rule `σ (f ⊗ g) = -(σ g ⊗ σ f)` for two dots
  (`Exterior.mirror_tensor_dots`).
-/

noncomputable section

open CategoryTheory

namespace StringDiagrams.TemperleyLieb

variable (R : Type*) [CommRing R] (δ : R)

instance : sig.IsEven := ⟨fun _ => rfl⟩

/-! ## The reflection in a horizontal axis -/

/-- Cups and caps are exchanged. -/
def flipGen : Gen → Gen
  | .cup => .cap
  | .cap => .cup

/-- The reflection in a horizontal axis. -/
def flip : SigFlip sig sig :=
  SigFlip.ofGen flipGen (fun g => by cases g <;> rfl) (fun g => by cases g <;> rfl)
    (fun _ => rfl) (fun _ => rfl)

theorem flip_map_dcup {m i : ℕ} (h : i ≤ m) : flip.toOpLayerMap.map (dcup h) = dcap h :=
  Diagram.ext rfl

theorem flip_map_dcap {m i : ℕ} (h : i ≤ m) : flip.toOpLayerMap.map (dcap h) = dcup h :=
  Diagram.ext rfl

theorem flip_map_id (n : ℕ) : flip.toOpLayerMap.map (𝟙 (strands n)) = 𝟙 (strands n) := rfl

theorem flip_rel (r : (pres R δ).Rel) :
    (freeLift R (flip.toOpLayerMap.toPresented (pres R δ) fun _ => 1)).map
      ((pres R δ).rel r) = 0 := by
  rw [OpLayerMap.freeLift_toPresented_one]
  apply Quiver.Hom.unop_inj
  rw [Quiver.Hom.unop_op, Limits.unop_zero]
  change (pres R δ).lin (flip.toOpLayerMap.lin (relation R δ r)) = 0
  cases r with
  | loop =>
    rw [relation, OpLayerMap.lin_sub, OpLayerMap.lin_smul, OpLayerMap.lin_of, OpLayerMap.lin_of,
      OpLayerMap.map_comp, flip_map_dcup, flip_map_dcap, flip_map_id, Presentation.lin_sub,
      Presentation.lin_smul, Presentation.lin_of, Presentation.lin_of, Presentation.diag_comp,
      loop_at]
    erw [Presentation.diag_id, sub_self]
  | zigzagA =>
    rw [relation, OpLayerMap.lin_sub, OpLayerMap.lin_of, OpLayerMap.lin_of, OpLayerMap.map_comp,
      flip_map_dcup, flip_map_dcap, flip_map_id, Presentation.lin_sub, Presentation.lin_of,
      Presentation.lin_of, Presentation.diag_comp, zigzagB_at δ (m := 1) (i := 0) le_rfl]
    erw [Presentation.diag_id, sub_self]
  | zigzagB =>
    rw [relation, OpLayerMap.lin_sub, OpLayerMap.lin_of, OpLayerMap.lin_of, OpLayerMap.map_comp,
      flip_map_dcup, flip_map_dcap, flip_map_id, Presentation.lin_sub, Presentation.lin_of,
      Presentation.lin_of, Presentation.diag_comp, zigzagA_at δ (m := 1) (i := 0) le_rfl]
    erw [Presentation.diag_id, sub_self]

/-- **The reflection of `TL(δ)` in a horizontal axis**, a contravariant functor exchanging cups
and caps. -/
def flipFunctor : (pres R δ).Presented ⥤ (pres R δ).Presentedᵒᵖ :=
  flip.lift (pres R δ) (fun _ => rfl) (flip_rel R δ)

instance : (flipFunctor R δ).Additive := by unfold flipFunctor; infer_instance

instance : (flipFunctor R δ).Linear R := by unfold flipFunctor; infer_instance

variable {R δ}

theorem flipFunctor_cup {m i : ℕ} (h : i ≤ m) :
    (flipFunctor R δ).map ((pres R δ).diag (dcup h)) = ((pres R δ).diag (dcap h)).op := by
  unfold flipFunctor
  rw [SigFlip.lift_diag, flip_map_dcup, Diagram.weight_one, one_smul]

theorem flipFunctor_cap {m i : ℕ} (h : i ≤ m) :
    (flipFunctor R δ).map ((pres R δ).diag (dcap h)) = ((pres R δ).diag (dcup h)).op := by
  unfold flipFunctor
  rw [SigFlip.lift_diag, flip_map_dcap, Diagram.weight_one, one_smul]

/-- The reflection fixes the Temperley–Lieb generators `e_i = cup_i ∘ cap_i`. -/
theorem flipFunctor_e (m i : ℕ) : ((flipFunctor R δ).map (e δ m i)).unop = e δ m i := by
  by_cases h : i ≤ m
  · rw [e_def δ h, Functor.map_comp, unop_comp, flipFunctor_cup, flipFunctor_cap,
      Quiver.Hom.unop_op, Quiver.Hom.unop_op]
  · simp [e, h]

/-! ## The reflection in a vertical axis -/

variable (R δ)

/-- The reflection in a vertical axis: cups and caps are fixed. -/
def mirror : SigMirror sig sig where
  region := id
  colour := id
  colourSrc _ := rfl
  colourTgt _ := rfl
  gen := id
  dom g := by cases g <;> rfl
  cod g := by cases g <;> rfl
  left _ := rfl
  right _ := rfl

theorem mirror_map_id₀ : mirror.toLayerMap.map (𝟙 (strands 0)) = 𝟙 (strands 0) := rfl

theorem mirror_map_id₁ : mirror.toLayerMap.map (𝟙 (strands 1)) = 𝟙 (strands 1) := rfl

theorem mirror_map_dcup₀ :
    mirror.toLayerMap.map (dcup (m := 0) (i := 0) le_rfl) = dcup (m := 0) (i := 0) le_rfl :=
  Diagram.ext rfl

theorem mirror_map_dcap₀ :
    mirror.toLayerMap.map (dcap (m := 0) (i := 0) le_rfl) = dcap (m := 0) (i := 0) le_rfl :=
  Diagram.ext rfl

theorem mirror_map_dcup₁ (i : ℕ) (h : i ≤ 1) :
    mirror.toLayerMap.map (dcup (m := 1) (i := i) h) = dcup (m := 1) (i := 1 - i) (by omega) := by
  apply Diagram.ext
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with rfl | rfl <;> rfl

theorem mirror_map_dcap₁ (i : ℕ) (h : i ≤ 1) :
    mirror.toLayerMap.map (dcap (m := 1) (i := i) h) = dcap (m := 1) (i := 1 - i) (by omega) := by
  apply Diagram.ext
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with rfl | rfl <;> rfl

theorem mirror_rel (r : (pres R δ).Rel) :
    (freeLift R (mirror.toLayerMap.toPresented (pres R δ) fun _ => 1)).map
      ((pres R δ).rel r) = 0 := by
  rw [LayerMap.freeLift_toPresented_one]
  change (pres R δ).lin (mirror.toLayerMap.lin (relation R δ r)) = 0
  cases r with
  | loop =>
    rw [relation, LayerMap.lin_sub, LayerMap.lin_smul, LayerMap.lin_of, LayerMap.lin_of,
      LayerMap.map_comp, mirror_map_dcup₀, mirror_map_dcap₀, mirror_map_id₀,
      Presentation.lin_sub, Presentation.lin_smul, Presentation.lin_of, Presentation.lin_of,
      Presentation.diag_comp, loop_at δ (m := 0) (i := 0) le_rfl]
    erw [Presentation.diag_id, sub_self]
  | zigzagA =>
    rw [relation, LayerMap.lin_sub, LayerMap.lin_of, LayerMap.lin_of, LayerMap.map_comp,
      mirror_map_dcup₁, mirror_map_dcap₁, mirror_map_id₁, Presentation.lin_sub,
      Presentation.lin_of, Presentation.lin_of, Presentation.diag_comp,
      zigzagB_at δ (m := 1) (i := 0) le_rfl]
    erw [Presentation.diag_id, sub_self]
  | zigzagB =>
    rw [relation, LayerMap.lin_sub, LayerMap.lin_of, LayerMap.lin_of, LayerMap.map_comp,
      mirror_map_dcup₁, mirror_map_dcap₁, mirror_map_id₁, Presentation.lin_sub,
      Presentation.lin_of, Presentation.lin_of, Presentation.diag_comp,
      zigzagA_at δ (m := 1) (i := 0) le_rfl]
    erw [Presentation.diag_id, sub_self]

/-- **The reflection of `TL(δ)` in a vertical axis**, reversing the order of the strands. -/
def mirrorFunctor : (pres R δ).Presented ⥤ (pres R δ).Presented :=
  mirror.lift (pres R δ) (fun _ => rfl) (pres R δ).wfDom_of_subsingleton (mirror_rel R δ)

/-! ## A closed generator evaluated as a loop -/

/-- One region, one strand colour, and a single closed generator `○ : [] ⟶ []`. -/
def loopSig : Signature where
  Region := Unit
  Colour := Unit
  colourSrc _ := ()
  colourTgt _ := ()
  Gen := Unit
  dom _ := []
  cod _ := []
  left _ := ()
  right _ := ()

instance : loopSig.IsEven := ⟨fun _ => rfl⟩

/-- The free linear category on a closed generator: no relations. -/
def loopPres : Presentation loopSig R where
  Rel := Empty
  dom _ := ⟨(), []⟩
  cod _ := ⟨(), []⟩
  rel r := r.elim

/-- Regions and strands of `loopSig` are those of `TL`. -/
def loopColours : ColourMap loopSig sig where
  region := id
  colour := id
  colourSrc _ := rfl
  colourTgt _ := rfl

/-- The image of the closed generator: the loop `cap ∘ cup`. -/
def loopImg (g : loopSig.Gen) :
    (pres R δ).obj (LocalMap.genDom loopColours g) ⟶ (pres R δ).obj (LocalMap.genCod loopColours g) :=
  (pres R δ).diag (dcup (m := 0) (i := 0) le_rfl ≫ dcap (m := 0) (i := 0) le_rfl)

/-- **The closed generator as a loop**: the functor from the free category on `○` to `TL(δ)`
sending `○` to `cap ∘ cup`, an image which is not a generator. -/
def loopFunctor : (loopPres R).Presented ⥤ (pres R δ).Presented :=
  LocalMap.liftGen loopColours (loopImg R δ) (loopPres R)
    (LocalMap.parity_of_isEven loopColours (loopImg R δ)) (fun r => r.elim)

/-- The closed generator as a layer. -/
def loopLayer : Layer loopSig := ⟨(), [], (), []⟩

theorem loopLayer_valid : loopLayer.Valid := ⟨trivial, rfl, trivial, rfl, trivial, rfl, trivial⟩

/-- The closed generator goes to `δ`. -/
theorem loopFunctor_loop :
    (loopFunctor R δ).map ((loopPres R).diag (Diagram.ofLayer loopLayer loopLayer_valid)) =
      δ • 𝟙 _ := by
  rw [loopFunctor, LocalMap.liftGen_layer, loopImg,
    (pres R δ).whisk_diag _ _ _ (Obj.whiskerOK_of_subsingleton _ _ _)]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rw [show Diagram.whisker (dcup (m := 0) (i := 0) le_rfl ≫ dcap (m := 0) (i := 0) le_rfl)
      (loopColours.obj ⟨loopLayer.start, loopLayer.left⟩) (loopColours.word loopLayer.right)
      (Obj.whiskerOK_of_subsingleton _ _ _) = dcup (m := 0) (i := 0) le_rfl ≫
        dcap (m := 0) (i := 0) le_rfl from Diagram.ext rfl,
    Presentation.diag_comp, loop_at]
  rfl

end StringDiagrams.TemperleyLieb

namespace StringDiagrams.Exterior

variable (R : Type*) [CommRing R]

/-! ## Odd dots: the reflection in a vertical axis -/

/-- The reflection in a vertical axis of the odd dots. -/
def mirror : SigMirror sig sig where
  region := id
  colour := id
  colourSrc _ := rfl
  colourTgt _ := rfl
  gen := id
  dom _ := rfl
  cod _ := rfl
  left _ := rfl
  right _ := rfl

/-- The dot on one strand. -/
abbrev dot : strands 1 ⟶ strands 1 := dlay (n := 1) (i := 0) (by decide)

theorem mirror_map_dot : mirror.toLayerMap.map dot = dot := Diagram.ext rfl

theorem mirror_rel (r : (pres R).Rel) :
    (freeLift R (mirror.toLayerMap.toPresented (pres R) fun _ => 1)).map ((pres R).rel r) = 0 := by
  rw [LayerMap.freeLift_toPresented_one]
  change (pres R).lin (mirror.toLayerMap.lin (LinDiagram.of (dot ≫ dot))) = 0
  rw [LayerMap.lin_of, LayerMap.map_comp, mirror_map_dot, Presentation.lin_of,
    Presentation.diag_comp]
  have := x_mul_x_self R 1 0
  rwa [x_def R (by decide), End.mul_def] at this

/-- **The reflection in a vertical axis of the odd dots.** No signs are needed for it to be
well defined. -/
def mirrorFunctor : (pres R).Presented ⥤ (pres R).Presented :=
  mirror.lift (pres R) (fun _ => rfl) (pres R).wfDom_of_subsingleton (mirror_rel R)

theorem composable_strands (m n : ℕ) : (strands m).Composable (strands n) :=
  ⟨Signature.ok_of_subsingleton _ _, rfl, Signature.ok_of_subsingleton _ _⟩

/-- **The Koszul rule for the reflection of two odd dots**: the reflection of `dot ⊗ dot` is
`-(dot ⊗ dot)`, the horizontal composite of the reflected dots in the reverse order, with the
sign `(-1)^{|dot||dot|} = -1`. -/
theorem mirror_tensor_dots :
    (pres R).diag (mirror.toLayerMap.map (Diagram.rwhisker dot (strands 1) (composable_strands 1 1)
      ≫ Diagram.lwhisker (strands 1) dot (composable_strands 1 1))) =
      -(pres R).diag (Diagram.rwhisker dot (strands 1) (composable_strands 1 1) ≫
        Diagram.lwhisker (strands 1) dot (composable_strands 1 1)) := by
  rw [SigMirror.diag_map_tensor _ _ (fun _ => rfl)]
  have h₁ : Diagram.oddCount dot = 1 := rfl
  rw [h₁]
  simp only [mul_one, pow_one, neg_smul, one_smul, neg_inj]
  exact (pres R).diag_eq_of_layers_eq' _ _ rfl rfl rfl |>.symm

end StringDiagrams.Exterior

end
