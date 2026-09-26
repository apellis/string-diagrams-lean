import StringDiagrams.Super.Bicategory
import StringDiagrams.Bicategory

/-!
# Presented monoidal supercategories and 2-supercategories

For a presentation `P` whose relations are homogeneous for the parity grading
(`Presentation.IsParityHomogeneous`), with odd generators allowed:

* for a monoidal signature (a single region), `P.Presented` with its existing data
  `Presentation.instMonoidalCategoryStruct` is a strict monoidal supercategory in the sense of
  Brundan–Ellis, Definition 1.4 (`Presentation.monoidalSupercategory`,
  `Presentation.isStrict`);
* for arbitrary regions, `P.Bicat` is a strict 2-supercategory in the sense of Brundan–Ellis,
  Definitions 2.1 and 2.2 (`Presentation.twoSupercategory`, `Presentation.Bicat.instStrict`),
  with hom supercategories `Presentation.Bicat.supercategory`.

The super interchange law is `Presentation.diag_interchange_diagrams` (monoidal case) and
`Presentation.wRAt_diag_comp_wL_diag` (general regions), whose Koszul sign
`(-1)^{oddCount f · oddCount g}` is the sign `(-1)^{|f||g|}` of the parities
(`Diagram.degree_parityDeg`), extended to homogeneous linear combinations by
`Presentation.homDeg_induction`.

For even signatures (`Signature.IsEven`) the presentation is automatically
parity-homogeneous with no odd morphisms, and the Mathlib structures obtained from the
supercategorical ones are the existing instances `Presentation.instMonoidalCategory` and
`Presentation.instBicategory` (`Presentation.toMonoidalCategory_eq`,
`Presentation.toBicategory_eq`, both by `rfl`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory MonoidalCategory Supercategory

universe w v u₀ u₁ u₂

variable {S : Signature.{u₀, u₁, u₂}}

/-! ## Parities of diagrams -/

theorem Diagram.degree_parityDeg {a b : Obj S} (f : a ⟶ b) :
    Diagram.degree (Presentation.parityDeg S) f = (Diagram.oddCount f : ZMod 2) := by
  obtain ⟨ls, h⟩ := f
  simp only [Diagram.degree, Diagram.oddCount, Diagram.layers]
  clear h
  induction ls with
  | nil => simp
  | cons L ls ih =>
    rw [Diagram.oddCountList_cons, List.map_cons, List.sum_cons, ih, Nat.cast_add]
    congr 1
    by_cases hL : S.odd L.gen <;>
      simp [Presentation.parityDeg, Diagram.oddCountList, List.filter_cons, hL]

/-- The Koszul sign of two diagrams of parities `p` and `q`. -/
theorem Diagram.neg_one_pow_oddCount {a b a' b' : Obj S} (f : a ⟶ b) (g : a' ⟶ b')
    {p q : ZMod 2} (hf : Diagram.degree (Presentation.parityDeg S) f = p)
    (hg : Diagram.degree (Presentation.parityDeg S) g = q) :
    (-1 : ℤ) ^ (Diagram.oddCount f * Diagram.oddCount g) = koszulSign p q := by
  rw [← koszulSign_natCast, ← Diagram.degree_parityDeg, ← Diagram.degree_parityDeg, hf, hg]

/-- An even signature has parity-homogeneous presentations only. -/
theorem Presentation.isParityHomogeneous_of_isEven [S.IsEven] {R : Type w} [CommRing R]
    (P : Presentation.{w, v} S R) : P.IsParityHomogeneous := by
  intro i
  refine ⟨0, LinDiagram.mem_homDeg_iff.mpr fun g _ => ?_⟩
  rw [Diagram.degree_parityDeg, Diagram.oddCount_eq_zero, Nat.cast_zero]

namespace Presentation

variable {R : Type w} [CommRing R] (P : Presentation.{w, v} S R)

/-! ## Induction on homogeneous morphisms -/

variable {P} in
/-- Induction on a homogeneous morphism of the presented category: it suffices to treat
classes of diagrams of the given degree, `0`, sums and scalar multiples. -/
theorem homDeg_induction {A : Type*} [AddCommMonoid A] {deg : S.Gen → A} {a b : Obj S} {d : A}
    {motive : (P.obj a ⟶ P.obj b) → Prop}
    (diag : ∀ f : a ⟶ b, Diagram.degree deg f = d → motive (P.diag f)) (zero : motive 0)
    (add : ∀ x y, motive x → motive y → motive (x + y))
    (smul : ∀ (r : R) x, motive x → motive (r • x)) {x : P.obj a ⟶ P.obj b}
    (hx : x ∈ P.homDeg deg a b d) : motive x := by
  obtain ⟨F, hF, rfl⟩ := mem_homDeg_iff.mp hx
  clear hx
  rw [LinDiagram.homDeg, Finsupp.supported_eq_span_single] at hF
  induction hF using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨f, hf, rfl⟩ := hy
    exact diag f hf
  | zero => rw [lin_zero]; exact zero
  | add y z _ _ hy hz => rw [lin_add]; exact add _ _ hy hz
  | smul r y _ hy => rw [lin_smul]; exact smul r _ hy

variable {P} in
theorem eqToHom_mem_homDeg {A : Type*} [AddCommMonoid A] (deg : S.Gen → A) {a b : Obj S}
    (h : P.obj a = P.obj b) : eqToHom h ∈ P.homDeg deg a b 0 := by
  rw [P.eqToHom_obj h]
  exact diag_mem_homDeg' (Diagram.degree_eqToHom deg _)

/-- Whiskering on the left preserves parities. -/
theorem wL_mem {A : Type*} [AddCommMonoid A] (deg : S.Gen → A) (a : Obj S) {b b' : Obj S}
    {d : A} {g : P.obj b ⟶ P.obj b'} (hg : g ∈ P.homDeg deg b b' d) :
    P.wL a g ∈ P.homDeg deg (a.tensor b) (a.tensor b') d := by
  have := comp_mem_homDeg (eqToHom_mem_homDeg (P := P) deg (congrArg P.obj
    (Obj.tensor_eq_whisker_nil a b))) (comp_mem_homDeg (whisk_mem_homDeg hg a [])
      (eqToHom_mem_homDeg (P := P) deg (congrArg P.obj (Obj.tensor_eq_whisker_nil a b').symm)))
  rwa [zero_add, add_zero] at this

/-- Right whiskering (for objects starting in a region `r`) preserves parities. -/
theorem wRAt_mem {A : Type*} [AddCommMonoid A] (deg : S.Gen → A) (r : S.Region) {a a' : Obj S}
    {d : A} {f : P.obj a ⟶ P.obj a'} (hf : f ∈ P.homDeg deg a a' d) (b : Obj S)
    (ha : a.start = r) (ha' : a'.start = r) :
    P.wRAt r f b ha ha' ∈ P.homDeg deg (a.tensor b) (a'.tensor b) d := by
  have := comp_mem_homDeg (eqToHom_mem_homDeg (P := P) deg (congrArg P.obj
    (Obj.tensor_eq_whisker_nil_of_start b ha))) (comp_mem_homDeg
      (whisk_mem_homDeg hf (Obj.nil r) b.word) (eqToHom_mem_homDeg (P := P) deg
        (congrArg P.obj (Obj.tensor_eq_whisker_nil_of_start b ha').symm)))
  rwa [zero_add, add_zero] at this

/-- The super interchange law for homogeneous morphisms of the presented category, for
general regions. -/
theorem wRAt_comp_wL_super {a a' b b' : Obj S} {r : S.Region} (h : a.Composable b)
    {p q : ZMod 2} {f : P.obj a ⟶ P.obj a'} {g : P.obj b ⟶ P.obj b'}
    (hf : f ∈ P.homDeg (parityDeg S) a a' p) (hg : g ∈ P.homDeg (parityDeg S) b b' q)
    (ha : a.start = r) (ha' : a'.start = r) :
    P.wRAt r f b ha ha' ≫ P.wL a' g = koszulSign p q • (P.wL a g ≫ P.wRAt r f b' ha ha') := by
  refine homDeg_induction (motive := fun f =>
    P.wRAt r f b ha ha' ≫ P.wL a' g = koszulSign p q • (P.wL a g ≫ P.wRAt r f b' ha ha'))
    (fun d hd => ?_) (by simp [wRAt_zero]) (fun f f' hf hf' => ?_) (fun x f hf => ?_) hf
  · refine homDeg_induction (motive := fun g => P.wRAt r (P.diag d) b ha ha' ≫ P.wL a' g =
      koszulSign p q • (P.wL a g ≫ P.wRAt r (P.diag d) b' ha ha'))
      (fun e he => ?_) (by simp [wL_zero]) (fun g g' hg hg' => ?_) (fun x g hg => ?_) hg
    · dsimp only
      rw [P.wRAt_diag_comp_wL_diag h d e, Diagram.neg_one_pow_oddCount d e hd he]
    · simp only [wL_add, Preadditive.add_comp, Preadditive.comp_add, hg, hg', smul_add]
    · simp only [wL_smul, Linear.smul_comp, Linear.comp_smul, hg, smul_comm x]
  · simp only [wRAt_add, Preadditive.add_comp, Preadditive.comp_add, hf, hf', smul_add]
  · simp only [wRAt_smul, Linear.smul_comp, Linear.comp_smul, hf, smul_comm x]

/-! ## Presented monoidal supercategories -/

section Monoidal

variable [Subsingleton S.Region] [Inhabited S.Region]

/-- Right whiskering preserves parities. -/
theorem wR_mem {A : Type*} [AddCommMonoid A] (deg : S.Gen → A) {a a' : Obj S} {d : A}
    {f : P.obj a ⟶ P.obj a'} (hf : f ∈ P.homDeg deg a a' d) (b : Obj S) :
    P.wR f b ∈ P.homDeg deg (a.tensor b) (a'.tensor b) d := by
  have := comp_mem_homDeg (eqToHom_mem_homDeg (P := P) deg (congrArg P.obj
    (Obj.tensor_eq_whisker_unit a b))) (comp_mem_homDeg (whisk_mem_homDeg hf Obj.unit b.word)
      (eqToHom_mem_homDeg (P := P) deg (congrArg P.obj (Obj.tensor_eq_whisker_unit a' b).symm)))
  rwa [zero_add, add_zero] at this

/-- The super interchange law for homogeneous morphisms of the presented category of a
monoidal signature: `(f ⊗ 1) ≫ (1 ⊗ g) = (-1)^{|f||g|} (1 ⊗ g) ≫ (f ⊗ 1)`. -/
theorem wR_comp_wL_super {a a' b b' : Obj S} {p q : ZMod 2} {f : P.obj a ⟶ P.obj a'}
    {g : P.obj b ⟶ P.obj b'} (hf : f ∈ P.homDeg (parityDeg S) a a' p)
    (hg : g ∈ P.homDeg (parityDeg S) b b' q) :
    P.wR f b ≫ P.wL a' g = koszulSign p q • (P.wL a g ≫ P.wR f b') := by
  refine homDeg_induction (motive := fun f =>
    P.wR f b ≫ P.wL a' g = koszulSign p q • (P.wL a g ≫ P.wR f b'))
    (fun d hd => ?_) (by simp [wR_zero]) (fun f f' hf hf' => ?_) (fun x f hf => ?_) hf
  · refine homDeg_induction (motive := fun g => P.wR (P.diag d) b ≫ P.wL a' g =
      koszulSign p q • (P.wL a g ≫ P.wR (P.diag d) b'))
      (fun e he => ?_) (by simp [wL_zero]) (fun g g' hg hg' => ?_) (fun x g hg => ?_) hg
    · dsimp only
      rw [wR_diag, wR_diag, wL_diag, wL_diag, ← diag_comp, ← diag_comp,
        P.diag_interchange_diagrams, Diagram.neg_one_pow_oddCount d e hd he]
    · simp only [wL_add, Preadditive.add_comp, Preadditive.comp_add, hg, hg', smul_add]
    · simp only [wL_smul, Linear.smul_comp, Linear.comp_smul, hg, smul_comm x]
  · simp only [wR_add, Preadditive.add_comp, Preadditive.comp_add, hf, hf', smul_add]
  · simp only [wR_smul, Linear.smul_comp, Linear.comp_smul, hf, smul_comm x]

variable {P}

/-- **Presented monoidal supercategories.** For a monoidal signature, with odd generators
allowed, and parity-homogeneous relations, the presented category is a monoidal supercategory
(Brundan–Ellis, Definition 1.4), with the data `Presentation.instMonoidalCategoryStruct`. -/
theorem monoidalSupercategory (hP : P.IsParityHomogeneous) :
    letI := P.supercategory hP
    MonoidalSupercategory R P.Presented :=
  letI := P.supercategory hP
  { tensorHom_def := fun _ _ => rfl
    whiskerLeft_id := fun X Y => P.wL_id (P.toObj X) (P.toObj Y)
    id_whiskerRight := fun X Y => P.wR_id (P.toObj X) (P.toObj Y)
    whiskerLeft_comp := fun X _ _ _ f g => P.wL_comp (P.toObj X) f g
    comp_whiskerRight := fun f g W => P.wR_comp f g (P.toObj W)
    whiskerLeft_add := fun X _ _ f g => P.wL_add (P.toObj X) f g
    add_whiskerRight := fun f g Z => P.wR_add f g (P.toObj Z)
    whiskerLeft_smul := fun X _ _ r f => P.wL_smul (P.toObj X) r f
    smul_whiskerRight := fun r f Z => P.wR_smul r f (P.toObj Z)
    whiskerLeft_mem := fun X _ _ _ _ hf => P.wL_mem (parityDeg S) (P.toObj X) hf
    whiskerRight_mem := fun Z hf => P.wR_mem (parityDeg S) hf (P.toObj Z)
    super_interchange := fun hf hg => P.wR_comp_wL_super hf hg
    associator_naturality := fun {X₁ X₂ X₃ Y₁ Y₂ Y₃} f₁ f₂ f₃ =>
      P.associator_naturality_aux (a₁ := P.toObj X₁) (a₂ := P.toObj X₂) (a₃ := P.toObj X₃)
        (b₁ := P.toObj Y₁) (b₂ := P.toObj Y₂) (b₃ := P.toObj Y₃) f₁ f₂ f₃
    leftUnitor_naturality := fun {X Y} f => P.unit_wL (b := P.toObj X) (b' := P.toObj Y) f
    rightUnitor_naturality := fun {X Y} f => P.wR_unit (a := P.toObj X) (a' := P.toObj Y) f
    pentagon := fun W X Y Z => P.pentagon_aux (P.toObj W) (P.toObj X) (P.toObj Y) (P.toObj Z)
    triangle := fun X Y => P.triangle_aux (P.toObj X) (P.toObj Y)
    associator_hom_mem := fun _ _ _ =>
      eqToHom_mem_homDeg (P := P) _ (congrArg P.obj (Obj.tensor_assoc _ _ _))
    leftUnitor_hom_mem := fun _ =>
      eqToHom_mem_homDeg (P := P) _ (congrArg P.obj (Obj.unit_tensor _))
    rightUnitor_hom_mem := fun _ =>
      eqToHom_mem_homDeg (P := P) _ (congrArg P.obj (Obj.tensor_unit _)) }

variable (P) in
/-- The presented monoidal structure is strict. -/
instance isStrict : MonoidalSupercategory.IsStrict P.Presented where
  tensor_assoc X Y Z := P.tensor_assoc_obj X Y Z
  unit_tensor X := P.unit_tensor_obj X
  tensor_unit X := P.tensor_unit_obj X
  associator_eq X Y Z := P.associator_eq X Y Z
  leftUnitor_eq X := P.leftUnitor_eq X
  rightUnitor_eq X := P.rightUnitor_eq X

omit [Subsingleton S.Region] [Inhabited S.Region] in
/-- For an even signature there are no odd morphisms. -/
theorem noOdd_of_isEven [S.IsEven] :
    letI := P.supercategory P.isParityHomogeneous_of_isEven
    MonoidalSupercategory.NoOdd R P.Presented := by
  intro X Y
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  refine homDeg_induction (motive := fun x => x = 0) (fun f hf => ?_) rfl
    (fun x y hx hy => by rw [hx, hy, add_zero]) (fun r x hx => by rw [hx, smul_zero]) hx
  rw [Diagram.degree_parityDeg, Diagram.oddCount_eq_zero] at hf
  exact absurd hf (by decide)

/-- For an even signature, the Mathlib monoidal structure obtained from the monoidal
supercategory structure is the existing instance `Presentation.instMonoidalCategory`. -/
theorem toMonoidalCategory_eq [S.IsEven] :
    letI := P.supercategory P.isParityHomogeneous_of_isEven
    letI := P.monoidalSupercategory P.isParityHomogeneous_of_isEven
    MonoidalSupercategory.toMonoidalCategory R P.noOdd_of_isEven = P.instMonoidalCategory :=
  rfl

end Monoidal

/-! ## Presented 2-supercategories -/


/-- The data of the 2-category `P.Bicat` (the same as that of `Presentation.instBicategory`
for even signatures): whiskerings `Presentation.wL`, `Presentation.wRAt` and coherence maps
given by equalities of words. -/
instance instBicategoryStruct : BicategoryStruct P.Bicat where
  toCategoryStruct := inferInstance
  homCategory := Bicat.homCategory
  whiskerLeft a _ _ θ := P.wL (Bicat.Hom.obj a) θ
  whiskerRight {l _ _} {a a'} η b :=
    P.wRAt l.region η (Bicat.Hom.obj b) (Bicat.Hom.start_eq a) (Bicat.Hom.start_eq a')
  associator a b c :=
    Bicat.isoOfEq (Obj.tensor_assoc (Bicat.Hom.obj a) (Bicat.Hom.obj b) (Bicat.Hom.obj c))
  leftUnitor a := Bicat.isoOfEq (Obj.nil_tensor (Bicat.Hom.start_eq a))
  rightUnitor {_ m} a := Bicat.isoOfEq (Obj.tensor_nil (Bicat.Hom.obj a) m.region)

namespace Bicat

variable {P} {l m : P.Bicat}

/-- The hom categories of `P.Bicat` are preadditive, as `P.Presented`. -/
instance homPreadditiveSuper (l m : P.Bicat) : Preadditive (l ⟶ m) where
  homGroup a b := inferInstanceAs (AddCommGroup (P.obj (Hom.obj a) ⟶ P.obj (Hom.obj b)))
  add_comp _ _ _ f f' g := Preadditive.add_comp (C := P.Presented) _ _ _ f f' g
  comp_add _ _ _ f g g' := Preadditive.comp_add (C := P.Presented) _ _ _ f g g'

/-- The hom categories of `P.Bicat` are `R`-linear, as `P.Presented`. -/
instance homLinearSuper (l m : P.Bicat) : Linear R (l ⟶ m) where
  homModule a b := inferInstanceAs (Module R (P.obj (Hom.obj a) ⟶ P.obj (Hom.obj b)))
  smul_comp _ _ _ r f g := Linear.smul_comp (C := P.Presented) _ _ _ r f g
  comp_smul _ _ _ f r g := Linear.comp_smul (C := P.Presented) _ _ _ f r g

/-- The hom supercategories of `P.Bicat`, for a parity-homogeneous presentation: the parity
of a 2-morphism is its parity in `P.Presented`. -/
def supercategory (hP : P.IsParityHomogeneous) (l m : P.Bicat) : Supercategory R (l ⟶ m) where
  parity a b := P.homDeg (parityDeg S) (Hom.obj a) (Hom.obj b)
  isInternal a b := isInternal_homDeg hP (Hom.obj a) (Hom.obj b)
  id_mem a := P.id_mem_homDeg (parityDeg S) (Hom.obj a)
  comp_mem hf hg := comp_mem_homDeg hf hg

end Bicat

variable {P}

theorem Bicat.isoOfEq_hom_mem {l m : P.Bicat} (hP : P.IsParityHomogeneous) {a b : l ⟶ m}
    (e : Bicat.Hom.obj a = Bicat.Hom.obj b) :
    letI := Bicat.supercategory hP l m
    ((Bicat.isoOfEq e).hom : a ⟶ b) ∈ parity (R := R) a b 0 :=
  eqToHom_mem_homDeg (P := P) _ (congrArg P.obj e)

/-- **Presented 2-supercategories.** For arbitrary regions, with odd generators allowed, and
parity-homogeneous relations, `P.Bicat` is a 2-supercategory (Brundan–Ellis,
Definition 2.2), strict by `Presentation.Bicat.instStrict` (Definition 2.1). -/
theorem twoSupercategory (hP : P.IsParityHomogeneous) :
    letI := Bicat.supercategory hP
    TwoSupercategory R P.Bicat :=
  letI := Bicat.supercategory hP
  { whiskerLeft_id := fun a b => P.wL_id_of_composable (Bicat.Hom.composable a b)
    whiskerLeft_comp := fun a _ _ _ η θ => P.wL_comp (Bicat.Hom.obj a) η θ
    id_whiskerLeft := fun {_ _} {a b} η =>
      P.wL_nil η (Bicat.Hom.wf a) (Bicat.Hom.start_eq a) (Bicat.Hom.start_eq b)
    comp_whiskerLeft := fun a b _ _ η =>
      P.wL_tensor (Bicat.Hom.composable a b) (Bicat.Hom.composable b _) η
    id_whiskerRight := fun a b =>
      P.wRAt_id (Bicat.Hom.start_eq a) (Bicat.Hom.obj b) (Bicat.Hom.composable a b).ok_endR
    comp_whiskerRight := fun η θ c => P.wRAt_comp _ _ _ η θ (Bicat.Hom.obj c)
    whiskerRight_id := fun {_ _} {a a'} η =>
      P.wRAt_nil η (Bicat.Hom.wf a) (Bicat.Hom.endR_eq a) (Bicat.Hom.start_eq a)
        (Bicat.Hom.start_eq a')
    whiskerRight_comp := fun {_ _ _ _} {a _} η b c =>
      P.wRAt_tensor (Bicat.Hom.composable a b) (Bicat.Hom.composable b c) η _ _
    whisker_assoc := fun {_ _ _ _} a {b b'} η c =>
      P.wRAt_wL (Bicat.Hom.composable a b) (Bicat.Hom.composable b c) η (Bicat.Hom.start_eq a)
        (Bicat.Hom.start_eq b) (Bicat.Hom.start_eq b')
    pentagon := fun a b c d => Bicat.pentagon_aux a b c d
    triangle := fun a b => Bicat.triangle_aux a b
    whiskerLeft_add := fun a _ _ η θ => P.wL_add (Bicat.Hom.obj a) η θ
    add_whiskerRight := fun η θ c => P.wRAt_add _ _ η θ (Bicat.Hom.obj c)
    whiskerLeft_smul := fun a _ _ r η => P.wL_smul (Bicat.Hom.obj a) r η
    smul_whiskerRight := fun r η c => P.wRAt_smul _ _ r η (Bicat.Hom.obj c)
    whiskerLeft_mem := fun a _ _ _ _ hη => P.wL_mem (parityDeg S) (Bicat.Hom.obj a) hη
    whiskerRight_mem := fun {l _ _} {a a'} _ _ c hη =>
      P.wRAt_mem (parityDeg S) l.region hη (Bicat.Hom.obj c) (Bicat.Hom.start_eq a)
        (Bicat.Hom.start_eq a')
    super_interchange := fun {_ _ _} {a a'} {b _} _ _ _ _ hη hθ =>
      P.wRAt_comp_wL_super (Bicat.Hom.composable a b) hη hθ (Bicat.Hom.start_eq a)
        (Bicat.Hom.start_eq a')
    associator_hom_mem := fun _ _ _ => Bicat.isoOfEq_hom_mem hP _
    leftUnitor_hom_mem := fun _ => Bicat.isoOfEq_hom_mem hP _
    rightUnitor_hom_mem := fun _ => Bicat.isoOfEq_hom_mem hP _ }

variable (P) in
/-- The presented 2-supercategory is strict. -/
instance Bicat.instStrict : BicategoryStruct.Strict P.Bicat where
  id_comp a := Bicat.Hom.ext (Obj.nil_tensor (Bicat.Hom.start_eq a))
  comp_id _ := Bicat.Hom.ext (Obj.tensor_nil _ _)
  assoc _ _ _ := Bicat.Hom.ext (Obj.tensor_assoc _ _ _)
  leftUnitor_eqToIso _ := Bicat.isoOfEq_eq_eqToIso _ _
  rightUnitor_eqToIso _ := Bicat.isoOfEq_eq_eqToIso _ _
  associator_eqToIso _ _ _ := Bicat.isoOfEq_eq_eqToIso _ _

/-- For an even signature there are no odd 2-morphisms. -/
theorem Bicat.noOdd_of_isEven [S.IsEven] :
    letI := Bicat.supercategory P.isParityHomogeneous_of_isEven
    TwoSupercategory.NoOdd R P.Bicat := by
  intro l m a b
  rw [eq_bot_iff]
  intro x hx
  rw [Submodule.mem_bot]
  refine homDeg_induction (motive := fun x => x = 0) (fun f hf => ?_) rfl
    (fun x y hx hy => by rw [hx, hy, add_zero]) (fun r x hx => by rw [hx, smul_zero]) hx
  rw [Diagram.degree_parityDeg, Diagram.oddCount_eq_zero] at hf
  exact absurd hf (by decide)

/-- For an even signature, the Mathlib bicategory obtained from the 2-supercategory structure
is the existing instance `Presentation.instBicategory`. -/
theorem toBicategory_eq [S.IsEven] :
    letI := Bicat.supercategory P.isParityHomogeneous_of_isEven
    letI := P.twoSupercategory P.isParityHomogeneous_of_isEven
    TwoSupercategory.toBicategory R Bicat.noOdd_of_isEven = P.instBicategory :=
  rfl

end Presentation

end StringDiagrams

end
