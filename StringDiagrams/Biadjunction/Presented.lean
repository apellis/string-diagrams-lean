import StringDiagrams.Biadjunction.Words
import StringDiagrams.Biadjunction.Linear

noncomputable section

namespace StringDiagrams

open CategoryTheory Bicategory Biadjunction

universe w v u₀ u₁ u₂

variable {S : Signature.{u₀, u₁, u₂}} {R : Type w} [CommRing R]

namespace Presentation

variable (P : Presentation.{w, v} S R) [S.IsEven]

theorem _root_.StringDiagrams.Biadjunction.congr_comp_heq {B : Type*} [Bicategory B] {a b c : B}
    {f f' : a ⟶ b} {g g' : b ⟶ a} {h : b ⟶ c} {k : c ⟶ b} (Q : f ⊣⊢ g) (hf : f = f')
    (hg : g = g') (T : h ⊣⊢ k) : HEq ((Q.congr hf hg).comp T) (Q.comp T) := by
  subst hf hg; rfl

theorem _root_.StringDiagrams.Biadjunction.congr_heq {B : Type*} [Bicategory B] {a b : B}
    {f f' : a ⟶ b} {g g' : b ⟶ a} (Q : f ⊣⊢ g) (hf : f = f') (hg : g = g') :
    HEq (Q.congr hf hg) Q := by
  subst hf hg; rfl

/-! ## Sliding 2-morphisms along cups and caps -/

section Sliding

variable {B : Type*} [Bicategory B] {a b : B} {f f' : a ⟶ b} {g g' : b ⟶ a}

/-- Sliding `α : f ⟶ f'` along the cup of `f ⊣ g` turns it into its right mate on the other
strand. -/
theorem _root_.StringDiagrams.Biadjunction.left_unit_comp_whiskerRight (Q : f ⊣⊢ g)
    (Q' : f' ⊣⊢ g') (α : f ⟶ f') :
    Q.left.unit ≫ α ▷ g = Q'.left.unit ≫ f' ◁ rightMate Q Q' α :=
  unit_comp_whiskerRight_eq Q'.left Q.left α

/-- Sliding `α : f ⟶ f'` along the cap of `f' ⊣ g'` turns it into its right mate on the other
strand. -/
theorem _root_.StringDiagrams.Biadjunction.whiskerLeft_comp_left_counit (Q : f ⊣⊢ g)
    (Q' : f' ⊣⊢ g') (α : f ⟶ f') :
    g' ◁ α ≫ Q'.left.counit = rightMate Q Q' α ▷ f ≫ Q.left.counit :=
  whiskerLeft_comp_counit_eq Q'.left Q.left α

/-- Sliding `α : f ⟶ f'` along the cup of `g ⊣ f` turns it into its left mate on the other
strand. -/
theorem _root_.StringDiagrams.Biadjunction.right_unit_comp_whiskerLeft (Q : f ⊣⊢ g)
    (Q' : f' ⊣⊢ g') (α : f ⟶ f') :
    Q.right.unit ≫ g ◁ α = Q'.right.unit ≫ leftMate Q Q' α ▷ f' :=
  unit_comp_whiskerLeft_eq Q.right Q'.right α

/-- Sliding `α : f ⟶ f'` along the cap of `g' ⊣ f'` turns it into its left mate on the other
strand. -/
theorem _root_.StringDiagrams.Biadjunction.whiskerRight_comp_right_counit (Q : f ⊣⊢ g)
    (Q' : f' ⊣⊢ g') (α : f ⟶ f') :
    α ▷ g' ≫ Q'.right.counit = f ◁ leftMate Q Q' α ≫ Q.right.counit :=
  whiskerRight_comp_counit_eq Q.right Q'.right α

/-- For a cyclic 2-morphism, sliding along a cup of either adjunction produces the same mate. -/
theorem _root_.StringDiagrams.Biadjunction.IsCyclic.right_unit_comp_whiskerLeft {Q : f ⊣⊢ g}
    {Q' : f' ⊣⊢ g'} {α : f ⟶ f'} (hα : Biadjunction.IsCyclic Q Q' α) :
    Q.right.unit ≫ g ◁ α = Q'.right.unit ≫ rightMate Q Q' α ▷ f' := by
  rw [hα.eq]; exact Q.right_unit_comp_whiskerLeft Q' α

/-- For a cyclic 2-morphism, sliding along a cap of either adjunction produces the same mate. -/
theorem _root_.StringDiagrams.Biadjunction.IsCyclic.whiskerRight_comp_right_counit
    {Q : f ⊣⊢ g} {Q' : f' ⊣⊢ g'} {α : f ⟶ f'} (hα : Biadjunction.IsCyclic Q Q' α) :
    α ▷ g' ≫ Q'.right.counit = f ◁ rightMate Q Q' α ≫ Q.right.counit := by
  rw [hα.eq]; exact Q.whiskerRight_comp_right_counit Q' α

end Sliding

/-- A morphism of the presented category between the underlying words of two 1-morphisms of
`P.Bicat`, as a 2-morphism. -/
abbrev Bicat.homOf {P : Presentation.{w, v} S R} {l m : P.Bicat} {x x' : l ⟶ m}
    (f : P.obj x.obj ⟶ P.obj x'.obj) : x ⟶ x' :=
  f

section HomOf

variable {P} {l m : P.Bicat} {x x' x'' : l ⟶ m}

theorem Bicat.homOf_comp (f : P.obj x.obj ⟶ P.obj x'.obj) (g : P.obj x'.obj ⟶ P.obj x''.obj) :
    Bicat.homOf f ≫ Bicat.homOf g = Bicat.homOf (f ≫ g) := rfl

theorem Bicat.homOf_id : Bicat.homOf (𝟙 (P.obj x.obj)) = 𝟙 x := rfl

theorem Bicat.eqToHom_eq (h : x = x') :
    eqToHom h = Bicat.homOf (eqToHom (congrArg (fun z : l ⟶ m => P.obj z.obj) h)) := by
  subst h; rfl

end HomOf

/-! ## Linear structure of the presented bicategory -/

instance Bicat.instPreadditiveHom (l m : P.Bicat) : Preadditive (l ⟶ m) where
  homGroup a b := inferInstanceAs (AddCommGroup (P.obj a.obj ⟶ P.obj b.obj))
  add_comp _ _ _ f f' g := Preadditive.add_comp (C := P.Presented) _ _ _ f f' g
  comp_add _ _ _ f g g' := Preadditive.comp_add (C := P.Presented) _ _ _ f g g'

instance Bicat.instLinearHom (l m : P.Bicat) : Linear R (l ⟶ m) where
  homModule a b := inferInstanceAs (Module R (P.obj a.obj ⟶ P.obj b.obj))
  smul_comp _ _ _ r f g := Linear.smul_comp (C := P.Presented) _ _ _ r f g
  comp_smul _ _ _ f r g := Linear.comp_smul (C := P.Presented) _ _ _ f r g

instance Bicat.instLocallyPreadditive : LocallyPreadditive P.Bicat where
  whiskerLeft_add f _ _ η θ := P.wL_add f.obj η θ
  add_whiskerRight {_ _ _} {f g} η θ h := P.wRAt_add f.start_eq g.start_eq η θ h.obj

instance Bicat.instLocallyLinear : LocallyLinear R P.Bicat where
  whiskerLeft_smul f _ _ r η := P.wL_smul f.obj r η
  smul_whiskerRight {_ _ _} {f g} r η h := P.wRAt_smul f.start_eq g.start_eq r η h.obj

/-! ## Biadjunctions of words and composition -/

section Words

variable {P} {D : S.ColourDuality} (B : ColourBiadjunctions P D)

theorem biadjW_eq (w : List S.Colour) {l m : P.Bicat} (x : l ⟶ m) (hx : x.obj.word = w) :
    biadjW B w x hx = biadj B x := by
  subst hx; rfl

omit [S.IsEven] in
@[simp] theorem dualHom_id (l : P.Bicat) : P.dualHom D (𝟙 l) = 𝟙 l := rfl

theorem nilBiadj_id (l : P.Bicat) (h : (𝟙 l : l ⟶ l).obj.word = []) :
    nilBiadj (D := D) (𝟙 l) h = Biadjunction.id l := by
  simp only [nilBiadj, Biadjunction.id, Biadjunction.mk.injEq, Bicategory.Adjunction.id,
    adjunctionOfZigzag, Bicategory.Adjunction.mk.injEq]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp [P.diag_eqToHom] <;> rfl

theorem isCyclic_biadj_comp {l m n : P.Bicat} (x : l ⟶ m) (y : m ⟶ n) :
    Biadjunction.IsCyclic ((biadj B x).comp (biadj B y)) (biadj B (x ≫ y)) (𝟙 _) := by
  suffices h : ∀ (w : List S.Colour) {l : P.Bicat} (x : l ⟶ m) (hx : x.obj.word = w),
      Biadjunction.IsCyclic ((biadjW B w x hx).comp (biadj B y)) (biadj B (x ≫ y)) (𝟙 _) from h _ x rfl
  intro w
  induction w with
  | nil =>
    intro l x hx
    obtain ⟨l⟩ := l
    have hlm : m = ⟨l⟩ := by
      have h₁ := x.endR_eq
      have h₂ := x.start_eq
      rw [Obj.endR, hx] at h₁
      exact Bicat.ext (h₁.symm.trans h₂)
    subst hlm
    have hx₁ : x = 𝟙 _ := Bicat.Hom.ext (Obj.ext x.start_eq (by rw [hx]; rfl))
    subst hx₁
    simp only [biadjW, nilBiadj_id]
    have h₁ := isCyclic_leftUnitor_hom (biadj B y)
    have h₂ := isCyclic_eqToHom (Strict.id_comp y).symm
      (congrArg (P.dualHom D ·) (Strict.id_comp y).symm)
      (congr_arg_heq (fun z => biadj B z) (Strict.id_comp y).symm)
    have key := h₁.comp h₂
    convert key using 1
    simp [Strict.leftUnitor_eqToIso]
  | cons c w ih =>
    intro l x hx
    have hxy : (x ≫ y).obj.word = c :: (w ++ y.obj.word) := by
      show x.obj.word ++ y.obj.word = _
      rw [hx]; rfl
    rw [← biadjW_eq B _ (x ≫ y) hxy]
    simp only [biadjW]
    set head := P.headHom x c w hx
    set tail := P.tailHom x c w hx
    have h₀ := isCyclic_eqToHom (congrArg (· ≫ y) (P.headHom_comp_tailHom x c w hx).symm)
      (congrArg (P.dualHom D y ≫ ·) (P.dualHom_tail_comp_head D x c w hx).symm)
      (Biadjunction.congr_comp_heq ((B head c rfl).comp (biadjW B w tail rfl))
        (P.headHom_comp_tailHom x c w hx) (P.dualHom_tail_comp_head D x c w hx) (biadj B y))
    have h₁ := isCyclic_associator_hom (B head c rfl) (biadjW B w tail rfl) (biadj B y)
    have h₂ := (ih tail rfl).whiskerLeft (B head c rfl)
    have h₃ := isCyclic_eqToHom (P.headHom_comp_tailHom (x ≫ y) c (w ++ y.obj.word) hxy)
      (P.dualHom_tail_comp_head D (x ≫ y) c (w ++ y.obj.word) hxy)
      (Biadjunction.congr_heq ((B head c rfl).comp (biadj B (tail ≫ y)))
        (P.headHom_comp_tailHom (x ≫ y) c (w ++ y.obj.word) hxy)
        (P.dualHom_tail_comp_head D (x ≫ y) c (w ++ y.obj.word) hxy)).symm
    have key := h₀.comp (h₁.comp (h₂.comp h₃))
    convert key using 1
    simp [Strict.associator_eqToIso]

theorem isCyclic_biadj_comp_symm {l m n : P.Bicat} (x : l ⟶ m) (y : m ⟶ n) :
    Biadjunction.IsCyclic (biadj B (x ≫ y)) ((biadj B x).comp (biadj B y)) (𝟙 _) := by
  simpa using (isCyclic_biadj_comp B x y).inv

theorem isCyclic_biadj_eqToHom {l m : P.Bicat} {x x' : l ⟶ m} (h : x = x') :
    Biadjunction.IsCyclic (biadj B x) (biadj B x') (eqToHom h) :=
  isCyclic_eqToHom h (congrArg (P.dualHom D ·) h) (congr_arg_heq (fun z => biadj B z) h)

end Words

/-! ## Biadjunctions from cups and caps -/

section CupsCaps

variable {P} {l m : P.Bicat}

/-- The biadjunction `x ⊣⊢ y` in `P.Bicat` given by two cups and two caps satisfying the four
zigzag identities: `cup`, `cap` for `x ⊣ y` and `cup'`, `cap'` for `y ⊣ x`. -/
@[simps]
def biadjunctionOfZigzag (x : l ⟶ m) (y : m ⟶ l)
    (cup : Obj.nil l.region ⟶ x.obj.tensor y.obj) (cap : y.obj.tensor x.obj ⟶ Obj.nil m.region)
    (hl : P.diag (P.leftZigzagD x y cup cap) = 𝟙 _)
    (hr : P.diag (P.rightZigzagD x y cup cap) = 𝟙 _)
    (cup' : Obj.nil m.region ⟶ y.obj.tensor x.obj) (cap' : x.obj.tensor y.obj ⟶ Obj.nil l.region)
    (hl' : P.diag (P.leftZigzagD y x cup' cap') = 𝟙 _)
    (hr' : P.diag (P.rightZigzagD y x cup' cap') = 𝟙 _) : x ⊣⊢ y where
  left := adjunctionOfZigzag x y cup cap hl hr
  right := adjunctionOfZigzag y x cup' cap' hl' hr'

omit [S.IsEven] in
theorem diag_eq_id_of_layers {a a' : Obj S} (Z : a ⟶ a) (Z' : a' ⟶ a') (h : a = a')
    (hZ : Diagram.layers Z = Diagram.layers Z') (h' : P.diag Z' = 𝟙 _) : P.diag Z = 𝟙 _ := by
  rw [P.diag_eq_of_layers_eq' Z Z' h h hZ, h']; simp

variable (P) (D : S.ColourDuality)

/-- Cups and caps exhibiting every colour `c` as biadjoint to its dual `c*`: the unit `cup c`
and counit `cap c` of `c ⊣ c*`, the unit `cup' c` and counit `cap' c` of `c* ⊣ c`, with the four
zigzag identities (in the presented category, at the canonical position of the colour). -/
structure ColourCupsCaps where
  /-- The unit of `c ⊣ c*`. -/
  cup : ∀ c : S.Colour, Obj.nil (S.colourSrc c) ⟶ ⟨S.colourSrc c, [c, D.dual c]⟩
  /-- The counit of `c ⊣ c*`. -/
  cap : ∀ c : S.Colour, (⟨S.colourTgt c, [D.dual c, c]⟩ : Obj S) ⟶ Obj.nil (S.colourTgt c)
  /-- The unit of `c* ⊣ c`. -/
  cup' : ∀ c : S.Colour, Obj.nil (S.colourTgt c) ⟶ ⟨S.colourTgt c, [D.dual c, c]⟩
  /-- The counit of `c* ⊣ c`. -/
  cap' : ∀ c : S.Colour, (⟨S.colourSrc c, [c, D.dual c]⟩ : Obj S) ⟶ Obj.nil (S.colourSrc c)
  left_zigzag : ∀ c, P.diag (P.leftZigzagD (P.colourHom c) (P.dualColourHom D c) (cup c) (cap c)) = 𝟙 _
  right_zigzag : ∀ c,
    P.diag (P.rightZigzagD (P.colourHom c) (P.dualColourHom D c) (cup c) (cap c)) = 𝟙 _
  left_zigzag' : ∀ c,
    P.diag (P.leftZigzagD (P.dualColourHom D c) (P.colourHom c) (cup' c) (cap' c)) = 𝟙 _
  right_zigzag' : ∀ c,
    P.diag (P.rightZigzagD (P.dualColourHom D c) (P.colourHom c) (cup' c) (cap' c)) = 𝟙 _

variable {P D}

omit [S.IsEven] in
theorem obj_eq_of_word_eq_singleton (x : l ⟶ m) {c : S.Colour} (hx : x.obj.word = [c]) :
    x.obj = ⟨S.colourSrc c, [c]⟩ := by
  have h := x.wf
  rw [Obj.WF, hx] at h
  exact Obj.ext h.1.symm hx

omit [S.IsEven] in
theorem dualHom_obj_eq_of_word_eq_singleton (x : l ⟶ m) {c : S.Colour} (hx : x.obj.word = [c]) :
    (P.dualHom D x).obj = ⟨S.colourTgt c, [D.dual c]⟩ := by
  have h := x.endR_eq
  rw [obj_eq_of_word_eq_singleton x hx] at h
  exact Obj.ext h.symm (by simp [hx])

/-- The biadjunctions of all colours, at every placement, given by chosen cups and caps. -/
def ColourCupsCaps.biadjunctions (Q : ColourCupsCaps P D) : ColourBiadjunctions P D :=
  fun {l m} x c hx =>
    have hx₁ := obj_eq_of_word_eq_singleton x hx
    have hy₁ := dualHom_obj_eq_of_word_eq_singleton (P := P) (D := D) x hx
    have hl : Obj.nil (S.colourSrc c) = Obj.nil l.region := by
      rw [← x.start_eq, hx₁]
    have hm : Obj.nil (S.colourTgt c) = Obj.nil m.region := by
      rw [← (P.dualHom D x).start_eq, hy₁]
    have hxy : (⟨S.colourSrc c, [c, D.dual c]⟩ : Obj S) = x.obj.tensor (P.dualHom D x).obj := by
      rw [hx₁, hy₁]; rfl
    have hyx : (⟨S.colourTgt c, [D.dual c, c]⟩ : Obj S) = (P.dualHom D x).obj.tensor x.obj := by
      rw [hx₁, hy₁]; rfl
    biadjunctionOfZigzag x (P.dualHom D x)
      (Diagram.cast (Q.cup c) hl hxy) (Diagram.cast (Q.cap c) hyx hm)
      (diag_eq_id_of_layers _ _ hx₁
        (by
          simp only [Diagram.layers_leftZigzag, Diagram.layers_cast]
          rw [hx₁])
        (Q.left_zigzag c))
      (diag_eq_id_of_layers _ _ hy₁
        (by
          simp only [Diagram.layers_rightZigzag, Diagram.layers_cast]
          rw [hy₁])
        (Q.right_zigzag c))
      (Diagram.cast (Q.cup' c) hm hyx) (Diagram.cast (Q.cap' c) hxy hl)
      (diag_eq_id_of_layers _ _ hy₁
        (by
          simp only [Diagram.layers_leftZigzag, Diagram.layers_cast]
          rw [hy₁])
        (Q.left_zigzag' c))
      (diag_eq_id_of_layers _ _ hx₁
        (by
          simp only [Diagram.layers_rightZigzag, Diagram.layers_cast]
          rw [hx₁])
        (Q.right_zigzag' c))

end CupsCaps

section Single

variable {P} {D : S.ColourDuality} (B : ColourBiadjunctions P D)

theorem colourBiadjunctions_heq {l m : P.Bicat} {z z' : l ⟶ m} (h : z = z') (c : S.Colour)
    (hc : z.obj.word = [c]) (hc' : z'.obj.word = [c]) : HEq (B z c hc) (B z' c hc') := by
  subst h; rfl

/-- The biadjunction of a one-letter word is the chosen biadjunction of the colour, up to
unitors. -/
theorem isCyclic_biadj_single {l m : P.Bicat} (x : l ⟶ m) (c : S.Colour) (hx : x.obj.word = [c]) :
    Biadjunction.IsCyclic (biadj B x) (B x c hx) (𝟙 x) := by
  obtain ⟨m⟩ := m
  have hm : S.colourTgt c = m := by
    have := x.endR_eq; rw [Obj.endR, hx] at this; exact this
  subst hm
  rw [← biadjW_eq B [c] x hx]
  simp only [biadjW]
  rw [show nilBiadj (D := D) (P.tailHom x c [] hx) rfl = Biadjunction.id _ from nilBiadj_id _ _]
  have hhx : P.headHom x c [] hx = x := Bicat.Hom.ext (Obj.ext x.start_eq.symm hx.symm)
  have k₀ := isCyclic_eqToHom (P.headHom_comp_tailHom x c [] hx).symm
    (P.dualHom_tail_comp_head D x c [] hx).symm
    (Biadjunction.congr_heq ((B (P.headHom x c [] hx) c rfl).comp (Biadjunction.id _))
      (P.headHom_comp_tailHom x c [] hx) (P.dualHom_tail_comp_head D x c [] hx))
  have k₁ := isCyclic_rightUnitor_hom (B (P.headHom x c [] hx) c rfl)
  have k₂ := isCyclic_eqToHom hhx (congrArg (P.dualHom D ·) hhx)
    (colourBiadjunctions_heq B hhx c rfl hx)
  convert k₀.comp (k₁.comp k₂) using 1
  simp [Strict.rightUnitor_eqToIso]

end Single

/-! ## Generators as 2-morphisms of the presented bicategory -/

section Generators

variable {P}

omit [S.IsEven] in
/-- The boundaries of a generator are well formed. -/
structure _root_.StringDiagrams.Signature.GenValid (S : Signature.{u₀, u₁, u₂}) (g : S.Gen) :
    Prop where
  dom_ok : S.ok (S.left g) (S.dom g)
  dom_end : S.endR (S.left g) (S.dom g) = S.right g
  cod_ok : S.ok (S.left g) (S.cod g)
  cod_end : S.endR (S.left g) (S.cod g) = S.right g

omit [S.IsEven] in
theorem _root_.StringDiagrams.Layer.Valid.genValid {L : Layer S} (hv : L.Valid) :
    S.GenValid L.gen :=
  ⟨hv.dom_ok, hv.dom_end, hv.cod_ok, hv.cod_end⟩

variable (P)

/-- The bottom boundary of a generator, as a 1-morphism of `P.Bicat`. -/
def genDom (g : S.Gen) (hg : S.GenValid g) : (⟨S.left g⟩ : P.Bicat) ⟶ ⟨S.right g⟩ :=
  ⟨⟨S.left g, S.dom g⟩, rfl, hg.dom_ok, hg.dom_end⟩

/-- The top boundary of a generator, as a 1-morphism of `P.Bicat`. -/
def genCod (g : S.Gen) (hg : S.GenValid g) : (⟨S.left g⟩ : P.Bicat) ⟶ ⟨S.right g⟩ :=
  ⟨⟨S.left g, S.cod g⟩, rfl, hg.cod_ok, hg.cod_end⟩

omit [S.IsEven] in
theorem _root_.StringDiagrams.Signature.GenValid.layer_valid {g : S.Gen} (hg : S.GenValid g) :
    (⟨S.left g, [], g, []⟩ : Layer S).Valid :=
  ⟨trivial, rfl, hg.dom_ok, hg.dom_end, hg.cod_ok, hg.cod_end, trivial⟩

/-- A generator on its own, as a diagram. -/
def genDiag (g : S.Gen) (hg : S.GenValid g) :
    (⟨S.left g, S.dom g⟩ : Obj S) ⟶ ⟨S.left g, S.cod g⟩ :=
  Diagram.layer ⟨S.left g, [], g, []⟩ hg.layer_valid (by simp [Layer.dom]) (by simp [Layer.cod])

/-- A generator as a 2-morphism of `P.Bicat`. -/
def gen2 (g : S.Gen) (hg : S.GenValid g) : P.genDom g hg ⟶ P.genCod g hg :=
  P.diag (genDiag g hg)

variable {P}

omit [S.IsEven] in
theorem hom_eq_zero_of_isEmpty {a b : Obj S} (h : IsEmpty (a ⟶ b)) (f : P.obj a ⟶ P.obj b) :
    f = 0 := by
  induction f using P.hom_induction with
  | diag d => exact (h.false d).elim
  | zero => rfl
  | add f g hf hg => rw [hf, hg, add_zero]
  | smul r f hf => rw [hf, smul_zero]

/-- A single layer is a whiskered generator, up to the identifications of the boundaries. -/
theorem diag_ofLayer_eq {l m : P.Bicat} (L : Layer S) (hv : L.Valid) (x x' : l ⟶ m)
    (hx : x.obj = L.dom) (hx' : x'.obj = L.cod) (u : l ⟶ ⟨S.left L.gen⟩)
    (hu : u.obj = ⟨l.region, L.left⟩) (v : (⟨S.right L.gen⟩ : P.Bicat) ⟶ m)
    (hv' : v.obj = ⟨S.right L.gen, L.right⟩)
    (h₁ : x = u ≫ (P.genDom L.gen hv.genValid ≫ v))
    (h₂ : x' = u ≫ (P.genCod L.gen hv.genValid ≫ v)) :
    Bicat.homOf (eqToHom (congrArg P.obj hx) ≫ P.diag (Diagram.ofLayer L hv) ≫
        eqToHom (congrArg P.obj hx'.symm)) =
      eqToHom h₁ ≫ u ◁ (P.gen2 L.gen hv.genValid ▷ v) ≫ eqToHom h₂.symm := by
  have hs : L.start = l.region := by
    have := x.start_eq; rw [hx] at this; exact this
  rw [Bicat.eqToHom_eq, Bicat.eqToHom_eq, Bicat.whiskerLeft_eq, Bicat.whiskerRight_eq]
  change eqToHom _ ≫ P.diag _ ≫ eqToHom _ = eqToHom _ ≫
    P.wL u.obj (P.wRAt _ (P.diag (genDiag L.gen hv.genValid)) v.obj _ _) ≫ eqToHom _
  rw [P.wRAt_diag _ _ (Bicat.Hom.composable (P.genDom L.gen hv.genValid) v),
    P.wL_diag_of_composable _ _ (Bicat.Hom.composable u (P.genDom L.gen hv.genValid ≫ v))]
  simp only [P.eqToHom_obj, ← P.diag_comp]
  apply P.diag_eq_of_layers_eq
  simp only [Diagram.layers_comp, Diagram.layers_eqToHom, Diagram.layers_ofLayer,
    Diagram.layers_lwhisker, Diagram.layers_rwhisker, genDiag, Diagram.layers_layer,
    List.map_cons, List.map_nil, List.nil_append, List.append_nil, hu, hv']
  congr 1
  exact Layer.ext hs (by simp [Layer.wl, Layer.wr]) rfl (by simp [Layer.wl, Layer.wr])

end Generators

/-! ## Cyclicity of all 2-morphisms -/

section Cyclic

variable {P} {D : S.ColourDuality} (B : ColourBiadjunctions P D)

theorem isCyclic_layer
    (hgen : ∀ (g : S.Gen) (hg : S.GenValid g),
      Biadjunction.IsCyclic (biadj B (P.genDom g hg)) (biadj B (P.genCod g hg)) (P.gen2 g hg))
    (L : Layer S) (hv : L.Valid) {l m : P.Bicat} (x x' : l ⟶ m) (hx : x.obj = L.dom)
    (hx' : x'.obj = L.cod) :
    Biadjunction.IsCyclic (biadj B x) (biadj B x')
      (Bicat.homOf (eqToHom (congrArg P.obj hx) ≫ P.diag (Diagram.ofLayer L hv) ≫
        eqToHom (congrArg P.obj hx'.symm))) := by
  have hs : L.start = l.region := by
    have := x.start_eq; rw [hx] at this; exact this
  have he : S.endR (S.right L.gen) L.right = m.region := by
    have := x.endR_eq; rw [hx, hv.endR_dom] at this; exact this
  let u : l ⟶ ⟨S.left L.gen⟩ :=
    ⟨⟨l.region, L.left⟩, rfl, by rw [← hs]; exact hv.left_ok,
      by show S.endR l.region L.left = _; rw [← hs]; exact hv.left_end⟩
  let v : (⟨S.right L.gen⟩ : P.Bicat) ⟶ m := ⟨⟨S.right L.gen, L.right⟩, rfl, hv.right_ok, he⟩
  have h₁ : x = u ≫ (P.genDom L.gen hv.genValid ≫ v) :=
    Bicat.Hom.ext (hx.trans (Obj.ext hs (by simp only [Layer.dom_word, List.append_assoc]; rfl)))
  have h₂ : x' = u ≫ (P.genCod L.gen hv.genValid ≫ v) :=
    Bicat.Hom.ext (hx'.trans (Obj.ext hs (by simp only [Layer.cod_word, List.append_assoc]; rfl)))
  rw [diag_ofLayer_eq L hv x x' hx hx' u rfl v rfl h₁ h₂]
  have c₂ := ((hgen L.gen hv.genValid).whiskerRight (biadj B v)).whiskerLeft (biadj B u)
  have k₁ := (isCyclic_biadj_eqToHom B h₁).comp ((isCyclic_biadj_comp_symm B u _).comp
    ((isCyclic_biadj_comp_symm B (P.genDom L.gen hv.genValid) v).whiskerLeft (biadj B u)))
  have k₂ := ((isCyclic_biadj_comp B (P.genCod L.gen hv.genValid) v).whiskerLeft
    (biadj B u)).comp ((isCyclic_biadj_comp B u _).comp (isCyclic_biadj_eqToHom B h₂.symm))
  convert k₁.comp (c₂.comp k₂) using 1
  simp

/-- **Rotation invariance.** If every generator is cyclic for the biadjunctions of its
boundary words, then every 2-morphism of the presented bicategory is cyclic for the
biadjunctions of its boundary words. -/
theorem isCyclic_of_generators
    (hgen : ∀ (g : S.Gen) (hg : S.GenValid g),
      Biadjunction.IsCyclic (biadj B (P.genDom g hg)) (biadj B (P.genCod g hg)) (P.gen2 g hg))
    {l m : P.Bicat} {x x' : l ⟶ m} (θ : x ⟶ x') : Biadjunction.IsCyclic (biadj B x) (biadj B x') θ := by
  let p : ∀ {a b : Obj S}, (P.obj a ⟶ P.obj b) → Prop := fun {a b} f =>
    ∀ (l m : P.Bicat) (x x' : l ⟶ m) (hx : x.obj = a) (hx' : x'.obj = b),
      Biadjunction.IsCyclic (biadj B x) (biadj B x')
        (Bicat.homOf (eqToHom (congrArg P.obj hx) ≫ f ≫ eqToHom (congrArg P.obj hx'.symm)))
  have key : p θ := by
    refine P.hom_induction_layers (p := p) ?_ ?_ ?_ ?_ ?_ ?_ θ
    · intro a b h l m y y' hy hy'
      subst h hy
      obtain rfl : y' = y := Bicat.Hom.ext hy'
      convert isCyclic_id (biadj B y') using 1
      simp [P.diag_eqToHom]
      rfl
    · intro L hv l m y y' hy hy'
      exact isCyclic_layer B hgen L hv y y' hy hy'
    · intro a b c f g hf hg l m x x' hx hx'
      by_cases hb : ∃ y : l ⟶ m, y.obj = b
      · obtain ⟨y, hy⟩ := hb
        convert (hf l m x y hx hy).comp (hg l m y x' hy hx') using 1
        rw [Bicat.homOf_comp]
        congr 1
        simp
      · have hf0 : f = 0 := hom_eq_zero_of_isEmpty ⟨fun d => hb
          ⟨⟨b, ((Diagram.chain d).start_eq.trans (hx ▸ x.start_eq)),
            (Diagram.chain d).wf (hx ▸ x.wf),
            ((Diagram.chain d).endR_eq.trans (hx ▸ x.endR_eq))⟩, rfl⟩⟩ f
        subst hf0
        convert isCyclic_zero (biadj B x) (biadj B x') using 1
        simp
    · intro a b l m x x' hx hx'
      convert isCyclic_zero (biadj B x) (biadj B x') using 1
      simp
    · intro a b f g hf hg l m x x' hx hx'
      convert (hf l m x x' hx hx').add (hg l m x x' hx hx') using 1
      simp only [Preadditive.add_comp, Preadditive.comp_add]
    · intro a b r f hf l m x x' hx hx'
      convert (hf l m x x' hx hx').smul r using 1
      simp only [Linear.smul_comp, Linear.comp_smul]
  simpa using key l m x x' rfl rfl

end Cyclic

end Presentation

end StringDiagrams
