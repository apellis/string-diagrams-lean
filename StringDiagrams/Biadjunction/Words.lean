import StringDiagrams.Biadjunction.Basic
import StringDiagrams.Biadjunction.Zigzag

noncomputable section

namespace StringDiagrams

open CategoryTheory Bicategory

universe w v u₀ u₁ u₂

variable {S : Signature.{u₀, u₁, u₂}} {R : Type w} [CommRing R]

/-- A duality on the colours of a signature, compatible with regions: the dual `c*` of a colour
`c` runs from the right region of `c` to its left region. -/
structure Signature.ColourDuality (S : Signature.{u₀, u₁, u₂}) where
  /-- The dual colour. -/
  dual : S.Colour → S.Colour
  /-- The left region of `c*` is the right region of `c`. -/
  src_dual : ∀ c, S.colourSrc (dual c) = S.colourTgt c
  /-- The right region of `c*` is the left region of `c`. -/
  tgt_dual : ∀ c, S.colourTgt (dual c) = S.colourSrc c

namespace Signature.ColourDuality

variable (D : S.ColourDuality)

/-- The dual `w* = c_k* ⋯ c_1*` of a word `w = c_1 ⋯ c_k`. -/
def dualWord : List S.Colour → List S.Colour
  | [] => []
  | c :: w => dualWord w ++ [D.dual c]

@[simp] theorem dualWord_nil : D.dualWord [] = [] := rfl

@[simp] theorem dualWord_cons (c : S.Colour) (w : List S.Colour) :
    D.dualWord (c :: w) = D.dualWord w ++ [D.dual c] := rfl

theorem dualWord_eq (w : List S.Colour) : D.dualWord w = (w.map D.dual).reverse := by
  induction w with
  | nil => rfl
  | cons c w ih => simp [ih]

@[simp] theorem dualWord_append (u w : List S.Colour) :
    D.dualWord (u ++ w) = D.dualWord w ++ D.dualWord u := by
  simp [dualWord_eq]

theorem ok_dualWord (r : S.Region) (w : List S.Colour) (h : S.ok r w) :
    S.ok (S.endR r w) (D.dualWord w) ∧ S.endR (S.endR r w) (D.dualWord w) = r := by
  induction w generalizing r with
  | nil => exact ⟨trivial, rfl⟩
  | cons c w ih =>
    obtain ⟨hc, hw⟩ := h
    obtain ⟨ih₁, ih₂⟩ := ih _ hw
    simp only [Signature.endR_cons, dualWord_cons, Signature.ok_append, Signature.endR_append,
      ih₂, Signature.ok_cons, Signature.ok_nil, and_true, Signature.endR_nil, D.src_dual,
      D.tgt_dual, hc]
    exact ih₁

end Signature.ColourDuality

namespace Presentation

variable (P : Presentation.{w, v} S R) (D : S.ColourDuality)

/-- The word `w`, read from the region `r`, as a 1-morphism of `P.Bicat`. -/
def wordHom (r : S.Region) (w : List S.Colour) (h : S.ok r w) :
    (⟨r⟩ : P.Bicat) ⟶ ⟨S.endR r w⟩ :=
  ⟨⟨r, w⟩, rfl, h, rfl⟩

/-- The dual word `w*` as a 1-morphism of `P.Bicat`, in the opposite direction. -/
def dualWordHom (r : S.Region) (w : List S.Colour) (h : S.ok r w) :
    (⟨S.endR r w⟩ : P.Bicat) ⟶ ⟨r⟩ :=
  ⟨⟨S.endR r w, D.dualWord w⟩, rfl, (D.ok_dualWord r w h).1, (D.ok_dualWord r w h).2⟩

/-- A single colour as a 1-morphism of `P.Bicat`. -/
abbrev colourHom (c : S.Colour) : (⟨S.colourSrc c⟩ : P.Bicat) ⟶ ⟨S.colourTgt c⟩ :=
  P.wordHom (S.colourSrc c) [c] ⟨rfl, trivial⟩

/-- The dual of a single colour as a 1-morphism of `P.Bicat`. -/
abbrev dualColourHom (c : S.Colour) : (⟨S.colourTgt c⟩ : P.Bicat) ⟶ ⟨S.colourSrc c⟩ :=
  P.dualWordHom D (S.colourSrc c) [c] ⟨rfl, trivial⟩

/-- The dual `x*` of a 1-morphism `x : l ⟶ m` of `P.Bicat`: the dual word, from `m` to `l`. -/
def dualHom {l m : P.Bicat} (x : l ⟶ m) : m ⟶ l :=
  ⟨⟨m.region, D.dualWord x.obj.word⟩, rfl,
    by
      have := (D.ok_dualWord _ _ x.wf).1
      rwa [← Obj.endR, x.endR_eq] at this,
    by
      have := (D.ok_dualWord _ _ x.wf).2
      rw [← Obj.endR, x.endR_eq] at this
      exact this.trans x.start_eq⟩

@[simp] theorem dualHom_obj {l m : P.Bicat} (x : l ⟶ m) :
    (P.dualHom D x).obj = ⟨m.region, D.dualWord x.obj.word⟩ := rfl

@[simp] theorem dualHom_comp {l m n : P.Bicat} (x : l ⟶ m) (y : m ⟶ n) :
    P.dualHom D (x ≫ y) = P.dualHom D y ≫ P.dualHom D x :=
  Bicat.Hom.ext (Obj.ext rfl (by
    show D.dualWord (x.obj.word ++ y.obj.word) = D.dualWord y.obj.word ++ D.dualWord x.obj.word
    simp))

/-- The first letter `c` of a 1-morphism `x : l ⟶ m` whose word is `c :: w`, as a 1-morphism
`l ⟶ c.tgt`. -/
def headHom {l m : P.Bicat} (x : l ⟶ m) (c : S.Colour) (w : List S.Colour)
    (hx : x.obj.word = c :: w) : l ⟶ ⟨S.colourTgt c⟩ :=
  ⟨⟨l.region, [c]⟩, rfl,
    ⟨by have := x.wf; rw [Obj.WF, hx, x.start_eq] at this; exact this.1, trivial⟩, rfl⟩

/-- The rest `w` of a 1-morphism `x : l ⟶ m` whose word is `c :: w`, as a 1-morphism
`c.tgt ⟶ m`. -/
def tailHom {l m : P.Bicat} (x : l ⟶ m) (c : S.Colour) (w : List S.Colour)
    (hx : x.obj.word = c :: w) : (⟨S.colourTgt c⟩ : P.Bicat) ⟶ m :=
  ⟨⟨S.colourTgt c, w⟩, rfl,
    by have := x.wf; rw [Obj.WF, hx] at this; exact this.2,
    by have := x.endR_eq; rw [Obj.endR, hx] at this; exact this⟩

theorem headHom_comp_tailHom {l m : P.Bicat} (x : l ⟶ m) (c : S.Colour) (w : List S.Colour)
    (hx : x.obj.word = c :: w) : P.headHom x c w hx ≫ P.tailHom x c w hx = x :=
  Bicat.Hom.ext (Obj.ext x.start_eq.symm (by
    show [c] ++ w = x.obj.word
    rw [hx]; rfl))

theorem dualHom_tail_comp_head {l m : P.Bicat} (x : l ⟶ m) (c : S.Colour) (w : List S.Colour)
    (hx : x.obj.word = c :: w) :
    P.dualHom D (P.tailHom x c w hx) ≫ P.dualHom D (P.headHom x c w hx) = P.dualHom D x := by
  rw [← dualHom_comp, headHom_comp_tailHom]

variable {P D} [S.IsEven]

/-- Transport of a biadjunction along equalities of 1-morphisms. -/
def _root_.StringDiagrams.Biadjunction.congr {B : Type*} [Bicategory B] {a b : B}
    {f f' : a ⟶ b} {g g' : b ⟶ a} (Q : f ⊣⊢ g) (hf : f = f') (hg : g = g') : f' ⊣⊢ g' :=
  hf ▸ hg ▸ Q

@[simp] theorem _root_.StringDiagrams.Biadjunction.congr_rfl {B : Type*} [Bicategory B]
    {a b : B} {f : a ⟶ b} {g : b ⟶ a} (Q : f ⊣⊢ g) : Q.congr rfl rfl = Q := rfl

/-- The biadjunction of a 1-morphism with the empty word (and its dual): all units and counits
are identities, retyped. -/
def nilBiadj {l m : P.Bicat} (x : l ⟶ m) (hx : x.obj.word = []) : x ⊣⊢ P.dualHom D x :=
  have hl : l = m := Bicat.ext (by
    have := x.endR_eq; rw [Obj.endR, hx, x.start_eq] at this; exact this)
  have e₁ : ∀ {a : Obj S} (h : a = a), P.diag (eqToHom h) = 𝟙 _ := fun h => by simp
  { left := adjunctionOfZigzag x (P.dualHom D x)
      (eqToHom (Obj.ext x.start_eq.symm (by simp [Obj.tensor, hx])))
      (eqToHom (Obj.ext rfl (by simp [Obj.tensor, hx])))
      (by rw [← P.diag_id]; exact P.diag_eq_of_layers_eq (by simp))
      (by rw [← P.diag_id]; exact P.diag_eq_of_layers_eq (by simp))
    right := adjunctionOfZigzag (P.dualHom D x) x
      (eqToHom (Obj.ext rfl (by simp [Obj.tensor, hx])))
      (eqToHom (Obj.ext (by exact x.start_eq) (by simp [Obj.tensor, hx])))
      (by rw [← P.diag_id]; exact P.diag_eq_of_layers_eq (by simp))
      (by rw [← P.diag_id]; exact P.diag_eq_of_layers_eq (by simp)) }

/-- Chosen biadjunctions `c ⊣⊢ c*` for all colours, at every placement: for every 1-morphism
`x` of `P.Bicat` whose word is a single colour `c`, a biadjunction `x ⊣⊢ x*`. -/
abbrev ColourBiadjunctions (P : Presentation.{w, v} S R) (D : S.ColourDuality) : Type _ :=
  ∀ {l m : P.Bicat} (x : l ⟶ m) (c : S.Colour), x.obj.word = [c] → (x ⊣⊢ P.dualHom D x)

variable (B : ColourBiadjunctions P D)

/-- The biadjunction `x ⊣⊢ x*` of a 1-morphism of `P.Bicat` whose word is `w`, composed from the
biadjunctions of its colours (`Biadjunction.comp`); its units and counits are nested cups and
caps. -/
def biadjW : (w : List S.Colour) → {l m : P.Bicat} → (x : l ⟶ m) → x.obj.word = w →
    (x ⊣⊢ P.dualHom D x)
  | [], _, _, x, hx => nilBiadj x hx
  | c :: w, _, _, x, hx =>
    ((B (P.headHom x c w hx) c rfl).comp (biadjW w (P.tailHom x c w hx) rfl)).congr
      (P.headHom_comp_tailHom x c w hx) (P.dualHom_tail_comp_head D x c w hx)

/-- The biadjunction `x ⊣⊢ x*` of an arbitrary 1-morphism of `P.Bicat`. -/
def biadj {l m : P.Bicat} (x : l ⟶ m) : x ⊣⊢ P.dualHom D x := biadjW B x.obj.word x rfl

end Presentation

end StringDiagrams
