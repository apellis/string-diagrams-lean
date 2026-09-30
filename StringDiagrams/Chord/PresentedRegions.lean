import StringDiagrams.Chord.Presented
import StringDiagrams.InterchangeLayers

/-!
# Chord diagrams in presented 2-categories with several regions

`StringDiagrams.Chord.Presented` interprets chord diagrams in the presented category of a
signature with a single region, cups and crossings being single generators. Here the signature
`S` may have several regions, and cups and crossings may be diagrams.

* **Letters** (`Letters S α`): a letter `a : α` with the region `ρ` on its right is the colour
  `col a ρ` (with target region `ρ`). A word `l` of letters with the region `ρ` on its right is
  the object `Letters.obj ρ l` of the free 2-category; its regions are determined by `ρ` and the
  letters.
* **Cups and crossings** (`RegionChordGens Λ d`): for every region `ρ`, chains of layers
  `cup ρ a` from `obj ρ []` to `obj ρ [a, d a]` and `cross ρ a b` from `obj ρ [a, b]` to
  `obj ρ [b, a]`, all of whose generators are even.

For a region `ρ` a chord diagram with boundary word `l` is interpreted in `P.Presented`
(`RegionChordGens.interp`): `l` goes to `obj ρ l`, a cup or crossing to the corresponding
chain of layers, whiskered by the letters to its left and right (with the appropriate regions).
Distant commutations of moves hold exactly (`RegionChordGens.near_sep`, by the interchange
law `Presentation.diag_interchange_layers_of_even`). For a filtration `Q` of the presented
category (`LayerFiltration`) such that cups have total weight `0` and crossings total weight `1`,
the braid relation on three strands modulo `Q.sub 3` and the pitchfork move on one strand modulo
`Q.sub 1`, **in every region**, imply that the chord moves hold in every position modulo lower
order terms (`RegionChordGens.respects`), whence the normal form
(`RegionChordGens.near_canon_or_reducible`).

In a monoidal signature, cups and crossings given by single generators (`ChordGens`) are an
instance (`ChordGens.toRegion`).
-/

noncomputable section

namespace StringDiagrams.Chord

open CategoryTheory

universe w v u₀ u₁ u₂

variable {S : Signature.{u₀, u₁, u₂}} {α : Type*}

/-! ## Letters acting on regions -/

/-- Letters labelling the strands of a signature: the letter `a` with the region `ρ` on its
right is the colour `col a ρ`. -/
structure Letters (S : Signature.{u₀, u₁, u₂}) (α : Type*) where
  /-- The colour of the letter `a` with the region `ρ` on its right. -/
  col : α → S.Region → S.Colour
  col_tgt : ∀ a ρ, S.colourTgt (col a ρ) = ρ

namespace Letters

variable (Λ : Letters S α)

/-- The region on the left of the word `l` with the region `ρ` on its right. -/
def lreg (ρ : S.Region) : List α → S.Region
  | [] => ρ
  | a :: l => S.colourSrc (Λ.col a (lreg ρ l))

/-- The colours of the word `l` with the region `ρ` on its right. -/
def word (ρ : S.Region) : List α → List S.Colour
  | [] => []
  | a :: l => Λ.col a (Λ.lreg ρ l) :: word ρ l

/-- The object of the word `l` with the region `ρ` on its right. -/
def obj (ρ : S.Region) (l : List α) : Obj S := ⟨Λ.lreg ρ l, Λ.word ρ l⟩

@[simp] theorem lreg_nil (ρ : S.Region) : Λ.lreg ρ [] = ρ := rfl
@[simp] theorem word_nil (ρ : S.Region) : Λ.word ρ [] = [] := rfl
@[simp] theorem lreg_cons (ρ : S.Region) (a : α) (l : List α) :
    Λ.lreg ρ (a :: l) = S.colourSrc (Λ.col a (Λ.lreg ρ l)) := rfl
@[simp] theorem word_cons (ρ : S.Region) (a : α) (l : List α) :
    Λ.word ρ (a :: l) = Λ.col a (Λ.lreg ρ l) :: Λ.word ρ l := rfl
@[simp] theorem obj_start (ρ : S.Region) (l : List α) : (Λ.obj ρ l).start = Λ.lreg ρ l := rfl
@[simp] theorem obj_word (ρ : S.Region) (l : List α) : (Λ.obj ρ l).word = Λ.word ρ l := rfl

@[simp] theorem lreg_append (ρ : S.Region) (l t : List α) :
    Λ.lreg ρ (l ++ t) = Λ.lreg (Λ.lreg ρ t) l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

@[simp] theorem word_append (ρ : S.Region) (l t : List α) :
    Λ.word ρ (l ++ t) = Λ.word (Λ.lreg ρ t) l ++ Λ.word ρ t := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

@[simp] theorem length_word (ρ : S.Region) (l : List α) : (Λ.word ρ l).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem ok_word (ρ : S.Region) (l : List α) : S.ok (Λ.lreg ρ l) (Λ.word ρ l) := by
  induction l with
  | nil => trivial
  | cons a l ih => exact ⟨rfl, by rw [Λ.col_tgt]; exact ih⟩

theorem endR_word (ρ : S.Region) (l : List α) : S.endR (Λ.lreg ρ l) (Λ.word ρ l) = ρ := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [word_cons, lreg_cons, Signature.endR_cons, Λ.col_tgt, ih]

theorem obj_ok (ρ : S.Region) (l : List α) : (Λ.obj ρ l).Ok := Λ.ok_word ρ l

@[simp] theorem obj_endR (ρ : S.Region) (l : List α) : (Λ.obj ρ l).endR = ρ := Λ.endR_word ρ l

/-- A word with a subword `w` is the subword whiskered by the letters on either side. -/
theorem obj_append3 (ρ : S.Region) (u w t : List α) :
    Λ.obj ρ (u ++ w ++ t) =
      (Λ.obj (Λ.lreg ρ t) w).whisker (Λ.obj (Λ.lreg ρ (w ++ t)) u) (Λ.word ρ t) := by
  simp [obj, Obj.whisker]

theorem whiskerOK (ρ : S.Region) (u w t : List α) :
    (Λ.obj (Λ.lreg ρ t) w).WhiskerOK (Λ.obj (Λ.lreg ρ (w ++ t)) u) (Λ.word ρ t) :=
  ⟨Λ.ok_word _ _, by simp [Obj.endR, endR_word], by rw [obj_endR]; exact Λ.ok_word ρ t⟩

end Letters

/-! ## Cups and crossings given by diagrams -/

/-- Cups and crossings in a signature whose strands are labelled by letters `Λ`, with the dual
letter `d a` for the right leg of a cup: for every region `ρ` (on the right), chains of layers
`cup ρ a : obj ρ [] ⟶ obj ρ [a, d a]` and `cross ρ a b : obj ρ [a, b] ⟶ obj ρ [b, a]`, all of
whose generators are even. -/
structure RegionChordGens (Λ : Letters S α) (d : α → α) where
  /-- The layers of the cup with left leg `a`. -/
  cup : S.Region → α → List (Layer S)
  /-- The layers of the crossing of `a` (bottom left) and `b` (bottom right). -/
  cross : S.Region → α → α → List (Layer S)
  chain_cup : ∀ ρ a, Chain (Λ.obj ρ []) (cup ρ a) (Λ.obj ρ [a, d a])
  chain_cross : ∀ ρ a b, Chain (Λ.obj ρ [a, b]) (cross ρ a b) (Λ.obj ρ [b, a])
  cup_even : ∀ ρ a, ∀ L ∈ cup ρ a, S.odd L.gen = false
  cross_even : ∀ ρ a b, ∀ L ∈ cross ρ a b, S.odd L.gen = false

namespace RegionChordGens

variable {Λ : Letters S α} {d : α → α} (G : RegionChordGens Λ d)

include G in
theorem lreg_cup (ρ : S.Region) (a : α) : Λ.lreg ρ [a, d a] = ρ :=
  (G.chain_cup ρ a).start_eq

include G in
/-- `lreg_cup` in simp normal form. -/
@[simp] theorem src_cup (ρ : S.Region) (a : α) :
    S.colourSrc (Λ.col a (S.colourSrc (Λ.col (d a) ρ))) = ρ :=
  G.lreg_cup ρ a

include G in
theorem lreg_cross (ρ : S.Region) (a b : α) : Λ.lreg ρ [b, a] = Λ.lreg ρ [a, b] :=
  (G.chain_cross ρ a b).start_eq

/-- The layers of a move applied to the word `l` with the region `ρ` on its right (no layers
for a crossing out of range). -/
def moveLayers (ρ : S.Region) (l : List α) : Move α → List (Layer S)
  | .cup g a => (G.cup (Λ.lreg ρ (l.drop g)) a).map
      (·.whisker (Λ.obj (Λ.lreg ρ (l.drop g)) (l.take g)) (Λ.word ρ (l.drop g)))
  | .cross p =>
    if h : p + 1 < l.length then
      (G.cross (Λ.lreg ρ (l.drop (p + 2))) l[p] l[p + 1]).map
        (·.whisker (Λ.obj (Λ.lreg ρ (l.drop p)) (l.take p)) (Λ.word ρ (l.drop (p + 2))))
    else []

theorem moveLayers_cup (ρ : S.Region) (u t : List α) (a : α) {g : ℕ} (hg : u.length = g) :
    G.moveLayers ρ (u ++ t) (.cup g a) =
      (G.cup (Λ.lreg ρ t) a).map (·.whisker (Λ.obj (Λ.lreg ρ t) u) (Λ.word ρ t)) := by
  subst hg; simp [moveLayers]

theorem moveLayers_cross (ρ : S.Region) (u : List α) (x y : α) (t : List α) {p : ℕ}
    (hp : u.length = p) :
    G.moveLayers ρ (u ++ x :: y :: t) (.cross p) =
      (G.cross (Λ.lreg ρ t) x y).map
        (·.whisker (Λ.obj (Λ.lreg ρ (x :: y :: t)) u) (Λ.word ρ t)) := by
  subst hp
  have h : u.length + 1 < (u ++ x :: y :: t).length := by simp
  simp only [moveLayers, dite_eq_left h]
  have e₁ : (u ++ x :: y :: t).drop (u.length + 2) = t := by
    rw [show u.length + 2 = u.length + 2 from rfl, List.drop_length_add_append]; rfl
  have e₂ : (u ++ x :: y :: t)[u.length] = x := by simp
  have e₃ : (u ++ x :: y :: t)[u.length + 1] = y := by simp [List.getElem_append_right]
  rw [e₁, e₂, e₃]
  simp

theorem chain_moveLayers (ρ : S.Region) (l : List α) (m : Move α) :
    Chain (Λ.obj ρ l) (G.moveLayers ρ l m) (Λ.obj ρ (lstep d l m)) := by
  cases m with
  | cup g a =>
    by_cases hg : g ≤ l.length
    · obtain ⟨u, t, rfl, rfl⟩ := exists_eq_append hg
      rw [G.moveLayers_cup ρ u t a rfl, lstep_cup_append]
      have hc := (G.chain_cup (Λ.lreg ρ t) a).whisker (Λ.whiskerOK ρ u [] t)
      refine hc.congr ?_ ?_
      · simpa using (Λ.obj_append3 ρ u [] t).symm
      · rw [show u ++ a :: d a :: t = u ++ [a, d a] ++ t by simp, Λ.obj_append3]
        simp [G.src_cup]
    · -- a cup out of range is inserted at the end
      have hl : l.drop g = [] := List.drop_eq_nil_of_le (by omega)
      have ht : l.take g = l := List.take_of_length_le (by omega)
      simp only [moveLayers, hl, ht]
      have hs : lstep d l (.cup g a) = l ++ [a, d a] := by
        simp [lstep, insAt, hl, ht]
      rw [hs]
      have hc := (G.chain_cup ρ a).whisker (Λ.whiskerOK ρ l [] [])
      refine hc.congr ?_ ?_
      · simpa using (Λ.obj_append3 ρ l [] []).symm
      · rw [show l ++ [a, d a] = l ++ [a, d a] ++ [] by simp, Λ.obj_append3]
        simp [G.src_cup]
  | cross p =>
    by_cases h : p + 1 < l.length
    · obtain ⟨u, x, y, t, rfl, rfl⟩ := exists_eq_append_cons_cons h
      rw [G.moveLayers_cross ρ u x y t rfl, lstep_cross_append]
      have hc := (G.chain_cross (Λ.lreg ρ t) x y).whisker (Λ.whiskerOK ρ u [x, y] t)
      refine hc.congr ?_ ?_
      · rw [show u ++ x :: y :: t = u ++ [x, y] ++ t by simp, Λ.obj_append3]
      · rw [show u ++ y :: x :: t = u ++ [y, x] ++ t by simp, Λ.obj_append3,
          show [y, x] ++ t = [y, x] ++ t from rfl, Letters.lreg_append, Letters.lreg_append,
          G.lreg_cross]
    · simp only [moveLayers, dite_eq_right h]
      simp [lstep, swapAt_of_le l h]

include G in
/-- A move does not change the region on the left. -/
@[simp] theorem lreg_lstep (ρ : S.Region) (l : List α) (m : Move α) :
    Λ.lreg ρ (lstep d l m) = Λ.lreg ρ l :=
  (G.chain_moveLayers ρ l m).start_eq

/-- The layers of a diagram applied to the word `l` with the region `ρ` on its right. -/
def layersOf (ρ : S.Region) : List α → List (Move α) → List (Layer S)
  | _, [] => []
  | l, m :: D => G.moveLayers ρ l m ++ layersOf ρ (lstep d l m) D

theorem chain_layersOf (ρ : S.Region) (l : List α) (D : List (Move α)) :
    Chain (Λ.obj ρ l) (G.layersOf ρ l D) (Λ.obj ρ (D.foldl (lstep d) l)) := by
  induction D generalizing l with
  | nil => rfl
  | cons m D ih => exact (G.chain_moveLayers ρ l m).append (ih _)

theorem layersOf_pair (ρ : S.Region) (l : List α) (m₁ m₂ : Move α) :
    G.layersOf ρ l [m₁, m₂] = G.moveLayers ρ l m₁ ++ G.moveLayers ρ (lstep d l m₁) m₂ := by
  simp [layersOf]

variable {R : Type w} [CommRing R] (P : Presentation.{w, v} S R)

/-- The interpretation of chord diagrams in the presented category, for the region `ρ` on the
right: the word `l` goes to `obj ρ l`, and a move to its whiskered cup or crossing. -/
abbrev interp (ρ : S.Region) : MoveInterp d P.Presented where
  obj l := P.obj (Λ.obj ρ l)
  map l m := P.diag ⟨G.moveLayers ρ l m, G.chain_moveLayers ρ l m⟩

/-- The image of a chord diagram is the class of the diagram with its layers. -/
theorem eval_interp (ρ : S.Region) (l : List α) (D : List (Move α)) :
    (G.interp P ρ).eval l D = P.diag ⟨G.layersOf ρ l D, G.chain_layersOf ρ l D⟩ := by
  induction D generalizing l with
  | nil => exact (P.diag_id _).symm
  | cons m D ih =>
    rw [MoveInterp.eval_cons, ih]
    exact (P.diag_comp _ _).symm

/-- The image of a chord diagram, retyped, is the class of any diagram with its layers. -/
theorem eval_comp_eqToHom_eq (ρ : S.Region) {l : List α} {X Y : List (Move α)}
    (e : X.foldl (lstep d) l = Y.foldl (lstep d) l)
    (f : Λ.obj ρ l ⟶ Λ.obj ρ (Y.foldl (lstep d) l)) (hf : Diagram.layers f = G.layersOf ρ l X) :
    (G.interp P ρ).eval l X ≫ eqToHom (congrArg (G.interp P ρ).obj e) = P.diag f := by
  have key : ∀ (t : List α) (c : Chain (Λ.obj ρ l) (G.layersOf ρ l X) (Λ.obj ρ t))
      (e : t = Y.foldl (lstep d) l),
      P.diag ⟨G.layersOf ρ l X, c⟩ ≫ eqToHom (congrArg (G.interp P ρ).obj e) =
        P.diag ⟨G.layersOf ρ l X, e ▸ c⟩ := by
    intro t c e; subst e; simp
  rw [eval_interp, key _ _ e]
  obtain ⟨ls, hc⟩ := f
  simp only [Diagram.layers] at hf
  subst hf
  rfl

/-- To show that two chord diagrams have the same image, it suffices to compare classes of
diagrams with their layers. -/
theorem near_of_diag_eq (ρ : S.Region) (Φ : (G.interp P ρ).Filtration) {n : ℕ} {l : List α}
    {X Y : List (Move α)}
    (h : ∀ f₁ f₂ : Λ.obj ρ l ⟶ Λ.obj ρ (Y.foldl (lstep d) l),
      Diagram.layers f₁ = G.layersOf ρ l X → Diagram.layers f₂ = G.layersOf ρ l Y →
        P.diag f₁ = P.diag f₂) :
    Φ.Near n l X Y := by
  intro e
  rw [G.eval_comp_eqToHom_eq P ρ e ⟨G.layersOf ρ l X, e ▸ G.chain_layersOf ρ l X⟩ rfl,
    eval_interp, h _ ⟨G.layersOf ρ l Y, G.chain_layersOf ρ l Y⟩ rfl rfl, sub_self]
  exact zero_mem _

/-! ## Moves on a subword -/

theorem moveLayers_shift (ρ : S.Region) (u w t : List α) {m : Move α} (hm : m.Ok w.length) :
    G.moveLayers ρ (u ++ w ++ t) (m.shift u.length) =
      (G.moveLayers (Λ.lreg ρ t) w m).map
        (·.whisker (Λ.obj (Λ.lreg ρ (w ++ t)) u) (Λ.word ρ t)) := by
  cases m with
  | cup g a =>
    simp only [Move.Ok] at hm
    obtain ⟨w₁, w₂, rfl, rfl⟩ := exists_eq_append hm
    rw [show u ++ (w₁ ++ w₂) ++ t = (u ++ w₁) ++ (w₂ ++ t) by simp, Move.shift,
      G.moveLayers_cup _ _ _ _ (by simp), G.moveLayers_cup _ _ _ _ rfl]
    simp [Layer.whisker, Letters.obj, List.append_assoc]
  | cross p =>
    simp only [Move.Ok] at hm
    obtain ⟨w₁, x, y, w₂, rfl, rfl⟩ := exists_eq_append_cons_cons hm
    rw [show u ++ (w₁ ++ x :: y :: w₂) ++ t = (u ++ w₁) ++ x :: y :: (w₂ ++ t) by simp,
      Move.shift, G.moveLayers_cross _ _ _ _ _ (by simp), G.moveLayers_cross _ _ _ _ _ rfl]
    simp [Layer.whisker, Letters.obj, List.append_assoc]

theorem layersOf_shift (ρ : S.Region) (u t : List α) {w : List α} {D : List (Move α)}
    (hf : Fits w.length D) :
    G.layersOf ρ (u ++ w ++ t) (D.map (Move.shift u.length)) =
      (G.layersOf (Λ.lreg ρ t) w D).map
        (·.whisker (Λ.obj (Λ.lreg ρ (w ++ t)) u) (Λ.word ρ t)) := by
  induction D generalizing w with
  | nil => rfl
  | cons m D ih =>
    obtain ⟨hm, hf⟩ := hf
    rw [← length_lstep (d := d)] at hf
    simp only [List.map_cons, layersOf, List.map_append, G.moveLayers_shift ρ u w t hm,
      lstep_shift d u w t hm, ih hf]
    congr 3
    simp only [Letters.lreg_append, G.lreg_lstep]

theorem moveLayers_even (ρ : S.Region) (l : List α) (m : Move α) :
    ∀ L ∈ G.moveLayers ρ l m, S.odd L.gen = false := by
  intro L hL
  cases m with
  | cup g a =>
    obtain ⟨L', hL', rfl⟩ := List.mem_map.1 hL
    exact G.cup_even _ _ L' hL'
  | cross p =>
    simp only [moveLayers] at hL
    split_ifs at hL with h
    · obtain ⟨L', hL', rfl⟩ := List.mem_map.1 hL
      exact G.cross_even _ _ _ L' hL'
    · simp at hL

/-! ## Distant moves commute -/

/-- **Moves on disjoint subwords commute exactly** (the interchange law): for moves `m₁` on
`w₁` and `m₂` on `w₂` in the word `u ++ w₁ ++ mid ++ w₂ ++ t`, applying `m₁` and then `m₂`
or `m₂` and then `m₁` gives diagrams with the same image. -/
theorem diag_sep (ρ : S.Region) (u w₁ mid w₂ t : List α) {m₁ m₂ : Move α}
    (h₁ : m₁.Ok w₁.length) (h₂ : m₂.Ok w₂.length) {l : List α}
    (hl : l = u ++ w₁ ++ mid ++ w₂ ++ t) {X Y : List (Move α)}
    (hX : X = [m₁.shift u.length, m₂.shift (u ++ lstep d w₁ m₁ ++ mid).length])
    (hY : Y = [m₂.shift (u ++ w₁ ++ mid).length, m₁.shift u.length]) {B : Obj S}
    (f₁ f₂ : Λ.obj ρ l ⟶ B) (hf₁ : Diagram.layers f₁ = G.layersOf ρ l X)
    (hf₂ : Diagram.layers f₂ = G.layersOf ρ l Y) :
    P.diag f₁ = P.diag f₂ := by
  subst hl hX hY
  -- the two pieces and their context
  have hF := G.chain_moveLayers (Λ.lreg ρ (mid ++ w₂ ++ t)) w₁ m₁
  have hG := G.chain_moveLayers (Λ.lreg ρ t) w₂ m₂
  let U := Λ.obj (Λ.lreg (Λ.lreg ρ (mid ++ w₂ ++ t)) w₁) u
  let M := Λ.word (Λ.lreg ρ (w₂ ++ t)) mid
  let V := Λ.word ρ t
  have hok : Presentation.SideBySideOK U M V (Λ.obj (Λ.lreg ρ (mid ++ w₂ ++ t)) w₁)
      (Λ.obj (Λ.lreg ρ t) w₂) := by
    refine .of_ok (Λ.ok_word _ _) (Λ.obj_ok _ _) ?_ (Λ.obj_ok _ _) ?_ ?_ ?_
    · rw [Letters.obj_endR]; simpa [M] using Λ.ok_word (Λ.lreg ρ (w₂ ++ t)) mid
    · rw [Letters.obj_endR]; exact Λ.ok_word ρ t
    · exact Λ.endR_word _ _
    · rw [Letters.obj_endR]; simpa [M] using Λ.endR_word (Λ.lreg ρ (w₂ ++ t)) mid
  have heven : ∀ L ∈ G.moveLayers (Λ.lreg ρ (mid ++ w₂ ++ t)) w₁ m₁,
      ∀ M ∈ G.moveLayers (Λ.lreg ρ t) w₂ m₂, S.odd L.gen = false ∨ S.odd M.gen = false :=
    fun L hL _ _ => Or.inl (G.moveLayers_even _ _ _ L hL)
  let g₁ := Diagram.mk _ ((Presentation.chain_leftLayers hF hok).append
    (Presentation.chain_rightLayers hG (hok.chain (G := []) hF rfl)))
  let g₂ := Diagram.mk _ ((Presentation.chain_rightLayers hG hok).append
    (Presentation.chain_leftLayers hF (hok.chain (F := []) rfl hG)))
  have key := P.diag_interchange_layers_of_even U M V hF hG heven hok g₁ g₂ rfl rfl
  have hA : Λ.obj ρ (u ++ w₁ ++ mid ++ w₂ ++ t) =
      Presentation.sbs U M V (Λ.obj (Λ.lreg ρ (mid ++ w₂ ++ t)) w₁) (Λ.obj (Λ.lreg ρ t) w₂) := by
    simp [U, M, V, Letters.obj]
  have e₁ : Diagram.layers f₁ = Diagram.layers g₁ := by
    rw [hf₁, layersOf_pair,
      show u ++ w₁ ++ mid ++ w₂ ++ t = u ++ w₁ ++ (mid ++ w₂ ++ t) by simp,
      lstep_shift d u w₁ _ h₁, G.moveLayers_shift ρ u w₁ _ h₁,
      show u ++ lstep d w₁ m₁ ++ (mid ++ w₂ ++ t) = (u ++ lstep d w₁ m₁ ++ mid) ++ w₂ ++ t by simp,
      G.moveLayers_shift ρ _ w₂ t h₂]
    simp [g₁, U, M, V, Letters.obj, Diagram.mk, Diagram.layers, Presentation.leftLayers,
      Presentation.rightLayers, G.lreg_lstep]
  have e₂ : Diagram.layers f₂ = Diagram.layers g₂ := by
    rw [hf₂, layersOf_pair,
      show u ++ w₁ ++ mid ++ w₂ ++ t = (u ++ w₁ ++ mid) ++ w₂ ++ t by simp,
      lstep_shift d _ w₂ t h₂, G.moveLayers_shift ρ _ w₂ t h₂,
      show u ++ w₁ ++ mid ++ lstep d w₂ m₂ ++ t = u ++ w₁ ++ (mid ++ lstep d w₂ m₂ ++ t) by simp,
      G.moveLayers_shift ρ u w₁ _ h₁]
    simp [g₂, U, M, V, Letters.obj, Diagram.mk, Diagram.layers, Presentation.leftLayers,
      Presentation.rightLayers, G.lreg_lstep]
  have hB : B = Presentation.sbs U M V (Λ.obj (Λ.lreg ρ (mid ++ w₂ ++ t)) (lstep d w₁ m₁))
      (Λ.obj (Λ.lreg ρ t) (lstep d w₂ m₂)) := by
    have c₁ := Diagram.chain f₁
    rw [e₁] at c₁
    exact Chain.target_unique c₁ ((Diagram.chain g₁).congr hA.symm rfl)
  exact P.diag_eq_of_diag_eq_of_layers f₁ f₂ g₁ g₂ hA hB e₁ e₂ key

variable (ρ : S.Region) (Φ : (G.interp P ρ).Filtration)

/-- Distant crossings commute. -/
theorem near_xx {n p p' : ℕ} (hp : p + 2 ≤ p') {l : List α}
    (hf : Fits l.length ([.cross p, .cross p'] : List (Move α))) :
    Φ.Near n l [.cross p, .cross p'] [.cross p', .cross p] := by
  have hl : p' + 1 < l.length := by simp [Fits, Move.Ok, Move.len] at hf; omega
  obtain ⟨u, x, y, t₀, rfl, rfl⟩ := exists_eq_append_cons_cons (show p + 1 < l.length by omega)
  obtain ⟨mid, z, w, t, rfl, hm⟩ :=
    exists_eq_append_cons_cons (show p' - u.length - 2 + 1 < t₀.length by simp at hl; omega)
  apply G.near_of_diag_eq P ρ
  intro f₁ f₂ h₁ h₂
  exact G.diag_sep P ρ u [x, y] mid [z, w] t (m₁ := .cross 0) (m₂ := .cross 0)
    (by simp [Move.Ok]) (by simp [Move.Ok]) (by simp)
    (by simp [Move.shift, lstep, swapAt]; omega) (by simp [Move.shift]; omega) f₁ f₂ h₁ h₂

/-- A crossing commutes with a cup to its right. -/
theorem near_xuL {n p g : ℕ} (a : α) (hp : p + 2 ≤ g) {l : List α}
    (hf : Fits l.length [.cross p, (.cup g a : Move α)]) :
    Φ.Near n l [.cross p, .cup g a] [.cup g a, .cross p] := by
  have hl : p + 1 < l.length ∧ g ≤ l.length := by simp [Fits, Move.Ok, Move.len] at hf; omega
  obtain ⟨u, x, y, t₀, rfl, rfl⟩ := exists_eq_append_cons_cons hl.1
  obtain ⟨mid, t, rfl, hm⟩ :=
    exists_eq_append (show g - u.length - 2 ≤ t₀.length by have := hl.2; simp at this; omega)
  apply G.near_of_diag_eq P ρ
  intro f₁ f₂ h₁ h₂
  exact G.diag_sep P ρ u [x, y] mid [] t (m₁ := .cross 0) (m₂ := .cup 0 a)
    (by simp [Move.Ok]) (by simp [Move.Ok]) (by simp)
    (by simp [Move.shift, lstep, swapAt]; omega) (by simp [Move.shift]; omega) f₁ f₂ h₁ h₂

/-- A crossing commutes with a cup to its left. -/
theorem near_xuR {n p g : ℕ} (a : α) (hg : g ≤ p) {l : List α}
    (hf : Fits l.length [.cross p, (.cup g a : Move α)]) :
    Φ.Near n l [.cross p, .cup g a] [.cup g a, .cross (p + 2)] := by
  have hl : p + 1 < l.length := by simp [Fits, Move.Ok, Move.len] at hf; omega
  obtain ⟨w₀, x, y, t, rfl, rfl⟩ := exists_eq_append_cons_cons hl
  obtain ⟨u, mid, rfl, rfl⟩ := exists_eq_append (show g ≤ w₀.length by omega)
  apply G.near_of_diag_eq P ρ
  intro f₁ f₂ h₁ h₂
  exact (G.diag_sep P ρ u [] mid [x, y] t (m₁ := .cup 0 a) (m₂ := .cross 0)
    (by simp [Move.Ok]) (by simp [Move.Ok]) (by simp)
    (by simp [Move.shift, lstep, insAt]; omega) (by simp [Move.shift]) f₂ f₁ h₂ h₁).symm

/-- Two cups commute. -/
theorem near_uu {n g g' : ℕ} (a b : α) (hg : g' ≤ g) {l : List α}
    (hf : Fits l.length [(.cup g a : Move α), .cup g' b]) :
    Φ.Near n l [.cup g a, .cup g' b] [.cup g' b, .cup (g + 2) a] := by
  have hl : g ≤ l.length := by simp [Fits, Move.Ok, Move.len] at hf; omega
  obtain ⟨w₀, t, rfl, rfl⟩ := exists_eq_append hl
  obtain ⟨u, mid, rfl, rfl⟩ := exists_eq_append hg
  apply G.near_of_diag_eq P ρ
  intro f₁ f₂ h₁ h₂
  exact (G.diag_sep P ρ u [] mid [] t (m₁ := .cup 0 b) (m₂ := .cup 0 a)
    (by simp [Move.Ok]) (by simp [Move.Ok]) (by simp)
    (by simp [Move.shift, lstep, insAt]; omega) (by simp [Move.shift]) f₂ f₁ h₂ h₁).symm

end RegionChordGens

/-! ## Filtrations -/

/-- The total weight of a list of layers. -/
def layerWeight (wt : S.Gen → ℕ) (ls : List (Layer S)) : ℕ := (ls.map fun L => wt L.gen).sum

@[simp] theorem layerWeight_nil (wt : S.Gen → ℕ) : layerWeight wt ([] : List (Layer S)) = 0 := rfl

@[simp] theorem layerWeight_cons (wt : S.Gen → ℕ) (L : Layer S) (ls : List (Layer S)) :
    layerWeight wt (L :: ls) = wt L.gen + layerWeight wt ls := by
  simp [layerWeight]

@[simp] theorem layerWeight_map_whisker (wt : S.Gen → ℕ) (ls : List (Layer S)) (u : Obj S)
    (v : List S.Colour) : layerWeight wt (ls.map (·.whisker u v)) = layerWeight wt ls := by
  simp [layerWeight, Layer.whisker, Function.comp_def]

namespace LayerFiltration

variable {R : Type w} [CommRing R] {P : Presentation.{w, v} S R} {wt : S.Gen → ℕ}
  (Q : LayerFiltration P wt)

/-- Precomposition with a diagram raises the order by its total weight. -/
theorem diag_comp_mem {n : ℕ} {a b c : Obj S} {ls : List (Layer S)} (h : Chain a ls b)
    {x : P.obj b ⟶ P.obj c} (hx : x ∈ Q.sub n b c) :
    P.diag ⟨ls, h⟩ ≫ x ∈ Q.sub (layerWeight wt ls + n) a c := by
  induction ls generalizing a with
  | nil =>
    obtain rfl : a = b := h
    rw [show (⟨[], rfl⟩ : a ⟶ a) = 𝟙 a from rfl, P.diag_id, Category.id_comp]; simpa using hx
  | cons L ls ih =>
    obtain ⟨hv, rfl, hc⟩ := h
    have e : (⟨L :: ls, hv, rfl, hc⟩ : L.dom ⟶ b) = Diagram.ofLayer L hv ≫ ⟨ls, hc⟩ := by
      ext; rfl
    rw [e, P.diag_comp, Category.assoc, layerWeight_cons, Nat.add_assoc]
    exact Q.layer_comp_mem hv (ih hc)

/-- Postcomposition with a diagram raises the order by its total weight. -/
theorem comp_diag_mem {n : ℕ} {a b c : Obj S} {ls : List (Layer S)} (h : Chain a ls b)
    {x : P.obj c ⟶ P.obj a} (hx : x ∈ Q.sub n c a) :
    x ≫ P.diag ⟨ls, h⟩ ∈ Q.sub (n + layerWeight wt ls) c b := by
  induction ls generalizing a n x with
  | nil =>
    obtain rfl : a = b := h
    rw [show (⟨[], rfl⟩ : a ⟶ a) = 𝟙 a from rfl, P.diag_id, Category.comp_id]; simpa using hx
  | cons L ls ih =>
    obtain ⟨hv, rfl, hc⟩ := h
    have e : (⟨L :: ls, hv, rfl, hc⟩ : L.dom ⟶ b) = Diagram.ofLayer L hv ≫ ⟨ls, hc⟩ := by
      ext; rfl
    rw [e, P.diag_comp, ← Category.assoc, layerWeight_cons, ← Nat.add_assoc]
    exact ih hc (Q.comp_layer_mem hv hx)

/-- Differences of diagrams with prescribed layers, between equal objects. -/
theorem sub_mem_of_layers {n : ℕ} {a b a' b' : Obj S} (ha : a = a') (hb : b = b')
    (f₁ f₂ : a ⟶ b) (g₁ g₂ : a' ⟶ b') (h₁ : Diagram.layers f₁ = Diagram.layers g₁)
    (h₂ : Diagram.layers f₂ = Diagram.layers g₂) (h : P.diag g₁ - P.diag g₂ ∈ Q.sub n a' b') :
    P.diag f₁ - P.diag f₂ ∈ Q.sub n a b := by
  subst ha hb
  rwa [P.diag_eq_of_layers_eq h₁, P.diag_eq_of_layers_eq h₂]

end LayerFiltration

namespace RegionChordGens

variable {Λ : Letters S α} {d : α → α} (G : RegionChordGens Λ d)
  {R : Type w} [CommRing R] {P : Presentation.{w, v} S R} {wt : S.Gen → ℕ}

theorem layerWeight_moveLayers (hcup : ∀ ρ a, layerWeight wt (G.cup ρ a) = 0)
    (hcross : ∀ ρ a b, layerWeight wt (G.cross ρ a b) = 1) (ρ : S.Region) {l : List α}
    {m : Move α} (hm : m.Ok l.length) : layerWeight wt (G.moveLayers ρ l m) = m.ncross := by
  cases m with
  | cup g a => simp [moveLayers, hcup, Move.ncross]
  | cross p =>
    simp only [Move.Ok] at hm
    simp [moveLayers, dite_eq_left hm, hcross, Move.ncross]

/-- The filtration of the interpretation of chord diagrams induced by a filtration of the
presented category, when cups have total weight `0` and crossings total weight `1`. -/
def toFiltration (ρ : S.Region) (Q : LayerFiltration P wt)
    (hcup : ∀ ρ a, layerWeight wt (G.cup ρ a) = 0)
    (hcross : ∀ ρ a b, layerWeight wt (G.cross ρ a b) = 1) : (G.interp P ρ).Filtration where
  sub n l l' := Q.sub n (Λ.obj ρ l) (Λ.obj ρ l')
  map_comp_mem {n l l' m x} hm hx := by
    rw [← G.layerWeight_moveLayers hcup hcross ρ hm]
    exact Q.diag_comp_mem _ hx
  comp_map_mem {n l l' m x} hm hx := by
    rw [← G.layerWeight_moveLayers hcup hcross ρ hm]
    exact Q.comp_diag_mem _ hx

include G in
theorem lreg_foldl (ρ : S.Region) (l : List α) (D : List (Move α)) :
    Λ.lreg ρ (D.foldl (lstep d) l) = Λ.lreg ρ l :=
  (G.chain_layersOf ρ l D).start_eq

/-- Moves applied to a subword: if two diagrams have equal images modulo `Q.sub n` on the word
`w` (with the region on its right that of `t`), then so do the shifted diagrams on
`u ++ w ++ t`, since the filtration is closed under whiskering. -/
theorem near_shift (Q : LayerFiltration P wt) (hcup : ∀ ρ a, layerWeight wt (G.cup ρ a) = 0)
    (hcross : ∀ ρ a b, layerWeight wt (G.cross ρ a b) = 1) (ρ : S.Region) {n : ℕ}
    {w : List α} {X Y : List (Move α)} (u t : List α)
    (h : (G.toFiltration (Λ.lreg ρ t) Q hcup hcross).Near n w X Y)
    (hX : Fits w.length X) (hY : Fits w.length Y) :
    (G.toFiltration ρ Q hcup hcross).Near n (u ++ w ++ t) (X.map (Move.shift u.length))
      (Y.map (Move.shift u.length)) := by
  intro e
  have e0 : X.foldl (lstep d) w = Y.foldl (lstep d) w := by
    have e' := e
    rw [foldl_shift d u t hX, foldl_shift d u t hY] at e'
    simpa using e'
  set ρ' := Λ.lreg ρ t
  have hw := Λ.whiskerOK ρ u w t
  have key := Q.whisk_mem (Λ.obj (Λ.lreg ρ (w ++ t)) u) (Λ.word ρ t) (h e0)
  rw [G.eval_comp_eqToHom_eq P ρ' e0 ⟨G.layersOf ρ' w X, e0 ▸ G.chain_layersOf ρ' w X⟩ rfl,
    eval_interp, P.whisk_sub, P.whisk_diag _ _ _ hw, P.whisk_diag _ _ _ hw] at key
  rw [G.eval_comp_eqToHom_eq P ρ e
    ⟨G.layersOf ρ (u ++ w ++ t) (X.map (Move.shift u.length)),
      e ▸ G.chain_layersOf ρ (u ++ w ++ t) (X.map (Move.shift u.length))⟩ rfl, eval_interp]
  refine Q.sub_mem_of_layers (Λ.obj_append3 ρ u w t) ?_ _ _ _ _ ?_ ?_ key
  · rw [foldl_shift d u t hY, Λ.obj_append3]
    simp [ρ', G.lreg_foldl]
  · rw [Diagram.layers_whisker]; exact G.layersOf_shift ρ u t hX
  · rw [Diagram.layers_whisker]; exact G.layersOf_shift ρ u t hY

/-- **Soundness of the chord moves in a presented 2-category with several regions.** For a
filtration `Q` compatible with single layers and with whiskering, such that cups have total
weight `0` and crossings total weight `1`, the braid relation on three strands modulo
`Q.sub 3` and the pitchfork move on one strand modulo `Q.sub 1`, in every region, imply that all
chord moves hold, in every position, modulo lower order terms (the distant commutations hold
exactly, by the interchange law). -/
theorem respects (Q : LayerFiltration P wt) (hcup : ∀ ρ a, layerWeight wt (G.cup ρ a) = 0)
    (hcross : ∀ ρ a b, layerWeight wt (G.cross ρ a b) = 1)
    (hbraid : ∀ (ρ : S.Region) (a b c : α), (G.toFiltration ρ Q hcup hcross).Near 3 [a, b, c]
      [.cross 0, .cross 1, .cross 0] [.cross 1, .cross 0, .cross 1])
    (hpitch : ∀ (ρ : S.Region) (a c : α), (G.toFiltration ρ Q hcup hcross).Near 1 [c]
      [.cup 0 a, .cross 1] [.cup 1 a, .cross 0]) (ρ : S.Region) :
    (G.toFiltration ρ Q hcup hcross).Respects := by
  intro L R hs l hf
  cases hs with
  | xx h => exact G.near_xx P ρ _ h hf
  | xuL a h => exact G.near_xuL P ρ _ a h hf
  | xuR a h => exact G.near_xuR P ρ _ a h hf
  | uu a b h => exact G.near_uu P ρ _ a b h hf
  | braid p =>
    have hl : p + 2 < l.length := by simp [Fits, Move.Ok, Move.len] at hf; omega
    obtain ⟨u, x, y, t, rfl, rfl⟩ := exists_eq_append_cons_cons (show p + 1 < l.length by omega)
    obtain ⟨z, v, rfl⟩ : ∃ z v, t = z :: v := by
      cases t with
      | nil => simp at hl
      | cons z v => exact ⟨z, v, rfl⟩
    have := G.near_shift Q hcup hcross ρ u v (hbraid (Λ.lreg ρ v) x y z)
      (by simp [Fits, Move.Ok, Move.len]) (by simp [Fits, Move.Ok, Move.len])
    have e3 : u ++ [x, y, z] ++ v = u ++ x :: y :: z :: v := by simp
    rw [e3] at this
    exact this
  | pitch g a =>
    have hl : g < l.length := by simp [Fits, Move.Ok, Move.len] at hf; omega
    obtain ⟨u, t, rfl, rfl⟩ := exists_eq_append (show g ≤ l.length by omega)
    obtain ⟨c, v, rfl⟩ : ∃ c v, t = c :: v := by
      cases t with
      | nil => simp at hl
      | cons c v => exact ⟨c, v, rfl⟩
    have := G.near_shift Q hcup hcross ρ u v (hpitch (Λ.lreg ρ v) a c)
      (by simp [Fits, Move.Ok, Move.len]) (by simp [Fits, Move.Ok, Move.len])
    have e3 : u ++ [c] ++ v = u ++ c :: v := by simp
    rw [e3] at this
    exact this

/-- **The normal form in a presented 2-category with several regions.** Under the hypotheses of
`respects`, the image of every chord diagram `D` on the empty boundary word (with the region `ρ`)
agrees, modulo terms of order less than its number of crossings, with the image of a diagram
containing a double crossing, with the image of a diagram containing a curl, or with the image
of the canonical diagram of its final pairing. -/
theorem near_canon_or_reducible (Q : LayerFiltration P wt)
    (hcup : ∀ ρ a, layerWeight wt (G.cup ρ a) = 0)
    (hcross : ∀ ρ a b, layerWeight wt (G.cross ρ a b) = 1)
    (hbraid : ∀ (ρ : S.Region) (a b c : α), (G.toFiltration ρ Q hcup hcross).Near 3 [a, b, c]
      [.cross 0, .cross 1, .cross 0] [.cross 1, .cross 0, .cross 1])
    (hpitch : ∀ (ρ : S.Region) (a c : α), (G.toFiltration ρ Q hcup hcross).Near 1 [c]
      [.cup 0 a, .cross 1] [.cup 1 a, .cross 0]) (ρ : S.Region)
    {D : List (Move α)} (hf : Fits 0 D) :
    (∃ A B : List (Move α), ∃ p : ℕ, (G.toFiltration ρ Q hcup hcross).Near (ncross D) []
        D (A ++ [.cross p, .cross p] ++ B)) ∨
      (∃ A B : List (Move α), ∃ p : ℕ, ∃ a : α,
        (G.toFiltration ρ Q hcup hcross).Near (ncross D) [] D (A ++ [.cup p a, .cross p] ++ B)) ∨
      (G.toFiltration ρ Q hcup hcross).Near (ncross D) [] D (canon (run d D)) :=
  MoveInterp.Filtration.near_canon_or_reducible
    (G.respects Q hcup hcross hbraid hpitch ρ) hf

end RegionChordGens

/-! ## Monoidal signatures -/

namespace ChordGens

variable [Subsingleton S.Region] {d : S.Colour → S.Colour}

/-- In a monoidal signature, colours are letters. -/
def letters (S : Signature.{u₀, u₁, u₂}) [Subsingleton S.Region] : Letters S S.Colour where
  col a _ := a
  col_tgt _ _ := Subsingleton.elim _ _

@[simp] theorem letters_word (ρ : S.Region) (l : List S.Colour) : (letters S).word ρ l = l := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [Letters.word_cons, ih]; rfl

theorem letters_obj (ρ : S.Region) (l : List S.Colour) : (letters S).obj ρ l = ⟨ρ, l⟩ :=
  Obj.ext (Subsingleton.elim _ _) (letters_word ρ l)

/-- Cups and crossings given by single generators in a monoidal signature, as cups and crossings
given by diagrams. -/
def toRegion (G : ChordGens S d) : RegionChordGens (letters S) d where
  cup ρ a := [⟨ρ, [], G.cup a, []⟩]
  cross ρ a b := [⟨ρ, [], G.cross a b, []⟩]
  chain_cup ρ a := by
    refine ⟨Layer.valid_of_subsingleton _, ?_, ?_⟩
    · rw [letters_obj]; simp [Layer.dom, G.cup_dom]
    · rw [letters_obj]; simp [Layer.cod, G.cup_cod]
  chain_cross ρ a b := by
    refine ⟨Layer.valid_of_subsingleton _, ?_, ?_⟩
    · rw [letters_obj]; simp [Layer.dom, G.cross_dom]
    · rw [letters_obj]; simp [Layer.cod, G.cross_cod]
  cup_even ρ a L hL := by simp only [List.mem_singleton] at hL; subst hL; exact G.cup_even a
  cross_even ρ a b L hL := by simp only [List.mem_singleton] at hL; subst hL; exact G.cross_even a b

end ChordGens

end StringDiagrams.Chord
