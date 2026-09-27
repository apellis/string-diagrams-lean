import StringDiagrams.Chord.Interpretation
import StringDiagrams.Positional
import StringDiagrams.Whisker

/-!
# Chord diagrams in presented monoidal categories

Let `P` be a presentation of an `R`-linear monoidal category (a signature `S` with a single
region) with even generators `cup a : 𝟙 ⟶ a (d a)` and `cross a b : a b ⟶ b a` for colours
`a`, `b` and a map `d` on colours (`ChordGens`). A chord diagram with letters in `S.Colour` is
interpreted in `P.Presented` (`ChordGens.interp`): the boundary word `l` goes to the object
`⟨r₀, l⟩`, `cup g a` to the cup `cup a` whiskered by the first `g` strands on the left, and
`cross p` to the crossing of the strands `p` and `p + 1`. The image of a diagram is the class of
the diagram with the corresponding layers (`ChordGens.eval_interp`).

Distant commutations of moves are instances of the interchange law, so they hold exactly
(`ChordGens.near_xx`, `near_xuL`, `near_xuR`, `near_uu`). Let `Q` be a filtration of the Hom
spaces of `P.Presented` (`LayerFiltration`) compatible with composition with single layers,
where a layer raises the order by a weight `wt` of its generator (`0` for cups, `1` for
crossings), and with whiskering. Then the braid relation on three strands modulo `Q.sub 3` and
the pitchfork move on one strand modulo `Q.sub 1` imply that the chord moves hold in every
position (`ChordGens.respects`): equivalent chord diagrams have equal images modulo lower order
terms, and the image of every chord diagram is, modulo lower order terms, that of the canonical
diagram of its matching or that of a diagram with a double crossing or a curl
(`MoveInterp.Filtration.near_canon_or_reducible`). With the trivial filtration
(`LayerFiltration.bot`) these are equalities.

Only presentations with a single region (monoidal categories) are treated here; with several
regions the letters of the boundary words would have to determine the regions.
-/

noncomputable section

namespace StringDiagrams.Chord

open CategoryTheory

universe w v u₀ u₁ u₂

/-! ## Lists with prescribed positions -/

section Lists

variable {β : Type*}

theorem swapAt_append_cons_cons (u : List β) (x y : β) (t : List β) :
    swapAt (u ++ x :: y :: t) u.length = u ++ y :: x :: t := by
  have h : u.length + 1 < (u ++ x :: y :: t).length := by simp
  rw [swapAt, dite_eq_left h]
  simp [List.set_append_right]

theorem exists_eq_append_cons_cons {l : List β} {p : ℕ} (h : p + 1 < l.length) :
    ∃ u x y t, l = u ++ x :: y :: t ∧ u.length = p := by
  refine ⟨l.take p, l[p], l[p + 1], l.drop (p + 2), ?_, by simp; omega⟩
  conv_lhs => rw [← List.take_append_drop p l]
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega)]

theorem exists_eq_append {l : List β} {g : ℕ} (h : g ≤ l.length) :
    ∃ u t, l = u ++ t ∧ u.length = g :=
  ⟨l.take g, l.drop g, (List.take_append_drop g l).symm, by simp; omega⟩

variable {α : Type*} (d : α → α)

theorem lstep_cup_append (u t : List α) (a : α) :
    lstep d (u ++ t) (.cup u.length a) = u ++ a :: d a :: t := by
  simp [lstep, insAt]

theorem lstep_cup_append' (u t : List α) (a : α) {g : ℕ} (hg : u.length = g) :
    lstep d (u ++ t) (.cup g a) = u ++ a :: d a :: t := by
  subst hg; exact lstep_cup_append d u t a

theorem lstep_cross_append' (u : List α) (x y : α) (t : List α) {p : ℕ} (hp : u.length = p) :
    lstep d (u ++ x :: y :: t) (.cross p) = u ++ y :: x :: t := by
  subst hp; exact swapAt_append_cons_cons u x y t

theorem lstep_cross_append (u : List α) (x y : α) (t : List α) :
    lstep d (u ++ x :: y :: t) (.cross u.length) = u ++ y :: x :: t :=
  swapAt_append_cons_cons u x y t

/-- Shift the position of a move by `k`. -/
def Move.shift (k : ℕ) : Move α → Move α
  | .cup g a => .cup (k + g) a
  | .cross p => .cross (k + p)

theorem Move.ok_shift {n : ℕ} (k m' : ℕ) {m : Move α} (hm : m.Ok n) : (m.shift k).Ok (k + n + m') := by
  cases m <;> simp only [Move.shift, Move.Ok] at hm ⊢ <;> omega

theorem lstep_shift (u l v : List α) {m : Move α} (hm : m.Ok l.length) :
    lstep d (u ++ l ++ v) (m.shift u.length) = u ++ lstep d l m ++ v := by
  cases m with
  | cup g a =>
    simp only [Move.Ok] at hm
    obtain ⟨l₁, l₂, rfl, rfl⟩ := exists_eq_append hm
    have := lstep_cup_append d (u ++ l₁) (l₂ ++ v) a
    simp only [List.length_append, List.append_assoc] at this
    simp only [Move.shift, List.append_assoc, this, lstep_cup_append]
    simp
  | cross p =>
    simp only [Move.Ok] at hm
    obtain ⟨l₁, x, y, t, rfl, rfl⟩ := exists_eq_append_cons_cons hm
    have := lstep_cross_append d (u ++ l₁) x y (t ++ v)
    simp only [List.length_append, List.append_assoc] at this
    simp only [Move.shift, List.append_assoc, List.cons_append, this, lstep_cross_append]

theorem foldl_shift (u v : List α) {l : List α} {D : List (Move α)} (hf : Fits l.length D) :
    (D.map (Move.shift u.length)).foldl (lstep d) (u ++ l ++ v) = u ++ D.foldl (lstep d) l ++ v := by
  induction D generalizing l with
  | nil => rfl
  | cons m D ih =>
    obtain ⟨hm, hf⟩ := hf
    rw [← length_lstep (d := d)] at hf
    simp only [List.map_cons, List.foldl_cons, lstep_shift d u l v hm]
    exact ih hf

theorem Move.len_shift (k j n : ℕ) (m : Move α) : (m.shift k).len (k + n + j) = k + m.len n + j := by
  cases m with
  | cup g a => simp only [Move.shift, Move.len]; omega
  | cross p => rfl

theorem fits_shift (k j : ℕ) {n : ℕ} {D : List (Move α)} (hf : Fits n D) :
    Fits (k + n + j) (D.map (Move.shift k)) := by
  induction D generalizing n with
  | nil => trivial
  | cons m D ih =>
    obtain ⟨hm, hf⟩ := hf
    refine ⟨Move.ok_shift k j hm, ?_⟩
    rw [Move.len_shift]
    exact ih hf

end Lists

/-! ## Cups and crossings in a signature -/

variable {S : Signature.{u₀, u₁, u₂}}

/-- Generators playing the roles of cups and crossings in a signature: `cup a` from the empty
word to `a (d a)` and `cross a b` from `a b` to `b a`, all even. -/
structure ChordGens (S : Signature.{u₀, u₁, u₂}) (d : S.Colour → S.Colour) where
  /-- The cup with left leg `a` and right leg `d a`. -/
  cup : S.Colour → S.Gen
  /-- The crossing of strands `a` (bottom left) and `b` (bottom right). -/
  cross : S.Colour → S.Colour → S.Gen
  cup_dom : ∀ a, S.dom (cup a) = []
  cup_cod : ∀ a, S.cod (cup a) = [a, d a]
  cross_dom : ∀ a b, S.dom (cross a b) = [a, b]
  cross_cod : ∀ a b, S.cod (cross a b) = [b, a]
  cup_even : ∀ a, S.odd (cup a) = false
  cross_even : ∀ a b, S.odd (cross a b) = false

namespace ChordGens

variable {d : S.Colour → S.Colour} (G : ChordGens S d) [Subsingleton S.Region] (r₀ : S.Region)

/-- The layers of a move applied to the boundary word `l`: a whiskered cup or crossing (no
layer for a crossing out of range). -/
def moveLayers (l : List S.Colour) : Move S.Colour → List (Layer S)
  | .cup g a => [⟨r₀, l.take g, G.cup a, l.drop g⟩]
  | .cross p =>
    if h : p + 1 < l.length then [⟨r₀, l.take p, G.cross l[p] l[p + 1], l.drop (p + 2)⟩] else []

omit [Subsingleton S.Region] in
theorem moveLayers_cup' (u t : List S.Colour) (a : S.Colour) {g : ℕ} (hg : u.length = g) :
    G.moveLayers r₀ (u ++ t) (.cup g a) = [⟨r₀, u, G.cup a, t⟩] := by
  subst hg; simp [moveLayers]

omit [Subsingleton S.Region] in
theorem moveLayers_cup (u t : List S.Colour) (a : S.Colour) :
    G.moveLayers r₀ (u ++ t) (.cup u.length a) = [⟨r₀, u, G.cup a, t⟩] := by
  simp [moveLayers]

omit [Subsingleton S.Region] in
theorem moveLayers_cross (u : List S.Colour) (x y : S.Colour) (t : List S.Colour) :
    G.moveLayers r₀ (u ++ x :: y :: t) (.cross u.length) = [⟨r₀, u, G.cross x y, t⟩] := by
  have h : u.length + 1 < (u ++ x :: y :: t).length := by simp
  simp only [moveLayers, dite_eq_left h]
  congr 3
  · simp
  · simp [List.getElem_append_right]
  · simp [List.getElem_append_right]
  · rw [show u.length + 2 = u.length + 2 from rfl, List.drop_length_add_append]; rfl

omit [Subsingleton S.Region] in
theorem moveLayers_cross' (u : List S.Colour) (x y : S.Colour) (t : List S.Colour) {p : ℕ}
    (hp : u.length = p) : G.moveLayers r₀ (u ++ x :: y :: t) (.cross p) = [⟨r₀, u, G.cross x y, t⟩] := by
  subst hp; exact G.moveLayers_cross r₀ u x y t

theorem chain_moveLayers (l : List S.Colour) (m : Move S.Colour) :
    Chain ⟨r₀, l⟩ (G.moveLayers r₀ l m) ⟨r₀, lstep d l m⟩ := by
  cases m with
  | cup g a =>
    refine ⟨Layer.valid_of_subsingleton _, ?_, ?_⟩
    · simp [Layer.dom, G.cup_dom]
    · simp [Layer.cod, G.cup_cod, lstep, insAt]
  | cross p =>
    by_cases h : p + 1 < l.length
    · obtain ⟨u, x, y, t, rfl, rfl⟩ := exists_eq_append_cons_cons h
      rw [moveLayers_cross, lstep_cross_append]
      refine ⟨Layer.valid_of_subsingleton _, ?_, ?_⟩
      · simp [Layer.dom, G.cross_dom]
      · simp [Layer.cod, G.cross_cod]
    · simp only [moveLayers, dite_eq_right h, chain_nil]
      simp [lstep, swapAt_of_le l h]

/-- The layers of a diagram applied to the boundary word `l`. -/
def layersOf : List S.Colour → List (Move S.Colour) → List (Layer S)
  | _, [] => []
  | l, m :: D => G.moveLayers r₀ l m ++ layersOf (lstep d l m) D

theorem chain_layersOf (l : List S.Colour) (D : List (Move S.Colour)) :
    Chain ⟨r₀, l⟩ (G.layersOf r₀ l D) ⟨r₀, D.foldl (lstep d) l⟩ := by
  induction D generalizing l with
  | nil => rfl
  | cons m D ih => exact (G.chain_moveLayers r₀ l m).append (ih _)

variable {R : Type w} [CommRing R] (P : Presentation.{w, v} S R)

/-- The interpretation of chord diagrams in the presented category: the boundary word `l` goes
to `⟨r₀, l⟩`, and a move to its whiskered cup or crossing. -/
abbrev interp : MoveInterp d P.Presented where
  obj l := P.obj ⟨r₀, l⟩
  map l m := P.diag ⟨G.moveLayers r₀ l m, G.chain_moveLayers r₀ l m⟩

/-- The image of a chord diagram is the class of the diagram with its layers. -/
theorem eval_interp (l : List S.Colour) (D : List (Move S.Colour)) :
    (G.interp r₀ P).eval l D = P.diag ⟨G.layersOf r₀ l D, G.chain_layersOf r₀ l D⟩ := by
  induction D generalizing l with
  | nil => exact (P.diag_id _).symm
  | cons m D ih =>
    rw [MoveInterp.eval_cons, ih]
    exact (P.diag_comp _ _).symm

/-! ## Retyping classes of diagrams given by their layers -/

/-- The image of a chord diagram, retyped, is the class of any diagram with its layers. -/
theorem eval_comp_eqToHom_eq {l : List S.Colour} {X Y : List (Move S.Colour)}
    (e : X.foldl (lstep d) l = Y.foldl (lstep d) l)
    (f : (⟨r₀, l⟩ : Obj S) ⟶ ⟨r₀, Y.foldl (lstep d) l⟩) (hf : Diagram.layers f = G.layersOf r₀ l X) :
    (G.interp r₀ P).eval l X ≫ eqToHom (congrArg (G.interp r₀ P).obj e) = P.diag f := by
  have key : ∀ (t : List S.Colour) (c : Chain ⟨r₀, l⟩ (G.layersOf r₀ l X) ⟨r₀, t⟩)
      (e : t = Y.foldl (lstep d) l),
      P.diag ⟨G.layersOf r₀ l X, c⟩ ≫ eqToHom (congrArg (G.interp r₀ P).obj e) =
        P.diag ⟨G.layersOf r₀ l X, e ▸ c⟩ := by
    intro t c e; subst e; simp
  rw [eval_interp, key _ _ e]
  obtain ⟨ls, hc⟩ := f
  simp only [Diagram.layers] at hf
  subst hf
  rfl

omit [Subsingleton S.Region] in
theorem diag_comp_eqToHom_of_layers_eq {a b b' : Obj S} (f : a ⟶ b) (f' : a ⟶ b') (h : b = b')
    (hl : Diagram.layers f = Diagram.layers f') :
    P.diag f ≫ eqToHom (congrArg P.obj h) = P.diag f' := by
  subst h; simpa using P.diag_eq_of_layers_eq hl

omit [Subsingleton S.Region] in
theorem diag_mk_congr {a b : Obj S} {ls ls' : List (Layer S)} (h : Chain a ls b) (e : ls = ls') :
    P.diag ⟨ls, h⟩ = P.diag ⟨ls', e ▸ h⟩ := by
  subst e; rfl

omit [Subsingleton S.Region] in
theorem diag_mk_singleton {a b : Obj S} (L : Layer S) (h : Chain a [L] b) :
    P.diag ⟨[L], h⟩ = eqToHom (congrArg P.obj h.2.1.symm) ≫
      P.diag (Diagram.ofLayer L h.1) ≫ eqToHom (congrArg P.obj h.2.2) := by
  obtain ⟨hv, rfl, rfl⟩ := h
  simp [Diagram.ofLayer]

end ChordGens

/-! ## Filtrations of presented categories -/

/-- A filtration of the Hom spaces of a presented category by lower order terms, for a weight
`wt` of the generators: subgroups `sub n a b` of `P.obj a ⟶ P.obj b` (terms of order less than
`n`), such that composing with a single layer of generator `g` maps `sub n` into
`sub (n + wt g)`, and closed under whiskering. -/
structure LayerFiltration {R : Type w} [CommRing R] (P : Presentation.{w, v} S R)
    (wt : S.Gen → ℕ) where
  /-- The terms of order less than `n`. -/
  sub : ℕ → (a b : Obj S) → AddSubgroup (P.obj a ⟶ P.obj b)
  /-- Precomposition with a layer. -/
  layer_comp_mem : ∀ {n : ℕ} {L : Layer S} (hv : L.Valid) {c : Obj S} {x : P.obj L.cod ⟶ P.obj c},
    x ∈ sub n L.cod c → P.diag (Diagram.ofLayer L hv) ≫ x ∈ sub (wt L.gen + n) L.dom c
  /-- Postcomposition with a layer. -/
  comp_layer_mem : ∀ {n : ℕ} {L : Layer S} (hv : L.Valid) {c : Obj S} {x : P.obj c ⟶ P.obj L.dom},
    x ∈ sub n c L.dom → x ≫ P.diag (Diagram.ofLayer L hv) ∈ sub (n + wt L.gen) c L.cod
  /-- Whiskering. -/
  whisk_mem : ∀ {n : ℕ} {a b : Obj S} {x : P.obj a ⟶ P.obj b} (u : Obj S) (v : List S.Colour),
    x ∈ sub n a b → P.whisk x u v ∈ sub n (a.whisker u v) (b.whisker u v)

namespace LayerFiltration

variable {R : Type w} [CommRing R] {P : Presentation.{w, v} S R} {wt : S.Gen → ℕ}

/-- The trivial filtration: equality on the nose. -/
def bot (P : Presentation.{w, v} S R) (wt : S.Gen → ℕ) : LayerFiltration P wt where
  sub _ _ _ := ⊥
  layer_comp_mem _ _ _ hx := by
    rw [AddSubgroup.mem_bot] at hx ⊢; rw [hx, Limits.comp_zero]
  comp_layer_mem _ _ _ hx := by
    rw [AddSubgroup.mem_bot] at hx ⊢; rw [hx, Limits.zero_comp]
  whisk_mem u v hx := by
    rw [AddSubgroup.mem_bot] at hx ⊢; rw [hx, P.whisk_zero]

variable (Q : LayerFiltration P wt)

theorem eqToHom_comp_mem {n : ℕ} {a a' b : Obj S} (h : a' = a) {x : P.obj a ⟶ P.obj b}
    (hx : x ∈ Q.sub n a b) : eqToHom (congrArg P.obj h) ≫ x ∈ Q.sub n a' b := by
  subst h; simpa using hx

theorem comp_eqToHom_mem {n : ℕ} {a b b' : Obj S} (h : b = b') {x : P.obj a ⟶ P.obj b}
    (hx : x ∈ Q.sub n a b) : x ≫ eqToHom (congrArg P.obj h) ∈ Q.sub n a b' := by
  subst h; simpa using hx

theorem layer_comp_mem' {n : ℕ} {L : Layer S} (hv : L.Valid) {a b c : Obj S} (ha : L.dom = a)
    (hb : L.cod = b) {x : P.obj b ⟶ P.obj c} (hx : x ∈ Q.sub n b c) :
    (eqToHom (congrArg P.obj ha.symm) ≫ P.diag (Diagram.ofLayer L hv) ≫
      eqToHom (congrArg P.obj hb)) ≫ x ∈ Q.sub (wt L.gen + n) a c := by
  subst ha hb; simpa using Q.layer_comp_mem hv hx

theorem comp_layer_mem' {n : ℕ} {L : Layer S} (hv : L.Valid) {a b c : Obj S} (ha : L.dom = a)
    (hb : L.cod = b) {x : P.obj c ⟶ P.obj a} (hx : x ∈ Q.sub n c a) :
    x ≫ eqToHom (congrArg P.obj ha.symm) ≫ P.diag (Diagram.ofLayer L hv) ≫
      eqToHom (congrArg P.obj hb) ∈ Q.sub (n + wt L.gen) c b := by
  subst ha hb; simpa using Q.comp_layer_mem hv hx

end LayerFiltration

namespace ChordGens

variable {d : S.Colour → S.Colour} (G : ChordGens S d) [Subsingleton S.Region] (r₀ : S.Region)
  {R : Type w} [CommRing R] {P : Presentation.{w, v} S R} {wt : S.Gen → ℕ}

theorem map_interp_of_singleton {l : List S.Colour} {m : Move S.Colour} {L : Layer S}
    (h : G.moveLayers r₀ l m = [L]) :
    (G.interp r₀ P).map l m = eqToHom (congrArg P.obj ((h ▸ G.chain_moveLayers r₀ l m :
        Chain _ [L] _).2.1.symm)) ≫
      P.diag (Diagram.ofLayer L (h ▸ G.chain_moveLayers r₀ l m : Chain _ [L] _).1) ≫
        eqToHom (congrArg P.obj (h ▸ G.chain_moveLayers r₀ l m : Chain _ [L] _).2.2) := by
  rw [← diag_mk_singleton]
  exact diag_mk_congr P _ h

omit [Subsingleton S.Region] in
theorem moveLayers_eq_singleton {l : List S.Colour} {m : Move S.Colour} (hm : m.Ok l.length) :
    ∃ L, G.moveLayers r₀ l m = [L] := by
  cases m with
  | cup g a => exact ⟨_, rfl⟩
  | cross p =>
    simp only [Move.Ok] at hm
    exact ⟨_, dite_eq_left hm⟩

variable (P) in
/-- To show that two chord diagrams have the same image, it suffices to compare classes of
diagrams with their layers. -/
theorem near_of_diag_eq (Φ : (G.interp r₀ P).Filtration) {n : ℕ} {l : List S.Colour}
    {X Y : List (Move S.Colour)}
    (h : ∀ f₁ f₂ : (⟨r₀, l⟩ : Obj S) ⟶ ⟨r₀, Y.foldl (lstep d) l⟩,
      Diagram.layers f₁ = G.layersOf r₀ l X → Diagram.layers f₂ = G.layersOf r₀ l Y →
        P.diag f₁ = P.diag f₂) :
    Φ.Near n l X Y := by
  intro e
  rw [G.eval_comp_eqToHom_eq r₀ P e ⟨G.layersOf r₀ l X, e ▸ G.chain_layersOf r₀ l X⟩ rfl,
    eval_interp, h _ ⟨G.layersOf r₀ l Y, G.chain_layersOf r₀ l Y⟩ rfl rfl, sub_self]
  exact zero_mem _

omit [Subsingleton S.Region] in
theorem layersOf_pair (l : List S.Colour) (m₁ m₂ : Move S.Colour) :
    G.layersOf r₀ l [m₁, m₂] = G.moveLayers r₀ l m₁ ++ G.moveLayers r₀ (lstep d l m₁) m₂ := by
  simp [layersOf]

variable (P) in
/-- Distant crossings commute (the interchange law). -/
theorem near_xx (Φ : (G.interp r₀ P).Filtration) {n p p' : ℕ} (hp : p + 2 ≤ p')
    {l : List S.Colour} (hf : Fits l.length ([.cross p, .cross p'] : List (Move S.Colour))) :
    Φ.Near n l [.cross p, .cross p'] [.cross p', .cross p] := by
  have hl : p' + 1 < l.length := by simp [Fits, Move.Ok, Move.len] at hf; omega
  obtain ⟨u, x, y, t, rfl, rfl⟩ := exists_eq_append_cons_cons (show p + 1 < l.length by omega)
  obtain ⟨m, z, w, v, rfl, hm⟩ :=
    exists_eq_append_cons_cons (show p' - u.length - 2 + 1 < t.length by simp at hl; omega)
  apply near_of_diag_eq G r₀ P
  intro f₁ f₂ h₁ h₂
  refine P.diag_interchange_of_layers_of_even r₀ u m v (G.cross x y) (G.cross z w)
    (Or.inl (G.cross_even _ _)) f₁ f₂ ?_ ?_
  · rw [h₁, layersOf_pair, moveLayers_cross, lstep_cross_append,
      show u ++ y :: x :: (m ++ z :: w :: v) = (u ++ y :: x :: m) ++ z :: w :: v by simp,
      moveLayers_cross' _ _ _ _ _ _ (by simp; omega)]
    simp [G.cross_dom, G.cross_cod]
  · rw [h₂, layersOf_pair,
      show u ++ x :: y :: (m ++ z :: w :: v) = (u ++ x :: y :: m) ++ z :: w :: v by simp,
      moveLayers_cross' _ _ _ _ _ _ (by simp; omega),
      lstep_cross_append' _ _ _ _ _ (by simp; omega),
      show (u ++ x :: y :: m) ++ w :: z :: v = u ++ x :: y :: (m ++ w :: z :: v) by simp,
      moveLayers_cross]
    simp [G.cross_dom, G.cross_cod]

variable (P) in
/-- A crossing commutes with a cup to its right (the interchange law). -/
theorem near_xuL (Φ : (G.interp r₀ P).Filtration) {n p g : ℕ} (a : S.Colour) (hp : p + 2 ≤ g)
    {l : List S.Colour} (hf : Fits l.length [.cross p, (.cup g a : Move S.Colour)]) :
    Φ.Near n l [.cross p, .cup g a] [.cup g a, .cross p] := by
  have hl : p + 1 < l.length ∧ g ≤ l.length := by simp [Fits, Move.Ok, Move.len] at hf; omega
  obtain ⟨u, x, y, t, rfl, rfl⟩ := exists_eq_append_cons_cons hl.1
  obtain ⟨m, v, rfl, hm⟩ :=
    exists_eq_append (show g - u.length - 2 ≤ t.length by have := hl.2; simp at this; omega)
  apply near_of_diag_eq G r₀ P
  intro f₁ f₂ h₁ h₂
  refine P.diag_interchange_of_layers_of_even r₀ u m v (G.cross x y) (G.cup a)
    (Or.inl (G.cross_even _ _)) f₁ f₂ ?_ ?_
  · rw [h₁, layersOf_pair, moveLayers_cross, lstep_cross_append,
      show u ++ y :: x :: (m ++ v) = (u ++ y :: x :: m) ++ v by simp,
      moveLayers_cup' _ _ _ _ _ (by simp; omega)]
    simp [G.cross_cod, G.cup_dom]
  · rw [h₂, layersOf_pair,
      show u ++ x :: y :: (m ++ v) = (u ++ x :: y :: m) ++ v by simp,
      moveLayers_cup' _ _ _ _ _ (by simp; omega),
      lstep_cup_append' _ _ _ _ (by simp; omega),
      show (u ++ x :: y :: m) ++ a :: d a :: v = u ++ x :: y :: (m ++ a :: d a :: v) by simp,
      moveLayers_cross]
    simp [G.cross_dom, G.cup_cod]

variable (P) in
/-- A crossing commutes with a cup to its left (the interchange law). -/
theorem near_xuR (Φ : (G.interp r₀ P).Filtration) {n p g : ℕ} (a : S.Colour) (hg : g ≤ p)
    {l : List S.Colour} (hf : Fits l.length [.cross p, (.cup g a : Move S.Colour)]) :
    Φ.Near n l [.cross p, .cup g a] [.cup g a, .cross (p + 2)] := by
  have hl : p + 1 < l.length := by simp [Fits, Move.Ok, Move.len] at hf; omega
  obtain ⟨w, x, y, v, rfl, rfl⟩ := exists_eq_append_cons_cons hl
  obtain ⟨u, m, rfl, rfl⟩ := exists_eq_append (show g ≤ w.length by omega)
  apply near_of_diag_eq G r₀ P
  intro f₁ f₂ h₁ h₂
  refine (P.diag_interchange_of_layers_of_even r₀ u m v (G.cup a) (G.cross x y)
    (Or.inl (G.cup_even _)) f₂ f₁ ?_ ?_).symm
  · rw [h₂, layersOf_pair,
      show (u ++ m) ++ x :: y :: v = u ++ (m ++ x :: y :: v) by simp,
      moveLayers_cup, lstep_cup_append,
      show u ++ a :: d a :: (m ++ x :: y :: v) = (u ++ a :: d a :: m) ++ x :: y :: v by simp,
      moveLayers_cross' _ _ _ _ _ _ (by simp; omega)]
    simp [G.cross_dom, G.cup_cod]
  · rw [h₁, layersOf_pair, moveLayers_cross' _ _ _ _ _ _ (by simp),
      lstep_cross_append' _ _ _ _ _ (by simp),
      show (u ++ m) ++ y :: x :: v = u ++ (m ++ y :: x :: v) by simp, moveLayers_cup]
    simp [G.cross_cod, G.cup_dom]

variable (P) in
/-- Two cups commute (the interchange law). -/
theorem near_uu (Φ : (G.interp r₀ P).Filtration) {n g g' : ℕ} (a b : S.Colour) (hg : g' ≤ g)
    {l : List S.Colour} (hf : Fits l.length [(.cup g a : Move S.Colour), .cup g' b]) :
    Φ.Near n l [.cup g a, .cup g' b] [.cup g' b, .cup (g + 2) a] := by
  have hl : g ≤ l.length := by simp [Fits, Move.Ok, Move.len] at hf; omega
  obtain ⟨w, v, rfl, rfl⟩ := exists_eq_append hl
  obtain ⟨u, m, rfl, rfl⟩ := exists_eq_append hg
  apply near_of_diag_eq G r₀ P
  intro f₁ f₂ h₁ h₂
  refine (P.diag_interchange_of_layers_of_even r₀ u m v (G.cup b) (G.cup a)
    (Or.inl (G.cup_even _)) f₂ f₁ ?_ ?_).symm
  · rw [h₂, layersOf_pair, show (u ++ m) ++ v = u ++ (m ++ v) by simp, moveLayers_cup,
      lstep_cup_append,
      show u ++ b :: d b :: (m ++ v) = (u ++ b :: d b :: m) ++ v by simp,
      moveLayers_cup' _ _ _ _ _ (by simp; omega)]
    simp [G.cup_dom, G.cup_cod]
  · rw [h₁, layersOf_pair, moveLayers_cup' _ _ _ _ _ (by simp),
      lstep_cup_append' _ _ _ _ (by simp),
      show (u ++ m) ++ a :: d a :: v = u ++ (m ++ a :: d a :: v) by simp, moveLayers_cup]
    simp [G.cup_dom, G.cup_cod]

/-- The filtration of the interpretation of chord diagrams induced by a filtration of the
presented category, when cups have weight `0` and crossings weight `1`. -/
def toFiltration (Q : LayerFiltration P wt) (hcup : ∀ a, wt (G.cup a) = 0)
    (hcross : ∀ a b, wt (G.cross a b) = 1) : (G.interp r₀ P).Filtration where
  sub n l l' := Q.sub n ⟨r₀, l⟩ ⟨r₀, l'⟩
  map_comp_mem {n l l' m x} hm hx := by
    have hw : ∀ L, G.moveLayers r₀ l m = [L] → wt L.gen = m.ncross := by
      intro L hL
      cases m with
      | cup g a => simp only [moveLayers, List.cons.injEq] at hL; rw [← hL.1, hcup]; rfl
      | cross p =>
        simp only [Move.Ok] at hm
        simp only [moveLayers, dite_eq_left hm, List.cons.injEq] at hL; rw [← hL.1, hcross]; rfl
    obtain ⟨L, hL⟩ := G.moveLayers_eq_singleton r₀ hm
    rw [G.map_interp_of_singleton r₀ hL, ← hw L hL]
    have hc : Chain ⟨r₀, l⟩ [L] ⟨r₀, lstep d l m⟩ := hL ▸ G.chain_moveLayers r₀ l m
    exact Q.layer_comp_mem' hc.1 hc.2.1 hc.2.2 hx
  comp_map_mem {n l l' m x} hm hx := by
    have hw : ∀ L, G.moveLayers r₀ l' m = [L] → wt L.gen = m.ncross := by
      intro L hL
      cases m with
      | cup g a => simp only [moveLayers, List.cons.injEq] at hL; rw [← hL.1, hcup]; rfl
      | cross p =>
        simp only [Move.Ok] at hm
        simp only [moveLayers, dite_eq_left hm, List.cons.injEq] at hL; rw [← hL.1, hcross]; rfl
    obtain ⟨L, hL⟩ := G.moveLayers_eq_singleton r₀ hm
    rw [G.map_interp_of_singleton r₀ hL, ← hw L hL]
    have hc : Chain ⟨r₀, l'⟩ [L] ⟨r₀, lstep d l' m⟩ := hL ▸ G.chain_moveLayers r₀ l' m
    exact Q.comp_layer_mem' hc.1 hc.2.1 hc.2.2 hx

end ChordGens

end StringDiagrams.Chord
