import StringDiagrams.Whisker

/-!
# The interchange law for arbitrary diagrams

For monoidal signatures (a single region), let `f : a ⟶ a'` and `g : b ⟶ b'` be diagrams.
Placing `f` to the left of `g`, the two ways of composing them agree up to the Koszul sign:

`(f ⊗ 1_b) ≫ (1_{a'} ⊗ g) = (-1)^{|f| |g|} (1_a ⊗ g) ≫ (f ⊗ 1_{b'})`

in the presented category of any presentation, where `|f|` is the number of odd
generators in `f` (`Presentation.diag_interchange_diagrams`). It is derived from the
instances of the interchange law for single generators imposed in
`Presentation.Presented`, by induction on the numbers of layers.

## Main definitions

* `Layer.wr L v`, `Layer.wl w L`: a layer with extra strands on the right / left.
* `Diagram.whiskerR f b : a ⊗ b ⟶ a' ⊗ b`, `Diagram.whiskerL a g : a ⊗ b ⟶ a ⊗ b'`
  (`⊗` is `Obj.tensor`).
* `Diagram.oddCount f`: the number of odd generators in `f`.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory

universe w v u₀ u₁ u₂

variable {S : Signature.{u₀, u₁, u₂}}

namespace Layer

/-- A layer with the strands `v` added on the right. -/
def wr (L : Layer S) (v : List S.Colour) : Layer S := ⟨L.start, L.left, L.gen, L.right ++ v⟩

/-- A layer with the object `w` added on the left. -/
def wl (w : Obj S) (L : Layer S) : Layer S := ⟨w.start, w.word ++ L.left, L.gen, L.right⟩

@[simp] theorem wr_gen (L : Layer S) (v : List S.Colour) : (L.wr v).gen = L.gen := rfl
@[simp] theorem wl_gen (w : Obj S) (L : Layer S) : (L.wl w).gen = L.gen := rfl

theorem wr_dom (L : Layer S) (b : Obj S) : (L.wr b.word).dom = L.dom.tensor b := by
  simp [wr, dom, Obj.tensor]

theorem wr_cod (L : Layer S) (b : Obj S) : (L.wr b.word).cod = L.cod.tensor b := by
  simp [wr, cod, Obj.tensor]

theorem wl_dom (a : Obj S) (L : Layer S) : (L.wl a).dom = a.tensor L.dom := by
  simp [wl, dom, Obj.tensor]

theorem wl_cod (a : Obj S) (L : Layer S) : (L.wl a).cod = a.tensor L.cod := by
  simp [wl, cod, Obj.tensor]

end Layer

theorem Chain.wr [Subsingleton S.Region] {a a' : Obj S} {ls : List (Layer S)} (h : Chain a ls a') (b : Obj S) :
    Chain (a.tensor b) (ls.map (·.wr b.word)) (a'.tensor b) := by
  induction ls generalizing a with
  | nil => cases h; rfl
  | cons L ls ih =>
    obtain ⟨-, rfl, hc⟩ := h
    exact ⟨Layer.valid_of_subsingleton _, L.wr_dom b, by rw [L.wr_cod]; exact ih hc⟩

theorem Chain.wl [Subsingleton S.Region] {b b' : Obj S} {ls : List (Layer S)} (h : Chain b ls b') (a : Obj S) :
    Chain (a.tensor b) (ls.map (·.wl a)) (a.tensor b') := by
  induction ls generalizing b with
  | nil => cases h; rfl
  | cons L ls ih =>
    obtain ⟨-, rfl, hc⟩ := h
    exact ⟨Layer.valid_of_subsingleton _, L.wl_dom a, by rw [L.wl_cod]; exact ih hc⟩

namespace Diagram

variable {a a' a'' b b' b'' : Obj S}

/-- `f ⊗ 1_b`. -/
def whiskerR [Subsingleton S.Region] (f : a ⟶ a') (b : Obj S) : a.tensor b ⟶ a'.tensor b :=
  mk ((layers f).map (·.wr b.word)) ((chain f).wr b)

/-- `1_a ⊗ g`. -/
def whiskerL [Subsingleton S.Region] (a : Obj S) (g : b ⟶ b') : a.tensor b ⟶ a.tensor b' :=
  mk ((layers g).map (·.wl a)) ((chain g).wl a)

@[simp] theorem layers_whiskerR [Subsingleton S.Region] (f : a ⟶ a') (b : Obj S) :
    layers (whiskerR f b) = (layers f).map (·.wr b.word) := rfl

@[simp] theorem layers_whiskerL [Subsingleton S.Region] (a : Obj S) (g : b ⟶ b') :
    layers (whiskerL a g) = (layers g).map (·.wl a) := rfl

theorem whiskerR_comp [Subsingleton S.Region] (f : a ⟶ a') (f' : a' ⟶ a'') (b : Obj S) :
    whiskerR (f ≫ f') b = whiskerR f b ≫ whiskerR f' b := by
  ext; simp

theorem whiskerL_comp [Subsingleton S.Region] (a : Obj S) (g : b ⟶ b') (g' : b' ⟶ b'') :
    whiskerL a (g ≫ g') = whiskerL a g ≫ whiskerL a g' := by
  ext; simp

/-- The number of odd generators in a list of layers. -/
def oddCountList (ls : List (Layer S)) : ℕ := (ls.filter fun L => S.odd L.gen).length

@[simp] theorem oddCountList_nil : oddCountList ([] : List (Layer S)) = 0 := rfl

theorem oddCountList_cons (L : Layer S) (ls : List (Layer S)) :
    oddCountList (L :: ls) = oddCountList [L] + oddCountList ls := by
  by_cases h : S.odd L.gen <;> simp [oddCountList, List.filter_cons, h, add_comm]

@[simp] theorem oddCountList_map_wr (ls : List (Layer S)) (v : List S.Colour) :
    oddCountList (ls.map (·.wr v)) = oddCountList ls := by
  simp [oddCountList, List.filter_map, Function.comp_def]

@[simp] theorem oddCountList_map_wl (ls : List (Layer S)) (w : Obj S) :
    oddCountList (ls.map (·.wl w)) = oddCountList ls := by
  simp [oddCountList, List.filter_map, Function.comp_def]

/-- The number of odd generators in a diagram. -/
def oddCount (f : a ⟶ b) : ℕ := oddCountList (layers f)

end Diagram

namespace Presentation

variable {R : Type w} [CommRing R] (P : Presentation.{w, v} S R) [Subsingleton S.Region]

open Diagram

omit [Subsingleton S.Region] in
theorem diag_mk_congr {a b : Obj S} {ls ms : List (Layer S)} (h : ls = ms) (hl : Chain a ls b)
    (hm : Chain a ms b) : P.diag (Diagram.mk ls hl) = P.diag (Diagram.mk ms hm) := by
  subst h; rfl

/-- The interchange law for two single layers. -/
theorem diag_swap_layers (L M : Layer S) :
    P.diag (whiskerR (ofLayer L (Layer.valid_of_subsingleton L)) M.dom ≫
        whiskerL L.cod (ofLayer M (Layer.valid_of_subsingleton M))) =
      ((-1 : ℤ) ^ (oddCountList [L] * oddCountList [M])) •
        P.diag (whiskerL L.dom (ofLayer M (Layer.valid_of_subsingleton M)) ≫
          whiskerR (ofLayer L (Layer.valid_of_subsingleton L)) M.cod) := by
  let x : InterchangeData S := ⟨L.start, L.gen, L.right ++ M.left, M.gen⟩
  have hx : x.Valid := InterchangeData.valid_of_subsingleton x
  let u : Obj S := ⟨L.start, L.left⟩
  have hw : x.dom.WhiskerOK u M.right := Obj.whiskerOK_of_subsingleton _ _ _
  have ha : x.dom.whisker u M.right = L.dom.tensor M.dom := by
    simp [x, u, InterchangeData.dom, Obj.whisker, Obj.tensor, Layer.dom]
  have hb : x.cod.whisker u M.right = L.cod.tensor M.cod := by
    simp [x, u, InterchangeData.cod, Obj.whisker, Obj.tensor, Layer.cod]
  have key := P.diag_interchange x hx u M.right hw ha hb
  have hs : ((x.sign : ℤ) : R) = (((-1 : ℤ) ^ (oddCountList [L] * oddCountList [M]) : ℤ) : R) := by
    congr 1
    by_cases hL : S.odd L.gen <;> by_cases hM : S.odd M.gen <;>
      simp [x, InterchangeData.sign, oddCountList, List.filter_cons, hL, hM]
  rw [hs, Int.cast_smul_eq_zsmul] at key
  refine Eq.trans (P.diag_eq_of_layers_eq ?_) (key.trans (congrArg _ (P.diag_eq_of_layers_eq ?_)))
  all_goals simp [x, u, InterchangeData.ghDiagram, InterchangeData.hgDiagram, InterchangeData.gh₁,
      InterchangeData.gh₂, InterchangeData.hg₁, InterchangeData.hg₂, Layer.whisker, Layer.wr,
      Layer.wl, Layer.dom, Layer.cod, Obj.tensor]

/-- Moving a single layer on the right past a diagram on the left. -/
theorem diag_swap_layer_right (f : a ⟶ a') (M : Layer S) :
    P.diag (whiskerR f M.dom ≫ whiskerL a' (ofLayer M (Layer.valid_of_subsingleton M))) =
      ((-1 : ℤ) ^ (oddCount f * oddCountList [M])) •
        P.diag (whiskerL a (ofLayer M (Layer.valid_of_subsingleton M)) ≫ whiskerR f M.cod) := by
  obtain ⟨ls, h⟩ := f
  induction ls generalizing a with
  | nil =>
    cases h
    simp only [oddCount, Diagram.layers, oddCountList_nil, zero_mul, pow_zero, one_smul]
    apply P.diag_eq_of_layers_eq
    simp only [layers_comp, layers_whiskerR, layers_whiskerL, layers_ofLayer]
    rfl
  | cons L ls ih =>
    obtain ⟨hv, rfl, hc⟩ := h
    have e₁ : (⟨L :: ls, hv, rfl, hc⟩ : L.dom ⟶ a') = ofLayer L hv ≫ (⟨ls, hc⟩ : L.cod ⟶ a') := by
      ext; rfl
    have hodd : oddCount (⟨L :: ls, hv, rfl, hc⟩ : L.dom ⟶ a') =
        oddCountList [L] + oddCount (⟨ls, hc⟩ : L.cod ⟶ a') := oddCountList_cons L ls
    rw [hodd, e₁, whiskerR_comp, whiskerR_comp, Category.assoc, P.diag_comp, ih hc,
      Linear.comp_smul, ← P.diag_comp, ← Category.assoc, P.diag_comp (_ ≫ _),
      P.diag_swap_layers, Linear.smul_comp, smul_smul, ← P.diag_comp, Category.assoc,
      add_mul, pow_add, mul_comm]

/-- The interchange law for arbitrary diagrams. -/
theorem diag_interchange_diagrams (f : a ⟶ a') (g : b ⟶ b') :
    P.diag (whiskerR f b ≫ whiskerL a' g) =
      ((-1 : ℤ) ^ (oddCount f * oddCount g)) • P.diag (whiskerL a g ≫ whiskerR f b') := by
  obtain ⟨ms, h⟩ := g
  induction ms generalizing b with
  | nil =>
    cases h
    simp only [oddCount, Diagram.layers, oddCountList_nil, mul_zero, pow_zero, one_smul]
    apply P.diag_eq_of_layers_eq
    simp only [layers_comp, layers_whiskerR, layers_whiskerL]
    show _ ++ [] = [] ++ _
    simp
  | cons M ms ih =>
    obtain ⟨hv, rfl, hc⟩ := h
    have e₁ : (⟨M :: ms, hv, rfl, hc⟩ : M.dom ⟶ b') = ofLayer M hv ≫ (⟨ms, hc⟩ : M.cod ⟶ b') := by
      ext; rfl
    have hodd : oddCount (⟨M :: ms, hv, rfl, hc⟩ : M.dom ⟶ b') =
        oddCountList [M] + oddCount (⟨ms, hc⟩ : M.cod ⟶ b') := oddCountList_cons M ms
    rw [hodd, e₁, whiskerL_comp, whiskerL_comp, ← Category.assoc, P.diag_comp (_ ≫ _),
      P.diag_swap_layer_right, Linear.smul_comp, P.diag_comp (whiskerL a _) (whiskerR f M.cod),
      Category.assoc, ← P.diag_comp (whiskerR f M.cod), ih hc, Linear.comp_smul, smul_smul,
      ← P.diag_comp, mul_add, pow_add, Category.assoc]

end Presentation

end StringDiagrams

end
