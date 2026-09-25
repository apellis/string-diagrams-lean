import StringDiagrams.Interchange

/-!
# Horizontal composition of diagrams and the interchange law for general regions

For a signature with arbitrary regions (a 2-category rather than a monoidal category), two
objects `a` and `b` can be placed side by side only when `a` ends in the region where `b`
starts. This file records that condition (`Obj.Composable`), defines the whiskered diagrams
`f ⊗ 1_b` and `1_a ⊗ g` under it (`Diagram.rwhisker`, `Diagram.lwhisker`), and proves the
interchange law for arbitrary diagrams without assuming a single region:

`(f ⊗ 1_b) ≫ (1_{a'} ⊗ g) = (-1)^{|f| |g|} (1_a ⊗ g) ≫ (f ⊗ 1_{b'})`

for `f : a ⟶ a'`, `g : b ⟶ b'` and `a.Composable b`
(`Presentation.diag_interchange_of_composable`). As in `StringDiagrams.Interchange`, it is
derived from the instances of the interchange law for single generators imposed in
`Presentation.Presented`, by induction on the numbers of layers; the only change is that the
generator on the left is now placed in its own left region.

For monoidal signatures the new whiskerings agree with `Diagram.whiskerR` and
`Diagram.whiskerL` (`Diagram.rwhisker_eq_whiskerR`, `Diagram.lwhisker_eq_whiskerL`).

## Main definitions and results

* `Obj.WF a`: the object `a` is well formed; `Obj.Composable a b`.
* `Chain.wf`: diagrams preserve well-formedness of objects;
  `Obj.Composable.map_left`, `Obj.Composable.map_right`: composability is preserved by
  diagrams on either side.
* `Diagram.rwhisker f b h : a.tensor b ⟶ a'.tensor b` and
  `Diagram.lwhisker a g h : a.tensor b ⟶ a.tensor b'`, with `rwhisker_comp`, `lwhisker_comp`.
* `Presentation.diag_interchange_of_composable`.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory

universe w v u₀ u₁ u₂

variable {S : Signature.{u₀, u₁, u₂}}

/-! ## Well-formed and composable objects -/

namespace Obj

/-- An object is well formed when its regions match up. -/
def WF (a : Obj S) : Prop := S.ok a.start a.word

/-- The objects `a` and `b` can be placed side by side: both are well formed and `a` ends in
the region where `b` starts. -/
structure Composable (a b : Obj S) : Prop where
  left_wf : a.WF
  endR_eq : a.endR = b.start
  right_wf : b.WF

theorem Composable.ok_endR {a b : Obj S} (h : a.Composable b) : S.ok a.endR b.word :=
  h.endR_eq ▸ h.right_wf

theorem endR_tensor (a b : Obj S) : (a.tensor b).endR = S.endR a.endR b.word := by
  simp [endR, tensor]

theorem Composable.endR_tensor {a b : Obj S} (h : a.Composable b) :
    (a.tensor b).endR = b.endR := by
  rw [Obj.endR_tensor, h.endR_eq]; rfl

theorem Composable.wf_tensor {a b : Obj S} (h : a.Composable b) : (a.tensor b).WF := by
  show S.ok a.start (a.word ++ b.word)
  rw [Signature.ok_append]; exact ⟨h.left_wf, h.ok_endR⟩

end Obj

theorem Layer.Valid.wf_dom {L : Layer S} (h : L.Valid) : L.dom.WF := by
  show S.ok L.start (L.left ++ S.dom L.gen ++ L.right)
  simp only [Signature.ok_append, Signature.endR_append, h.left_end, h.dom_end]
  exact ⟨⟨h.left_ok, h.dom_ok⟩, h.right_ok⟩

theorem Layer.Valid.wf_cod {L : Layer S} (h : L.Valid) : L.cod.WF := by
  show S.ok L.start (L.left ++ S.cod L.gen ++ L.right)
  simp only [Signature.ok_append, Signature.endR_append, h.left_end, h.cod_end]
  exact ⟨⟨h.left_ok, h.cod_ok⟩, h.right_ok⟩

/-- Diagrams preserve well-formedness of objects. -/
theorem Chain.wf {a b : Obj S} {ls : List (Layer S)} (h : Chain a ls b) (ha : a.WF) : b.WF := by
  induction ls generalizing a with
  | nil => cases h; exact ha
  | cons L ls ih => exact ih h.2.2 h.1.wf_cod

/-- Every layer of a diagram starts in the starting region of the diagram. -/
theorem Chain.start_of_mem {a b : Obj S} {ls : List (Layer S)} (h : Chain a ls b) {L : Layer S}
    (hL : L ∈ ls) : L.start = a.start := by
  induction ls generalizing a with
  | nil => cases hL
  | cons M ls ih =>
    obtain ⟨-, rfl, hc⟩ := h
    rcases List.mem_cons.mp hL with rfl | hL
    · rfl
    · have := ih hc hL
      exact this

namespace Obj.Composable

variable {a a' b b' : Obj S}

/-- Composability is preserved by a diagram on the left. -/
theorem map_left (h : a.Composable b) (f : a ⟶ a') : a'.Composable b :=
  ⟨(Diagram.chain f).wf h.left_wf, by rw [(Diagram.chain f).endR_eq]; exact h.endR_eq,
    h.right_wf⟩

/-- Composability is preserved by a diagram on the right. -/
theorem map_right (h : a.Composable b) (g : b ⟶ b') : a.Composable b' :=
  ⟨h.left_wf, by rw [(Diagram.chain g).start_eq]; exact h.endR_eq,
    (Diagram.chain g).wf h.right_wf⟩

end Obj.Composable

/-! ## Whiskering layers and chains -/

namespace Layer

theorem Valid.wr {L : Layer S} (h : L.Valid) {v : List S.Colour} (hv : S.ok L.dom.endR v) :
    (L.wr v).Valid where
  left_ok := h.left_ok
  left_end := h.left_end
  dom_ok := h.dom_ok
  dom_end := h.dom_end
  cod_ok := h.cod_ok
  cod_end := h.cod_end
  right_ok := by
    show S.ok (S.right L.gen) (L.right ++ v)
    rw [Signature.ok_append, ← h.endR_dom]; exact ⟨h.right_ok, hv⟩

theorem Valid.wl {L : Layer S} (h : L.Valid) {w : Obj S} (hw : w.WF) (he : w.endR = L.start) :
    (L.wl w).Valid where
  left_ok := by
    have he' : S.endR w.start w.word = L.start := he
    show S.ok w.start (w.word ++ L.left)
    rw [Signature.ok_append, he']; exact ⟨hw, h.left_ok⟩
  left_end := by
    have he' : S.endR w.start w.word = L.start := he
    show S.endR w.start (w.word ++ L.left) = S.left L.gen
    rw [Signature.endR_append, he']; exact h.left_end
  dom_ok := h.dom_ok
  dom_end := h.dom_end
  cod_ok := h.cod_ok
  cod_end := h.cod_end
  right_ok := h.right_ok

end Layer

/-- Right whiskering of a chain, for general regions. -/
theorem Chain.rwhisker {a a' : Obj S} {ls : List (Layer S)} (h : Chain a ls a') (b : Obj S)
    (hb : S.ok a.endR b.word) :
    Chain (a.tensor b) (ls.map (·.wr b.word)) (a'.tensor b) := by
  induction ls generalizing a with
  | nil => cases h; rfl
  | cons L ls ih =>
    obtain ⟨hv, rfl, hc⟩ := h
    exact ⟨hv.wr hb, L.wr_dom b, by rw [L.wr_cod]; exact ih hc (by rwa [hv.endR_eq])⟩

/-- Left whiskering of a chain, for general regions. -/
theorem Chain.lwhisker {b b' : Obj S} {ls : List (Layer S)} (h : Chain b ls b') (a : Obj S)
    (ha : a.WF) (he : a.endR = b.start) :
    Chain (a.tensor b) (ls.map (·.wl a)) (a.tensor b') := by
  induction ls generalizing b with
  | nil => cases h; rfl
  | cons L ls ih =>
    obtain ⟨hv, rfl, hc⟩ := h
    exact ⟨hv.wl ha he, L.wl_dom a, by rw [L.wl_cod]; exact ih hc he⟩

/-! ## Whiskering diagrams -/

namespace Diagram

variable {a a' a'' b b' b'' : Obj S}

/-- `f ⊗ 1_b`, for `a` composable with `b`. -/
def rwhisker (f : a ⟶ a') (b : Obj S) (h : a.Composable b) : a.tensor b ⟶ a'.tensor b :=
  mk ((layers f).map (·.wr b.word)) ((chain f).rwhisker b h.ok_endR)

/-- `1_a ⊗ g`, for `a` composable with `b`. -/
def lwhisker (a : Obj S) (g : b ⟶ b') (h : a.Composable b) : a.tensor b ⟶ a.tensor b' :=
  mk ((layers g).map (·.wl a)) ((chain g).lwhisker a h.left_wf h.endR_eq)

@[simp] theorem layers_rwhisker (f : a ⟶ a') (b : Obj S) (h : a.Composable b) :
    layers (rwhisker f b h) = (layers f).map (·.wr b.word) := rfl

@[simp] theorem layers_lwhisker (a : Obj S) (g : b ⟶ b') (h : a.Composable b) :
    layers (lwhisker a g h) = (layers g).map (·.wl a) := rfl

theorem rwhisker_id (a b : Obj S) (h : a.Composable b) : rwhisker (𝟙 a) b h = 𝟙 _ := rfl

theorem lwhisker_id (a b : Obj S) (h : a.Composable b) : lwhisker a (𝟙 b) h = 𝟙 _ := rfl

theorem rwhisker_comp (f : a ⟶ a') (f' : a' ⟶ a'') (b : Obj S) (h : a.Composable b)
    (h' : a'.Composable b) : rwhisker (f ≫ f') b h = rwhisker f b h ≫ rwhisker f' b h' := by
  ext; simp

theorem lwhisker_comp (a : Obj S) (g : b ⟶ b') (g' : b' ⟶ b'') (h : a.Composable b)
    (h' : a.Composable b') : lwhisker a (g ≫ g') h = lwhisker a g h ≫ lwhisker a g' h' := by
  ext; simp

/-- For monoidal signatures, `rwhisker` is `whiskerR`. -/
theorem rwhisker_eq_whiskerR [Subsingleton S.Region] (f : a ⟶ a') (b : Obj S)
    (h : a.Composable b) : rwhisker f b h = whiskerR f b := rfl

/-- For monoidal signatures, `lwhisker` is `whiskerL`. -/
theorem lwhisker_eq_whiskerL [Subsingleton S.Region] (a : Obj S) (g : b ⟶ b')
    (h : a.Composable b) : lwhisker a g h = whiskerL a g := rfl

@[simp] theorem oddCount_rwhisker (f : a ⟶ a') (b : Obj S) (h : a.Composable b) :
    oddCount (rwhisker f b h) = oddCount f :=
  oddCountList_map_wr _ _

@[simp] theorem oddCount_lwhisker (a : Obj S) (g : b ⟶ b') (h : a.Composable b) :
    oddCount (lwhisker a g h) = oddCount g :=
  oddCountList_map_wl _ _

end Diagram

/-! ## The interchange law -/

namespace InterchangeData

/-- The instance of the interchange law moving the layer `M` past the layer `L` on its left:
the generator of `L` is placed in its own left region, and the strands between the two
generators are the right strands of `L` followed by the left strands of `M`. -/
def ofLayers (L M : Layer S) : InterchangeData S :=
  ⟨S.left L.gen, L.gen, L.right ++ M.left, M.gen⟩

theorem valid_ofLayers {L M : Layer S} (hL : L.Valid) (hM : M.Valid)
    (h : L.dom.endR = M.start) : (ofLayers L M).Valid := by
  have hRM : S.endR (S.right L.gen) L.right = M.start := by rw [← hL.endR_dom, h]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  all_goals
    simp only [ofLayers, gh₁, gh₂, hg₁, hg₂, Signature.ok_append, Signature.endR_append,
      Signature.ok_nil, Signature.endR_nil, hL.dom_end, hL.cod_end, hRM, hM.left_end, hM.dom_end,
      hM.cod_end, hL.dom_ok, hL.cod_ok, hL.right_ok, hM.left_ok, hM.dom_ok, hM.cod_ok,
      hM.right_ok, true_and, and_true]

end InterchangeData

namespace Presentation

variable {R : Type w} [CommRing R] (P : Presentation.{w, v} S R)

open Diagram

variable {a a' b b' : Obj S}

/-- The interchange law for two single layers, for general regions. -/
theorem diag_swap_layers_of_composable (L M : Layer S) (hL : L.Valid) (hM : M.Valid)
    (h : L.dom.Composable M.dom) (h₁ : L.cod.Composable M.dom) (h₂ : L.dom.Composable M.cod) :
    P.diag (rwhisker (ofLayer L hL) M.dom h ≫ lwhisker L.cod (ofLayer M hM) h₁) =
      ((-1 : ℤ) ^ (oddCountList [L] * oddCountList [M])) •
        P.diag (lwhisker L.dom (ofLayer M hM) h ≫ rwhisker (ofLayer L hL) M.cod h₂) := by
  let x : InterchangeData S := InterchangeData.ofLayers L M
  have hx : x.Valid := InterchangeData.valid_ofLayers hL hM h.endR_eq
  let u : Obj S := ⟨L.start, L.left⟩
  have hw : x.dom.WhiskerOK u M.right := by
    refine ⟨hL.left_ok, hL.left_end, ?_⟩
    have : x.dom.endR = S.right M.gen := by
      have hRM : S.endR (S.right L.gen) L.right = M.start := by
        rw [← hL.endR_dom]; exact h.endR_eq
      simp [x, InterchangeData.ofLayers, InterchangeData.dom, Obj.endR, hL.dom_end, hRM,
        hM.left_end, hM.dom_end]
    rw [this]; exact hM.right_ok
  have ha : x.dom.whisker u M.right = L.dom.tensor M.dom := by
    simp [x, u, InterchangeData.ofLayers, InterchangeData.dom, Obj.whisker, Obj.tensor,
      Layer.dom]
  have hb : x.cod.whisker u M.right = L.cod.tensor M.cod := by
    simp [x, u, InterchangeData.ofLayers, InterchangeData.cod, Obj.whisker, Obj.tensor,
      Layer.cod]
  have key := P.diag_interchange x hx u M.right hw ha hb
  have hs : ((x.sign : ℤ) : R) = (((-1 : ℤ) ^ (oddCountList [L] * oddCountList [M]) : ℤ) : R) := by
    congr 1
    by_cases hL' : S.odd L.gen <;> by_cases hM' : S.odd M.gen <;>
      simp [x, InterchangeData.ofLayers, InterchangeData.sign, oddCountList, List.filter_cons,
        hL', hM']
  rw [hs, Int.cast_smul_eq_zsmul] at key
  refine Eq.trans (P.diag_eq_of_layers_eq ?_) (key.trans (congrArg _ (P.diag_eq_of_layers_eq ?_)))
  all_goals simp [x, u, InterchangeData.ofLayers, InterchangeData.ghDiagram,
      InterchangeData.hgDiagram, InterchangeData.gh₁, InterchangeData.gh₂, InterchangeData.hg₁,
      InterchangeData.hg₂, Layer.whisker, Layer.wr, Layer.wl, Layer.dom, Layer.cod, Obj.tensor]

/-- Moving a single layer on the right past a diagram on the left, for general regions. -/
theorem diag_swap_layer_right_of_composable (f : a ⟶ a') (M : Layer S) (hM : M.Valid)
    (h : a.Composable M.dom) (h₁ : a'.Composable M.dom) (h₂ : a.Composable M.cod) :
    P.diag (rwhisker f M.dom h ≫ lwhisker a' (ofLayer M hM) h₁) =
      ((-1 : ℤ) ^ (oddCount f * oddCountList [M])) •
        P.diag (lwhisker a (ofLayer M hM) h ≫ rwhisker f M.cod h₂) := by
  obtain ⟨ls, hf⟩ := f
  induction ls generalizing a with
  | nil =>
    cases hf
    simp only [oddCount, Diagram.layers, oddCountList_nil, zero_mul, pow_zero, one_smul]
    apply P.diag_eq_of_layers_eq
    simp only [layers_comp, layers_rwhisker, layers_lwhisker, layers_ofLayer]
    rfl
  | cons L ls ih =>
    obtain ⟨hv, rfl, hc⟩ := hf
    have e₁ : (⟨L :: ls, hv, rfl, hc⟩ : L.dom ⟶ a') = ofLayer L hv ≫ (⟨ls, hc⟩ : L.cod ⟶ a') := by
      ext; rfl
    have hodd : oddCount (⟨L :: ls, hv, rfl, hc⟩ : L.dom ⟶ a') =
        oddCountList [L] + oddCount (⟨ls, hc⟩ : L.cod ⟶ a') := oddCountList_cons L ls
    have hL₁ : L.cod.Composable M.dom := h.map_left (ofLayer L hv)
    have hL₂ : L.cod.Composable M.cod := hL₁.map_right (ofLayer M hM)
    rw [hodd, e₁, rwhisker_comp _ _ _ h hL₁, rwhisker_comp _ _ _ h₂ hL₂, Category.assoc,
      P.diag_comp, ih hL₁ hL₂ hc, Linear.comp_smul, ← P.diag_comp, ← Category.assoc,
      P.diag_comp (_ ≫ _), P.diag_swap_layers_of_composable L M hv hM h hL₁ h₂, Linear.smul_comp,
      smul_smul, ← P.diag_comp, Category.assoc, add_mul, pow_add, mul_comm]

/-- The interchange law for arbitrary diagrams, for general regions, with the composability
hypotheses at all four corners given separately. -/
theorem diag_interchange_of_composable' (f : a ⟶ a') (g : b ⟶ b') (h : a.Composable b)
    (h₁ : a'.Composable b) (h₂ : a.Composable b') :
    P.diag (rwhisker f b h ≫ lwhisker a' g h₁) =
      ((-1 : ℤ) ^ (oddCount f * oddCount g)) • P.diag (lwhisker a g h ≫ rwhisker f b' h₂) := by
  obtain ⟨ms, hg⟩ := g
  induction ms generalizing b with
  | nil =>
    cases hg
    simp only [oddCount, Diagram.layers, oddCountList_nil, mul_zero, pow_zero, one_smul]
    apply P.diag_eq_of_layers_eq
    simp only [layers_comp, layers_rwhisker, layers_lwhisker]
    show _ ++ [] = [] ++ _
    simp
  | cons M ms ih =>
    obtain ⟨hv, rfl, hc⟩ := hg
    have e₁ : (⟨M :: ms, hv, rfl, hc⟩ : M.dom ⟶ b') = ofLayer M hv ≫ (⟨ms, hc⟩ : M.cod ⟶ b') := by
      ext; rfl
    have hodd : oddCount (⟨M :: ms, hv, rfl, hc⟩ : M.dom ⟶ b') =
        oddCountList [M] + oddCount (⟨ms, hc⟩ : M.cod ⟶ b') := oddCountList_cons M ms
    have hM₁ : a.Composable M.cod := h.map_right (ofLayer M hv)
    have hM₂ : a'.Composable M.cod := h₁.map_right (ofLayer M hv)
    rw [hodd, e₁, lwhisker_comp _ _ _ h hM₁, lwhisker_comp _ _ _ h₁ hM₂, ← Category.assoc,
      P.diag_comp (_ ≫ _), P.diag_swap_layer_right_of_composable f M hv h h₁ hM₁,
      Linear.smul_comp, P.diag_comp (lwhisker a _ _) (rwhisker f M.cod _), Category.assoc,
      ← P.diag_comp (rwhisker f M.cod _), ih hM₁ hM₂ hc, Linear.comp_smul, smul_smul,
      ← P.diag_comp, mul_add, pow_add, Category.assoc]

/-- The interchange law for arbitrary diagrams, for general regions: if `a` ends in the
region where `b` starts (and both are well formed), then for `f : a ⟶ a'` and `g : b ⟶ b'`,
`(f ⊗ 1_b) ≫ (1_{a'} ⊗ g) = (-1)^{|f||g|} (1_a ⊗ g) ≫ (f ⊗ 1_{b'})`. -/
theorem diag_interchange_of_composable (f : a ⟶ a') (g : b ⟶ b') (h : a.Composable b) :
    P.diag (rwhisker f b h ≫ lwhisker a' g (h.map_left f)) =
      ((-1 : ℤ) ^ (oddCount f * oddCount g)) •
        P.diag (lwhisker a g h ≫ rwhisker f b' (h.map_right g)) :=
  P.diag_interchange_of_composable' f g h _ _

end Presentation

end StringDiagrams

end
