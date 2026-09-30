import StringDiagrams.Positional

/-!
# The interchange law for diagrams side by side, with several regions

This is the interchange law for two diagrams side by side (`Presentation.diag_interchange_diagrams`
for monoidal signatures, `Presentation.diag_interchange_of_composable` for general regions) in a
positional form, like `Presentation.diag_interchange_of_layers` for single generators: two
diagrams given by lists of layers `F` (from `a` to `a'`) and `G` (from `b` to `b'`) are placed
side by side in the context

`u ⊗ (F) ⊗ m ⊗ (G) ⊗ v`

in a signature with arbitrary regions, and the statement is about arbitrary diagrams with the
resulting lists of layers, so that no retyping of objects appears. If every generator of `F` or
every generator of `G` facing it is even, applying `F` first and then `G`, or `G` first and then
`F`, gives the same morphism of the presented category
(`Presentation.diag_interchange_layers_of_even`).

## Main definitions and results

* `Obj.Ok a`: the word of `a` is well formed from its starting region; `Chain.ok` (well-formedness
  is preserved along a diagram).
* `Chain.of_append`: a chain of layers `ls ++ ms` splits at `Chain.target a ls`.
* `Presentation.diag_eq_of_layers_eq_append`: replacing, inside a diagram, a block of layers by a
  block with the same image does not change the image.
* `Presentation.diag_interchange_layers_of_even`: the interchange law for two diagrams.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory

universe w v u₀ u₁ u₂

variable {S : Signature.{u₀, u₁, u₂}}

/-! ## Well-formed objects and chains -/

/-- An object is well formed when its word is well formed from its starting region. -/
def Obj.Ok (a : Obj S) : Prop := S.ok a.start a.word

theorem Layer.Valid.dom_obj_ok {L : Layer S} (h : L.Valid) : L.dom.Ok := by
  simp only [Obj.Ok, Layer.dom, Signature.ok_append, Signature.endR_append]
  rw [h.left_end, h.dom_end]
  exact ⟨⟨h.left_ok, h.dom_ok⟩, h.right_ok⟩

theorem Layer.Valid.cod_obj_ok {L : Layer S} (h : L.Valid) : L.cod.Ok := by
  simp only [Obj.Ok, Layer.cod, Signature.ok_append, Signature.endR_append]
  rw [h.left_end, h.cod_end]
  exact ⟨⟨h.left_ok, h.cod_ok⟩, h.right_ok⟩

theorem Chain.ok {a b : Obj S} {ls : List (Layer S)} (h : Chain a ls b) (ha : a.Ok) : b.Ok := by
  induction ls generalizing a with
  | nil => cases h; exact ha
  | cons L ls ih => exact ih h.2.2 h.1.cod_obj_ok

theorem Chain.congr {a a' b b' : Obj S} {ls : List (Layer S)} (h : Chain a ls b) (ha : a = a')
    (hb : b = b') : Chain a' ls b' := by
  subst ha hb; exact h

theorem Chain.of_append {a b : Obj S} {ls ms : List (Layer S)} (h : Chain a (ls ++ ms) b) :
    Chain a ls (Chain.target a ls) ∧ Chain (Chain.target a ls) ms b := by
  induction ls generalizing a with
  | nil => exact ⟨rfl, h⟩
  | cons L ls ih =>
    obtain ⟨hv, rfl, hc⟩ := h
    obtain ⟨h₁, h₂⟩ := ih hc
    exact ⟨⟨hv, rfl, h₁⟩, h₂⟩

/-- The target of a chain is determined by its source and its layers. -/
theorem Chain.target_unique {a b b' : Obj S} {ls : List (Layer S)} (h : Chain a ls b)
    (h' : Chain a ls b') : b = b' :=
  (Chain.target_eq h).symm.trans (Chain.target_eq h')

/-- Two chains with the same layers ending at the same object start at the same object, unless
there are no layers. -/
theorem Chain.source_eq {a a' b : Obj S} {ls : List (Layer S)} (hne : ls ≠ [])
    (h : Chain a ls b) (h' : Chain a' ls b) : a = a' := by
  cases ls with
  | nil => exact absurd rfl hne
  | cons L ls => exact h.2.1.symm.trans h'.2.1

namespace Presentation

variable {R : Type w} [CommRing R] (P : Presentation.{w, v} S R)

theorem diag_mk_append {a b c : Obj S} {ls ms : List (Layer S)} (h₁ : Chain a ls b)
    (h₂ : Chain b ms c) :
    P.diag (Diagram.mk (ls ++ ms) (h₁.append h₂)) = P.diag (Diagram.mk ls h₁) ≫ P.diag (Diagram.mk ms h₂) := by
  rw [← P.diag_comp]; rfl

/-- Retyping: diagrams with the same layers between equal objects have the same image. -/
theorem diag_eq_of_diag_eq_of_layers {a b a' b' : Obj S} (f₁ f₂ : a ⟶ b) (g₁ g₂ : a' ⟶ b')
    (ha : a = a') (hb : b = b') (h₁ : Diagram.layers f₁ = Diagram.layers g₁)
    (h₂ : Diagram.layers f₂ = Diagram.layers g₂) (h : P.diag g₁ = P.diag g₂) :
    P.diag f₁ = P.diag f₂ := by
  subst ha hb
  rw [P.diag_eq_of_layers_eq h₁, P.diag_eq_of_layers_eq h₂, h]

/-- Replacing a block `Z` of layers by a block `Z'` with the same image does not change the image
of a diagram. -/
theorem diag_eq_of_layers_eq_append {a b : Obj S} (f₁ f₂ : a ⟶ b) (X Y Z Z' : List (Layer S))
    (h₁ : Diagram.layers f₁ = X ++ Z ++ Y) (h₂ : Diagram.layers f₂ = X ++ Z' ++ Y)
    (hZ : ∀ (c d : Obj S) (g₁ g₂ : c ⟶ d), Chain a X c → Diagram.layers g₁ = Z →
      Diagram.layers g₂ = Z' → P.diag g₁ = P.diag g₂) :
    P.diag f₁ = P.diag f₂ := by
  have c₁ := Diagram.chain f₁
  have c₂ := Diagram.chain f₂
  rw [h₁, List.append_assoc] at c₁
  rw [h₂, List.append_assoc] at c₂
  obtain ⟨hX, hZY⟩ := c₁.of_append
  obtain ⟨hX', hZY'⟩ := c₂.of_append
  obtain ⟨hZ₁, hY⟩ := hZY.of_append
  obtain ⟨hZ₂, hY'⟩ := hZY'.of_append
  -- the two blocks end at the same object
  have hd : Chain.target (Chain.target a X) Z = Chain.target (Chain.target a X) Z' := by
    by_cases hYe : Y = []
    · subst hYe; exact hY.trans hY'.symm
    · exact Chain.source_eq hYe hY hY'
  have e₁ : f₁ = Diagram.mk X hX ≫ Diagram.mk Z hZ₁ ≫ Diagram.mk Y hY := by
    apply Subtype.ext
    change Diagram.layers f₁ = Diagram.layers (Diagram.mk X hX ≫ Diagram.mk Z hZ₁ ≫ Diagram.mk Y hY)
    rw [h₁, Diagram.layers_comp, Diagram.layers_comp, List.append_assoc]; rfl
  have e₂ : f₂ = Diagram.mk X hX' ≫ Diagram.mk Z' (hZ₂.congr rfl hd.symm) ≫
      Diagram.mk Y (hY'.congr hd.symm rfl) := by
    apply Subtype.ext
    change Diagram.layers f₂ = Diagram.layers (Diagram.mk X hX' ≫ Diagram.mk Z' _ ≫ Diagram.mk Y _)
    rw [h₂, Diagram.layers_comp, Diagram.layers_comp, List.append_assoc]; rfl
  rw [e₁, e₂, P.diag_comp, P.diag_comp, P.diag_comp, P.diag_comp,
    hZ _ _ (Diagram.mk Z hZ₁) (Diagram.mk Z' (hZ₂.congr rfl hd.symm)) hX rfl rfl]

/-! ## Two diagrams side by side -/

section SideBySide

variable {a a' b b' : Obj S} (u : Obj S) (m v : List S.Colour)

/-- The object `u ⊗ c ⊗ m ⊗ e ⊗ v`. -/
abbrev sbs (c e : Obj S) : Obj S := ⟨u.start, u.word ++ c.word ++ m ++ e.word ++ v⟩

/-- The layers of `F` on the left, next to the object `e` on the right. -/
abbrev leftLayers (F : List (Layer S)) (e : Obj S) : List (Layer S) :=
  F.map (·.whisker u (m ++ e.word ++ v))

/-- The layers of `G` on the right, next to the object `c` on the left. -/
abbrev rightLayers (G : List (Layer S)) (c : Obj S) : List (Layer S) :=
  G.map (·.whisker ⟨u.start, u.word ++ c.word ++ m⟩ v)

/-- The hypotheses under which `F` and `G` can be placed side by side: the bottom boundary is
well formed and the regions match. -/
structure SideBySideOK (a b : Obj S) : Prop where
  ok : S.ok u.start (u.word ++ a.word ++ m ++ b.word ++ v)
  left_end : u.endR = a.start
  mid_end : S.endR a.endR m = b.start

variable {u m v}

theorem SideBySideOK.parts {a b : Obj S} (h : SideBySideOK u m v a b) :
    S.ok u.start u.word ∧ a.Ok ∧ S.ok a.endR m ∧ b.Ok ∧ S.ok b.endR v := by
  obtain ⟨hok, hu, hm⟩ := h
  have hu' : S.endR u.start u.word = a.start := hu
  simp only [Signature.ok_append, Signature.endR_append, hu'] at hok
  obtain ⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, h₅⟩ := hok
  have ha : S.endR a.start a.word = a.endR := rfl
  rw [ha, hm] at h₄ h₅
  exact ⟨h₁, h₂, h₃, h₄, h₅⟩

theorem SideBySideOK.of_ok {a b : Obj S} (hu : S.ok u.start u.word) (ha : a.Ok)
    (hm : S.ok a.endR m) (hb : b.Ok) (hv : S.ok b.endR v) (hua : u.endR = a.start)
    (hmb : S.endR a.endR m = b.start) : SideBySideOK u m v a b := by
  refine ⟨?_, hua, hmb⟩
  have hu' : S.endR u.start u.word = a.start := hua
  have ha' : S.endR a.start a.word = a.endR := rfl
  simp only [Signature.ok_append, Signature.endR_append, hu', ha', hmb]
  exact ⟨⟨⟨⟨hu, ha⟩, hm⟩, hb⟩, hv⟩

/-- Replacing `a` by the target of a chain from `a`, and `b` by the target of a chain from `b`,
preserves `SideBySideOK`. -/
theorem SideBySideOK.chain {a a' b b' : Obj S} (h : SideBySideOK u m v a b) {F G : List (Layer S)}
    (hF : Chain a F a') (hG : Chain b G b') : SideBySideOK u m v a' b' := by
  obtain ⟨hu, ha, hm, hb, hv⟩ := h.parts
  refine .of_ok hu (hF.ok ha) (by rw [hF.endR_eq]; exact hm) (hG.ok hb)
    (by rw [hG.endR_eq]; exact hv) (by rw [hF.start_eq]; exact h.left_end)
    (by rw [hF.endR_eq, hG.start_eq]; exact h.mid_end)

theorem chain_leftLayers {a a' e : Obj S} {F : List (Layer S)} (hF : Chain a F a')
    (h : SideBySideOK u m v a e) :
    Chain (sbs u m v a e) (leftLayers u m v F e) (sbs u m v a' e) := by
  obtain ⟨hu, -, hm, he, hv⟩ := h.parts
  have hw : a.WhiskerOK u (m ++ e.word ++ v) := by
    refine ⟨hu, h.left_end, ?_⟩
    simp only [Signature.ok_append, Signature.endR_append, h.mid_end]
    exact ⟨⟨hm, he⟩, hv⟩
  exact (hF.whisker hw).congr (by simp [Obj.whisker]) (by simp [Obj.whisker])

theorem chain_rightLayers {b b' c : Obj S} {G : List (Layer S)} (hG : Chain b G b')
    (h : SideBySideOK u m v c b) :
    Chain (sbs u m v c b) (rightLayers u m v G c) (sbs u m v c b') := by
  obtain ⟨hu, hc, hm, -, hv⟩ := h.parts
  have hw : b.WhiskerOK ⟨u.start, u.word ++ c.word ++ m⟩ v := by
    have hu' : S.endR u.start u.word = c.start := h.left_end
    have hc' : S.endR c.start c.word = c.endR := rfl
    refine ⟨?_, ?_, hv⟩
    · simp only [Signature.ok_append, Signature.endR_append, hu', hc']; exact ⟨⟨hu, hc⟩, hm⟩
    · show S.endR u.start (u.word ++ c.word ++ m) = b.start
      simp only [Signature.endR_append, hu', hc', h.mid_end]
  exact (hG.whisker hw).congr (by simp [Obj.whisker]) (by simp [Obj.whisker])

variable (u m v)

/-- One layer `M` on the right moves below a diagram `F` on the left. -/
theorem diag_interchange_layer_right {a a' : Obj S} {F : List (Layer S)} (hF : Chain a F a')
    {M : Layer S} (hM : M.Valid) (heven : ∀ L ∈ F, S.odd L.gen = false ∨ S.odd M.gen = false)
    (h : SideBySideOK u m v a M.dom)
    (f₁ f₂ : sbs u m v a M.dom ⟶ sbs u m v a' M.cod)
    (h₁ : Diagram.layers f₁ = leftLayers u m v F M.dom ++ rightLayers u m v [M] a')
    (h₂ : Diagram.layers f₂ = rightLayers u m v [M] a ++ leftLayers u m v F M.cod) :
    P.diag f₁ = P.diag f₂ := by
  induction F generalizing a with
  | nil =>
    cases hF
    exact P.diag_eq_of_layers_eq (by rw [h₁, h₂]; simp)
  | cons L F ih =>
    obtain ⟨hv, rfl, hc⟩ := hF
    have hL : SideBySideOK u m v L.cod M.dom := h.chain (F := [L]) (G := []) ⟨hv, rfl, rfl⟩ rfl
    have hLM : SideBySideOK u m v L.dom M.cod := h.chain (F := []) (G := [M]) rfl ⟨hM, rfl, rfl⟩
    -- intermediate diagram: `L` on the left, then `M` on the right, then the rest of `F`
    have c₃ : Chain (sbs u m v L.dom M.dom)
        (rightLayers u m v [M] L.dom ++ leftLayers u m v (L :: F) M.cod) (sbs u m v a' M.cod) :=
      (chain_rightLayers (G := [M]) ⟨hM, rfl, rfl⟩ h).append
        (chain_leftLayers ⟨hv, rfl, hc⟩ hLM)
    have c₄ : Chain (sbs u m v L.dom M.dom)
        (leftLayers u m v [L] M.dom ++ rightLayers u m v [M] L.cod ++ leftLayers u m v F M.cod)
        (sbs u m v a' M.cod) :=
      ((chain_leftLayers (F := [L]) ⟨hv, rfl, rfl⟩ h).append
        (chain_rightLayers (G := [M]) ⟨hM, rfl, rfl⟩ hL)).append
        (chain_leftLayers hc (h.chain (F := [L]) (G := [M]) ⟨hv, rfl, rfl⟩ ⟨hM, rfl, rfl⟩))
    -- move `M` below the rest of `F`
    have step₁ : P.diag f₁ = P.diag (Diagram.mk _ c₄) := by
      refine P.diag_eq_of_layers_eq_append f₁ _ (leftLayers u m v [L] M.dom) []
        (leftLayers u m v F M.dom ++ rightLayers u m v [M] a')
        (rightLayers u m v [M] L.cod ++ leftLayers u m v F M.cod)
        (by rw [h₁]; simp) (by simp [Diagram.mk, Diagram.layers]) ?_
      intro c d g₁ g₂ hX hg₁ hg₂
      obtain rfl := Chain.target_unique hX (chain_leftLayers (F := [L]) ⟨hv, rfl, rfl⟩ h)
      have hg := Diagram.chain g₁
      rw [hg₁] at hg
      obtain rfl := Chain.target_unique hg ((chain_leftLayers hc hL).append
        (chain_rightLayers (G := [M]) ⟨hM, rfl, rfl⟩ (hL.chain (G := []) hc rfl)))
      exact ih hc (fun L' hL' => heven L' (List.mem_cons_of_mem _ hL')) hL g₁ g₂ hg₁ hg₂
    -- swap `L` and `M`
    have step₂ : P.diag (Diagram.mk _ c₄) = P.diag (Diagram.mk _ c₃) := by
      refine P.diag_eq_of_layers_eq_append _ _ [] (leftLayers u m v F M.cod)
        (leftLayers u m v [L] M.dom ++ rightLayers u m v [M] L.cod)
        (rightLayers u m v [M] L.dom ++ leftLayers u m v [L] M.cod)
        (by simp [Diagram.mk, Diagram.layers]) (by simp [Diagram.mk, Diagram.layers]) ?_
      intro c d g₁ g₂ _ hg₁ hg₂
      refine P.diag_interchange_of_layers_of_even u.start (u.word ++ L.left)
        (L.right ++ m ++ M.left) (M.right ++ v) L.gen M.gen
        (heven L List.mem_cons_self) g₁ g₂ ?_ ?_
      · rw [hg₁]; simp [Layer.whisker, Layer.dom, Layer.cod]
      · rw [hg₂]; simp [Layer.whisker, Layer.dom, Layer.cod]
    rw [step₁, step₂]
    exact P.diag_eq_of_layers_eq (by rw [h₂]; simp [Diagram.mk, Diagram.layers])

/-- **The interchange law for two diagrams side by side**, in a signature with arbitrary
regions: for chains of layers `F` from `a` to `a'` and `G` from `b` to `b'` placed as
`u ⊗ F ⊗ m ⊗ G ⊗ v`, where every generator of `F` or every generator of `G` facing it is even,
the diagram applying `F` and then `G` and the one applying `G` and then `F` have the same image
in the presented category. -/
theorem diag_interchange_layers_of_even {a a' b b' : Obj S} {F G : List (Layer S)}
    (hF : Chain a F a') (hG : Chain b G b')
    (heven : ∀ L ∈ F, ∀ M ∈ G, S.odd L.gen = false ∨ S.odd M.gen = false)
    (h : SideBySideOK u m v a b) (f₁ f₂ : sbs u m v a b ⟶ sbs u m v a' b')
    (h₁ : Diagram.layers f₁ = leftLayers u m v F b ++ rightLayers u m v G a')
    (h₂ : Diagram.layers f₂ = rightLayers u m v G a ++ leftLayers u m v F b') :
    P.diag f₁ = P.diag f₂ := by
  induction G generalizing b with
  | nil =>
    cases hG
    exact P.diag_eq_of_layers_eq (by rw [h₁, h₂]; simp)
  | cons M G ih =>
    obtain ⟨hM, rfl, hc⟩ := hG
    have hM' : SideBySideOK u m v a M.cod := h.chain (F := []) (G := [M]) rfl ⟨hM, rfl, rfl⟩
    -- intermediate diagram: `M`, then `F`, then the rest of `G`
    have c₃ : Chain (sbs u m v a M.dom)
        (rightLayers u m v [M] a ++ leftLayers u m v F M.cod ++ rightLayers u m v G a')
        (sbs u m v a' b') :=
      ((chain_rightLayers (G := [M]) ⟨hM, rfl, rfl⟩ h).append (chain_leftLayers hF hM')).append
        (chain_rightLayers hc (hM'.chain (G := []) hF rfl))
    have step₁ : P.diag f₁ = P.diag (Diagram.mk _ c₃) := by
      refine P.diag_eq_of_layers_eq_append f₁ _ [] (rightLayers u m v G a')
        (leftLayers u m v F M.dom ++ rightLayers u m v [M] a')
        (rightLayers u m v [M] a ++ leftLayers u m v F M.cod)
        (by rw [h₁]; simp) (by simp [Diagram.mk, Diagram.layers]) ?_
      intro c d g₁ g₂ hX hg₁ hg₂
      cases hX
      have hg := Diagram.chain g₁
      rw [hg₁] at hg
      obtain rfl := Chain.target_unique hg ((chain_leftLayers hF h).append
        (chain_rightLayers (G := [M]) ⟨hM, rfl, rfl⟩ (h.chain (G := []) hF rfl)))
      exact P.diag_interchange_layer_right u m v hF hM
        (fun L hL => heven L hL M List.mem_cons_self) h g₁ g₂ hg₁ hg₂
    have step₂ : P.diag (Diagram.mk _ c₃) = P.diag f₂ := by
      refine P.diag_eq_of_layers_eq_append _ f₂ (rightLayers u m v [M] a) []
        (leftLayers u m v F M.cod ++ rightLayers u m v G a')
        (rightLayers u m v G a ++ leftLayers u m v F b')
        (by simp [Diagram.mk, Diagram.layers]) (by rw [h₂]; simp) ?_
      intro c d g₁ g₂ hX hg₁ hg₂
      obtain rfl := Chain.target_unique hX (chain_rightLayers (G := [M]) ⟨hM, rfl, rfl⟩ h)
      have hg := Diagram.chain g₁
      rw [hg₁] at hg
      obtain rfl := Chain.target_unique hg ((chain_leftLayers hF hM').append
        (chain_rightLayers hc (hM'.chain (G := []) hF rfl)))
      exact ih hc (fun L hL M' hM'' => heven L hL M' (List.mem_cons_of_mem _ hM'')) hM' g₁ g₂
        hg₁ hg₂
    exact step₁.trans step₂

end SideBySide

end Presentation

end StringDiagrams
