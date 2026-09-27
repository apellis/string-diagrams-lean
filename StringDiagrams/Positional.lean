import StringDiagrams.Transport
import StringDiagrams.Horizontal

/-!
# Diagrams described by their layers

When a relation or the interchange law is used at a given position, it is convenient to state
it for arbitrary diagrams whose lists of layers are prescribed: the boundary objects are then
determined by the layers (`Diagram.eq_dom_of_layers_eq_cons`,
`Diagram.eq_cod_of_layers_eq_append`), and no retyping of objects appears in the statement.

## Main results

* `Layer.eq_of_dom_eq`, `Layer.eq_of_cod_eq`: a layer is determined by its source (or target),
  the number of strands to the left of its generator, and its generator.
* `Presentation.diag_interchange_of_layers`: the interchange law for two generators `g`
  (on the left) and `h` (on the right) at an arbitrary position, for diagrams given by their
  layers, with the Koszul sign; `Presentation.diag_interchange_of_layers_of_even` without sign.
* `Presentation.linAlgHom`, `LinDiagram.whiskerAlgHom`, `Presentation.whiskAlgHom`: the
  quotient map and whiskering as homomorphisms of endomorphism algebras (so that they commute
  with the evaluation of polynomials in endomorphisms).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory

universe w v u₀ u₁ u₂

variable {S : Signature.{u₀, u₁, u₂}}

/-! ## Layers determined by their boundaries -/

private theorem append_three_inj {α : Type*} {l₁ w₁ r₁ l₂ w₂ r₂ : List α}
    (h : l₁ ++ w₁ ++ r₁ = l₂ ++ w₂ ++ r₂) (hl : l₁.length = l₂.length)
    (hw : w₁.length = w₂.length) : l₁ = l₂ ∧ w₁ = w₂ ∧ r₁ = r₂ := by
  rw [List.append_assoc, List.append_assoc] at h
  obtain ⟨rfl, h'⟩ := List.append_inj h hl
  obtain ⟨rfl, rfl⟩ := List.append_inj h' hw
  exact ⟨rfl, rfl, rfl⟩

namespace Layer

/-- A layer is determined by its source, the number of strands to the left of its generator,
and its generator. -/
theorem eq_of_dom_eq {L L' : Layer S} (hd : L.dom = L'.dom)
    (hl : L.left.length = L'.left.length) (hg : L.gen = L'.gen) : L = L' := by
  obtain ⟨st, l, g, r⟩ := L
  obtain ⟨st', l', g', r'⟩ := L'
  simp only at hl hg
  subst hg
  have hs : st = st' := congrArg Obj.start hd
  obtain ⟨rfl, -, rfl⟩ := append_three_inj (congrArg Obj.word hd) hl rfl
  rw [hs]

/-- A layer is determined by its target, the number of strands to the left of its generator,
and its generator. -/
theorem eq_of_cod_eq {L L' : Layer S} (hc : L.cod = L'.cod)
    (hl : L.left.length = L'.left.length) (hg : L.gen = L'.gen) : L = L' := by
  obtain ⟨st, l, g, r⟩ := L
  obtain ⟨st', l', g', r'⟩ := L'
  simp only at hl hg
  subst hg
  have hs : st = st' := congrArg Obj.start hc
  obtain ⟨rfl, -, rfl⟩ := append_three_inj (congrArg Obj.word hc) hl rfl
  rw [hs]

end Layer

/-! ## The interchange law for diagrams given by their layers -/

namespace Presentation

variable {R : Type w} [CommRing R] (P : Presentation.{w, v} S R)

/-- **The interchange law at an arbitrary position.** Let `f₁` be the diagram applying `g`
and then `h`, and `f₂` the diagram applying `h` and then `g`, where `g` and `h` sit side by
side (`g` on the left, separated by the strands `m`, with the strands `l` on the left and `v`
on the right). Then `f₁ = (-1)^{|g||h|} f₂` in the presented category. -/
theorem diag_interchange_of_layers {a b : Obj S} (r : S.Region) (l m v : List S.Colour)
    (g h : S.Gen) (f₁ f₂ : a ⟶ b)
    (h₁ : Diagram.layers f₁ = [⟨r, l, g, m ++ S.dom h ++ v⟩, ⟨r, l ++ S.cod g ++ m, h, v⟩])
    (h₂ : Diagram.layers f₂ = [⟨r, l ++ S.dom g ++ m, h, v⟩, ⟨r, l, g, m ++ S.cod h ++ v⟩]) :
    P.diag f₁ = ((if S.odd g && S.odd h then -1 else 1 : ℤ) : R) • P.diag f₂ := by
  obtain ⟨ha, -, hb⟩ := Diagram.eq_of_layers_eq_pair f₁ h₁
  have hc := Diagram.chain f₁
  rw [h₁] at hc
  obtain ⟨hv₁, -, hv₂, -, -⟩ := hc
  -- the regions around the two generators
  have hlg : S.endR r l = S.left g := hv₁.left_end
  have hmh : S.endR (S.right g) m = S.left h := by
    have := hv₂.left_end
    simp only [Signature.endR_append] at this
    rwa [hlg, hv₁.cod_end] at this
  have hm : S.ok (S.right g) m := by
    have := hv₁.right_ok
    simp only [Signature.ok_append] at this
    exact this.1.1
  let L : Layer S := ⟨r, l, g, []⟩
  let M : Layer S := ⟨S.right g, m, h, v⟩
  have hL : L.Valid := ⟨hv₁.left_ok, hv₁.left_end, hv₁.dom_ok, hv₁.dom_end, hv₁.cod_ok,
    hv₁.cod_end, trivial⟩
  have hM : M.Valid := ⟨hm, hmh, hv₂.dom_ok, hv₂.dom_end, hv₂.cod_ok, hv₂.cod_end, hv₂.right_ok⟩
  have hLM : L.dom.endR = M.start := by
    simp [L, M, Layer.dom, Obj.endR, hlg, hv₁.dom_end]
  let x : InterchangeData S := InterchangeData.ofLayers L M
  have hx : x.Valid := InterchangeData.valid_ofLayers hL hM hLM
  let u : Obj S := ⟨r, l⟩
  have hw : x.dom.WhiskerOK u v := by
    refine ⟨hv₁.left_ok, hlg, ?_⟩
    have : x.dom.endR = S.right h := by
      simp [x, L, M, InterchangeData.ofLayers, InterchangeData.dom, Obj.endR, hv₁.dom_end, hmh,
        hv₂.dom_end]
    rw [this]; exact hv₂.right_ok
  have ha' : x.dom.whisker u v = a := by
    rw [ha]
    simp [x, u, L, M, InterchangeData.ofLayers, InterchangeData.dom, Obj.whisker, Layer.dom]
  have hb' : x.cod.whisker u v = b := by
    rw [hb]
    simp [x, u, L, M, InterchangeData.ofLayers, InterchangeData.cod, Obj.whisker, Layer.cod]
  have key := P.diag_interchange x hx u v hw ha' hb'
  refine Eq.trans (P.diag_eq_of_layers_eq ?_) (key.trans (congrArg _ (P.diag_eq_of_layers_eq ?_)))
  all_goals simp only [Diagram.layers_cast, Diagram.layers_whisker]
  · simp [h₁, x, u, L, M, InterchangeData.ofLayers, InterchangeData.ghDiagram,
      InterchangeData.gh₁, InterchangeData.gh₂, Layer.whisker]
  · simp [h₂, x, u, L, M, InterchangeData.ofLayers, InterchangeData.hgDiagram,
      InterchangeData.hg₁, InterchangeData.hg₂, Layer.whisker]

/-- The interchange law at an arbitrary position, when one of the two generators is even. -/
theorem diag_interchange_of_layers_of_even {a b : Obj S} (r : S.Region) (l m v : List S.Colour)
    (g h : S.Gen) (hgh : S.odd g = false ∨ S.odd h = false) (f₁ f₂ : a ⟶ b)
    (h₁ : Diagram.layers f₁ = [⟨r, l, g, m ++ S.dom h ++ v⟩, ⟨r, l ++ S.cod g ++ m, h, v⟩])
    (h₂ : Diagram.layers f₂ = [⟨r, l ++ S.dom g ++ m, h, v⟩, ⟨r, l, g, m ++ S.cod h ++ v⟩]) :
    P.diag f₁ = P.diag f₂ := by
  rw [P.diag_interchange_of_layers r l m v g h f₁ f₂ h₁ h₂]
  rcases hgh with hg | hh <;> simp [*]

/-- The interchange law at an arbitrary position, for two odd generators. -/
theorem diag_interchange_of_layers_of_odd {a b : Obj S} (r : S.Region) (l m v : List S.Colour)
    (g h : S.Gen) (hg : S.odd g = true) (hh : S.odd h = true) (f₁ f₂ : a ⟶ b)
    (h₁ : Diagram.layers f₁ = [⟨r, l, g, m ++ S.dom h ++ v⟩, ⟨r, l ++ S.cod g ++ m, h, v⟩])
    (h₂ : Diagram.layers f₂ = [⟨r, l ++ S.dom g ++ m, h, v⟩, ⟨r, l, g, m ++ S.cod h ++ v⟩]) :
    P.diag f₁ = -P.diag f₂ := by
  rw [P.diag_interchange_of_layers r l m v g h f₁ f₂ h₁ h₂]
  simp [hg, hh]

/-! ## Endomorphism algebras -/

/-- The quotient map on endomorphisms, as a homomorphism of `R`-algebras. -/
def linAlgHom (a : Obj S) : End (Free.of R a) →ₐ[R] End (P.obj a) where
  toFun := P.lin
  map_one' := P.lin_id a
  map_mul' f g := P.lin_comp g f
  map_zero' := P.lin_zero
  map_add' := P.lin_add
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one]
    rw [P.lin_smul]
    exact congrArg (r • ·) (P.lin_id a)

@[simp] theorem linAlgHom_apply (a : Obj S) (f : End (Free.of R a)) : P.linAlgHom a f = P.lin f :=
  rfl

/-- Whiskering on endomorphisms of the presented category, as a homomorphism of `R`-algebras. -/
def whiskAlgHom (a u : Obj S) (v : List S.Colour) (hw : a.WhiskerOK u v) :
    End (P.obj a) →ₐ[R] End (P.obj (a.whisker u v)) where
  toFun f := P.whisk f u v
  map_one' := P.whisk_id a u v hw
  map_mul' f g := P.whisk_comp g f u v
  map_zero' := P.whisk_zero u v
  map_add' f g := P.whisk_add f g u v
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one]
    rw [P.whisk_smul]
    exact congrArg (r • ·) (P.whisk_id a u v hw)

@[simp] theorem whiskAlgHom_apply (a u : Obj S) (v : List S.Colour) (hw : a.WhiskerOK u v)
    (f : End (P.obj a)) : P.whiskAlgHom a u v hw f = P.whisk f u v := rfl

end Presentation

namespace LinDiagram

variable (R : Type w) [CommRing R]

/-- Whiskering on endomorphisms of the free linear 2-category, as a homomorphism of
`R`-algebras. -/
def whiskerAlgHom (a u : Obj S) (v : List S.Colour) (hw : a.WhiskerOK u v) :
    End (Free.of R a) →ₐ[R] End (Free.of R (a.whisker u v)) where
  toFun f := whisker f u v hw
  map_one' := whisker_single _ _ _ _ _
  map_mul' f g := whisker_comp g f u v hw hw
  map_zero' := Finsupp.mapDomain_zero
  map_add' f g := whisker_add f g u v hw
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one]
    rw [whisker_smul]
    exact congrArg (r • ·) (whisker_single _ _ _ _ _)

@[simp] theorem whiskerAlgHom_apply (a u : Obj S) (v : List S.Colour) (hw : a.WhiskerOK u v)
    (f : End (Free.of R a)) : whiskerAlgHom R a u v hw f = whisker f u v hw := rfl

end LinDiagram

end StringDiagrams

end
