import StringDiagrams.Presentation

/-!
# Generation of presented categories by layers

Every morphism of a presented category is an `R`-linear combination of classes of diagrams
(`Presentation.hom_induction`), and every diagram is a composite of single layers
(`Diagram.eq_layer_comp`, `Presentation.diag_induction`). Consequently a property of
morphisms that holds for identities (retyped along equalities of objects) and single layers
and is stable under composition, sums and scalar multiples holds for all morphisms
(`Presentation.hom_induction_layers`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory

universe w v u₀ u₁ u₂

variable {S : Signature.{u₀, u₁, u₂}}

namespace Diagram

variable {a b : Obj S}

/-- A diagram with at least one layer is its first layer followed by the rest. -/
theorem eq_layer_comp {L : Layer S} {ls : List (Layer S)} (h : Chain a (L :: ls) b) :
    mk (L :: ls) h = layer L h.1 h.2.1 rfl ≫ mk ls h.2.2 := by
  ext; simp

/-- The empty diagram is an identity, retyped. -/
theorem mk_nil (h : Chain a [] b) : mk [] h = eqToHom h := by
  ext; simp

end Diagram

namespace Presentation

variable {R : Type w} [CommRing R] (P : Presentation.{w, v} S R)

/-- Induction on morphisms of the presented category: classes of diagrams, sums, scalar
multiples. -/
theorem hom_induction {a b : Obj S} {p : (P.obj a ⟶ P.obj b) → Prop}
    (diag : ∀ d : a ⟶ b, p (P.diag d)) (zero : p 0) (add : ∀ f g, p f → p g → p (f + g))
    (smul : ∀ (r : R) f, p f → p (r • f)) (f : P.obj a ⟶ P.obj b) : p f := by
  obtain ⟨f, rfl⟩ := P.linFunctor.map_surjective f
  change p (P.lin f)
  induction f using Finsupp.induction_linear with
  | zero => rw [lin_zero]; exact zero
  | add f g hf hg => rw [lin_add]; exact add _ _ hf hg
  | single d r => rw [lin_single]; exact smul r _ (diag d)

/-- Induction on diagrams: retyped identities, and a layer followed by a diagram. -/
theorem diag_induction {p : ∀ {a b : Obj S}, (P.obj a ⟶ P.obj b) → Prop}
    (nil : ∀ {a b : Obj S} (h : a = b), p (P.diag (eqToHom h)))
    (cons : ∀ {b : Obj S} (L : Layer S) (hv : L.Valid) (d : L.cod ⟶ b),
      p (P.diag d) → p (P.diag (Diagram.ofLayer L hv ≫ d)))
    {a b : Obj S} (d : a ⟶ b) : p (P.diag d) := by
  obtain ⟨ls, h⟩ := d
  induction ls generalizing a with
  | nil =>
    have e : (⟨[], h⟩ : a ⟶ b) = eqToHom h := Diagram.mk_nil h
    rw [e]; exact nil h
  | cons L ls ih =>
    obtain ⟨hv, rfl, hc⟩ := h
    exact cons L hv _ (ih hc)

/-- Induction on morphisms of the presented category via layers. -/
theorem hom_induction_layers {p : ∀ {a b : Obj S}, (P.obj a ⟶ P.obj b) → Prop}
    (nil : ∀ {a b : Obj S} (h : a = b), p (P.diag (eqToHom h)))
    (layer : ∀ (L : Layer S) (hv : L.Valid), p (P.diag (Diagram.ofLayer L hv)))
    (comp : ∀ {a b c : Obj S} (f : P.obj a ⟶ P.obj b) (g : P.obj b ⟶ P.obj c),
      p f → p g → p (f ≫ g))
    (zero : ∀ {a b : Obj S}, p (0 : P.obj a ⟶ P.obj b))
    (add : ∀ {a b : Obj S} (f g : P.obj a ⟶ P.obj b), p f → p g → p (f + g))
    (smul : ∀ {a b : Obj S} (r : R) (f : P.obj a ⟶ P.obj b), p f → p (r • f))
    {a b : Obj S} (f : P.obj a ⟶ P.obj b) : p f :=
  P.hom_induction (p := p)
    (P.diag_induction (p := p) nil fun L hv d hd => by
      rw [diag_comp]; exact comp _ _ (layer L hv) hd)
    zero add smul f

end Presentation

end StringDiagrams

end
