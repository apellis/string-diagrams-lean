import StringDiagrams.Super.Presented

/-!
# Endomorphisms of identity 1-morphisms commute (Eckmann–Hilton)

In a presented 2-category, the endomorphisms of the empty word `Obj.nil r` (the identity
1-morphism of the region `r`; the unit object `Obj.unit` in the monoidal case) commute: both
`f ≫ g` and `g ≫ f` are horizontal composites of `f` and `g`, which agree by the interchange
law. For even signatures this makes `End (P.obj (Obj.nil r))` a commutative ring
(`Presentation.nilEndCommRing`); in general, homogeneous endomorphisms of parities `p` and `q`
supercommute, `f ≫ g = (-1)^{pq} g ≫ f` (`Presentation.nil_comp_comm_super`).

## Main results

* `Presentation.nil_comp_comm`, `Presentation.nil_commute`, `Presentation.nilEndCommRing`
  (even signatures, arbitrary regions).
* `Presentation.nil_comp_comm_super` (homogeneous morphisms, with the Koszul sign).
* `Presentation.unit_comp_comm` (the monoidal unit).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory

universe w v u₀ u₁ u₂

variable {S : Signature.{u₀, u₁, u₂}}

namespace Presentation

variable {R : Type w} [CommRing R] (P : Presentation.{w, v} S R)

theorem nil_composable (r : S.Region) : (Obj.nil r).Composable (Obj.nil r) :=
  ⟨trivial, rfl, trivial⟩

/-- Right whiskering by the empty word of the same region is the identity on endomorphisms of
the empty word. -/
theorem wRAt_nil_nil (r : S.Region) (f : P.obj (Obj.nil r) ⟶ P.obj (Obj.nil r)) :
    P.wRAt r f (Obj.nil r) rfl rfl = f := by
  rw [P.wRAt_nil (s := r) (r := r) f trivial rfl rfl rfl]
  simp

/-- Left whiskering by the empty word of the same region is the identity on endomorphisms of
the empty word. -/
theorem wL_nil_nil (r : S.Region) (g : P.obj (Obj.nil r) ⟶ P.obj (Obj.nil r)) :
    P.wL (Obj.nil r) g = g := by
  rw [P.wL_nil (r := r) g trivial rfl rfl]
  simp

/-- **Eckmann–Hilton.** For an even signature, endomorphisms of an identity 1-morphism
commute. -/
theorem nil_comp_comm [S.IsEven] (r : S.Region) (f g : P.obj (Obj.nil r) ⟶ P.obj (Obj.nil r)) :
    f ≫ g = g ≫ f := by
  have key := P.wRAt_comp_wL (r := r) (nil_composable r) f g rfl rfl
  rwa [wRAt_nil_nil, wL_nil_nil] at key

theorem nil_commute [S.IsEven] (r : S.Region) (f g : End (P.obj (Obj.nil r))) : Commute f g :=
  P.nil_comp_comm r g f

/-- For an even signature, the endomorphism ring of an identity 1-morphism is commutative. -/
abbrev nilEndCommRing [S.IsEven] (r : S.Region) : CommRing (End (P.obj (Obj.nil r))) :=
  { (inferInstance : Ring (End (P.obj (Obj.nil r)))) with
    mul_comm := fun f g => P.nil_comp_comm r g f }

/-- **Eckmann–Hilton, super version.** Homogeneous endomorphisms of an identity 1-morphism
of parities `p` and `q` supercommute: `f ≫ g = (-1)^{pq} g ≫ f`. -/
theorem nil_comp_comm_super (r : S.Region) {p q : ZMod 2}
    {f g : P.obj (Obj.nil r) ⟶ P.obj (Obj.nil r)}
    (hf : f ∈ P.homDeg (parityDeg S) (Obj.nil r) (Obj.nil r) p)
    (hg : g ∈ P.homDeg (parityDeg S) (Obj.nil r) (Obj.nil r) q) :
    f ≫ g = koszulSign p q • (g ≫ f) := by
  have key := P.wRAt_comp_wL_super (r := r) (nil_composable r) hf hg rfl rfl
  rwa [wRAt_nil_nil, wL_nil_nil] at key

/-- The monoidal case: for an even signature, endomorphisms of the unit object commute. -/
theorem unit_comp_comm [S.IsEven] [Inhabited S.Region]
    (f g : P.obj Obj.unit ⟶ P.obj Obj.unit) : f ≫ g = g ≫ f :=
  P.nil_comp_comm default f g

end Presentation

end StringDiagrams

end
