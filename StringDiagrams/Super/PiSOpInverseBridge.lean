import StringDiagrams.Super.PiSOpTwo

/-!
# The inverse of the parity bridge on hom categories

`PiSOp.bridge : (𝒜^{sop})_π → (𝒜_π)^{sop}` is the graded superequivalence of
arXiv:1701.04133v2, §9 (before Lemma 9.1), which multiplies a morphism from `Πᵃ` to `Πᵇ` by the
sign `PiSOp.correction`. Since this sign squares to one, the same correction gives a strict
inverse `PiSOp.reverseBridge`: both composites are equal to identity functors
(`PiSOp.bridge_comp_reverseBridge`, `PiSOp.reverseBridge_comp_bridge`), and the inverse is a
graded superfunctor.
-/
noncomputable section
namespace StringDiagrams.PiSOp
open CategoryTheory Supercategory GradedSupercategory
universe r u v
variable {R : Type r} [CommRing R] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear R C] [Supercategory R C]

/-- Unwrap the target, retaining the parity tag and the underlying object. -/
def reverseBridgeObj (X : SOp R (Envelope R C)) : Envelope R (SOp R C) :=
  ⟨X.unop.par, ⟨X.unop.obj⟩⟩

/-- Apply the same ordered endpoint correction to the underlying reverse morphism. -/
def reverseBridgeMap {X Y : SOp R (Envelope R C)} (f : X ⟶ Y) :
    reverseBridgeObj X ⟶ reverseBridgeObj Y :=
  Envelope.ofHom (SOp.mk' (correction (R := R) X.unop.par Y.unop.par
    (Envelope.toHom (SOp.unsop f))))

/-- The bridge after the inverse is the identity on morphisms. -/
theorem bridge_reverseBridgeMap {X Y : SOp R (Envelope R C)} (f : X ⟶ Y) :
    bridge.map (reverseBridgeMap f) = f := by
  apply SOp.hom_ext
  exact correction_twice X.unop.par Y.unop.par (Envelope.toHom (SOp.unsop f))

/-- The inverse after the bridge is the identity on morphisms. -/
theorem reverseBridgeMap_bridge {X Y : Envelope R (SOp R C)} (f : X ⟶ Y) :
    reverseBridgeMap (bridge.map f) = f := by
  apply Envelope.hom_ext
  apply SOp.hom_ext
  exact correction_twice X.par Y.par (SOp.unsop (Envelope.toHom f))

/-- The reverse is a functor; composition is reflected through the faithful bridge. -/
def reverseBridge : SOp R (Envelope R C) ⥤ Envelope R (SOp R C) where
  obj := reverseBridgeObj
  map := reverseBridgeMap
  map_id X := by
    apply (bridge (R := R) (C := C)).map_injective
    rw [bridge_reverseBridgeMap]
    exact (bridge.map_id (reverseBridgeObj X)).symm
  map_comp f g := by
    apply (bridge (R := R) (C := C)).map_injective
    rw [bridge_reverseBridgeMap, Functor.map_comp,
      bridge_reverseBridgeMap, bridge_reverseBridgeMap]
    rfl

instance reverseBridge_additive : (reverseBridge (R := R) (C := C)).Additive where
  map_add {X Y} f g := by
    apply (bridge (R := R) (C := C)).map_injective
    change bridge.map (reverseBridgeMap (f + g)) =
      bridge.map (reverseBridgeMap f + reverseBridgeMap g)
    rw [bridge_reverseBridgeMap, Functor.map_add,
      bridge_reverseBridgeMap, bridge_reverseBridgeMap]
    rfl

instance reverseBridge_linear : (reverseBridge (R := R) (C := C)).Linear R where
  map_smul {X Y} f r := by
    apply (bridge (R := R) (C := C)).map_injective
    change bridge.map (reverseBridgeMap (r • f)) = bridge.map (r • reverseBridgeMap f)
    rw [bridge_reverseBridgeMap, Functor.map_smul, bridge_reverseBridgeMap]
    rfl

instance reverseBridge_super : IsSuperfunctor R (reverseBridge (R := R) (C := C)) where
  map_mem {X Y p f} hf := by
    change correction (R := R) X.unop.par Y.unop.par (Envelope.toHom (SOp.unsop f)) ∈
      parity (R := R) Y.unop.obj X.unop.obj (p + (X.unop.par + Y.unop.par))
    have hf' : Envelope.toHom (SOp.unsop f) ∈
        parity (R := R) Y.unop.obj X.unop.obj (p + (Y.unop.par + X.unop.par)) := hf
    rw [add_comm Y.unop.par X.unop.par] at hf'
    exact correction_mem _ _ hf'

/-- The bridge followed by its inverse is the identity functor. -/
theorem bridge_comp_reverseBridge :
    bridge (R := R) (C := C) ⋙ reverseBridge = 𝟭 _ := by
  refine CategoryTheory.Functor.ext (F := bridge ⋙ reverseBridge) (G := 𝟭 _)
    (fun _ => rfl) ?_
  intro X Y f
  change reverseBridgeMap (bridge.map f) = 𝟙 X ≫ f ≫ 𝟙 Y
  rw [Category.id_comp, Category.comp_id]
  exact reverseBridgeMap_bridge f

/-- The inverse followed by the bridge is the identity functor. -/
theorem reverseBridge_comp_bridge :
    reverseBridge (R := R) (C := C) ⋙ bridge = 𝟭 _ := by
  refine CategoryTheory.Functor.ext (F := reverseBridge ⋙ bridge) (G := 𝟭 _)
    (fun _ => rfl) ?_
  intro X Y f
  change bridge.map (reverseBridgeMap f) = 𝟙 X ≫ f ≫ 𝟙 Y
  rw [Category.id_comp, Category.comp_id]
  exact bridge_reverseBridgeMap f

variable [GradedSupercategory R C]

/-- The correction sign preserves every integer degree. -/
instance reverseBridge_graded : IsGradedSuperfunctor R (reverseBridge (R := R) (C := C)) where
  map_mem_degree {X Y n f} hf := by
    change sign R (X.unop.par * (X.unop.par + Y.unop.par)) •
        twist R (X.unop.par + Y.unop.par) (Envelope.toHom (SOp.unsop f)) ∈
      degree (R := R) Y.unop.obj X.unop.obj n
    have hf' : Envelope.toHom (SOp.unsop f) ∈
        degree (R := R) Y.unop.obj X.unop.obj n := hf
    exact Submodule.smul_mem _ _ (twist_mem_degree _ hf')
end StringDiagrams.PiSOp
