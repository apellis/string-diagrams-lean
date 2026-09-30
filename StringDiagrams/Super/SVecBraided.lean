import StringDiagrams.Super.SVec
import StringDiagrams.Super.Braided

/-!
# The symmetric braiding of superspaces

J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §1.2 (after
Example 1.2(iv)) and §2 (before Definition 2.1): the monoidal category `SVec̲` of superspaces and
even linear maps is symmetric with braiding `u ⊗ v ↦ (-1)^{|u||v|} v ⊗ u`.

* `SVec.braidingMap V W : V ⊗ W → W ⊗ V` is `TensorProduct.comm` twisted by the parity signs,
  `c_{V,W} = comm ∘ (proj₀ ⊗ 1 + proj₁ ⊗ sgn)`; on homogeneous vectors
  `c_{V,W}(v ⊗ w) = (-1)^{|v||w|} w ⊗ v` (`SVec.braidingMap_tmul`). It is even
  (`SVec.braidingMap_mem`) and `c_{W,V} ∘ c_{V,W} = 1` (`SVec.braidingMap_comp_braidingMap`).
* `c` is natural in each variable for all (not necessarily homogeneous) linear maps, with the
  Koszul sign rule of the whiskerings of `SVec k` (`SVec.braidingMap_naturality_right`,
  `SVec.braidingMap_naturality_left`), and satisfies the two hexagon axioms
  (`SVec.hexagon_forward`, `SVec.hexagon_reverse`): `SVec k` is a braided monoidal
  supercategory (`SVec.instBraidedMonoidalSupercategory`), and the braiding is symmetric
  (`SVec.braiding_hom_comp_braiding_hom`).
* A braided monoidal supercategory has an underlying braided monoidal category (even
  morphisms, `Underlying.instBraidedCategory`); for `SVec k` this is the symmetric monoidal
  category `SVec̲` of the paper (`SVec.instSymmetricCategoryUnderlying`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory MonoidalCategory Supercategory TensorProduct

/-! ## The underlying braided monoidal category -/

namespace Underlying

universe w w₁ w₂

variable {R : Type w} [CommRing R] {C : Type w₁} [Category.{w₂} C] [Preadditive C] [Linear R C]
  [Supercategory R C] [MonoidalCategoryStruct C] [MonoidalSupercategory R C]
  [BraidedMonoidalSupercategory R C]

/-- The underlying category of even morphisms of a braided monoidal supercategory is a braided
monoidal category. -/
instance instBraidedCategory : BraidedCategory (Underlying R C) where
  braiding X Y := isoMk (BraidedMonoidalSupercategory.braiding (R := R) X.obj Y.obj)
    (BraidedMonoidalSupercategory.braiding_hom_mem X.obj Y.obj)
  braiding_naturality_right X _ _ f :=
    Subtype.ext (BraidedMonoidalSupercategory.braiding_naturality_right X.obj f.1)
  braiding_naturality_left f Z :=
    Subtype.ext (BraidedMonoidalSupercategory.braiding_naturality_left f.1 Z.obj)
  hexagon_forward X Y Z :=
    Subtype.ext (BraidedMonoidalSupercategory.hexagon_forward (R := R) X.obj Y.obj Z.obj)
  hexagon_reverse X Y Z :=
    Subtype.ext (BraidedMonoidalSupercategory.hexagon_reverse (R := R) X.obj Y.obj Z.obj)

@[simp] theorem braiding_hom_val (X Y : Underlying R C) :
    (β_ X Y).hom.1 = (BraidedMonoidalSupercategory.braiding (R := R) X.obj Y.obj).hom := rfl

@[simp] theorem braiding_inv_val (X Y : Underlying R C) :
    (β_ X Y).inv.1 = (BraidedMonoidalSupercategory.braiding (R := R) X.obj Y.obj).inv := rfl

end Underlying

namespace SVec

universe u

variable {k : Type u} [CommRing k]

/-! ## Homogeneous tensors of three factors -/

/-- Linear maps out of `(U ⊗ V) ⊗ W` agreeing on tensors of homogeneous vectors are equal. -/
theorem ext_tensor₃ {U V W : SVec k} {M : Type u} [AddCommGroup M] [Module k M]
    {f g : (U ⊗[k] V) ⊗[k] W →ₗ[k] M}
    (h : ∀ p q r (u : U) (v : V) (w : W), u ∈ U.part p → v ∈ V.part q → w ∈ W.part r →
      f ((u ⊗ₜ v) ⊗ₜ w) = g ((u ⊗ₜ v) ⊗ₜ w)) : f = g := by
  apply TensorProduct.ext'
  intro x w
  have key : ∀ r, f ∘ₗ (TensorProduct.mk k (U ⊗[k] V) W).flip (W.proj r w) =
      g ∘ₗ (TensorProduct.mk k (U ⊗[k] V) W).flip (W.proj r w) := fun r =>
    ext_tensor fun p q u v hu hv => h p q r u v _ hu hv (proj_mem_part W r w)
  rw [← proj_apply_add W w, tmul_add, map_add, map_add]
  exact congrArg₂ (· + ·) (LinearMap.congr_fun (key 0) x) (LinearMap.congr_fun (key 1) x)

/-- Linear maps out of `U ⊗ (V ⊗ W)` agreeing on tensors of homogeneous vectors are equal. -/
theorem ext_tensor₃' {U V W : SVec k} {M : Type u} [AddCommGroup M] [Module k M]
    {f g : U ⊗[k] (V ⊗[k] W) →ₗ[k] M}
    (h : ∀ p q r (u : U) (v : V) (w : W), u ∈ U.part p → v ∈ V.part q → w ∈ W.part r →
      f (u ⊗ₜ (v ⊗ₜ w)) = g (u ⊗ₜ (v ⊗ₜ w))) : f = g := by
  apply TensorProduct.ext'
  intro u y
  have key : ∀ p, f ∘ₗ TensorProduct.mk k U (V ⊗[k] W) (U.proj p u) =
      g ∘ₗ TensorProduct.mk k U (V ⊗[k] W) (U.proj p u) := fun p =>
    ext_tensor fun q r v w hv hw => h p q r _ v w (proj_mem_part U p u) hv hw
  rw [← proj_apply_add U u, add_tmul, map_add, map_add]
  exact congrArg₂ (· + ·) (LinearMap.congr_fun (key 0) y) (LinearMap.congr_fun (key 1) y)

/-! ## The braiding -/

/-- The braiding `c_{V,W} : V ⊗ W → W ⊗ V`, `v ⊗ w ↦ (-1)^{|v||w|} w ⊗ v`: the flip of
`TensorProduct.comm` after `proj₀ ⊗ 1 + proj₁ ⊗ sgn`. -/
def braidingMap (V W : SVec k) : tensorObj V W ⟶ tensorObj W V :=
  ofHom ((TensorProduct.comm k V W).toLinearMap ∘ₗ
    (map (V.proj 0) LinearMap.id + map (V.proj 1) (W.sgn 1)))

/-- **Brundan–Ellis, §1.2.** `c_{V,W}(v ⊗ w) = (-1)^{|v||w|} w ⊗ v` for homogeneous
`v` and `w`. -/
theorem braidingMap_tmul {V W : SVec k} {p q : ZMod 2} {v : V} {w : W} (hv : v ∈ V.part p)
    (hw : w ∈ W.part q) : braidingMap V W (v ⊗ₜ w) = sign k (p * q) • (w ⊗ₜ v) := by
  change TensorProduct.comm k V W
    ((map (V.proj 0) LinearMap.id + map (V.proj 1) (W.sgn 1) : V ⊗[k] W →ₗ[k] V ⊗[k] W)
      (v ⊗ₜ w)) = _
  rw [LinearMap.add_apply, map_tmul, map_tmul, proj_apply_of_mem_part _ hv,
    proj_apply_of_mem_part _ hv, LinearMap.id_apply, sgn_apply_of_mem _ hw]
  rcases parity_eq_zero_or_one p with rfl | rfl
  · simp
  · simp [smul_tmul']

/-- The braiding is even. -/
theorem braidingMap_mem (V W : SVec k) :
    braidingMap V W ∈ parityHom (tensorObj V W) (tensorObj W V) 0 := by
  intro r
  refine ext_tensor fun p q v w hv hw => ?_
  change braidingMap V W ((tensorObj V W).proj r (v ⊗ₜ w)) =
    (tensorObj W V).proj (r + 0) (braidingMap V W (v ⊗ₜ w))
  rw [add_zero, proj_apply_of_mem_part _ (tmul_mem_part hv hw), braidingMap_tmul hv hw, map_smul,
    proj_apply_of_mem_part _ (tmul_mem_part hw hv), add_comm q p]
  split_ifs
  · rw [braidingMap_tmul hv hw]
  · rw [smul_zero]; exact map_zero (toLinearMap (braidingMap V W))

/-- **The braiding is symmetric:** `c_{W,V} ∘ c_{V,W} = 1`. -/
theorem braidingMap_comp_braidingMap (V W : SVec k) :
    braidingMap V W ≫ braidingMap W V = 𝟙 (tensorObj V W) :=
  ext_tensor fun p q v w hv hw => by
    change braidingMap W V (braidingMap V W (v ⊗ₜ w)) = v ⊗ₜ w
    rw [braidingMap_tmul hv hw, map_smul, braidingMap_tmul hw hv, mul_comm,
      sign_smul_sign_smul]

/-- The braiding isomorphism `V ⊗ W ≅ W ⊗ V`, with inverse `c_{W,V}`. -/
@[simps]
def braidingIso (V W : SVec k) : tensorObj V W ≅ tensorObj W V where
  hom := braidingMap V W
  inv := braidingMap W V
  hom_inv_id := braidingMap_comp_braidingMap V W
  inv_hom_id := braidingMap_comp_braidingMap W V

/-- Naturality of the braiding in the second variable: `c_{X,Z} ∘ (1_X ⊗ f) = (f ⊗ 1_X) ∘ c_{X,Y}`
(for homogeneous `f`, both sides send `x ⊗ y` to `(-1)^{|x||y|} f(y) ⊗ x`). -/
theorem braidingMap_naturality_right (X : SVec k) {Y Z : SVec k} (f : Y ⟶ Z) :
    whiskerLeft X f ≫ braidingMap X Z = braidingMap X Y ≫ whiskerRight f X := by
  refine Supercategory.induction_on (R := k) f ?_ ?_ ?_
  · rw [whiskerLeft_zero, whiskerRight_zero, Limits.zero_comp, Limits.comp_zero]
  · intro b f hf
    refine ext_tensor fun p q x y hx hy => ?_
    change braidingMap X Z (whiskerLeft X f (x ⊗ₜ y)) = whiskerRight f X (braidingMap X Y (x ⊗ₜ y))
    rw [whiskerLeft_tmul hf hx, map_smul, braidingMap_tmul hx (apply_mem_part hf hy),
      braidingMap_tmul hx hy, map_smul, whiskerRight_tmul, smul_smul, ← sign_add]
    congr 2
    rcases parity_eq_zero_or_one p with rfl | rfl <;>
      rcases parity_eq_zero_or_one q with rfl | rfl <;>
      rcases parity_eq_zero_or_one b with rfl | rfl <;> decide
  · intro f f' hf hf'
    rw [whiskerLeft_add, Preadditive.add_comp, hf, hf', whiskerRight_add, Preadditive.comp_add]

/-- Naturality of the braiding in the first variable: `c_{Y,Z} ∘ (f ⊗ 1_Z) = (1_Z ⊗ f) ∘ c_{X,Z}`
(for homogeneous `f`, both sides send `x ⊗ z` to `(-1)^{(|x| + |f|)|z|} z ⊗ f(x)`). -/
theorem braidingMap_naturality_left {X Y : SVec k} (f : X ⟶ Y) (Z : SVec k) :
    whiskerRight f Z ≫ braidingMap Y Z = braidingMap X Z ≫ whiskerLeft Z f := by
  refine Supercategory.induction_on (R := k) f ?_ ?_ ?_
  · rw [whiskerLeft_zero, whiskerRight_zero, Limits.zero_comp, Limits.comp_zero]
  · intro b f hf
    refine ext_tensor fun p q x z hx hz => ?_
    change braidingMap Y Z (whiskerRight f Z (x ⊗ₜ z)) = whiskerLeft Z f (braidingMap X Z (x ⊗ₜ z))
    rw [whiskerRight_tmul, braidingMap_tmul (apply_mem_part hf hx) hz, braidingMap_tmul hx hz,
      map_smul, whiskerLeft_tmul hf hz, smul_smul, ← sign_add]
    congr 2
    rcases parity_eq_zero_or_one p with rfl | rfl <;>
      rcases parity_eq_zero_or_one q with rfl | rfl <;>
      rcases parity_eq_zero_or_one b with rfl | rfl <;> decide
  · intro f f' hf hf'
    rw [whiskerRight_add, Preadditive.add_comp, hf, hf', whiskerLeft_add, Preadditive.comp_add]

/-- The first hexagon axiom: both sides send `(x ⊗ y) ⊗ z` to
`(-1)^{|x|(|y| + |z|)} y ⊗ (z ⊗ x)`. -/
theorem hexagon_forward (X Y Z : SVec k) :
    (α_ X Y Z).hom ≫ braidingMap X (tensorObj Y Z) ≫ (α_ Y Z X).hom =
      whiskerRight (braidingMap X Y) Z ≫ (α_ Y X Z).hom ≫ whiskerLeft Y (braidingMap X Z) := by
  rw [whiskerLeft_even Y (braidingMap_mem X Z)]
  refine ext_tensor₃ fun p q r x y z hx hy hz => ?_
  change (α_ Y Z X).hom (braidingMap X (tensorObj Y Z) ((α_ X Y Z).hom ((x ⊗ₜ y) ⊗ₜ z))) =
    map LinearMap.id (toLinearMap (braidingMap X Z))
      ((α_ Y X Z).hom (whiskerRight (braidingMap X Y) Z ((x ⊗ₜ y) ⊗ₜ z)))
  rw [associator_hom_tmul, braidingMap_tmul hx (tmul_mem_part hy hz), map_smul,
    associator_hom_tmul, whiskerRight_tmul, braidingMap_tmul hx hy, ← smul_tmul', map_smul,
    associator_hom_tmul, map_smul, map_tmul, LinearMap.id_apply, coe_toLinearMap,
    braidingMap_tmul hx hz, tmul_smul, smul_smul, ← sign_add, mul_add]

/-- The second hexagon axiom: both sides send `x ⊗ (y ⊗ z)` to
`(-1)^{(|x| + |y|)|z|} (z ⊗ x) ⊗ y`. -/
theorem hexagon_reverse (X Y Z : SVec k) :
    (α_ X Y Z).inv ≫ braidingMap (tensorObj X Y) Z ≫ (α_ Z X Y).inv =
      whiskerLeft X (braidingMap Y Z) ≫ (α_ X Z Y).inv ≫ whiskerRight (braidingMap X Z) Y := by
  rw [whiskerLeft_even X (braidingMap_mem Y Z)]
  refine ext_tensor₃' fun p q r x y z hx hy hz => ?_
  change (α_ Z X Y).inv (braidingMap (tensorObj X Y) Z ((α_ X Y Z).inv (x ⊗ₜ (y ⊗ₜ z)))) =
    whiskerRight (braidingMap X Z) Y
      ((α_ X Z Y).inv (map LinearMap.id (toLinearMap (braidingMap Y Z)) (x ⊗ₜ (y ⊗ₜ z))))
  rw [associator_inv_tmul, braidingMap_tmul (tmul_mem_part hx hy) hz, map_smul,
    associator_inv_tmul, map_tmul, LinearMap.id_apply, coe_toLinearMap, braidingMap_tmul hy hz,
    tmul_smul, map_smul, associator_inv_tmul, map_smul, whiskerRight_tmul,
    braidingMap_tmul hx hz, ← smul_tmul', smul_smul, ← sign_add, add_mul, add_comm]

/-- **Brundan–Ellis, §1.2.** `SVec k` is a braided monoidal supercategory with
the braiding `c_{V,W}(v ⊗ w) = (-1)^{|v||w|} w ⊗ v`. -/
instance instBraidedMonoidalSupercategory : BraidedMonoidalSupercategory k (SVec k) where
  braiding := braidingIso
  braiding_hom_mem := braidingMap_mem
  braiding_naturality_right := braidingMap_naturality_right
  braiding_naturality_left := braidingMap_naturality_left
  hexagon_forward := hexagon_forward
  hexagon_reverse := hexagon_reverse

theorem braiding_hom (V W : SVec k) :
    (BraidedMonoidalSupercategory.braiding (R := k) V W).hom = braidingMap V W := rfl

/-- `c_{V,W}(v ⊗ w) = (-1)^{|v||w|} w ⊗ v`, in the notation of `BraidedMonoidalSupercategory`. -/
theorem braiding_hom_tmul {V W : SVec k} {p q : ZMod 2} {v : V} {w : W} (hv : v ∈ V.part p)
    (hw : w ∈ W.part q) :
    (BraidedMonoidalSupercategory.braiding (R := k) V W).hom (v ⊗ₜ w) =
      sign k (p * q) • (w ⊗ₜ v) :=
  braidingMap_tmul hv hw

/-- **The braiding of `SVec k` is symmetric:** `c_{W,V} ∘ c_{V,W} = 1`. -/
theorem braiding_hom_comp_braiding_hom (V W : SVec k) :
    (BraidedMonoidalSupercategory.braiding (R := k) V W).hom ≫
      (BraidedMonoidalSupercategory.braiding (R := k) W V).hom = 𝟙 (V ⊗ W) :=
  braidingMap_comp_braidingMap V W

/-- **Brundan–Ellis, §1.2 and §2.** The underlying category `SVec̲` of superspaces and even linear maps
is a symmetric monoidal category. -/
instance instSymmetricCategoryUnderlying : SymmetricCategory (Underlying k (SVec k)) where
  symmetry X Y := Subtype.ext (braiding_hom_comp_braiding_hom X.obj Y.obj)

end SVec

end StringDiagrams

end
