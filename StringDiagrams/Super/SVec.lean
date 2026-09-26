import StringDiagrams.Super.MonoidalPi
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Projection

/-!
# The supercategory of superspaces

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
§1.2, Examples 1.2(i), 1.5(i), 1.8 and 1.13(i), over a commutative ground ring `k` (as in §2 of
the paper; §1 works over a field of characteristic different from `2`).

A *superspace* is a `ℤ/2`-graded `k`-module `V = V₀ ⊕ V₁`. We record the grading by the
projection `V.odd : V → V` onto `V₁` along `V₀` (an idempotent linear map); the homogeneous
components are `V.part p` (`isInternal_part`), and conversely every decomposition of a module
into two complementary submodules defines a superspace (`SVec.ofIsCompl`, `SVec.ofProd`).

## The supercategory `SVec`

Morphisms `V ⟶ W` in `SVec k` are *all* `k`-linear maps. A linear map is even (resp. odd) if
it preserves (resp. reverses) parity; every linear map is uniquely the sum of an even and an odd
map (`homProj`), which makes `SVec k` a supercategory (Example 1.2(i),
`SVec.instSupercategory`). Its underlying category of even maps is
`Underlying k (SVec k)`.

## The monoidal supercategory `SVec`

The tensor product of superspaces is the tensor product of modules with
`(V ⊗ W)₀ = V₀ ⊗ W₀ ⊕ V₁ ⊗ W₁` and `(V ⊗ W)₁ = V₀ ⊗ W₁ ⊕ V₁ ⊗ W₀`. The tensor product of
linear maps carries the Koszul sign `(f ⊗ g)(v ⊗ w) = (-1)^{|g||v|} f(v) ⊗ g(w)`
(`superTensorHom_tmul`); in whiskering form `(1_V ⊗ g)(v ⊗ w) = (-1)^{|g||v|} v ⊗ g(w)`
(`whiskerLeft_tmul`) and `(f ⊗ 1_W)(v ⊗ w) = f(v) ⊗ w` (`whiskerRight_tmul`). With the unit
object `k` (even) and the associator and unitors of `TensorProduct`, `SVec k` is a monoidal
supercategory (Example 1.5(i), `SVec.instMonoidalSupercategory`); the composition rule (1.1) is
`MonoidalSupercategory.superTensorHom_comp_superTensorHom`.

## Parity shift

`Π V` is `V` with the opposite grading and `ζ_V : Π V → V` the identity function, an odd
isomorphism; this makes `SVec k` a Π-supercategory (Example 1.8 with `A = B = k`,
`SVec.instPiSupercategory`), with `Π f = (-1)^{|f|} f` (`pi_map_of_mem`) and `ξ_V = -1`
(`ξ_hom`). With `π := Π k` and `ζ : Π k → k` the identity function, `SVec k` is a monoidal
Π-supercategory (Example 1.13(i) for `A = k`, `SVec.instMonoidalPiSupercategory`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory MonoidalCategory Supercategory TensorProduct

universe u

/-- A superspace over `k` (Brundan–Ellis, §1.2): a `k`-module with a `ℤ/2`-grading, recorded by
the projection `odd` onto the odd part along the even part. -/
structure SVec (k : Type u) [CommRing k] where
  /-- The underlying module. -/
  carrier : Type u
  [isAddCommGroup : AddCommGroup carrier]
  [isModule : Module k carrier]
  /-- The projection onto the odd part. -/
  odd : carrier →ₗ[k] carrier
  odd_comp_odd : odd ∘ₗ odd = odd

namespace SVec

variable {k : Type u} [CommRing k]

instance : CoeSort (SVec k) (Type u) := ⟨SVec.carrier⟩

attribute [instance] isAddCommGroup isModule

/-! ## Homogeneous components -/

@[simp] theorem zmod2_one_add_one : (1 : ZMod 2) + 1 = 0 := rfl

section Proj

variable (V : SVec k)

/-- The projection `V → V_p` onto the component of parity `p`. -/
def proj (p : ZMod 2) : V →ₗ[k] V := if p = 0 then LinearMap.id - V.odd else V.odd

theorem proj_zero : V.proj 0 = LinearMap.id - V.odd := if_pos rfl

theorem proj_one : V.proj 1 = V.odd := if_neg (by decide)

theorem odd_apply_odd (v : V) : V.odd (V.odd v) = V.odd v :=
  LinearMap.congr_fun V.odd_comp_odd v

theorem proj_add_proj : V.proj 0 + V.proj 1 = LinearMap.id := by simp [proj_zero, proj_one]

theorem proj_apply_add (v : V) : V.proj 0 v + V.proj 1 v = v := by
  simp [proj_zero, proj_one]

theorem proj_comp_proj_self (p : ZMod 2) : V.proj p ∘ₗ V.proj p = V.proj p := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · ext v; simp [proj_zero, odd_apply_odd]
  · simpa [proj_one] using V.odd_comp_odd

theorem proj_comp_proj_add_one (p : ZMod 2) : V.proj p ∘ₗ V.proj (p + 1) = 0 := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · ext v; simp [proj_zero, proj_one, odd_apply_odd]
  · ext v; simp [proj_zero, proj_one, odd_apply_odd]

theorem proj_comp_proj_of_ne {p q : ZMod 2} (h : p ≠ q) : V.proj p ∘ₗ V.proj q = 0 := by
  have : q = p + 1 := by
    rcases parity_eq_zero_or_one p with rfl | rfl <;>
      rcases parity_eq_zero_or_one q with rfl | rfl <;> simp_all
  subst this; exact proj_comp_proj_add_one V p

theorem proj_proj_apply (p : ZMod 2) (v : V) : V.proj p (V.proj p v) = V.proj p v :=
  LinearMap.congr_fun (proj_comp_proj_self V p) v

theorem proj_proj_apply_of_ne {p q : ZMod 2} (h : p ≠ q) (v : V) :
    V.proj p (V.proj q v) = 0 :=
  LinearMap.congr_fun (proj_comp_proj_of_ne V h) v

@[simp] theorem proj_zero_proj_one (v : V) : V.proj 0 (V.proj 1 v) = 0 :=
  proj_proj_apply_of_ne V (by decide) v

@[simp] theorem proj_one_proj_zero (v : V) : V.proj 1 (V.proj 0 v) = 0 :=
  proj_proj_apply_of_ne V (by decide) v

theorem proj_apply_add' (q : ZMod 2) (v : V) : V.proj q v + V.proj (q + 1) v = v := by
  rcases parity_eq_zero_or_one q with rfl | rfl
  · exact proj_apply_add V v
  · rw [add_comm]; exact proj_apply_add V v

/-- The homogeneous component `V_p`. -/
def part (p : ZMod 2) : Submodule k V := LinearMap.range (V.proj p)

theorem mem_part_iff {p : ZMod 2} {v : V} : v ∈ V.part p ↔ V.proj p v = v := by
  constructor
  · rintro ⟨w, rfl⟩; exact proj_proj_apply V p w
  · intro h; exact ⟨v, h⟩

theorem proj_mem_part (p : ZMod 2) (v : V) : V.proj p v ∈ V.part p := ⟨v, rfl⟩

theorem proj_apply_of_mem_part {p q : ZMod 2} {v : V} (hv : v ∈ V.part q) :
    V.proj p v = if p = q then v else 0 := by
  obtain ⟨w, rfl⟩ := hv
  split_ifs with h
  · subst h; exact proj_proj_apply V p w
  · exact proj_proj_apply_of_ne V h w

theorem mem_part_zero_iff {v : V} : v ∈ V.part 0 ↔ V.odd v = 0 := by
  rw [mem_part_iff, proj_zero, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_self]

theorem mem_part_one_iff {v : V} : v ∈ V.part 1 ↔ V.odd v = v := by
  rw [mem_part_iff, proj_one]

/-- A superspace is the direct sum of its even and odd parts. -/
theorem isInternal_part : DirectSum.IsInternal V.part := by
  rw [DirectSum.isInternal_submodule_iff_isCompl V.part (i := 0) (j := 1) (by decide)
    (by ext p; rcases parity_eq_zero_or_one p with rfl | rfl <;> simp)]
  constructor
  · rw [Submodule.disjoint_def]
    intro v h0 h1
    rw [mem_part_iff] at h0 h1
    rw [← h0, ← h1, proj_proj_apply_of_ne V (by decide)]
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    rw [← proj_apply_add V v]
    exact Submodule.add_mem_sup (proj_mem_part V 0 v) (proj_mem_part V 1 v)

end Proj

/-! ## Constructions of superspaces -/

/-- The superspace with even part `V₀` and odd part `V₁`: the module `V₀ × V₁`. -/
def ofProd (V₀ V₁ : Type u) [AddCommGroup V₀] [Module k V₀] [AddCommGroup V₁] [Module k V₁] :
    SVec k where
  carrier := V₀ × V₁
  odd := LinearMap.inr k V₀ V₁ ∘ₗ LinearMap.snd k V₀ V₁
  odd_comp_odd := by ext <;> simp

theorem ofProd_mem_part_zero {V₀ V₁ : Type u} [AddCommGroup V₀] [Module k V₀] [AddCommGroup V₁]
    [Module k V₁] (v : V₀) : ((v, 0) : ofProd (k := k) V₀ V₁) ∈ (ofProd (k := k) V₀ V₁).part 0 := by
  rw [mem_part_zero_iff]; simp [ofProd]

theorem ofProd_mem_part_one {V₀ V₁ : Type u} [AddCommGroup V₀] [Module k V₀] [AddCommGroup V₁]
    [Module k V₁] (v : V₁) : ((0, v) : ofProd (k := k) V₀ V₁) ∈ (ofProd (k := k) V₀ V₁).part 1 := by
  rw [mem_part_one_iff]; simp [ofProd]

/-- The superspace structure on a module given by complementary submodules `M₀`, `M₁`
(even and odd parts). -/
def ofIsCompl (M : Type u) [AddCommGroup M] [Module k M] (M₀ M₁ : Submodule k M)
    (h : IsCompl M₀ M₁) : SVec k where
  carrier := M
  odd := M₁.subtype ∘ₗ Submodule.linearProjOfIsCompl M₁ M₀ h.symm
  odd_comp_odd := by
    ext v
    simp

theorem ofIsCompl_part_one (M : Type u) [AddCommGroup M] [Module k M] (M₀ M₁ : Submodule k M)
    (h : IsCompl M₀ M₁) : (ofIsCompl M M₀ M₁ h).part 1 = M₁ := by
  ext v
  rw [mem_part_one_iff]
  simp only [ofIsCompl, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype]
  constructor
  · intro hv; rw [← hv]; exact Submodule.coe_mem _
  · intro hv; rw [Submodule.linearProjOfIsCompl_apply_left h.symm ⟨v, hv⟩]

theorem ofIsCompl_part_zero (M : Type u) [AddCommGroup M] [Module k M] (M₀ M₁ : Submodule k M)
    (h : IsCompl M₀ M₁) : (ofIsCompl M M₀ M₁ h).part 0 = M₀ := by
  ext v
  rw [mem_part_zero_iff]
  simp only [ofIsCompl, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
    ZeroMemClass.coe_eq_zero]
  exact Submodule.linearProjOfIsCompl_apply_eq_zero_iff h.symm


/-! ## The supercategory `SVec` -/

instance : Category (SVec k) where
  Hom V W := V →ₗ[k] W
  id V := LinearMap.id
  comp f g := g ∘ₗ f

instance {V W : SVec k} : FunLike (V ⟶ W) V W := LinearMap.instFunLike

instance {V W : SVec k} : LinearMapClass (V ⟶ W) k V W := LinearMap.semilinearMapClass

/-- A linear map, as a morphism of `SVec k`. -/
def ofHom {V W : SVec k} (f : V →ₗ[k] W) : V ⟶ W := f

/-- The linear map underlying a morphism of `SVec k`. -/
def toLinearMap {V W : SVec k} (f : V ⟶ W) : V →ₗ[k] W := f

@[simp] theorem toLinearMap_ofHom {V W : SVec k} (f : V →ₗ[k] W) : toLinearMap (ofHom f) = f :=
  rfl

@[simp] theorem ofHom_toLinearMap {V W : SVec k} (f : V ⟶ W) : ofHom (toLinearMap f) = f := rfl

@[simp] theorem coe_toLinearMap {V W : SVec k} (f : V ⟶ W) : ⇑(toLinearMap f) = ⇑f := rfl

@[simp] theorem ofHom_apply {V W : SVec k} (f : V →ₗ[k] W) (v : V) : ofHom f v = f v := rfl

@[ext] theorem hom_ext {V W : SVec k} {f g : V ⟶ W} (h : ∀ v, f v = g v) : f = g :=
  LinearMap.ext h

@[simp] theorem id_apply (V : SVec k) (v : V) : (𝟙 V : V ⟶ V) v = v := rfl

@[simp] theorem comp_apply {U V W : SVec k} (f : U ⟶ V) (g : V ⟶ W) (u : U) :
    (f ≫ g) u = g (f u) := rfl

theorem toLinearMap_comp {U V W : SVec k} (f : U ⟶ V) (g : V ⟶ W) :
    toLinearMap (f ≫ g) = toLinearMap g ∘ₗ toLinearMap f := rfl

@[simp] theorem toLinearMap_id (V : SVec k) : toLinearMap (𝟙 V) = LinearMap.id := rfl

instance : Preadditive (SVec k) where
  homGroup V W := inferInstanceAs (AddCommGroup (V →ₗ[k] W))
  add_comp _ _ _ _ _ _ := LinearMap.comp_add _ _ _
  comp_add _ _ _ _ _ _ := LinearMap.add_comp _ _ _

instance : Linear k (SVec k) where
  homModule V W := inferInstanceAs (Module k (V →ₗ[k] W))
  smul_comp _ _ _ r f g := LinearMap.comp_smul g r f
  comp_smul _ _ _ f r g := LinearMap.smul_comp r g f

@[simp] theorem add_apply {V W : SVec k} (f g : V ⟶ W) (v : V) : (f + g) v = f v + g v := rfl

@[simp] theorem sub_apply {V W : SVec k} (f g : V ⟶ W) (v : V) : (f - g) v = f v - g v := rfl

@[simp] theorem neg_apply {V W : SVec k} (f : V ⟶ W) (v : V) : (-f) v = -f v := rfl

@[simp] theorem zero_apply {V W : SVec k} (v : V) : (0 : V ⟶ W) v = 0 := rfl

@[simp] theorem smul_apply {V W : SVec k} (r : k) (f : V ⟶ W) (v : V) : (r • f) v = r • f v :=
  rfl

@[simp] theorem zsmul_apply {V W : SVec k} (n : ℤ) (f : V ⟶ W) (v : V) : (n • f) v = n • f v :=
  rfl

@[simp] theorem toLinearMap_add {V W : SVec k} (f g : V ⟶ W) :
    toLinearMap (f + g) = toLinearMap f + toLinearMap g := rfl

@[simp] theorem toLinearMap_smul {V W : SVec k} (r : k) (f : V ⟶ W) :
    toLinearMap (r • f) = r • toLinearMap f := rfl

/-- A linear map `f : V → W` has parity `p` if it maps `V_q` to `W_{q+p}` for all `q`, i.e.
`f ∘ proj_q = proj_{q+p} ∘ f`. -/
def parityHom (V W : SVec k) (p : ZMod 2) : Submodule k (V ⟶ W) where
  carrier := {f | ∀ q, toLinearMap f ∘ₗ V.proj q = W.proj (q + p) ∘ₗ toLinearMap f}
  add_mem' {f g} hf hg q := by
    simp only [Set.mem_setOf_eq, toLinearMap_add, LinearMap.add_comp, LinearMap.comp_add] at *
    rw [hf, hg]
  zero_mem' q := by ext; simp [toLinearMap]
  smul_mem' r f hf q := by
    simp only [Set.mem_setOf_eq, toLinearMap_smul, LinearMap.smul_comp, LinearMap.comp_smul] at *
    rw [hf]

theorem mem_parityHom_iff {V W : SVec k} {p : ZMod 2} {f : V ⟶ W} :
    f ∈ parityHom V W p ↔ ∀ q, toLinearMap f ∘ₗ V.proj q = W.proj (q + p) ∘ₗ toLinearMap f :=
  Iff.rfl

theorem apply_proj_of_mem {V W : SVec k} {p : ZMod 2} {f : V ⟶ W} (hf : f ∈ parityHom V W p)
    (q : ZMod 2) (v : V) : f (V.proj q v) = W.proj (q + p) (f v) :=
  LinearMap.congr_fun (hf q) v

/-- A homogeneous linear map of parity `p` maps `V_q` to `W_{q+p}`. -/
theorem apply_mem_part {V W : SVec k} {p q : ZMod 2} {f : V ⟶ W} (hf : f ∈ parityHom V W p)
    {v : V} (hv : v ∈ V.part q) : f v ∈ W.part (q + p) := by
  rw [mem_part_iff] at hv ⊢
  rw [← hv, apply_proj_of_mem hf, proj_proj_apply]

/-- Conversely, a linear map mapping every `V_q` into `W_{q+p}` has parity `p`. -/
theorem mem_parityHom_of_apply_mem {V W : SVec k} {p : ZMod 2} {f : V ⟶ W}
    (h : ∀ q (v : V), v ∈ V.part q → f v ∈ W.part (q + p)) : f ∈ parityHom V W p := by
  intro q
  ext v
  simp only [LinearMap.coe_comp, Function.comp_apply, coe_toLinearMap]
  have hv := h q _ (proj_mem_part V q v)
  have hv' := h (q + 1) _ (proj_mem_part V (q + 1) v)
  have hne : q + p ≠ q + 1 + p := by
    rcases parity_eq_zero_or_one p with rfl | rfl <;>
      rcases parity_eq_zero_or_one q with rfl | rfl <;> decide
  conv_rhs => rw [← proj_apply_add' V q v]
  rw [map_add, map_add, (mem_part_iff _).1 hv, proj_apply_of_mem_part _ hv', if_neg hne, add_zero]

/-- The component of parity `p` of a linear map: `f_p = ∑_q proj_{q+p} ∘ f ∘ proj_q`. -/
def homProj (p : ZMod 2) {V W : SVec k} : (V ⟶ W) →ₗ[k] (V ⟶ W) where
  toFun f := ofHom (W.proj p ∘ₗ toLinearMap f ∘ₗ V.proj 0 +
    W.proj (1 + p) ∘ₗ toLinearMap f ∘ₗ V.proj 1)
  map_add' f g := by
    ext v
    simp only [ofHom_apply, add_apply, LinearMap.add_apply, LinearMap.comp_apply,
      coe_toLinearMap, map_add]
    abel
  map_smul' r f := by
    ext v
    simp only [ofHom_apply, smul_apply, LinearMap.add_apply, LinearMap.comp_apply,
      coe_toLinearMap, map_smul, RingHom.id_apply, smul_add]

theorem homProj_apply (p : ZMod 2) {V W : SVec k} (f : V ⟶ W) (v : V) :
    homProj p f v = W.proj p (f (V.proj 0 v)) + W.proj (1 + p) (f (V.proj 1 v)) := rfl

theorem homProj_mem (p : ZMod 2) {V W : SVec k} (f : V ⟶ W) : homProj p f ∈ parityHom V W p := by
  refine mem_parityHom_of_apply_mem fun q v hv => ?_
  rw [homProj_apply, proj_apply_of_mem_part _ hv, proj_apply_of_mem_part _ hv]
  rcases parity_eq_zero_or_one q with rfl | rfl
  · simpa using proj_mem_part W p (f v)
  · simpa using proj_mem_part W (1 + p) (f v)

theorem homProj_add_homProj {V W : SVec k} (f : V ⟶ W) : homProj 0 f + homProj 1 f = f := by
  ext v
  simp only [add_apply, homProj_apply, show (1 : ZMod 2) + 0 = 1 from rfl,
    show (1 : ZMod 2) + 1 = 0 from rfl]
  conv_rhs => rw [← proj_apply_add V v, map_add, ← proj_apply_add W (f (V.proj 0 v)),
    ← proj_apply_add W (f (V.proj 1 v))]
  abel

theorem homProj_of_mem {p : ZMod 2} {V W : SVec k} {f : V ⟶ W} (hf : f ∈ parityHom V W p) :
    homProj p f = f := by
  ext v
  rw [homProj_apply, apply_proj_of_mem hf, apply_proj_of_mem hf, zero_add, proj_proj_apply,
    proj_proj_apply, add_comm 1 p, proj_apply_add']

theorem homProj_of_mem_ne {p q : ZMod 2} (h : p ≠ q) {V W : SVec k} {f : V ⟶ W}
    (hf : f ∈ parityHom V W q) : homProj p f = 0 := by
  ext v
  rw [homProj_apply, apply_proj_of_mem hf, apply_proj_of_mem hf, zero_apply]
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    rcases parity_eq_zero_or_one q with rfl | rfl <;> simp_all

/-- **Brundan–Ellis, Example 1.2(i).** `SVec k` is a supercategory: every linear map is uniquely
the sum of an even and an odd linear map. -/
instance instSupercategory : Supercategory k (SVec k) where
  parity := parityHom
  isInternal V W := by
    rw [DirectSum.isInternal_submodule_iff_isCompl (parityHom V W) (i := 0) (j := 1) (by decide)
      (by ext p; rcases parity_eq_zero_or_one p with rfl | rfl <;> simp)]
    constructor
    · rw [Submodule.disjoint_def]
      intro f h0 h1
      rw [← homProj_of_mem h0, homProj_of_mem_ne (by decide) h1]
    · rw [codisjoint_iff, eq_top_iff]
      intro f _
      rw [← homProj_add_homProj f]
      exact Submodule.add_mem_sup (homProj_mem 0 f) (homProj_mem 1 f)
  id_mem V q := by rw [add_zero]; rfl
  comp_mem {U V W p q f g} hf hg r := by
    rw [toLinearMap_comp, LinearMap.comp_assoc, hf r, ← LinearMap.comp_assoc, hg, add_assoc]
    rfl

theorem parity_eq (V W : SVec k) (p : ZMod 2) : parity (R := k) V W p = parityHom V W p := rfl

/-- The parity components of the supercategory structure are the maps `homProj`. -/
theorem proj_eq_homProj (p : ZMod 2) {V W : SVec k} (f : V ⟶ W) :
    Supercategory.proj k p f = homProj p f := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · exact proj_eq_of_add (homProj_add_homProj f).symm (homProj_mem 0 f) (homProj_mem 1 f)
  · exact proj_eq_of_add ((add_comm _ _).trans (homProj_add_homProj f)).symm
      (homProj_mem 1 f) (by simpa using homProj_mem 0 f)

theorem homProj_eq_of_add {p : ZMod 2} {V W : SVec k} {f g h : V ⟶ W} (e : f = g + h)
    (hg : g ∈ parityHom V W p) (hh : h ∈ parityHom V W (p + 1)) : homProj p f = g := by
  rw [← proj_eq_homProj]; exact proj_eq_of_add e hg hh

theorem ext_part {V : SVec k} {M : Type u} [AddCommGroup M] [Module k M] {f g : V →ₗ[k] M}
    (h : ∀ q (v : V), v ∈ V.part q → f v = g v) : f = g := by
  ext v
  rw [← proj_apply_add V v, map_add, map_add, h 0 _ (proj_mem_part V 0 v),
    h 1 _ (proj_mem_part V 1 v)]

/-- An isomorphism of `SVec k` given by a linear equivalence. -/
@[simps]
def isoOfLinearEquiv {V W : SVec k} (e : V ≃ₗ[k] W) : V ≅ W where
  hom := ofHom e.toLinearMap
  inv := ofHom e.symm.toLinearMap
  hom_inv_id := by ext; simp
  inv_hom_id := by ext; simp

/-! ## Signs -/

/-- The map `v ↦ (-1)^{b|v|} v` (the grading involution for `b = 1`). -/
def sgn (V : SVec k) (b : ZMod 2) : V →ₗ[k] V := V.proj 0 + sign k b • V.proj 1

theorem sgn_apply (V : SVec k) (b : ZMod 2) (v : V) :
    V.sgn b v = V.proj 0 v + sign k b • V.proj 1 v := rfl

@[simp] theorem sgn_zero (V : SVec k) : V.sgn 0 = LinearMap.id := by
  rw [sgn, sign_zero, one_smul, proj_add_proj]

theorem sgn_apply_of_mem {V : SVec k} (b : ZMod 2) {q : ZMod 2} {v : V} (hv : v ∈ V.part q) :
    V.sgn b v = sign k (q * b) • v := by
  rw [sgn_apply, proj_apply_of_mem_part _ hv, proj_apply_of_mem_part _ hv]
  rcases parity_eq_zero_or_one q with rfl | rfl <;> simp

theorem sgn_comp_sgn (V : SVec k) (a b : ZMod 2) : V.sgn a ∘ₗ V.sgn b = V.sgn (a + b) := by
  refine ext_part fun q v hv => ?_
  rw [LinearMap.comp_apply, sgn_apply_of_mem _ hv, map_smul, sgn_apply_of_mem _ hv,
    sgn_apply_of_mem _ hv, smul_smul, ← sign_add, mul_add, add_comm]

theorem sgn_sgn_apply (V : SVec k) (b : ZMod 2) (v : V) : V.sgn b (V.sgn b v) = v := by
  rw [← LinearMap.comp_apply, sgn_comp_sgn, zmod2_add_self, sgn_zero, LinearMap.id_apply]

theorem sgn_mem (V : SVec k) (b : ZMod 2) : ofHom (V.sgn b) ∈ parityHom V V 0 := by
  intro q
  refine ext_part fun r v hv => ?_
  simp only [add_zero, LinearMap.comp_apply, toLinearMap_ofHom, proj_apply_of_mem_part _ hv]
  split_ifs <;> simp [sgn_apply_of_mem _ hv, proj_apply_of_mem_part _ hv, *]

/-- A homogeneous linear map of parity `p` commutes with the signs up to `(-1)^{pb}`. -/
theorem sgn_comp_of_mem {V W : SVec k} {p : ZMod 2} {f : V ⟶ W} (hf : f ∈ parityHom V W p)
    (b : ZMod 2) : W.sgn b ∘ₗ toLinearMap f = sign k (p * b) • (toLinearMap f ∘ₗ V.sgn b) := by
  refine ext_part fun q v hv => ?_
  rw [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.comp_apply, sgn_apply_of_mem _ hv,
    coe_toLinearMap, map_smul, sgn_apply_of_mem _ (apply_mem_part hf hv), smul_smul, ← sign_add,
    add_mul, add_comm]

/-! ## The tensor product of superspaces -/

/-- The tensor product of superspaces: `(V ⊗ W)₁ = V₀ ⊗ W₁ ⊕ V₁ ⊗ W₀`. -/
abbrev tensorObj (V W : SVec k) : SVec k where
  carrier := V ⊗[k] W
  odd := map (V.proj 1) (W.proj 0) + map (V.proj 0) (W.proj 1)
  odd_comp_odd := by
    apply TensorProduct.ext'
    intro v w
    simp [map_tmul, proj_proj_apply]

theorem tensorObj_odd_tmul (V W : SVec k) (v : V) (w : W) :
    (tensorObj V W).odd (v ⊗ₜ w) = V.proj 1 v ⊗ₜ W.proj 0 w + V.proj 0 v ⊗ₜ W.proj 1 w := rfl

/-- `(V ⊗ W)_q = V₀ ⊗ W_q ⊕ V₁ ⊗ W_{1+q}`. -/
@[simp] theorem tensorObj_proj_tmul (V W : SVec k) (q : ZMod 2) (v : V) (w : W) :
    (tensorObj V W).proj q (v ⊗ₜ w) =
      V.proj 0 v ⊗ₜ W.proj q w + V.proj 1 v ⊗ₜ W.proj (1 + q) w := by
  rcases parity_eq_zero_or_one q with rfl | rfl
  · rw [proj_zero, LinearMap.sub_apply, LinearMap.id_apply, tensorObj_odd_tmul, add_zero]
    have e : v ⊗ₜ[k] w = (V.proj 0 v + V.proj 1 v) ⊗ₜ (W.proj 0 w + W.proj 1 w) := by
      rw [proj_apply_add, proj_apply_add]
    rw [e]
    simp only [add_tmul, tmul_add]
    abel
  · rw [proj_one, tensorObj_odd_tmul, zmod2_one_add_one, add_comm]

theorem tmul_mem_part {V W : SVec k} {p q : ZMod 2} {v : V} {w : W} (hv : v ∈ V.part p)
    (hw : w ∈ W.part q) : v ⊗ₜ[k] w ∈ (tensorObj V W).part (p + q) := by
  rw [mem_part_iff, tensorObj_proj_tmul, proj_apply_of_mem_part _ hv, proj_apply_of_mem_part _ hv,
    proj_apply_of_mem_part _ hw, proj_apply_of_mem_part _ hw]
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    rcases parity_eq_zero_or_one q with rfl | rfl <;> simp

/-- Linear maps out of `V ⊗ W` agreeing on tensors of homogeneous vectors are equal. -/
theorem ext_tensor {V W : SVec k} {M : Type u} [AddCommGroup M] [Module k M]
    {f g : V ⊗[k] W →ₗ[k] M}
    (h : ∀ p q (v : V) (w : W), v ∈ V.part p → w ∈ W.part q → f (v ⊗ₜ w) = g (v ⊗ₜ w)) :
    f = g := by
  apply TensorProduct.ext'
  intro v w
  rw [← proj_apply_add V v, ← proj_apply_add W w]
  simp only [add_tmul, tmul_add, map_add]
  rw [h _ _ _ _ (proj_mem_part V 0 v) (proj_mem_part W 0 w),
    h _ _ _ _ (proj_mem_part V 0 v) (proj_mem_part W 1 w),
    h _ _ _ _ (proj_mem_part V 1 v) (proj_mem_part W 0 w),
    h _ _ _ _ (proj_mem_part V 1 v) (proj_mem_part W 1 w)]

theorem tensorObj_sgn (V W : SVec k) (b : ZMod 2) :
    (tensorObj V W).sgn b = map (V.sgn b) (W.sgn b) := by
  refine ext_tensor fun p q v w hv hw => ?_
  rw [sgn_apply_of_mem _ (tmul_mem_part hv hw), map_tmul, sgn_apply_of_mem _ hv,
    sgn_apply_of_mem _ hw, smul_tmul_smul, ← sign_add, add_mul]

/-- The tensor product of homogeneous linear maps is homogeneous, with parities adding. -/
theorem map_mem {V V' W W' : SVec k} {a b : ZMod 2} {f : V ⟶ V'} {g : W ⟶ W'}
    (hf : f ∈ parityHom V V' a) (hg : g ∈ parityHom W W' b) :
    (ofHom (map (toLinearMap f) (toLinearMap g)) : tensorObj V W ⟶ tensorObj V' W') ∈
      parityHom (tensorObj V W) (tensorObj V' W') (a + b) := by
  intro q
  refine ext_tensor fun p r v w hv hw => ?_
  have hfg : f v ⊗ₜ[k] g w ∈ (tensorObj V' W').part (p + a + (r + b)) :=
    tmul_mem_part (apply_mem_part hf hv) (apply_mem_part hg hw)
  simp only [LinearMap.comp_apply, toLinearMap_ofHom]
  rw [proj_apply_of_mem_part _ (tmul_mem_part hv hw), map_tmul, coe_toLinearMap,
    coe_toLinearMap, proj_apply_of_mem_part _ hfg]
  split_ifs with h1 h2 h2
  · rw [map_tmul]; rfl
  · exact absurd (by rw [h1]; abel) h2
  · refine absurd (add_right_cancel (b := a + b) ?_) h1
    rw [h2]; abel
  · exact map_zero _

/-! ## Whiskering -/

/-- The unit superspace `k`, concentrated in even parity. -/
abbrev unit : SVec k where
  carrier := k
  odd := 0
  odd_comp_odd := by simp

@[simp] theorem unit_proj_zero_apply (r : k) : (unit : SVec k).proj 0 r = r := by
  simp [proj_zero]

@[simp] theorem unit_proj_one_apply (r : k) : (unit : SVec k).proj 1 r = 0 := by
  simp [proj_one]

theorem unit_sgn (b : ZMod 2) : (unit : SVec k).sgn b = LinearMap.id :=
  LinearMap.ext fun r => by
    rw [sgn_apply, unit_proj_zero_apply, unit_proj_one_apply, smul_zero, add_zero]; rfl

/-- `1_V ⊗ g`: `v ⊗ w ↦ (-1)^{|g||v|} v ⊗ g(w)`, extended linearly in `g`. -/
def whiskerLeft (V : SVec k) {W W' : SVec k} (g : W ⟶ W') : tensorObj V W ⟶ tensorObj V W' :=
  ofHom (map LinearMap.id (toLinearMap (homProj 0 g)) + map (V.sgn 1) (toLinearMap (homProj 1 g)))

/-- `f ⊗ 1_W`: `v ⊗ w ↦ f(v) ⊗ w`. -/
def whiskerRight {V V' : SVec k} (f : V ⟶ V') (W : SVec k) : tensorObj V W ⟶ tensorObj V' W :=
  ofHom (map (toLinearMap f) LinearMap.id)

theorem whiskerRight_tmul {V V' : SVec k} (f : V ⟶ V') (W : SVec k) (v : V) (w : W) :
    whiskerRight f W (v ⊗ₜ w) = f v ⊗ₜ w := rfl

theorem whiskerLeft_of_mem (V : SVec k) {W W' : SVec k} {b : ZMod 2} {g : W ⟶ W'}
    (hg : g ∈ parityHom W W' b) : whiskerLeft V g = ofHom (map (V.sgn b) (toLinearMap g)) := by
  rcases parity_eq_zero_or_one b with rfl | rfl
  · rw [whiskerLeft, homProj_of_mem hg, homProj_of_mem_ne (by decide) hg, sgn_zero]
    simp [toLinearMap, ofHom]
  · rw [whiskerLeft, homProj_of_mem hg, homProj_of_mem_ne (by decide) hg]
    simp [toLinearMap, ofHom]

/-- **The Koszul sign rule** for `1_V ⊗ g`: `(1 ⊗ g)(v ⊗ w) = (-1)^{|v||g|} v ⊗ g(w)`. -/
theorem whiskerLeft_tmul {V W W' : SVec k} {p q : ZMod 2} {g : W ⟶ W'}
    (hg : g ∈ parityHom W W' q) {v : V} (hv : v ∈ V.part p) (w : W) :
    whiskerLeft V g (v ⊗ₜ w) = sign k (p * q) • (v ⊗ₜ g w) := by
  rw [whiskerLeft_of_mem V hg, ofHom_apply, map_tmul, sgn_apply_of_mem _ hv, smul_tmul']
  rfl

theorem whiskerLeft_add (V : SVec k) {W W' : SVec k} (g g' : W ⟶ W') :
    whiskerLeft V (g + g') = whiskerLeft V g + whiskerLeft V g' := by
  simp only [whiskerLeft, map_add, toLinearMap_add, map_add_right]
  ext x
  rw [add_apply, ofHom_apply, ofHom_apply, ofHom_apply]
  simp only [LinearMap.add_apply]
  abel

theorem whiskerLeft_smul (V : SVec k) {W W' : SVec k} (r : k) (g : W ⟶ W') :
    whiskerLeft V (r • g) = r • whiskerLeft V g := by
  simp only [whiskerLeft, map_smul, toLinearMap_smul, map_smul_right]
  ext x
  rw [smul_apply, ofHom_apply, ofHom_apply]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_add]

theorem whiskerLeft_zero (V : SVec k) {W W' : SVec k} : whiskerLeft V (0 : W ⟶ W') = 0 := by
  simpa using whiskerLeft_smul V (0 : k) (0 : W ⟶ W')

theorem whiskerLeft_mem (V : SVec k) {W W' : SVec k} {b : ZMod 2} {g : W ⟶ W'}
    (hg : g ∈ parityHom W W' b) :
    whiskerLeft V g ∈ parityHom (tensorObj V W) (tensorObj V W') b := by
  rw [whiskerLeft_of_mem V hg]
  simpa using map_mem (sgn_mem V b) hg

theorem whiskerRight_mem {V V' : SVec k} {a : ZMod 2} {f : V ⟶ V'} (hf : f ∈ parityHom V V' a)
    (W : SVec k) : whiskerRight f W ∈ parityHom (tensorObj V W) (tensorObj V' W) a := by
  simpa using map_mem hf (instSupercategory.id_mem W)

theorem whiskerLeft_comp (V : SVec k) {W W' W'' : SVec k} (f : W ⟶ W') (g : W' ⟶ W'') :
    whiskerLeft V (f ≫ g) = whiskerLeft V f ≫ whiskerLeft V g := by
  refine Supercategory.induction_on (R := k) f ?_ ?_ ?_
  · simp only [Limits.zero_comp, whiskerLeft_zero]
  · intro a f hfa
    refine Supercategory.induction_on (R := k) g ?_ ?_ ?_
    · simp only [Limits.comp_zero, whiskerLeft_zero]
    · intro b g hgb
      rw [whiskerLeft_of_mem V (Supercategory.comp_mem hfa hgb), whiskerLeft_of_mem V hfa,
        whiskerLeft_of_mem V hgb, add_comm, ← sgn_comp_sgn]
      exact map_comp _ _ _ _
    · intro g g' hg hg'
      rw [Preadditive.comp_add, whiskerLeft_add, whiskerLeft_add, hg, hg', Preadditive.comp_add]
  · intro f f' hf hf'
    rw [Preadditive.add_comp, whiskerLeft_add, whiskerLeft_add, hf, hf', Preadditive.add_comp]

theorem whiskerLeft_id (V W : SVec k) : whiskerLeft V (𝟙 W) = 𝟙 (tensorObj V W) := by
  rw [whiskerLeft_of_mem V (instSupercategory.id_mem W), sgn_zero]
  exact TensorProduct.map_id

theorem whiskerRight_id (V W : SVec k) : whiskerRight (𝟙 V) W = 𝟙 (tensorObj V W) :=
  TensorProduct.map_id

theorem comp_whiskerRight {U V W : SVec k} (f : U ⟶ V) (g : V ⟶ W) (X : SVec k) :
    whiskerRight (f ≫ g) X = whiskerRight f X ≫ whiskerRight g X :=
  TensorProduct.ext' fun _ _ => rfl

/-- The super interchange law in whiskering form. -/
theorem super_interchange {V V' W W' : SVec k} {p q : ZMod 2} {f : V ⟶ V'} {g : W ⟶ W'}
    (hf : f ∈ parityHom V V' p) (hg : g ∈ parityHom W W' q) :
    whiskerRight f W ≫ whiskerLeft V' g =
      koszulSign p q • (whiskerLeft V g ≫ whiskerRight f W') := by
  rw [whiskerLeft_of_mem V' hg, whiskerLeft_of_mem V hg, koszulSign_smul (R := k)]
  change map _ _ ∘ₗ map _ _ = sign k (p * q) • (map _ _ ∘ₗ map _ _)
  rw [← map_comp, ← map_comp, sgn_comp_of_mem hf, LinearMap.id_comp, LinearMap.comp_id,
    map_smul_left]

/-! ## The monoidal supercategory `SVec` -/

/-- The associativity isomorphism `(U ⊗ V) ⊗ W ≅ U ⊗ (V ⊗ W)` of `TensorProduct`. -/
def associator (U V W : SVec k) : tensorObj (tensorObj U V) W ≅ tensorObj U (tensorObj V W) :=
  isoOfLinearEquiv (TensorProduct.assoc k U V W)

/-- The left unitor `k ⊗ V ≅ V`. -/
def leftUnitor (V : SVec k) : tensorObj unit V ≅ V := isoOfLinearEquiv (TensorProduct.lid k V)

/-- The right unitor `V ⊗ k ≅ V`. -/
def rightUnitor (V : SVec k) : tensorObj V unit ≅ V := isoOfLinearEquiv (TensorProduct.rid k V)

instance instMonoidalCategoryStruct : MonoidalCategoryStruct (SVec k) where
  tensorObj := tensorObj
  whiskerLeft := whiskerLeft
  whiskerRight := whiskerRight
  tensorUnit := unit
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor

theorem tensorObj_def (V W : SVec k) : V ⊗ W = tensorObj V W := rfl

theorem tensorUnit_def : 𝟙_ (SVec k) = unit := rfl

theorem whiskerLeft_def (V : SVec k) {W W' : SVec k} (g : W ⟶ W') : V ◁ g = whiskerLeft V g :=
  rfl

theorem whiskerRight_def {V V' : SVec k} (f : V ⟶ V') (W : SVec k) : f ▷ W = whiskerRight f W :=
  rfl

@[simp] theorem associator_hom_tmul (U V W : SVec k) (u : U) (v : V) (w : W) :
    (α_ U V W).hom ((u ⊗ₜ v) ⊗ₜ w) = u ⊗ₜ (v ⊗ₜ w) := rfl

@[simp] theorem associator_inv_tmul (U V W : SVec k) (u : U) (v : V) (w : W) :
    (α_ U V W).inv (u ⊗ₜ (v ⊗ₜ w)) = (u ⊗ₜ v) ⊗ₜ w := rfl

@[simp] theorem leftUnitor_hom_tmul (V : SVec k) (r : k) (v : V) :
    (λ_ V).hom (r ⊗ₜ v) = r • v := by
  change TensorProduct.lid k V (r ⊗ₜ v) = r • v; simp

@[simp] theorem rightUnitor_hom_tmul (V : SVec k) (r : k) (v : V) :
    (ρ_ V).hom (v ⊗ₜ r) = r • v := by
  change TensorProduct.rid k V (v ⊗ₜ r) = r • v; simp

@[simp] theorem whiskerRight_tmul' {V V' : SVec k} (f : V ⟶ V') (W : SVec k) (v : V) (w : W) :
    (f ▷ W) (v ⊗ₜ w) = f v ⊗ₜ w := rfl

/-- `(1 ⊗ g)(v ⊗ w) = (-1)^{|v||g|} v ⊗ g(w)`, in the notation of `MonoidalCategoryStruct`. -/
theorem whiskerLeft_tmul' {V W W' : SVec k} {p q : ZMod 2} {g : W ⟶ W'}
    (hg : g ∈ parity (R := k) W W' q) {v : V} (hv : v ∈ V.part p) (w : W) :
    (V ◁ g) (v ⊗ₜ w) = sign k (p * q) • (v ⊗ₜ g w) :=
  whiskerLeft_tmul hg hv w

theorem associator_mem (U V W : SVec k) :
    (associator U V W).hom ∈ parityHom (tensorObj (tensorObj U V) W) (tensorObj U (tensorObj V W)) 0 := by
  intro q
  apply TensorProduct.ext_threefold
  intro u v w
  simp only [add_zero, LinearMap.comp_apply, associator, isoOfLinearEquiv_hom, toLinearMap_ofHom,
    LinearEquiv.coe_coe, tensorObj_proj_tmul, add_tmul, map_add, assoc_tmul, tmul_add]
  repeat rw [tensorObj_proj_tmul]
  simp only [add_tmul, tmul_add, map_add, assoc_tmul]
  rcases parity_eq_zero_or_one q with rfl | rfl
  · simp only [zero_add, add_zero, zmod2_one_add_one]; abel
  · simp only [zero_add, add_zero, zmod2_one_add_one, ← add_assoc]; abel

theorem leftUnitor_mem (V : SVec k) : (leftUnitor V).hom ∈ parityHom (tensorObj unit V) V 0 := by
  intro q
  apply TensorProduct.ext'
  intro r v
  change TensorProduct.lid k V ((tensorObj unit V).proj q (r ⊗ₜ v)) =
    V.proj (q + 0) (TensorProduct.lid k V (r ⊗ₜ v))
  rw [tensorObj_proj_tmul, unit_proj_zero_apply, unit_proj_one_apply, zero_tmul, add_zero,
    add_zero]
  simp

theorem rightUnitor_mem (V : SVec k) : (rightUnitor V).hom ∈ parityHom (tensorObj V unit) V 0 := by
  intro q
  apply TensorProduct.ext'
  intro v r
  change TensorProduct.rid k V ((tensorObj V unit).proj q (v ⊗ₜ r)) =
    V.proj (q + 0) (TensorProduct.rid k V (v ⊗ₜ r))
  rw [tensorObj_proj_tmul, add_zero]
  rcases parity_eq_zero_or_one q with rfl | rfl
  · rw [unit_proj_zero_apply, add_zero, unit_proj_one_apply, tmul_zero, add_zero]
    simp
  · rw [unit_proj_one_apply, zmod2_one_add_one, unit_proj_zero_apply, tmul_zero, zero_add]
    simp

theorem whiskerLeft_even (V : SVec k) {W W' : SVec k} {g : W ⟶ W'} (hg : g ∈ parityHom W W' 0) :
    whiskerLeft V g = ofHom (map LinearMap.id (toLinearMap g)) := by
  rw [whiskerLeft_of_mem V hg, sgn_zero]

theorem homProj_whiskerLeft (p : ZMod 2) (V : SVec k) {W W' : SVec k} (g : W ⟶ W') :
    homProj p (whiskerLeft V g) = whiskerLeft V (homProj p g) := by
  have e : whiskerLeft V g = whiskerLeft V (homProj p g) + whiskerLeft V (homProj (p + 1) g) := by
    rw [← whiskerLeft_add]
    rcases parity_eq_zero_or_one p with rfl | rfl
    · rw [zero_add, homProj_add_homProj]
    · rw [zmod2_one_add_one, add_comm, homProj_add_homProj]
  exact homProj_eq_of_add e (whiskerLeft_mem V (homProj_mem p g))
    (whiskerLeft_mem V (homProj_mem (p + 1) g))

theorem homProj_whiskerRight (p : ZMod 2) {V V' : SVec k} (f : V ⟶ V') (W : SVec k) :
    homProj p (whiskerRight f W) = whiskerRight (homProj p f) W := by
  have e : whiskerRight f W = whiskerRight (homProj p f) W + whiskerRight (homProj (p + 1) f) W := by
    have : f = homProj p f + homProj (p + 1) f := by
      rcases parity_eq_zero_or_one p with rfl | rfl
      · rw [zero_add, homProj_add_homProj]
      · rw [zmod2_one_add_one, add_comm, homProj_add_homProj]
    conv_lhs => rw [this]
    exact map_add_left _ _ _
  exact homProj_eq_of_add e (whiskerRight_mem (homProj_mem p f) W)
    (whiskerRight_mem (homProj_mem (p + 1) f) W)

theorem associator_naturality_left {U U' : SVec k} (f : U ⟶ U') (V W : SVec k) :
    whiskerRight (whiskerRight f V) W ≫ (associator U' V W).hom =
      (associator U V W).hom ≫ whiskerRight f (tensorObj V W) :=
  TensorProduct.ext_threefold fun _ _ _ => rfl

theorem whiskerRight_add {V V' : SVec k} (f f' : V ⟶ V') (W : SVec k) :
    whiskerRight (f + f') W = whiskerRight f W + whiskerRight f' W :=
  map_add_left _ _ _

theorem whiskerRight_zero {V V' : SVec k} (W : SVec k) :
    whiskerRight (0 : V ⟶ V') W = 0 :=
  map_zero_left _

theorem associator_naturality_middle (U : SVec k) {V V' : SVec k} (g : V ⟶ V') (W : SVec k) :
    whiskerRight (whiskerLeft U g) W ≫ (associator U V' W).hom =
      (associator U V W).hom ≫ whiskerLeft U (whiskerRight g W) := by
  refine Supercategory.induction_on (R := k) g ?_ ?_ ?_
  · rw [whiskerLeft_zero, whiskerRight_zero, whiskerRight_zero, whiskerLeft_zero,
      Limits.zero_comp, Limits.comp_zero]
  · intro b g hg
    rw [whiskerLeft_of_mem U hg, whiskerLeft_of_mem U (whiskerRight_mem hg W)]
    exact TensorProduct.ext_threefold fun _ _ _ => rfl
  · intro g g' hg hg'
    rw [whiskerLeft_add, whiskerRight_add, Preadditive.add_comp, hg, hg', whiskerRight_add,
      whiskerLeft_add, Preadditive.comp_add]

theorem associator_naturality_right (U V : SVec k) {W W' : SVec k} (h : W ⟶ W') :
    whiskerLeft (tensorObj U V) h ≫ (associator U V W').hom =
      (associator U V W).hom ≫ whiskerLeft U (whiskerLeft V h) := by
  refine Supercategory.induction_on (R := k) h ?_ ?_ ?_
  · rw [whiskerLeft_zero, whiskerLeft_zero, whiskerLeft_zero, Limits.zero_comp, Limits.comp_zero]
  · intro c h hh
    rw [whiskerLeft_of_mem _ hh, whiskerLeft_of_mem U (whiskerLeft_mem V hh),
      whiskerLeft_of_mem V hh, tensorObj_sgn]
    exact TensorProduct.ext_threefold fun _ _ _ => rfl
  · intro h h' hh hh'
    rw [whiskerLeft_add, Preadditive.add_comp, hh, hh', whiskerLeft_add, whiskerLeft_add,
      Preadditive.comp_add]

/-- **Brundan–Ellis, Example 1.5(i).** `SVec k` is a monoidal supercategory. -/
instance instMonoidalSupercategory : MonoidalSupercategory k (SVec k) where
  tensorHom_def _ _ := rfl
  whiskerLeft_id := whiskerLeft_id
  id_whiskerRight := whiskerRight_id
  whiskerLeft_comp := whiskerLeft_comp
  comp_whiskerRight := comp_whiskerRight
  whiskerLeft_add := whiskerLeft_add
  add_whiskerRight f g _ := map_add_left _ _ _
  whiskerLeft_smul := whiskerLeft_smul
  smul_whiskerRight r f _ := map_smul_left r _ _
  whiskerLeft_mem V _ _ _ _ hg := whiskerLeft_mem V hg
  whiskerRight_mem W hf := whiskerRight_mem hf W
  super_interchange hf hg := super_interchange hf hg
  associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} f₁ f₂ f₃ := by
    change (whiskerRight (whiskerRight f₁ X₂ ≫ whiskerLeft Y₁ f₂) X₃ ≫
        whiskerLeft (tensorObj Y₁ Y₂) f₃) ≫ (associator Y₁ Y₂ Y₃).hom =
      (associator X₁ X₂ X₃).hom ≫
        (whiskerRight f₁ (tensorObj X₂ X₃) ≫ whiskerLeft Y₁ (whiskerRight f₂ X₃ ≫ whiskerLeft Y₂ f₃))
    rw [comp_whiskerRight, Category.assoc, Category.assoc, associator_naturality_right,
      ← Category.assoc (whiskerRight (whiskerLeft Y₁ f₂) X₃), associator_naturality_middle]
    simp only [Category.assoc]
    rw [← Category.assoc (whiskerRight (whiskerRight f₁ X₂) X₃), associator_naturality_left,
      whiskerLeft_comp]
    simp only [Category.assoc]
  leftUnitor_naturality {V W} f := by
    change whiskerLeft unit f ≫ (leftUnitor W).hom = (leftUnitor V).hom ≫ f
    apply TensorProduct.ext'
    intro r v
    change TensorProduct.lid k W ((map LinearMap.id (toLinearMap (homProj 0 f)) +
      map (unit.sgn 1) (toLinearMap (homProj 1 f)) : k ⊗[k] V →ₗ[k] k ⊗[k] W) (r ⊗ₜ v)) =
        f (TensorProduct.lid k V (r ⊗ₜ v))
    rw [unit_sgn, LinearMap.add_apply, map_tmul, map_tmul, ← tmul_add, lid_tmul, lid_tmul,
      coe_toLinearMap, coe_toLinearMap, ← add_apply, homProj_add_homProj, map_smul]
    rfl
  rightUnitor_naturality {V W} f := by
    apply TensorProduct.ext'
    intro v r
    change TensorProduct.rid k W (f v ⊗ₜ r) = f (TensorProduct.rid k V (v ⊗ₜ r))
    rw [rid_tmul, rid_tmul, map_smul]
  pentagon U V W X := by
    change whiskerRight (associator U V W).hom X ≫ (associator U (tensorObj V W) X).hom ≫
        whiskerLeft U (associator V W X).hom = _
    rw [whiskerLeft_even U (associator_mem V W X)]
    exact TensorProduct.ext_fourfold fun _ _ _ _ => rfl
  triangle V W := by
    change (associator V unit W).hom ≫ whiskerLeft V (leftUnitor W).hom =
      whiskerRight (rightUnitor V).hom W
    rw [whiskerLeft_even V (leftUnitor_mem W)]
    refine TensorProduct.ext_threefold fun v r w => ?_
    change v ⊗ₜ TensorProduct.lid k W (r ⊗ₜ w) = TensorProduct.rid k V (v ⊗ₜ r) ⊗ₜ w
    rw [lid_tmul, rid_tmul, smul_tmul]
  associator_hom_mem := associator_mem
  leftUnitor_hom_mem := leftUnitor_mem
  rightUnitor_hom_mem := rightUnitor_mem

/-- **The Koszul sign rule** (Brundan–Ellis, §1.2): the paper's tensor product of linear maps
`f ⊗ g = (f ⊗ 1) ∘ (1 ⊗ g)` is `(f ⊗ g)(v ⊗ w) = (-1)^{|g||v|} f(v) ⊗ g(w)`. -/
theorem superTensorHom_tmul {V V' W W' : SVec k} (f : V ⟶ V') {p q : ZMod 2} {g : W ⟶ W'}
    (hg : g ∈ parity (R := k) W W' q) {v : V} (hv : v ∈ V.part p) (w : W) :
    MonoidalSupercategory.superTensorHom f g (v ⊗ₜ w) = sign k (q * p) • (f v ⊗ₜ g w) := by
  change (f ▷ W') ((V ◁ g) (v ⊗ₜ w)) = _
  rw [whiskerLeft_tmul' hg hv, map_smul, whiskerRight_tmul', mul_comm]

/-- Mathlib's `tensorHom f g = (1 ⊗ g) ∘ (f ⊗ 1)`:
`(f ⊗ g)(v ⊗ w) = (-1)^{|g|(|f| + |v|)} f(v) ⊗ g(w)`. -/
theorem tensorHom_tmul {V V' W W' : SVec k} {a b : ZMod 2} {f : V ⟶ V'} {g : W ⟶ W'}
    (hf : f ∈ parity (R := k) V V' a) (hg : g ∈ parity (R := k) W W' b) {p : ZMod 2} {v : V}
    (hv : v ∈ V.part p) (w : W) :
    (f ⊗ g) (v ⊗ₜ w) = sign k ((p + a) * b) • (f v ⊗ₜ g w) := by
  change (V' ◁ g) ((f ▷ W) (v ⊗ₜ w)) = _
  rw [whiskerRight_tmul', whiskerLeft_tmul' hg (apply_mem_part hf hv)]

/-! ## The parity shift -/

/-- The parity shift `Π V`: the module `V` with the opposite grading. -/
def piObj (V : SVec k) : SVec k where
  carrier := V
  odd := LinearMap.id - V.odd
  odd_comp_odd := by
    ext v
    simp [odd_apply_odd]

theorem piObj_proj (V : SVec k) (p : ZMod 2) : (piObj V).proj p = V.proj (p + 1) := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [proj_zero, zero_add, proj_one]
    ext v; simp [piObj]
  · rw [proj_one, zmod2_one_add_one, proj_zero]; rfl

theorem piObj_part (V : SVec k) (p : ZMod 2) : (piObj V).part p = V.part (p + 1) := by
  simp only [part, piObj_proj]

/-- The odd isomorphism `ζ_V : Π V → V`, the identity function. -/
def ζIso (V : SVec k) : piObj V ≅ V where
  hom := ofHom LinearMap.id
  inv := ofHom LinearMap.id
  hom_inv_id := rfl
  inv_hom_id := rfl

theorem ζIso_hom_mem (V : SVec k) : (ζIso V).hom ∈ parityHom (piObj V) V 1 := by
  intro q
  rw [piObj_proj]
  rfl

/-- **Brundan–Ellis, Example 1.8 (for `A = B = k`).** `SVec k` is a Π-supercategory, with
`Π V` the module `V` with the opposite grading and `ζ_V : Π V → V` the identity function. -/
instance instPiSupercategory : PiSupercategory k (SVec k) :=
  PiSupercategory.ofIso piObj ζIso ζIso_hom_mem

theorem pi_obj (V : SVec k) : (PiSupercategory.pi (R := k)).obj V = piObj V := rfl

/-- A linear map `V → W`, viewed as a linear map `Π V → Π W` (the same function). -/
def piHom {V W : SVec k} : (V ⟶ W) →ₗ[k] (piObj V ⟶ piObj W) where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem piHom_comp {U V W : SVec k} (f : U ⟶ V) (g : V ⟶ W) :
    piHom (f ≫ g) = piHom f ≫ piHom g := rfl

@[simp] theorem piHom_id (V : SVec k) : piHom (𝟙 V) = 𝟙 (piObj V) := rfl

@[simp] theorem piHom_apply {V W : SVec k} (f : V ⟶ W) (v : V) : piHom f v = f v := rfl

/-- A linear map has the same parity as a map `V → W` and as a map `Π V → Π W`. -/
theorem piHom_mem_iff {V W : SVec k} {p : ZMod 2} {f : V ⟶ W} :
    piHom f ∈ parityHom (piObj V) (piObj W) p ↔ f ∈ parityHom V W p := by
  constructor
  · intro h q
    have := h (q + 1)
    rw [piObj_proj, piObj_proj] at this
    have e1 : q + 1 + 1 = q := by rw [add_assoc, zmod2_one_add_one, add_zero]
    have e2 : q + 1 + p + 1 = q + p := by rw [add_right_comm, e1]
    rw [e1, e2] at this
    exact this
  · intro h q
    rw [piObj_proj, piObj_proj, show q + p + 1 = q + 1 + p by rw [add_right_comm]]
    exact h (q + 1)

theorem ζ_eq (V : SVec k) : PiSupercategory.ζ (R := k) V = ζIso V := rfl

/-- **Example 1.8.** `Π f = (-1)^{|f|} f` on the underlying linear maps. -/
theorem pi_map_of_mem {V W : SVec k} {p : ZMod 2} {f : V ⟶ W} (hf : f ∈ parity (R := k) V W p) :
    toLinearMap ((PiSupercategory.pi (R := k)).map f) = sign k p • toLinearMap f := by
  change toLinearMap (twist k 1 f) = _
  rw [twist_of_mem 1 hf, one_mul]
  rfl

/-- **Example 1.8.** `ξ_V : Π² V → V` is minus the identity function. -/
theorem ξ_hom (V : SVec k) :
    toLinearMap (PiSupercategory.ξ (R := k) V).hom = -LinearMap.id := by
  rw [PiSupercategory.ξ_hom_eq_neg]
  rfl

/-- **Brundan–Ellis, Example 1.13(i) (for `A = k`).** `SVec k` is a monoidal Π-supercategory
with `π := Π k` and `ζ : Π k → k` the identity function. -/
instance instMonoidalPiSupercategory : MonoidalPiSupercategory k (SVec k) where
  pi := piObj unit
  ζ := ζIso unit
  ζ_hom_mem := ζIso_hom_mem unit

/-! ## Graded subspaces -/

section Sub

variable (V : SVec k) (U : Submodule k V) (hU : ∀ v ∈ U, V.odd v ∈ U)

/-- A graded submodule `U ⊆ V` (one stable under the projection onto `V₁`), as a superspace. -/
abbrev sub : SVec k where
  carrier := U
  odd := V.odd.restrict hU
  odd_comp_odd := by
    ext v
    simp [odd_apply_odd]

theorem sub_odd_apply (v : U) : ((sub V U hU).odd v : V) = V.odd v := rfl

theorem sub_proj_apply (q : ZMod 2) (v : U) : ((sub V U hU).proj q v : V) = V.proj q v := by
  rcases parity_eq_zero_or_one q with rfl | rfl
  · simp [proj_zero, sub_odd_apply]
  · simp [proj_one, sub_odd_apply]

theorem mem_sub_part_iff {q : ZMod 2} {v : U} : v ∈ (sub V U hU).part q ↔ (v : V) ∈ V.part q := by
  rw [mem_part_iff, mem_part_iff, ← sub_proj_apply V U hU, Subtype.ext_iff]

variable {V U hU} {W : SVec k} {U' : Submodule k W} {hU' : ∀ w ∈ U', W.odd w ∈ U'}

/-- The restriction of a linear map to graded submodules. -/
def restrictHom (f : V ⟶ W) (hf : ∀ v ∈ U, f v ∈ U') : sub V U hU ⟶ sub W U' hU' :=
  ofHom ((toLinearMap f).restrict hf)

@[simp] theorem restrictHom_apply (f : V ⟶ W) (hf : ∀ v ∈ U, f v ∈ U') (v : U) :
    (restrictHom (hU := hU) (hU' := hU') f hf v : W) = f v := rfl

theorem restrictHom_mem {p : ZMod 2} {f : V ⟶ W} (hfp : f ∈ parityHom V W p)
    (hf : ∀ v ∈ U, f v ∈ U') : restrictHom (hU := hU) (hU' := hU') f hf ∈
      parityHom (sub V U hU) (sub W U' hU') p := by
  intro q
  ext v
  show f ((sub V U hU).proj q v : V) = ((sub W U' hU').proj (q + p) ⟨f v, hf v v.2⟩ : W)
  rw [sub_proj_apply, sub_proj_apply]
  exact apply_proj_of_mem hfp q v

end Sub

/-! ## Dimensions -/

section Dim

/-- The decomposition `V ≅ V₀ × V₁` of a superspace. -/
def partEquiv (V : SVec k) : V ≃ₗ[k] V.part 0 × V.part 1 where
  toFun v := (⟨V.proj 0 v, proj_mem_part V 0 v⟩, ⟨V.proj 1 v, proj_mem_part V 1 v⟩)
  map_add' _ _ := by ext <;> simp
  map_smul' _ _ := by ext <;> simp
  invFun x := x.1 + x.2
  left_inv v := proj_apply_add V v
  right_inv x := by
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := x
    ext
    · simp [proj_apply_of_mem_part _ ha, proj_apply_of_mem_part _ hb]
    · simp [proj_apply_of_mem_part _ ha, proj_apply_of_mem_part _ hb]

/-- An even linear map sends `V_q` to `W_q`. -/
def partMap {V W : SVec k} (f : V ⟶ W) (hf : f ∈ parityHom V W 0) (q : ZMod 2) :
    V.part q →ₗ[k] W.part q :=
  (toLinearMap f).restrict fun v hv => by simpa using apply_mem_part hf hv

@[simp] theorem partMap_apply {V W : SVec k} (f : V ⟶ W) (hf : f ∈ parityHom V W 0) (q : ZMod 2)
    (v : V.part q) : (partMap f hf q v : W) = f v := rfl

/-- An even isomorphism of superspaces restricts to isomorphisms of the homogeneous
components. -/
def partEquivOfIso {V W : SVec k} (e : V ≅ W) (he : e.hom ∈ parityHom V W 0) (q : ZMod 2) :
    V.part q ≃ₗ[k] W.part q :=
  LinearEquiv.ofLinear (partMap e.hom he q) (partMap e.inv (inv_mem e he) q)
    (by ext v; simp [← comp_apply]) (by ext v; simp [← comp_apply])

/-- Superspaces with isomorphic homogeneous components are evenly isomorphic. -/
def isoOfPartEquiv {V W : SVec k} (e₀ : V.part 0 ≃ₗ[k] W.part 0) (e₁ : V.part 1 ≃ₗ[k] W.part 1) :
    V ≅ W :=
  isoOfLinearEquiv (V.partEquiv ≪≫ₗ e₀.prodCongr e₁ ≪≫ₗ W.partEquiv.symm)

theorem isoOfPartEquiv_hom_mem {V W : SVec k} (e₀ : V.part 0 ≃ₗ[k] W.part 0)
    (e₁ : V.part 1 ≃ₗ[k] W.part 1) : (isoOfPartEquiv e₀ e₁).hom ∈ parityHom V W 0 := by
  refine mem_parityHom_of_apply_mem fun q v hv => ?_
  rw [add_zero]
  change ((e₀ (⟨V.proj 0 v, _⟩) : W) + e₁ ⟨V.proj 1 v, _⟩) ∈ W.part q
  rcases parity_eq_zero_or_one q with rfl | rfl
  · have : V.proj 1 v = 0 := by rw [proj_apply_of_mem_part _ hv]; rfl
    simp only [this]
    rw [show (⟨0, _⟩ : V.part 1) = 0 from rfl, map_zero, Submodule.coe_zero, add_zero]
    exact (e₀ _).2
  · have : V.proj 0 v = 0 := by rw [proj_apply_of_mem_part _ hv]; rfl
    simp only [this]
    rw [show (⟨0, _⟩ : V.part 0) = 0 from rfl, map_zero, Submodule.coe_zero, zero_add]
    exact (e₁ _).2

end Dim

end SVec

end StringDiagrams
