import StringDiagrams.Super.BoxProduct
import StringDiagrams.Super.SuperOpposite
import StringDiagrams.Super.FunctorCategory

/-!
# Superbimodules as superfunctors `A ⊠ B^{sop} → SVec`

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, Remark 1.3:
Example 1.2(iii) is a special case of Example 1.2(iv). For superalgebras `A` and `B`, viewed
as supercategories with one object (Example 1.2(ii)), and `B^{sop}` the super-opposite
supercategory (`StringDiagrams.Super.SuperOpposite`), the supercategory
`Hom(A ⊠ B^{sop}, SVec)` of superfunctors and supernatural transformations is isomorphic to
`A-SMod-B`: a superfunctor `V` is identified with the superspace `V(⋆)` obtained by evaluating
at the only object, viewed as a superbimodule via `a v b := (-1)^{|b||v|} V(a ⊗ b)(v)`, and
supernatural transformations are the same data as superbimodule homomorphisms.

## Main definitions and results

* `BimodCat 𝒜 ℬ := A ⊠ B^{sop}` (`StringDiagrams.BoxProd`).
* `SuperBimodule.toFunctor M : A ⊠ B^{sop} ⥤ SVec` (a superfunctor,
  `SuperBimodule.toSuperfunctor`), with `V(a ⊗ b)(v) = (-1)^{|b||v|} a v b`
  (`toFunctor_map_tmulHom_apply`).
* `SuperBimodule.ofFunctor V`: the `(A, B)`-superbimodule `V(⋆)` with
  `a v b := (-1)^{|b||v|} V(a ⊗ b)(v)` (`ofFunctor_lact_ract_apply`).
* `ofFunctor_toFunctor`, `toFunctor_ofFunctor`: the two constructions are mutually inverse on
  objects.
* On morphisms, `SuperBimodule.homOfNatTrans` (the total morphism `x_⋆ = x_{⋆,0} + x_{⋆,1}` of
  a supernatural transformation is a superbimodule homomorphism) and
  `SuperBimodule.natTransOfHom` (the parity components of a superbimodule homomorphism form a
  supernatural transformation), mutually inverse (`homOfNatTrans_natTransOfHom`,
  `natTransOfHom_homOfNatTrans`).
* `SuperBimodule.equivSuperfunctor`: **Remark 1.3**, the isomorphism of supercategories
  `Hom(A ⊠ B^{sop}, SVec) ≅ A-SMod-B`, as mutually inverse superfunctors
  (`SuperBimodule.evalSuperfunctor`, `SuperBimodule.bimoduleSuperfunctor`) whose composites are
  the identity functors (`eval_comp_bimodule`, `bimodule_comp_eval`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory TensorProduct

universe u

variable {k : Type u} [CommRing k] {A : Type u} [Ring A] [Algebra k A] {B : Type u} [Ring B]
  [Algebra k B] (𝒜 : ZMod 2 → Submodule k A) (ℬ : ZMod 2 → Submodule k B) [GradedAlgebra 𝒜]
  [GradedAlgebra ℬ]

/-- The supercategory `A ⊠ B^{sop}` (Brundan–Ellis, Remark 1.3). -/
abbrev BimodCat : Type := BoxProd k (SuperalgebraCat 𝒜) (SuperOppositeCat ℬ)

namespace BimodCat

/-- The only object of `A ⊠ B^{sop}`. -/
def pt : BimodCat 𝒜 ℬ := ⟨SuperalgebraCat.star 𝒜, SuperalgebraCat.star _⟩

variable {𝒜 ℬ}

omit [GradedAlgebra 𝒜] in
theorem eq_pt (X : BimodCat 𝒜 ℬ) : X = pt 𝒜 ℬ := rfl

/-- The morphism `a ⊗ b` of `A ⊠ B^{sop}`. -/
def tmul {X Y : BimodCat 𝒜 ℬ} (a : A) (b : B) : X ⟶ Y :=
  BoxProd.tmulHom (SuperalgebraCat.ofElem a) (SuperalgebraCat.ofElem (SuperOpposite.op ℬ b))

theorem tmul_mem {X Y : BimodCat 𝒜 ℬ} {p q : ZMod 2} {a : A} {b : B} (ha : a ∈ 𝒜 p) (hb : b ∈ ℬ q) :
    (tmul a b : X ⟶ Y) ∈ parity (R := k) X Y (p + q) :=
  BoxProd.tmul_mem_parity ha hb

theorem id_eq_tmul (X : BimodCat 𝒜 ℬ) : 𝟙 X = tmul 1 1 := rfl

/-- The composition rule of `A ⊠ B^{sop}`:
`(a ⊗ b) ≫ (a' ⊗ b') = (-1)^{|a||b'| + |b||b'|} (a' a) ⊗ (b b')` for homogeneous elements. -/
theorem tmul_comp_tmul {X Y Z : BimodCat 𝒜 ℬ} {p q q' : ZMod 2} {a a' : A} {b b' : B}
    (ha : a ∈ 𝒜 p) (hb : b ∈ ℬ q) (hb' : b' ∈ ℬ q') :
    (tmul a b : X ⟶ Y) ≫ (tmul a' b' : Y ⟶ Z) =
      sign k (p * q' + q * q') • (tmul (a' * a) (b * b') : X ⟶ Z) := by
  have h := BoxProd.tmulHom_comp_tmulHom (k := k) (X := X) (Y := Y) (Z := Z)
    (f := SuperalgebraCat.ofElem a) ha (SuperalgebraCat.ofElem (SuperOpposite.op ℬ b))
    (SuperalgebraCat.ofElem a') (l := SuperalgebraCat.ofElem (SuperOpposite.op ℬ b')) hb'
  have e1 : ((SuperalgebraCat.ofElem a : X.fst ⟶ Y.fst) ≫ (SuperalgebraCat.ofElem a' : Y.fst ⟶ Z.fst)) =
      SuperalgebraCat.ofElem (a' * a) := rfl
  have e2 : ((SuperalgebraCat.ofElem (SuperOpposite.op ℬ b) : X.snd ⟶ Y.snd) ≫
        (SuperalgebraCat.ofElem (SuperOpposite.op ℬ b') : Y.snd ⟶ Z.snd)) =
      sign k (q * q') • SuperalgebraCat.ofElem (SuperOpposite.op ℬ (b * b')) := by
    change (SuperalgebraCat.ofElem (SuperOpposite.mulBilin ℬ b' b) : X.snd ⟶ Z.snd) = _
    rw [SuperOpposite.mulBilin_of_mem ℬ hb' hb, mul_comm q' q]
    rfl
  rw [e1, e2, koszulSign_smul (R := k), BoxProd.tmulHom_smul_right] at h
  change BoxProd.tmulHom _ _ ≫ BoxProd.tmulHom _ _ = _
  rw [h, sign_add, mul_smul]
  rfl

/-- Linear maps out of `Hom(X, Y)` are determined by their values on `a ⊗ b` with `a`, `b`
homogeneous. -/
theorem hom_ext_tmul {X Y : BimodCat 𝒜 ℬ} {M : Type u} [AddCommGroup M] [Module k M]
    {φ ψ : (X ⟶ Y) →ₗ[k] M}
    (h : ∀ (p q : ZMod 2) (a : A) (b : B), a ∈ 𝒜 p → b ∈ ℬ q → φ (tmul a b) = ψ (tmul a b)) :
    φ = ψ :=
  BoxProd.hom_ext_homogeneous fun p q a b ha hb => h p q a b ha hb

/-- Induction on morphisms of `A ⊠ B^{sop}` via `a ⊗ b` with `a`, `b` homogeneous. -/
theorem induction_on {X Y : BimodCat 𝒜 ℬ} {P : (X ⟶ Y) → Prop} (x : X ⟶ Y) (zero : P 0)
    (tmul : ∀ (p q : ZMod 2) (a : A) (b : B), a ∈ 𝒜 p → b ∈ ℬ q → P (tmul a b))
    (add : ∀ x y, P x → P y → P (x + y)) : P x :=
  BoxProd.induction_on_homogeneous x zero (fun p q a b ha hb => tmul p q a b ha hb) add

end BimodCat

namespace SuperBimodule

open BimodCat

/-! ## Signs on superspaces -/

/-- Morphisms of `SVec k` agreeing on homogeneous vectors are equal. -/
theorem _root_.StringDiagrams.SVec.hom_ext_part {V W : SVec k} {f g : V ⟶ W}
    (h : ∀ (q : ZMod 2) (v : V), v ∈ V.part q → f v = g v) : f = g :=
  SVec.ext_part h

/-- The sign involution `v ↦ (-1)^{q|v|} v`, as a morphism of `SVec k`. -/
abbrev sgnHom (V : SVec k) (q : ZMod 2) : V ⟶ V := SVec.ofHom (V.sgn q)

theorem sgnHom_mem (V : SVec k) (q : ZMod 2) : sgnHom V q ∈ SVec.parityHom V V 0 := SVec.sgn_mem V q

theorem sgnHom_apply_of_mem {V : SVec k} (q : ZMod 2) {s : ZMod 2} {v : V} (hv : v ∈ V.part s) :
    sgnHom V q v = sign k (s * q) • v :=
  SVec.sgn_apply_of_mem q hv

theorem sgnHom_comp_sgnHom (V : SVec k) (q q' : ZMod 2) :
    sgnHom V q ≫ sgnHom V q' = sgnHom V (q + q') := by
  change SVec.ofHom (V.sgn q' ∘ₗ V.sgn q) = _
  rw [SVec.sgn_comp_sgn, add_comm]

theorem sgnHom_zero (V : SVec k) : sgnHom V 0 = 𝟙 V := by
  change SVec.ofHom (V.sgn 0) = _
  rw [SVec.sgn_zero]; rfl

/-- A homogeneous map of parity `p` commutes with the signs up to `(-1)^{pq}`. -/
theorem comp_sgnHom_of_mem {V W : SVec k} {p : ZMod 2} {f : V ⟶ W} (hf : f ∈ SVec.parityHom V W p)
    (q : ZMod 2) : f ≫ sgnHom W q = sign k (p * q) • (sgnHom V q ≫ f) :=
  SVec.sgn_comp_of_mem hf q

/-! ## From superbimodules to superfunctors -/

section ToFunctor

variable {𝒜 ℬ} (M : SuperBimodule 𝒜 ℬ)

/-- The signed right action `v ↦ (-1)^{|b||v|} v b`, linear in `b`. -/
def sract : B →ₗ[k] (M.toSVec ⟶ M.toSVec) :=
  M.ract ∘ₗ algProj ℬ 0 + (Linear.leftComp k M.toSVec (sgnHom M.toSVec 1)) ∘ₗ M.ract ∘ₗ algProj ℬ 1

omit [GradedAlgebra 𝒜] in
theorem sract_apply (b : B) :
    sract M b = M.ract (algProj ℬ 0 b) + sgnHom M.toSVec 1 ≫ M.ract (algProj ℬ 1 b) := rfl

omit [GradedAlgebra 𝒜] in
theorem sract_of_mem {q : ZMod 2} {b : B} (hb : b ∈ ℬ q) : sract M b = sgnHom M.toSVec q ≫ M.ract b := by
  rw [sract_apply]
  rcases parity_eq_zero_or_one q with rfl | rfl
  · rw [algProj_of_mem ℬ hb, algProj_of_mem_ne ℬ hb (by decide), map_zero, Limits.comp_zero,
      add_zero, sgnHom_zero, Category.id_comp]
  · rw [algProj_of_mem ℬ hb, algProj_of_mem_ne ℬ hb (by decide), map_zero, zero_add]

omit [GradedAlgebra 𝒜] in
theorem sract_apply_of_mem {q : ZMod 2} {b : B} (hb : b ∈ ℬ q) {s : ZMod 2} {v : M.toSVec}
    (hv : v ∈ M.toSVec.part s) : sract M b v = sign k (s * q) • M.ract b v := by
  rw [sract_of_mem M hb, SVec.comp_apply, sgnHom_apply_of_mem q hv, SVec.hom_map_smul]

/-- The bilinear map `(a, b) ↦ (v ↦ (-1)^{|b||v|} a v b)`. -/
def toFunctorBilin : A →ₗ[k] SuperOpposite ℬ →ₗ[k] (M.toSVec ⟶ M.toSVec) :=
  ((Linear.comp (S := k) M.toSVec M.toSVec M.toSVec).compl₁₂ (sract M) M.lact).flip

omit [GradedAlgebra 𝒜] in
theorem toFunctorBilin_apply (a : A) (b : B) :
    toFunctorBilin M a (SuperOpposite.op ℬ b) = sract M b ≫ M.lact a := rfl

omit [GradedAlgebra 𝒜] in
/-- `(a ⊗ b)(v) = (-1)^{|b||v|} a v b` for homogeneous `b`, `v`. -/
theorem toFunctorBilin_apply_of_mem (a : A) {q : ZMod 2} {b : B} (hb : b ∈ ℬ q) {s : ZMod 2}
    {v : M.toSVec} (hv : v ∈ M.toSVec.part s) :
    toFunctorBilin M a (SuperOpposite.op ℬ b) v = sign k (s * q) • M.lact a (M.ract b v) := by
  rw [toFunctorBilin_apply, SVec.comp_apply, sract_apply_of_mem M hb hv, SVec.hom_map_smul]

/-- The linear map `Hom(X, Y) → End(M)` underlying the superfunctor of a superbimodule. -/
def toFunctorMap (X Y : BimodCat 𝒜 ℬ) : (X ⟶ Y) →ₗ[k] (M.toSVec ⟶ M.toSVec) :=
  TensorProduct.lift (toFunctorBilin M)

theorem toFunctorMap_tmul (X Y : BimodCat 𝒜 ℬ) (a : A) (b : B) :
    toFunctorMap M X Y (tmul a b) = sract M b ≫ M.lact a :=
  lift.tmul _ _

theorem toFunctorMap_comp {X Y Z : BimodCat 𝒜 ℬ} (x : X ⟶ Y) (y : Y ⟶ Z) :
    toFunctorMap M X Z (x ≫ y) = toFunctorMap M X Y x ≫ toFunctorMap M Y Z y := by
  induction x using BimodCat.induction_on with
  | zero => rw [Limits.zero_comp, map_zero, map_zero, Limits.zero_comp]
  | add x x' hx hx' => rw [Preadditive.add_comp, map_add, map_add, hx, hx', Preadditive.add_comp]
  | tmul p q a b ha hb =>
    induction y using BimodCat.induction_on with
    | zero => rw [Limits.comp_zero, map_zero, map_zero, Limits.comp_zero]
    | add y y' hy hy' => rw [Preadditive.comp_add, map_add, map_add, hy, hy', Preadditive.comp_add]
    | tmul p' q' a' b' ha' hb' =>
      rw [tmul_comp_tmul ha hb hb', map_smul, toFunctorMap_tmul, toFunctorMap_tmul,
        toFunctorMap_tmul]
      refine SVec.hom_ext_part fun s v hv => ?_
      have h1 : M.ract b v ∈ M.toSVec.part (s + q) := SVec.apply_mem_part (M.ract_mem q b hb) hv
      have h2 : M.lact a (M.ract b v) ∈ M.toSVec.part (s + q + p) :=
        SVec.apply_mem_part (M.lact_mem p a ha) h1
      have h3 : M.ract b' (M.lact a (M.ract b v)) = M.lact a (M.ract b' (M.ract b v)) := by
        have := congrArg (fun φ : M.toSVec ⟶ M.toSVec => φ (M.ract b v)) (M.lact_ract a b')
        simp only [SVec.comp_apply] at this
        exact this
      simp only [SVec.smul_apply, SVec.comp_apply]
      rw [sract_apply_of_mem M (SetLike.GradedMul.mul_mem hb hb') hv, sract_apply_of_mem M hb hv]
      simp only [SVec.hom_map_smul]
      rw [sract_apply_of_mem M hb' h2]
      simp only [SVec.hom_map_smul, smul_smul, ← sign_add]
      rw [M.lact_mul, M.ract_mul, SVec.comp_apply, SVec.comp_apply, h3]
      congr 2
      ring

/-- **Brundan–Ellis, Remark 1.3.** The superfunctor `A ⊠ B^{sop} → SVec` of an
`(A, B)`-superbimodule `M`: `⋆ ↦ M`, `(a ⊗ b) ↦ (v ↦ (-1)^{|b||v|} a v b)`. -/
def toFunctor : BimodCat 𝒜 ℬ ⥤ SVec k where
  obj _ := M.toSVec
  map {X Y} x := toFunctorMap M X Y x
  map_id X := by
    rw [id_eq_tmul, toFunctorMap_tmul, sract_of_mem M SetLike.GradedOne.one_mem, sgnHom_zero,
      Category.id_comp, M.ract_one, M.lact_one, Category.id_comp]
  map_comp x y := toFunctorMap_comp M x y

theorem toFunctor_obj (X : BimodCat 𝒜 ℬ) : (toFunctor M).obj X = M.toSVec := rfl

theorem toFunctor_map {X Y : BimodCat 𝒜 ℬ} (x : X ⟶ Y) : (toFunctor M).map x = toFunctorMap M X Y x :=
  rfl

theorem toFunctor_map_tmul {X Y : BimodCat 𝒜 ℬ} (a : A) (b : B) :
    (toFunctor M).map (tmul a b : X ⟶ Y) = sract M b ≫ M.lact a :=
  toFunctorMap_tmul M X Y a b

/-- **Remark 1.3**: `V(a ⊗ b)(v) = (-1)^{|b||v|} a v b`. -/
theorem toFunctor_map_tmul_apply {X Y : BimodCat 𝒜 ℬ} (a : A) {q : ZMod 2} {b : B} (hb : b ∈ ℬ q)
    {s : ZMod 2} {v : M.toSVec} (hv : v ∈ M.toSVec.part s) :
    (toFunctor M).map (tmul a b : X ⟶ Y) v = sign k (s * q) • M.lact a (M.ract b v) := by
  change (sract M b ≫ M.lact a) v = _
  rw [SVec.comp_apply, sract_apply_of_mem M hb hv, SVec.hom_map_smul]

instance : (toFunctor M).Additive where
  map_add := map_add (toFunctorMap M _ _) _ _

instance : (toFunctor M).Linear k where
  map_smul x r := map_smul (toFunctorMap M _ _) r x

theorem toFunctor_map_mem {X Y : BimodCat 𝒜 ℬ} {p : ZMod 2} {x : X ⟶ Y} (hx : x ∈ parity (R := k) X Y p) :
    (toFunctor M).map x ∈ parity (R := k) M.toSVec M.toSVec p := by
  have key : ∀ x : X ⟶ Y, (toFunctor M).map ((BoxProd.homObj k X Y).proj p x) ∈
      SVec.parityHom M.toSVec M.toSVec p := by
    intro x
    induction x using BimodCat.induction_on with
    | zero => rw [map_zero, Functor.map_zero]; exact Submodule.zero_mem _
    | add x x' hx hx' => rw [map_add, Functor.map_add]; exact Submodule.add_mem _ hx hx'
    | tmul a' b' a b ha hb =>
      rw [SVec.proj_apply_of_mem_part _ (tmul_mem ha hb)]
      split_ifs with h
      · subst h
        rw [toFunctor_map_tmul, sract_of_mem M hb, Category.assoc]
        simpa [add_comm] using! comp_mem (sgnHom_mem M.toSVec b') (comp_mem (M.ract_mem b' b hb)
          (M.lact_mem a' a ha))
      · rw [Functor.map_zero]; exact Submodule.zero_mem _
  have := key x
  rwa [(SVec.mem_part_iff _).1 hx] at this

instance : IsSuperfunctor k (toFunctor M) where
  map_mem hx := toFunctor_map_mem M hx

/-- **Remark 1.3.** The superfunctor `A ⊠ B^{sop} → SVec` of a superbimodule, bundled. -/
def toSuperfunctor : Superfunctor k (BimodCat 𝒜 ℬ) (SVec k) := ⟨toFunctor M⟩

end ToFunctor

/-! ## From superfunctors to superbimodules -/

section OfFunctor

variable {𝒜 ℬ}

theorem _root_.StringDiagrams.Supercategory.Superfunctor.map_zero'
    (V : Superfunctor k (BimodCat 𝒜 ℬ) (SVec k)) {X Y : BimodCat 𝒜 ℬ} :
    V.map (0 : X ⟶ Y) = 0 :=
  V.toFunctor.map_zero X Y

theorem _root_.StringDiagrams.Supercategory.Superfunctor.map_add'
    (V : Superfunctor k (BimodCat 𝒜 ℬ) (SVec k)) {X Y : BimodCat 𝒜 ℬ} (x y : X ⟶ Y) :
    V.map (x + y) = V.map x + V.map y :=
  V.toFunctor.map_add

theorem _root_.StringDiagrams.Supercategory.Superfunctor.map_smul'
    (V : Superfunctor k (BimodCat 𝒜 ℬ) (SVec k)) {X Y : BimodCat 𝒜 ℬ} (r : k) (x : X ⟶ Y) :
    V.map (r • x) = r • V.map x :=
  V.toFunctor.map_smul r x

variable (𝒜 ℬ) in
/-- `a ↦ a ⊗ 1`. -/
def tmulLeft : A →ₗ[k] (pt 𝒜 ℬ ⟶ pt 𝒜 ℬ) :=
  (TensorProduct.mk k ((pt 𝒜 ℬ).fst ⟶ (pt 𝒜 ℬ).fst) ((pt 𝒜 ℬ).snd ⟶ (pt 𝒜 ℬ).snd)).flip (𝟙 _)

variable (𝒜 ℬ) in
/-- `b ↦ 1 ⊗ b`. -/
def tmulRight : B →ₗ[k] (pt 𝒜 ℬ ⟶ pt 𝒜 ℬ) :=
  TensorProduct.mk k ((pt 𝒜 ℬ).fst ⟶ (pt 𝒜 ℬ).fst) ((pt 𝒜 ℬ).snd ⟶ (pt 𝒜 ℬ).snd) (𝟙 _)

theorem tmulLeft_apply (a : A) : tmulLeft 𝒜 ℬ a = tmul a 1 := rfl

theorem tmulRight_apply (b : B) : tmulRight 𝒜 ℬ b = tmul 1 b := rfl

variable (V : Superfunctor k (BimodCat 𝒜 ℬ) (SVec k))

/-- The linear map `V.map` on `Hom(⋆, ⋆)`. -/
abbrev evalMap : (pt 𝒜 ℬ ⟶ pt 𝒜 ℬ) →ₗ[k] (V.obj (pt 𝒜 ℬ) ⟶ V.obj (pt 𝒜 ℬ)) :=
  V.toFunctor.mapLinearMap k

/-- The right action `v ↦ (-1)^{|b||v|} V(1 ⊗ b)(v)` of `ofFunctor V`, linear in `b`. -/
def ofFunctorRact : B →ₗ[k] (V.obj (pt 𝒜 ℬ) ⟶ V.obj (pt 𝒜 ℬ)) :=
  evalMap V ∘ₗ tmulRight 𝒜 ℬ ∘ₗ algProj ℬ 0 +
    (Linear.leftComp k (V.obj (pt 𝒜 ℬ)) (sgnHom (V.obj (pt 𝒜 ℬ)) 1)) ∘ₗ evalMap V ∘ₗ
      tmulRight 𝒜 ℬ ∘ₗ algProj ℬ 1

theorem ofFunctorRact_apply (b : B) :
    ofFunctorRact V b = V.map (tmulRight 𝒜 ℬ (algProj ℬ 0 b)) +
      sgnHom (V.obj (pt 𝒜 ℬ)) 1 ≫ V.map (tmulRight 𝒜 ℬ (algProj ℬ 1 b)) := rfl

theorem ofFunctorRact_of_mem {q : ZMod 2} {b : B} (hb : b ∈ ℬ q) :
    ofFunctorRact V b = sgnHom (V.obj (pt 𝒜 ℬ)) q ≫ V.map (tmul 1 b) := by
  rw [ofFunctorRact_apply]
  rcases parity_eq_zero_or_one q with rfl | rfl
  · rw [algProj_of_mem ℬ hb, algProj_of_mem_ne ℬ hb (by decide), sgnHom_zero, Category.id_comp,
      map_zero, Superfunctor.map_zero', Limits.comp_zero, add_zero, tmulRight_apply]
  · rw [algProj_of_mem ℬ hb, algProj_of_mem_ne ℬ hb (by decide), map_zero, Superfunctor.map_zero',
      zero_add, tmulRight_apply]

theorem map_tmul_mem {p q : ZMod 2} {a : A} {b : B} (ha : a ∈ 𝒜 p) (hb : b ∈ ℬ q) :
    V.map (tmul a b : pt 𝒜 ℬ ⟶ pt 𝒜 ℬ) ∈ parity (R := k) _ _ (p + q) :=
  V.map_mem (tmul_mem ha hb)

theorem map_tmul_comp_tmul {p q q' : ZMod 2} {a a' : A} {b b' : B} (ha : a ∈ 𝒜 p) (hb : b ∈ ℬ q)
    (hb' : b' ∈ ℬ q') :
    V.map (tmul a b : pt 𝒜 ℬ ⟶ pt 𝒜 ℬ) ≫ V.map (tmul a' b' : pt 𝒜 ℬ ⟶ pt 𝒜 ℬ) =
      sign k (p * q' + q * q') • V.map (tmul (a' * a) (b * b') : pt 𝒜 ℬ ⟶ pt 𝒜 ℬ) := by
  rw [← V.toFunctor.map_comp, tmul_comp_tmul ha hb hb']
  exact V.toFunctor.map_smul _ _

/-- **Brundan–Ellis, Remark 1.3.** The `(A, B)`-superbimodule of a superfunctor
`V : A ⊠ B^{sop} → SVec`: the superspace `V(⋆)` with `a v b := (-1)^{|b||v|} V(a ⊗ b)(v)`. -/
def ofFunctor : SuperBimodule 𝒜 ℬ where
  toSVec := V.obj (pt 𝒜 ℬ)
  lact := evalMap V ∘ₗ tmulLeft 𝒜 ℬ
  ract := ofFunctorRact V
  lact_one := by
    change V.map (tmulLeft 𝒜 ℬ 1) = 𝟙 _
    rw [tmulLeft_apply, ← id_eq_tmul]; exact V.toFunctor.map_id _
  lact_mul a a' := by
    change V.map (tmulLeft 𝒜 ℬ (a * a')) = V.map (tmulLeft 𝒜 ℬ a') ≫ V.map (tmulLeft 𝒜 ℬ a)
    induction a' using alg_induction_on 𝒜 with
    | zero => rw [mul_zero, map_zero, Superfunctor.map_zero', Limits.zero_comp]
    | add a₁ a₂ h₁ h₂ =>
      rw [mul_add, map_add, map_add, Superfunctor.map_add', Superfunctor.map_add',
        Preadditive.add_comp, h₁, h₂]
    | hom p' a' ha' =>
      rw [tmulLeft_apply, tmulLeft_apply, tmulLeft_apply,
        map_tmul_comp_tmul V ha' SetLike.GradedOne.one_mem SetLike.GradedOne.one_mem, mul_zero,
        mul_zero, add_zero, sign_zero, one_smul, one_mul]
  ract_one := by
    rw [ofFunctorRact_of_mem V SetLike.GradedOne.one_mem, sgnHom_zero, Category.id_comp,
      ← id_eq_tmul]
    exact V.toFunctor.map_id _
  ract_mul b b' := by
    induction b using alg_induction_on ℬ with
    | zero => simp only [zero_mul, map_zero, Limits.zero_comp]
    | add b₁ b₂ h₁ h₂ => simp only [add_mul, map_add, h₁, h₂, Preadditive.add_comp]
    | hom q b hb =>
      induction b' using alg_induction_on ℬ with
      | zero => simp only [mul_zero, map_zero, Limits.comp_zero]
      | add b₁ b₂ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂, Preadditive.comp_add]
      | hom q' b' hb' =>
        rw [ofFunctorRact_of_mem V (SetLike.GradedMul.mul_mem hb hb'), ofFunctorRact_of_mem V hb,
          ofFunctorRact_of_mem V hb', Category.assoc, ← Category.assoc (V.map _),
          comp_sgnHom_of_mem (map_tmul_mem V SetLike.GradedOne.one_mem hb) q', zero_add,
          Linear.smul_comp, Linear.comp_smul, Category.assoc, ← Category.assoc (sgnHom _ q),
          sgnHom_comp_sgnHom, map_tmul_comp_tmul V SetLike.GradedOne.one_mem hb hb', one_mul,
          zero_mul, zero_add, Linear.comp_smul, smul_smul, sign_mul_self, one_smul]
  lact_ract a b := by
    change V.map (tmulLeft 𝒜 ℬ a) ≫ ofFunctorRact V b = ofFunctorRact V b ≫ V.map (tmulLeft 𝒜 ℬ a)
    induction a using alg_induction_on 𝒜 with
    | zero => simp only [map_zero, Superfunctor.map_zero', Limits.zero_comp, Limits.comp_zero]
    | add a₁ a₂ h₁ h₂ =>
      simp only [map_add, Superfunctor.map_add', Preadditive.add_comp, Preadditive.comp_add, h₁, h₂]
    | hom p a ha =>
      induction b using alg_induction_on ℬ with
      | zero => simp only [map_zero, Limits.zero_comp, Limits.comp_zero]
      | add b₁ b₂ h₁ h₂ => simp only [map_add, Preadditive.add_comp, Preadditive.comp_add, h₁, h₂]
      | hom q b hb =>
        rw [tmulLeft_apply, ofFunctorRact_of_mem V hb, ← Category.assoc,
          comp_sgnHom_of_mem (map_tmul_mem V ha SetLike.GradedOne.one_mem) q, add_zero,
          Linear.smul_comp, Category.assoc, Category.assoc,
          map_tmul_comp_tmul V ha SetLike.GradedOne.one_mem hb,
          map_tmul_comp_tmul V SetLike.GradedOne.one_mem hb SetLike.GradedOne.one_mem]
        simp only [one_mul, mul_one, mul_zero, zero_mul, add_zero, sign_zero, one_smul,
          Linear.comp_smul, smul_smul, sign_mul_self]
  lact_mem p a ha := by
    change V.map (tmulLeft 𝒜 ℬ a) ∈ _
    rw [tmulLeft_apply]
    simpa using map_tmul_mem V ha SetLike.GradedOne.one_mem
  ract_mem q b hb := by
    rw [ofFunctorRact_of_mem V hb]
    simpa using comp_mem (sgnHom_mem (V.obj (pt 𝒜 ℬ)) q) (map_tmul_mem V SetLike.GradedOne.one_mem hb)

theorem ofFunctor_toSVec : (ofFunctor V).toSVec = V.obj (pt 𝒜 ℬ) := rfl

theorem ofFunctor_lact (a : A) : (ofFunctor V).lact a = V.map (tmul a 1) := rfl

theorem ofFunctor_ract_of_mem {q : ZMod 2} {b : B} (hb : b ∈ ℬ q) :
    (ofFunctor V).ract b = sgnHom (V.obj (pt 𝒜 ℬ)) q ≫ V.map (tmul 1 b) :=
  ofFunctorRact_of_mem V hb

/-- **Remark 1.3**: `a v b = (-1)^{|b||v|} V(a ⊗ b)(v)` for homogeneous `b`, `v`. -/
theorem ofFunctor_lact_ract_apply (a : A) {q : ZMod 2} {b : B} (hb : b ∈ ℬ q) {s : ZMod 2}
    {v : V.obj (pt 𝒜 ℬ)} (hv : v ∈ (V.obj (pt 𝒜 ℬ)).part s) :
    (ofFunctor V).lact a ((ofFunctor V).ract b v) = sign k (s * q) • V.map (tmul a b) v := by
  rw [ofFunctor_ract_of_mem V hb]
  show (V.map (tmul a 1) : V.obj (pt 𝒜 ℬ) ⟶ V.obj (pt 𝒜 ℬ))
    ((sgnHom (V.obj (pt 𝒜 ℬ)) q ≫ V.map (tmul 1 b)) v) = _
  rw [SVec.comp_apply, sgnHom_apply_of_mem q hv, SVec.hom_map_smul, SVec.hom_map_smul,
    ← SVec.comp_apply, map_tmul_comp_tmul V SetLike.GradedOne.one_mem hb SetLike.GradedOne.one_mem,
    zero_mul, mul_zero, add_zero, sign_zero, one_smul, mul_one, mul_one]

end OfFunctor

/-! ## The two constructions are mutually inverse on objects -/

section Inverse

variable {𝒜 ℬ}

set_option backward.isDefEq.respectTransparency false in
theorem ofFunctor_toSuperfunctor (M : SuperBimodule 𝒜 ℬ) : ofFunctor (toSuperfunctor M) = M := by
  have hl : (ofFunctor (toSuperfunctor M)).lact = M.lact := LinearMap.ext fun a => by
    change (toFunctor M).map (tmul a 1) = M.lact a
    rw [toFunctor_map_tmul, sract_of_mem M SetLike.GradedOne.one_mem, sgnHom_zero,
      Category.id_comp, M.ract_one, Category.id_comp]
  have hr : (ofFunctor (toSuperfunctor M)).ract = M.ract := LinearMap.ext fun b => by
    induction b using alg_induction_on ℬ with
    | zero => rw [map_zero, map_zero]
    | add b₁ b₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
    | hom q b hb =>
      rw [ofFunctor_ract_of_mem _ hb]
      change sgnHom M.toSVec q ≫ (toFunctor M).map (tmul 1 b) = M.ract b
      rw [toFunctor_map_tmul, sract_of_mem M hb, M.lact_one, Category.comp_id, ← Category.assoc,
        sgnHom_comp_sgnHom, zmod2_add_self, sgnHom_zero, Category.id_comp]
  revert hl hr
  cases M
  intro hl hr
  unfold ofFunctor
  congr 1

set_option backward.isDefEq.respectTransparency false in
theorem toFunctor_ofFunctor_map (V : Superfunctor k (BimodCat 𝒜 ℬ) (SVec k)) {X Y : BimodCat 𝒜 ℬ}
    (x : X ⟶ Y) : (toFunctor (ofFunctor V)).map x = V.map x := by
  induction x using BimodCat.induction_on with
  | zero => rw [Functor.map_zero, Superfunctor.map_zero']
  | add x x' hx hx' => rw [Functor.map_add, Superfunctor.map_add', hx, hx']
  | tmul p q a b ha hb =>
    rw [toFunctor_map_tmul, sract_of_mem _ hb, ofFunctor_ract_of_mem V hb, ofFunctor_lact]
    change ((sgnHom (V.obj (pt 𝒜 ℬ)) q ≫ sgnHom (V.obj (pt 𝒜 ℬ)) q) ≫ V.map (tmul 1 b)) ≫
      V.map (tmul a 1) = V.map (tmul a b)
    rw [sgnHom_comp_sgnHom, zmod2_add_self, sgnHom_zero, Category.id_comp,
      map_tmul_comp_tmul V SetLike.GradedOne.one_mem hb SetLike.GradedOne.one_mem, zero_mul,
      mul_zero, add_zero, sign_zero, one_smul, mul_one, mul_one]

set_option backward.isDefEq.respectTransparency false in
theorem toSuperfunctor_ofFunctor (V : Superfunctor k (BimodCat 𝒜 ℬ) (SVec k)) :
    toSuperfunctor (ofFunctor V) = V := by
  refine Superfunctor.ext (CategoryTheory.Functor.ext (fun X => rfl) fun X Y x => ?_)
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact toFunctor_ofFunctor_map V x

end Inverse

/-! ## Supernatural transformations and superbimodule homomorphisms -/

section Morphisms

variable {𝒜 ℬ}

theorem total_eq_twist {V W : Superfunctor k (BimodCat 𝒜 ℬ) (SVec k)} (x : V ⟶ W) (p : ZMod 2)
    (X : BimodCat 𝒜 ℬ) :
    twist k p (SuperNatTrans.total x X) = x.app 0 X + sign k p • x.app 1 X := by
  rw [SuperNatTrans.total, map_add, twist_of_mem p (x.app_mem 0 X), twist_of_mem p (x.app_mem 1 X),
    mul_zero, sign_zero, one_smul, mul_one]

set_option backward.isDefEq.respectTransparency false in
/-- The total morphism of a supernatural transformation is a superbimodule homomorphism. -/
theorem isHom_total {V W : Superfunctor k (BimodCat 𝒜 ℬ) (SVec k)} (x : V ⟶ W) :
    IsHom (ofFunctor V) (ofFunctor W) (SuperNatTrans.total x (pt 𝒜 ℬ)) := by
  refine ⟨fun p a ha => ?_, fun b => ?_⟩
  · have h0 := x.naturality 0 (tmul a 1 : pt 𝒜 ℬ ⟶ pt 𝒜 ℬ) (tmul_mem ha SetLike.GradedOne.one_mem)
    have h1 := x.naturality 1 (tmul a 1 : pt 𝒜 ℬ ⟶ pt 𝒜 ℬ) (tmul_mem ha SetLike.GradedOne.one_mem)
    rw [koszulSign_zero_left, one_smul] at h0
    rw [koszulSign_smul (R := k), one_mul, add_zero] at h1
    change V.map (tmul a 1) ≫ SuperNatTrans.total x (pt 𝒜 ℬ) =
      twist k p (SuperNatTrans.total x (pt 𝒜 ℬ)) ≫ W.map (tmul a 1)
    rw [total_eq_twist, SuperNatTrans.total, Preadditive.comp_add, Preadditive.add_comp,
      Linear.smul_comp, h0, h1]
  · induction b using alg_induction_on ℬ with
    | zero => simp only [map_zero, Limits.zero_comp, Limits.comp_zero]
    | add b₁ b₂ h₁ h₂ => simp only [map_add, Preadditive.add_comp, Preadditive.comp_add, h₁, h₂]
    | hom q b hb =>
      have key : ∀ s : ZMod 2, (ofFunctor V).ract b ≫ x.app s (pt 𝒜 ℬ) =
          x.app s (pt 𝒜 ℬ) ≫ (ofFunctor W).ract b := by
        intro s
        have h := x.naturality s (tmul 1 b : pt 𝒜 ℬ ⟶ pt 𝒜 ℬ) (tmul_mem SetLike.GradedOne.one_mem hb)
        rw [zero_add, koszulSign_smul (R := k)] at h
        have hs : sgnHom (V.obj (pt 𝒜 ℬ)) q ≫ x.app s (pt 𝒜 ℬ) =
            sign k (s * q) • (x.app s (pt 𝒜 ℬ) ≫ sgnHom (W.obj (pt 𝒜 ℬ)) q) := by
          rw [comp_sgnHom_of_mem (x.app_mem s (pt 𝒜 ℬ)) q, smul_smul, sign_mul_self, one_smul]
        rw [ofFunctor_ract_of_mem V hb, ofFunctor_ract_of_mem W hb]
        change sgnHom (V.obj (pt 𝒜 ℬ)) q ≫ V.map (tmul 1 b) ≫ x.app s (pt 𝒜 ℬ) =
          x.app s (pt 𝒜 ℬ) ≫ sgnHom (W.obj (pt 𝒜 ℬ)) q ≫ W.map (tmul 1 b)
        rw [h, Linear.comp_smul, ← Category.assoc, hs, Linear.smul_comp, smul_smul, sign_mul_self,
          one_smul, Category.assoc]
      rw [SuperNatTrans.total, Preadditive.comp_add, Preadditive.add_comp, key, key]

/-- A supernatural transformation `V ⇒ W`, as a superbimodule homomorphism
`ofFunctor V ⟶ ofFunctor W`. -/
def homOfNatTrans {V W : Superfunctor k (BimodCat 𝒜 ℬ) (SVec k)} (x : V ⟶ W) :
    ofFunctor V ⟶ ofFunctor W :=
  ⟨SuperNatTrans.total x (pt 𝒜 ℬ), isHom_total x⟩

theorem homOfNatTrans_val {V W : Superfunctor k (BimodCat 𝒜 ℬ) (SVec k)} (x : V ⟶ W) :
    (homOfNatTrans x).1 = x.app 0 (pt 𝒜 ℬ) + x.app 1 (pt 𝒜 ℬ) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem toFunctor_map_proj_comp_proj {M N : SuperBimodule 𝒜 ℬ} (f : M ⟶ N) (s t : ZMod 2)
    {X Y : BimodCat 𝒜 ℬ} (x : X ⟶ Y) :
    ((toFunctor M).map ((BoxProd.homObj k X Y).proj t x) : M.toSVec ⟶ M.toSVec) ≫
        (proj k s f.1 : M.toSVec ⟶ N.toSVec) =
      koszulSign s t • ((proj k s f.1 : M.toSVec ⟶ N.toSVec) ≫
        ((toFunctor N).map ((BoxProd.homObj k X Y).proj t x) : N.toSVec ⟶ N.toSVec)) := by
  induction x using BimodCat.induction_on with
  | zero => simp only [map_zero, Functor.map_zero, Limits.zero_comp, Limits.comp_zero, smul_zero]
  | add x x' hx hx' =>
    rw [map_add, Functor.map_add, Functor.map_add, Preadditive.add_comp, Preadditive.comp_add, hx,
      hx', smul_add]
  | tmul p q a b ha hb =>
    rw [SVec.proj_apply_of_mem_part _ (tmul_mem ha hb)]
    split_ifs with h
    · subst h
      have hf := (isHom_iff_of_mem (proj_mem s f.1)).1 (f.2.proj s)
      have hs : sgnHom M.toSVec q ≫ proj k s f.1 =
          sign k (s * q) • (proj k s f.1 ≫ sgnHom N.toSVec q) := by
        rw [comp_sgnHom_of_mem (proj_mem s f.1) q, smul_smul, sign_mul_self, one_smul]
      rw [toFunctor_map_tmul, toFunctor_map_tmul, sract_of_mem M hb, sract_of_mem N hb,
        koszulSign_smul (R := k)]
      simp only [Category.assoc]
      rw [hf.1 p a ha, Linear.comp_smul, Linear.comp_smul, ← Category.assoc (M.ract b), hf.2 b,
        Category.assoc, ← Category.assoc (sgnHom M.toSVec q), hs, Linear.smul_comp, smul_smul,
        ← sign_add, show p * s + s * q = s * (p + q) by ring]
      simp only [Category.assoc]
    · simp only [Functor.map_zero, Limits.zero_comp, Limits.comp_zero, smul_zero]

/-- A superbimodule homomorphism `M ⟶ N`, as a supernatural transformation
`toSuperfunctor M ⇒ toSuperfunctor N`: its components are the parity components of the
homomorphism. -/
def natTransOfHom {M N : SuperBimodule 𝒜 ℬ} (f : M ⟶ N) : toSuperfunctor M ⟶ toSuperfunctor N where
  app s _ := proj k s f.1
  app_mem s _ := proj_mem s f.1
  naturality s {X Y} t x hx := by
    have := toFunctor_map_proj_comp_proj f s t x
    rwa [(SVec.mem_part_iff _).1 hx] at this

theorem natTransOfHom_app {M N : SuperBimodule 𝒜 ℬ} (f : M ⟶ N) (s : ZMod 2) (X : BimodCat 𝒜 ℬ) :
    (natTransOfHom f).app s X = proj k s f.1 := rfl

set_option backward.isDefEq.respectTransparency false in
theorem homOfNatTrans_natTransOfHom {M N : SuperBimodule 𝒜 ℬ} (f : M ⟶ N) :
    (homOfNatTrans (natTransOfHom f)).1 = f.1 := by
  rw [homOfNatTrans_val, natTransOfHom_app, natTransOfHom_app, proj_add_proj]

theorem natTransOfHom_homOfNatTrans {V W : Superfunctor k (BimodCat 𝒜 ℬ) (SVec k)} (x : V ⟶ W)
    (s : ZMod 2) (X : BimodCat 𝒜 ℬ) :
    (natTransOfHom (homOfNatTrans x)).app s X = x.app s X := by
  rcases parity_eq_zero_or_one s with rfl | rfl
  · show proj k 0 (x.app 0 (pt 𝒜 ℬ) + x.app 1 (pt 𝒜 ℬ)) = x.app 0 (pt 𝒜 ℬ)
    rw [map_add, proj_of_mem (x.app_mem 0 _), proj_of_mem_ne (x.app_mem 1 _) (by decide), add_zero]
  · show proj k 1 (x.app 0 (pt 𝒜 ℬ) + x.app 1 (pt 𝒜 ℬ)) = x.app 1 (pt 𝒜 ℬ)
    rw [map_add, proj_of_mem (x.app_mem 1 _), proj_of_mem_ne (x.app_mem 0 _) (by decide), zero_add]

end Morphisms

/-! ## The isomorphism of supercategories `Hom(A ⊠ B^{sop}, SVec) ≅ A-SMod-B` -/

section Equiv

set_option backward.isDefEq.respectTransparency false in
/-- The functor `Hom(A ⊠ B^{sop}, SVec) → A-SMod-B`, `V ↦ V(⋆)`. -/
def evalFunctor : Superfunctor k (BimodCat 𝒜 ℬ) (SVec k) ⥤ SuperBimodule 𝒜 ℬ where
  obj := ofFunctor
  map := homOfNatTrans
  map_id V := hom_ext (by
    show (𝟙 V : V ⟶ V).app 0 (pt 𝒜 ℬ) + (𝟙 V : V ⟶ V).app 1 (pt 𝒜 ℬ) = 𝟙 _
    rw [Superfunctor.id_app_zero, Superfunctor.id_app_one, add_zero])
  map_comp x y := hom_ext (by
    rw [comp_val, homOfNatTrans_val, homOfNatTrans_val, homOfNatTrans_val,
      Superfunctor.comp_app_zero, Superfunctor.comp_app_one, Preadditive.add_comp,
      Preadditive.comp_add, Preadditive.comp_add]
    abel)

instance : (evalFunctor 𝒜 ℬ).Additive where
  map_add {_ _ x y} := hom_ext (by
    show (x + y).app 0 _ + (x + y).app 1 _ = (x.app 0 _ + x.app 1 _) + (y.app 0 _ + y.app 1 _)
    rw [Superfunctor.add_app, Superfunctor.add_app]; abel)

set_option backward.isDefEq.respectTransparency false in
instance : (evalFunctor 𝒜 ℬ).Linear k where
  map_smul x r := hom_ext (by
    show (r • x).app 0 _ + (r • x).app 1 _ = r • (x.app 0 _ + x.app 1 _)
    rw [Superfunctor.smul_app, Superfunctor.smul_app, smul_add])

instance : IsSuperfunctor k (evalFunctor 𝒜 ℬ) where
  map_mem {V W p x} hx := by
    rw [Superfunctor.mem_parity_iff] at hx
    refine mem_parity_iff.2 ?_
    show x.app 0 (pt 𝒜 ℬ) + x.app 1 (pt 𝒜 ℬ) ∈ parity (R := k) _ _ p
    rcases parity_eq_zero_or_one p with rfl | rfl
    · rw [show x.app 1 (pt 𝒜 ℬ) = 0 from congrFun hx _, add_zero]; exact x.app_mem 0 _
    · rw [show x.app 0 (pt 𝒜 ℬ) = 0 from congrFun hx _, zero_add]; exact x.app_mem 1 _

/-- **Brundan–Ellis, Remark 1.3.** The superfunctor `Hom(A ⊠ B^{sop}, SVec) → A-SMod-B`,
`V ↦ V(⋆)`, `x ↦ x_⋆ = x_{⋆,0} + x_{⋆,1}`. -/
def evalSuperfunctor :
    Superfunctor k (Superfunctor k (BimodCat 𝒜 ℬ) (SVec k)) (SuperBimodule 𝒜 ℬ) :=
  ⟨evalFunctor 𝒜 ℬ⟩

set_option backward.isDefEq.respectTransparency false in
variable {𝒜 ℬ} in
theorem natTransOfHom_comp_app {M N P : SuperBimodule 𝒜 ℬ} (f : M ⟶ N) (g : N ⟶ P) (s : ZMod 2)
    (X : BimodCat 𝒜 ℬ) :
    (natTransOfHom (f ≫ g)).app s X =
      (natTransOfHom f ≫ natTransOfHom g : toSuperfunctor M ⟶ toSuperfunctor P).app s X := by
  rw [Superfunctor.comp_app]
  simp only [natTransOfHom_app, comp_val]
  have h0 := proj_comp_of_mem_left s (proj_mem (R := k) 0 f.1) g.1
  have h1 := proj_comp_of_mem_left (s + 1) (proj_mem (R := k) 1 f.1) g.1
  rw [zero_add] at h0
  rw [show (1 : ZMod 2) + (s + 1) = s by rcases parity_eq_zero_or_one s with rfl | rfl <;> rfl]
    at h1
  rw [← h0, ← h1, ← (proj k s).map_add, ← Preadditive.add_comp, proj_add_proj]

/-- The functor `A-SMod-B → Hom(A ⊠ B^{sop}, SVec)`. -/
def bimoduleFunctor : SuperBimodule 𝒜 ℬ ⥤ Superfunctor k (BimodCat 𝒜 ℬ) (SVec k) where
  obj := toSuperfunctor
  map := natTransOfHom
  map_id M := Superfunctor.hom_ext_parity
    (fun X => by rw [natTransOfHom_app, id_val, proj_id, ite_eq_left rfl]; rfl)
    (fun X => by rw [natTransOfHom_app, id_val, proj_id, ite_eq_right (by decide)]; rfl)
  map_comp f g := Superfunctor.hom_ext fun s X => natTransOfHom_comp_app f g s X

theorem bimoduleFunctor_map {M N : SuperBimodule 𝒜 ℬ} (f : M ⟶ N) :
    (bimoduleFunctor 𝒜 ℬ).map f = natTransOfHom f := rfl

set_option backward.isDefEq.respectTransparency false in
instance : (bimoduleFunctor 𝒜 ℬ).Additive where
  map_add {_ _ f g} := Superfunctor.hom_ext fun s X => by
    rw [Superfunctor.add_app, bimoduleFunctor_map, bimoduleFunctor_map, bimoduleFunctor_map,
      natTransOfHom_app, natTransOfHom_app, natTransOfHom_app, add_val, map_add]

set_option backward.isDefEq.respectTransparency false in
instance : (bimoduleFunctor 𝒜 ℬ).Linear k where
  map_smul f r := Superfunctor.hom_ext fun s X => by
    rw [Superfunctor.smul_app, bimoduleFunctor_map, bimoduleFunctor_map, natTransOfHom_app,
      natTransOfHom_app, smul_val, map_smul]

instance : IsSuperfunctor k (bimoduleFunctor 𝒜 ℬ) where
  map_mem {M N p f} hf := by
    rw [Superfunctor.mem_parity_iff, bimoduleFunctor_map]
    funext X
    rw [natTransOfHom_app, proj_of_mem_ne (mem_parity_iff.1 hf) (zmod2_add_one_ne p).symm]
    rfl

/-- **Brundan–Ellis, Remark 1.3.** The superfunctor `A-SMod-B → Hom(A ⊠ B^{sop}, SVec)`,
`M ↦ (⋆ ↦ M, a ⊗ b ↦ (v ↦ (-1)^{|b||v|} a v b))`, `f ↦ (f₀, f₁)`. -/
def bimoduleSuperfunctor :
    Superfunctor k (SuperBimodule 𝒜 ℬ) (Superfunctor k (BimodCat 𝒜 ℬ) (SVec k)) :=
  ⟨bimoduleFunctor 𝒜 ℬ⟩

theorem evalSuperfunctor_obj (V : Superfunctor k (BimodCat 𝒜 ℬ) (SVec k)) :
    (evalSuperfunctor 𝒜 ℬ).obj V = ofFunctor V := rfl

theorem bimoduleSuperfunctor_obj (M : SuperBimodule 𝒜 ℬ) :
    Superfunctor.obj (bimoduleSuperfunctor 𝒜 ℬ) M = toSuperfunctor M := rfl

omit [GradedAlgebra 𝒜] [GradedAlgebra ℬ] in
theorem eqToHom_val {M N : SuperBimodule 𝒜 ℬ} (h : M = N) :
    (eqToHom h).1 = eqToHom (congrArg SuperBimodule.toSVec h) := by
  subst h; rfl

set_option backward.isDefEq.respectTransparency false in
/-- `A-SMod-B → Hom(A ⊠ B^{sop}, SVec) → A-SMod-B` is the identity. -/
theorem bimodule_comp_eval :
    (bimoduleSuperfunctor 𝒜 ℬ).comp (evalSuperfunctor 𝒜 ℬ) =
      Superfunctor.id k (SuperBimodule 𝒜 ℬ) := by
  refine Superfunctor.ext (CategoryTheory.Functor.ext
    (fun M => show ofFunctor (toSuperfunctor M) = M from ofFunctor_toSuperfunctor M)
    fun M N f => hom_ext ?_)
  rw [comp_val, comp_val, eqToHom_val, eqToHom_val]
  change (homOfNatTrans (natTransOfHom f)).1 = _
  rw [homOfNatTrans_natTransOfHom]
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

theorem eqToHom_app {V W : Superfunctor k (BimodCat 𝒜 ℬ) (SVec k)} (h : V = W) (s : ZMod 2)
    (X : BimodCat 𝒜 ℬ) :
    (eqToHom h).app s X =
      if s = 0 then
        eqToHom (congrArg (fun F : Superfunctor k (BimodCat 𝒜 ℬ) (SVec k) => F.obj X) h)
      else 0 := by
  subst h; rfl

set_option backward.isDefEq.respectTransparency false in
/-- `Hom(A ⊠ B^{sop}, SVec) → A-SMod-B → Hom(A ⊠ B^{sop}, SVec)` is the identity. -/
theorem eval_comp_bimodule :
    (evalSuperfunctor 𝒜 ℬ).comp (bimoduleSuperfunctor 𝒜 ℬ) =
      Superfunctor.id k (Superfunctor k (BimodCat 𝒜 ℬ) (SVec k)) := by
  refine Superfunctor.ext (CategoryTheory.Functor.ext
    (fun V => show toSuperfunctor (ofFunctor V) = V from toSuperfunctor_ofFunctor V)
    fun V W x => Superfunctor.hom_ext fun s X => ?_)
  change (natTransOfHom (homOfNatTrans x)).app s X = _
  rw [natTransOfHom_homOfNatTrans, Superfunctor.comp_app, Superfunctor.comp_app, eqToHom_app,
    eqToHom_app, eqToHom_app, eqToHom_app]
  rcases parity_eq_zero_or_one s with rfl | rfl
  · simp only [ite_true, ite_eq_right (show (1 : ZMod 2) ≠ 0 by decide), Limits.comp_zero, add_zero,
      zero_add, Limits.zero_comp]
    exact ((Category.id_comp _).trans (Category.comp_id _)).symm
  · simp only [ite_true, ite_eq_right (show (1 : ZMod 2) ≠ 0 by decide), Limits.comp_zero, zero_add,
      SuperNatTrans.zmod2_one_add_one, Limits.zero_comp, add_zero]
    exact ((Category.id_comp _).trans (Category.comp_id _)).symm

end Equiv

end SuperBimodule

end StringDiagrams

end
