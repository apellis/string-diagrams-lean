import StringDiagrams.Super.Superbimodule
import StringDiagrams.Super.SVecQuotient

/-!
# The balanced tensor product of superbimodules

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Example 1.5(i) and Section 2 (the 2-supercategory `𝔖𝔅𝔦𝔪`, after Definition 2.2): "the usual
tensor product of superbimodules over `A`".

For superalgebras `A`, `B`, `C` over the commutative ground ring `k`, an `(A, B)`-superbimodule
`M` and a `(B, C)`-superbimodule `N`, the balanced tensor product `M ⊗_B N` is the quotient of
the tensor product of superspaces `M ⊗_k N` (`SVec.tensorObj`) by the submodule spanned by the
balancing relations `(m b) ⊗ n - m ⊗ (b n)`. It is an `(A, C)`-superbimodule with
`a (m ⊗ n) = (a m) ⊗ n` and `(m ⊗ n) c = m ⊗ (n c)`: the action map
`A ⊗ (M ⊗_B N) ⊗ C → M ⊗_B N` is induced by `m_M ⊗ m_N`, so no sign appears
(`SuperBimodule.tensor`, `SuperBimodule.btmul`).

## Main definitions and results

* `SuperBimodule.tensorK M N`: the tensor product over `k` with the outer actions.
* `SuperBimodule.balanceRel M N`: the balancing relations (a graded sub-bimodule).
* `SuperBimodule.tensor M N`: the balanced tensor product; `btmul m n` is the class of
  `m ⊗ n`, with `btmul_ract_lact : btmul (m b) n = btmul m (b n)`, `lact_btmul`, `ract_btmul`.
* Universal property: `SuperBimodule.tensor.lift` for balanced bilinear maps, with
  `lift_btmul`; extensionality `tensor.hom_ext` and induction `tensor.induction_on`.
* Functoriality with the Koszul signs: `tensor.whiskerLeft M g` (`(1 ⊗ g)(m ⊗ n) =
  (-1)^{|g||m|} m ⊗ g(n)`, `whiskerLeft_btmul`) and `tensor.whiskerRight f N`
  (`(f ⊗ 1)(m ⊗ n) = f(m) ⊗ n`, `whiskerRight_btmul`), superbimodule homomorphisms, with the
  functoriality, linearity, parity and super interchange laws inherited from `SVec`
  (`tensor.whiskerLeft_comp`, `tensor.super_interchange`, …), so that
  `- ⊗_B - : A-SMod-B ⊠ B-SMod-C → A-SMod-C` is a superfunctor.
* The regular superbimodule `SuperBimodule.regular 𝒜`, the associator `tensor.assoc` and the
  unitors `tensor.leftUnitor`, `tensor.rightUnitor` (even isomorphisms of superbimodules), their
  naturality, the pentagon and triangle identities, in the generality of four superalgebras.

The monoidal supercategory `A-SMod-A` (Example 1.5(i)) and the 2-supercategory `𝔖𝔅𝔦𝔪` are
assembled from these in `StringDiagrams.Super.BimoduleMonoidal` and
`StringDiagrams.Super.SBim`.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory MonoidalCategory Supercategory TensorProduct

universe u v v' v'' v''' w

variable {k : Type u} [CommRing k]

namespace SVec

variable {V V' W W' : SVec k}

theorem hom_map_add (f : V ⟶ W) (x y : V) : f (x + y) = f x + f y := (toLinearMap f).map_add x y

theorem hom_map_sub (f : V ⟶ W) (x y : V) : f (x - y) = f x - f y := (toLinearMap f).map_sub x y

theorem hom_map_smul (f : V ⟶ W) (r : k) (x : V) : f (r • x) = r • f x := (toLinearMap f).map_smul r x

theorem hom_map_zero (f : V ⟶ W) : f 0 = 0 := (toLinearMap f).map_zero

theorem twist_whiskerLeft (p : ZMod 2) (V : SVec k) (g : W ⟶ W') :
    twist k p (whiskerLeft V g) = whiskerLeft V (twist k p g) := by
  rw [twist_apply, twist_apply, proj_eq_homProj, proj_eq_homProj, proj_eq_homProj, proj_eq_homProj,
    homProj_whiskerLeft, homProj_whiskerLeft, whiskerLeft_add, whiskerLeft_smul]

theorem twist_whiskerRight (p : ZMod 2) (f : V ⟶ V') (W : SVec k) :
    twist k p (whiskerRight f W) = whiskerRight (twist k p f) W := by
  rw [twist_apply, twist_apply, proj_eq_homProj, proj_eq_homProj, proj_eq_homProj, proj_eq_homProj,
    homProj_whiskerRight, homProj_whiskerRight, whiskerRight_add]
  congr 1
  exact (map_smul_left _ _ _).symm

end SVec

namespace SuperBimodule

/-! ## Parity components in a superalgebra -/

section AlgProj

variable {B : Type v} [Ring B] [Algebra k B] (ℬ : ZMod 2 → Submodule k B) [GradedAlgebra ℬ]

/-- The parity component `b ↦ b_p` of an element of a superalgebra. -/
def algProj (p : ZMod 2) : B →ₗ[k] B :=
  Supercategory.proj k p (C := SuperalgebraCat ℬ) (X := SuperalgebraCat.star ℬ)
    (Y := SuperalgebraCat.star ℬ)

theorem algProj_mem (p : ZMod 2) (b : B) : algProj ℬ p b ∈ ℬ p :=
  proj_mem (R := k) p (C := SuperalgebraCat ℬ) (X := SuperalgebraCat.star ℬ)
    (Y := SuperalgebraCat.star ℬ) b

theorem algProj_add_algProj (b : B) : algProj ℬ 0 b + algProj ℬ 1 b = b :=
  proj_add_proj (R := k) (C := SuperalgebraCat ℬ) (X := SuperalgebraCat.star ℬ)
    (Y := SuperalgebraCat.star ℬ) b

theorem algProj_of_mem {p : ZMod 2} {b : B} (hb : b ∈ ℬ p) : algProj ℬ p b = b :=
  proj_of_mem (R := k) (C := SuperalgebraCat ℬ) (X := SuperalgebraCat.star ℬ)
    (Y := SuperalgebraCat.star ℬ) hb

theorem algProj_of_mem_ne {p q : ZMod 2} {b : B} (hb : b ∈ ℬ q) (h : q ≠ p) : algProj ℬ p b = 0 :=
  proj_of_mem_ne (R := k) (C := SuperalgebraCat ℬ) (X := SuperalgebraCat.star ℬ)
    (Y := SuperalgebraCat.star ℬ) hb h

/-- Induction on the elements of a superalgebra via homogeneous elements. -/
theorem alg_induction_on {P : B → Prop} (b : B) (zero : P 0)
    (hom : ∀ (p : ZMod 2) (b : B), b ∈ ℬ p → P b) (add : ∀ b b', P b → P b' → P (b + b')) : P b :=
  Supercategory.induction_on (R := k) (C := SuperalgebraCat ℬ) (X := SuperalgebraCat.star ℬ)
    (Y := SuperalgebraCat.star ℬ) (P := P) b zero hom add

end AlgProj

variable {A : Type v} [Ring A] [Algebra k A] {B : Type v'} [Ring B] [Algebra k B]
  {C : Type v''} [Ring C] [Algebra k C] {D : Type v'''} [Ring D] [Algebra k D]
  {𝒜 : ZMod 2 → Submodule k A} {ℬ : ZMod 2 → Submodule k B} {𝒞 : ZMod 2 → Submodule k C}
  {𝒟 : ZMod 2 → Submodule k D}

/-! ## Quotient superbimodules -/

section Quotient

variable (V : SuperBimodule 𝒜 ℬ)

/-- A graded sub-bimodule of a superbimodule. -/
structure SubBimodule extends SVec.GradedSubmodule V.toSVec where
  lact_mem : ∀ a : A, ∀ v ∈ toSubmodule, V.lact a v ∈ toSubmodule
  ract_mem : ∀ b : B, ∀ v ∈ toSubmodule, V.ract b v ∈ toSubmodule

namespace SubBimodule

variable {V}

instance : SetLike (SubBimodule V) V.toSVec where
  coe U := U.toSubmodule
  coe_injective' U U' h := by
    cases U; cases U'
    congr
    exact SVec.GradedSubmodule.toSubmodule_injective (SetLike.coe_injective h)

theorem mem_toGradedSubmodule {U : SubBimodule V} {v : V.toSVec} :
    v ∈ U.toGradedSubmodule ↔ v ∈ U := Iff.rfl

theorem mem_toSubmodule {U : SubBimodule V} {v : V.toSVec} : v ∈ U.toSubmodule ↔ v ∈ U := Iff.rfl

end SubBimodule

variable (U : SubBimodule V)

/-- The quotient of a superbimodule by a graded sub-bimodule. -/
def quotient : SuperBimodule 𝒜 ℬ where
  toSVec := SVec.quot V.toSVec U.toGradedSubmodule
  lact :=
    { toFun := fun a => SVec.quotMap (V.lact a) (U.lact_mem a)
      map_add' := fun a a' => by rw [SVec.quotMap_congr (V.lact.map_add a a'), SVec.quotMap_add]
      map_smul' := fun r a => by
        rw [SVec.quotMap_congr (V.lact.map_smul r a), SVec.quotMap_smul]; rfl }
  ract :=
    { toFun := fun b => SVec.quotMap (V.ract b) (U.ract_mem b)
      map_add' := fun b b' => by rw [SVec.quotMap_congr (V.ract.map_add b b'), SVec.quotMap_add]
      map_smul' := fun r b => by
        rw [SVec.quotMap_congr (V.ract.map_smul r b), SVec.quotMap_smul]; rfl }
  lact_one := by
    change SVec.quotMap (V.lact 1) (U.lact_mem 1) = _
    rw [SVec.quotMap_congr V.lact_one, SVec.quotMap_id]
  lact_mul a a' := by
    change SVec.quotMap (V.lact (a * a')) (U.lact_mem _) =
      SVec.quotMap (V.lact a') (U.lact_mem a') ≫ SVec.quotMap (V.lact a) (U.lact_mem a)
    rw [SVec.quotMap_congr (V.lact_mul a a'), SVec.quotMap_comp]
  ract_one := by
    change SVec.quotMap (V.ract 1) (U.ract_mem 1) = _
    rw [SVec.quotMap_congr V.ract_one, SVec.quotMap_id]
  ract_mul b b' := by
    change SVec.quotMap (V.ract (b * b')) (U.ract_mem _) =
      SVec.quotMap (V.ract b) (U.ract_mem b) ≫ SVec.quotMap (V.ract b') (U.ract_mem b')
    rw [SVec.quotMap_congr (V.ract_mul b b'), SVec.quotMap_comp]
  lact_ract a b := by
    change SVec.quotMap (V.lact a) (U.lact_mem a) ≫ SVec.quotMap (V.ract b) (U.ract_mem b) =
      SVec.quotMap (V.ract b) (U.ract_mem b) ≫ SVec.quotMap (V.lact a) (U.lact_mem a)
    rw [← SVec.quotMap_comp, ← SVec.quotMap_comp]
    exact SVec.quotMap_congr (V.lact_ract a b) _
  lact_mem p a ha := SVec.quotMap_mem (V.lact_mem p a ha) (U.lact_mem a)
  ract_mem p b hb := SVec.quotMap_mem (V.ract_mem p b hb) (U.ract_mem b)

theorem quotient_toSVec : (quotient V U).toSVec = SVec.quot V.toSVec U.toGradedSubmodule := rfl

theorem quotient_lact (a : A) : (quotient V U).lact a = SVec.quotMap (V.lact a) (U.lact_mem a) := rfl

theorem quotient_ract (b : B) : (quotient V U).ract b = SVec.quotMap (V.ract b) (U.ract_mem b) := rfl

theorem isHom_quotMk : IsHom V (quotient V U) (SVec.quotMk V.toSVec U.toGradedSubmodule) := by
  refine ⟨fun p a _ => ?_, fun b => rfl⟩
  change V.lact a ≫ SVec.quotMk V.toSVec U.toGradedSubmodule =
    twist k p (SVec.quotMk V.toSVec U.toGradedSubmodule) ≫ SVec.quotMap (V.lact a) (U.lact_mem a)
  rw [twist_of_mem p (SVec.quotMk_mem V.toSVec U.toGradedSubmodule), mul_zero, sign_zero, one_smul]
  rfl

/-- The quotient map, as a superbimodule homomorphism. -/
def quotientMk : V ⟶ quotient V U := ⟨SVec.quotMk V.toSVec U.toGradedSubmodule, isHom_quotMk V U⟩

variable {V U} {W : SuperBimodule 𝒜 ℬ} {U' : SubBimodule W}

theorem isHom_quotMap {f : V.toSVec ⟶ W.toSVec} (hf : IsHom V W f) (hfU : ∀ v ∈ U, f v ∈ U') :
    IsHom (quotient V U) (quotient W U') (SVec.quotMap f hfU) := by
  refine ⟨fun p a ha => ?_, fun b => ?_⟩
  · change SVec.quotMap (V.lact a) (U.lact_mem a) ≫ SVec.quotMap f hfU =
      twist k p (SVec.quotMap f hfU) ≫ SVec.quotMap (W.lact a) (U'.lact_mem a)
    rw [← SVec.quotMap_comp, SVec.twist_quotMap, ← SVec.quotMap_comp]
    exact SVec.quotMap_congr (hf.1 p a ha) _
  · change SVec.quotMap (V.ract b) (U.ract_mem b) ≫ SVec.quotMap f hfU =
      SVec.quotMap f hfU ≫ SVec.quotMap (W.ract b) (U'.ract_mem b)
    rw [← SVec.quotMap_comp, ← SVec.quotMap_comp]
    exact SVec.quotMap_congr (hf.2 b) _

/-- A superbimodule homomorphism carrying `U` into `U'` descends to the quotients. -/
def descend (f : V ⟶ W) (hf : ∀ v ∈ U, f.1 v ∈ U') : quotient V U ⟶ quotient W U' :=
  ⟨SVec.quotMap f.1 hf, isHom_quotMap f.2 hf⟩

@[simp] theorem descend_val (f : V ⟶ W) (hf : ∀ v ∈ U, f.1 v ∈ U') :
    (descend f hf).1 = SVec.quotMap f.1 hf := rfl

end Quotient

/-- `IsHom` for even maps: it suffices that the map commutes with the actions. -/
theorem isHom_of_even {V W : SuperBimodule 𝒜 ℬ} {f : V.toSVec ⟶ W.toSVec}
    (hf : f ∈ SVec.parityHom V.toSVec W.toSVec 0) (hl : ∀ a : A, V.lact a ≫ f = f ≫ W.lact a)
    (hr : ∀ b : B, V.ract b ≫ f = f ≫ W.ract b) : IsHom V W f :=
  (isHom_iff_of_mem hf).2 ⟨fun p a _ => by rw [hl, mul_zero, sign_zero, one_smul], hr⟩

/-! ## The tensor product over `k` with the outer actions -/

section TensorK

variable (M : SuperBimodule 𝒜 ℬ) (N : SuperBimodule ℬ 𝒞)

/-- The left action of `A` on `M ⊗_k N`, `a (m ⊗ n) = (a m) ⊗ n`. -/
def lactK : A →ₗ[k] (SVec.tensorObj M.toSVec N.toSVec ⟶ SVec.tensorObj M.toSVec N.toSVec) where
  toFun a := SVec.whiskerRight (M.lact a) N.toSVec
  map_add' a a' := by rw [map_add, SVec.whiskerRight_add]
  map_smul' r a := by rw [map_smul]; exact map_smul_left r _ _

/-- The right action of `C` on `M ⊗_k N`, `(m ⊗ n) c = m ⊗ (n c)`. -/
def ractK : C →ₗ[k] (SVec.tensorObj M.toSVec N.toSVec ⟶ SVec.tensorObj M.toSVec N.toSVec) where
  toFun c := SVec.ofHom (map LinearMap.id (SVec.toLinearMap (N.ract c)))
  map_add' c c' := by
    rw [map_add, SVec.toLinearMap_add]; exact map_add_right _ _ _
  map_smul' r c := by
    rw [map_smul, SVec.toLinearMap_smul]; exact map_smul_right r _ _

theorem lactK_apply (a : A) : lactK M N a = SVec.whiskerRight (M.lact a) N.toSVec := rfl

theorem ractK_apply (c : C) :
    ractK M N c = SVec.ofHom (map LinearMap.id (SVec.toLinearMap (N.ract c))) := rfl

theorem lactK_tmul (a : A) (m : M.toSVec) (n : N.toSVec) :
    lactK M N a (m ⊗ₜ n) = M.lact a m ⊗ₜ n := rfl

theorem ractK_tmul (c : C) (m : M.toSVec) (n : N.toSVec) :
    ractK M N c (m ⊗ₜ n) = m ⊗ₜ N.ract c n := rfl

/-- The tensor product over `k` of an `(A, B)`-superbimodule and a `(B, C)`-superbimodule, an
`(A, C)`-superbimodule with the outer actions. -/
def tensorK : SuperBimodule 𝒜 𝒞 where
  toSVec := SVec.tensorObj M.toSVec N.toSVec
  lact := lactK M N
  ract := ractK M N
  lact_one := by rw [lactK_apply, M.lact_one, SVec.whiskerRight_id]
  lact_mul a a' := by rw [lactK_apply, lactK_apply, lactK_apply, M.lact_mul, SVec.comp_whiskerRight]
  ract_one := by
    rw [ractK_apply, N.ract_one, SVec.toLinearMap_id]; exact TensorProduct.map_id
  ract_mul c c' := by
    rw [ractK_apply, ractK_apply, ractK_apply, N.ract_mul, SVec.toLinearMap_comp]
    exact TensorProduct.ext' fun _ _ => rfl
  lact_ract a c := TensorProduct.ext' fun _ _ => rfl
  lact_mem p a ha := SVec.whiskerRight_mem (M.lact_mem p a ha) N.toSVec
  ract_mem p c hc := by
    simpa using SVec.map_mem (SVec.instSupercategory.id_mem M.toSVec) (N.ract_mem p c hc)

theorem tensorK_lact_tmul (a : A) (m : M.toSVec) (n : N.toSVec) :
    (tensorK M N).lact a (m ⊗ₜ n) = M.lact a m ⊗ₜ n := rfl

theorem tensorK_ract_tmul (c : C) (m : M.toSVec) (n : N.toSVec) :
    (tensorK M N).ract c (m ⊗ₜ n) = m ⊗ₜ N.ract c n := rfl

/-! ## The balancing relations -/

/-- The balancing element `(m b) ⊗ n - m ⊗ (b n)`. -/
def balance (m : M.toSVec) (b : B) (n : N.toSVec) : SVec.tensorObj M.toSVec N.toSVec :=
  M.ract b m ⊗ₜ n - m ⊗ₜ N.lact b n

theorem balance_add_left (m m' : M.toSVec) (b : B) (n : N.toSVec) :
    balance M N (m + m') b n = balance M N m b n + balance M N m' b n := by
  simp only [balance, map_add, add_tmul]; abel

theorem balance_add_middle (m : M.toSVec) (b b' : B) (n : N.toSVec) :
    balance M N m (b + b') n = balance M N m b n + balance M N m b' n := by
  simp only [balance, map_add, add_tmul, tmul_add, SVec.add_apply]; abel

theorem balance_add_right (m : M.toSVec) (b : B) (n n' : N.toSVec) :
    balance M N m b (n + n') = balance M N m b n + balance M N m b n' := by
  simp only [balance, map_add, tmul_add]; abel

theorem balance_mem_part {p q r : ZMod 2} {m : M.toSVec} {b : B} {n : N.toSVec}
    (hm : m ∈ M.toSVec.part p) (hb : b ∈ ℬ q) (hn : n ∈ N.toSVec.part r) :
    balance M N m b n ∈ (SVec.tensorObj M.toSVec N.toSVec).part (p + q + r) := by
  refine Submodule.sub_mem _ (SVec.tmul_mem_part (SVec.apply_mem_part (M.ract_mem q b hb) hm) hn)
    ?_
  have := SVec.tmul_mem_part hm (SVec.apply_mem_part (N.lact_mem q b hb) hn)
  rwa [← add_assoc, add_right_comm] at this

/-- The submodule of `M ⊗_k N` spanned by the balancing elements `(m b) ⊗ n - m ⊗ (b n)` with
`m`, `b`, `n` homogeneous (it contains all balancing elements, `balance_mem`). -/
def balanceRel : Submodule k (SVec.tensorObj M.toSVec N.toSVec) :=
  Submodule.span k {x | ∃ (p q r : ZMod 2) (m : M.toSVec) (b : B) (n : N.toSVec),
    m ∈ M.toSVec.part p ∧ b ∈ ℬ q ∧ n ∈ N.toSVec.part r ∧ x = balance M N m b n}

theorem balance_mem_balanceRel_of_mem {p q r : ZMod 2} {m : M.toSVec} {b : B} {n : N.toSVec}
    (hm : m ∈ M.toSVec.part p) (hb : b ∈ ℬ q) (hn : n ∈ N.toSVec.part r) :
    balance M N m b n ∈ balanceRel M N :=
  Submodule.subset_span ⟨p, q, r, m, b, n, hm, hb, hn, rfl⟩

/-- Induction on the balancing relations: a submodule containing the homogeneous balancing
elements contains `balanceRel`. -/
theorem balanceRel_le {S : Submodule k (SVec.tensorObj M.toSVec N.toSVec)}
    (h : ∀ (p q r : ZMod 2) (m : M.toSVec) (b : B) (n : N.toSVec), m ∈ M.toSVec.part p → b ∈ ℬ q →
      n ∈ N.toSVec.part r → balance M N m b n ∈ S) : balanceRel M N ≤ S := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨p, q, r, m, b, n, hm, hb, hn, rfl⟩
  exact h p q r m b n hm hb hn

theorem balanceRel_odd : ∀ x ∈ balanceRel M N, (SVec.tensorObj M.toSVec N.toSVec).odd x ∈ balanceRel M N := by
  intro x hx
  refine balanceRel_le M N (S := (balanceRel M N).comap (SVec.tensorObj M.toSVec N.toSVec).odd)
    (fun p q r m b n hm hb hn => ?_) hx
  rw [Submodule.mem_comap, ← SVec.proj_one, SVec.proj_apply_of_mem_part _ (balance_mem_part M N hm hb hn)]
  split_ifs
  · exact balance_mem_balanceRel_of_mem M N hm hb hn
  · exact Submodule.zero_mem _

variable [GradedAlgebra ℬ]

/-- Every balancing element lies in `balanceRel`. -/
theorem balance_mem (m : M.toSVec) (b : B) (n : N.toSVec) : balance M N m b n ∈ balanceRel M N := by
  rw [← SVec.proj_apply_add M.toSVec m, ← algProj_add_algProj ℬ b, ← SVec.proj_apply_add N.toSVec n,
    balance_add_left, balance_add_middle, balance_add_middle, balance_add_right,
    balance_add_right, balance_add_right, balance_add_right]
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_)
    (Submodule.add_mem _ ?_ ?_)) (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_)
    (Submodule.add_mem _ ?_ ?_)) <;>
  exact balance_mem_balanceRel_of_mem M N (SVec.proj_mem_part _ _ _) (algProj_mem ℬ _ _)
    (SVec.proj_mem_part _ _ _)

theorem balanceRel_lact (a : A) : ∀ x ∈ balanceRel M N, (tensorK M N).lact a x ∈ balanceRel M N := by
  intro x hx
  refine balanceRel_le M N (S := (balanceRel M N).comap (SVec.toLinearMap ((tensorK M N).lact a)))
    (fun p q r m b n hm hb hn => ?_) hx
  change (tensorK M N).lact a (balance M N m b n) ∈ balanceRel M N
  have : (tensorK M N).lact a (balance M N m b n) = balance M N (M.lact a m) b n := by
    simp only [balance, map_sub, tensorK_lact_tmul]
    rw [← SVec.comp_apply, ← M.lact_ract, SVec.comp_apply]
  rw [this]
  exact balance_mem M N _ b n

theorem balanceRel_ract (c : C) : ∀ x ∈ balanceRel M N, (tensorK M N).ract c x ∈ balanceRel M N := by
  intro x hx
  refine balanceRel_le M N (S := (balanceRel M N).comap (SVec.toLinearMap ((tensorK M N).ract c)))
    (fun p q r m b n hm hb hn => ?_) hx
  change (tensorK M N).ract c (balance M N m b n) ∈ balanceRel M N
  have : (tensorK M N).ract c (balance M N m b n) = balance M N m b (N.ract c n) := by
    simp only [balance, map_sub, tensorK_ract_tmul]
    rw [← SVec.comp_apply, N.lact_ract, SVec.comp_apply]
  rw [this]
  exact balance_mem M N m b _

end TensorK

/-! ## The balanced tensor product -/

section Tensor

variable [GradedAlgebra ℬ] (M : SuperBimodule 𝒜 ℬ) (N : SuperBimodule ℬ 𝒞)

/-- The balancing relations, as a graded sub-bimodule of `M ⊗_k N`. -/
def balanceSub : SubBimodule (tensorK M N) where
  toSubmodule := balanceRel M N
  odd_mem := balanceRel_odd M N
  lact_mem := balanceRel_lact M N
  ract_mem := balanceRel_ract M N

theorem mem_balanceSub {x : SVec.tensorObj M.toSVec N.toSVec} :
    x ∈ balanceSub M N ↔ x ∈ balanceRel M N := Iff.rfl

/-- **Brundan–Ellis, Example 1.5(i) and Section 2.** The balanced tensor product `M ⊗_B N` of
an `(A, B)`-superbimodule and a `(B, C)`-superbimodule: the quotient of `M ⊗_k N` by the
balancing relations `(m b) ⊗ n = m ⊗ (b n)`, an `(A, C)`-superbimodule with the outer actions. -/
def tensor : SuperBimodule 𝒜 𝒞 := quotient (tensorK M N) (balanceSub M N)

/-- The class `m ⊗ n` in `M ⊗_B N`. -/
def btmul (m : M.toSVec) (n : N.toSVec) : (tensor M N).toSVec :=
  SVec.quotMkFun _ (balanceSub M N).toGradedSubmodule (m ⊗ₜ n)

/-- The class of an element of `M ⊗_k N` in `M ⊗_B N`. -/
def tensorMk (x : SVec.tensorObj M.toSVec N.toSVec) : (tensor M N).toSVec :=
  SVec.quotMkFun _ (balanceSub M N).toGradedSubmodule x

theorem tensorMk_tmul (m : M.toSVec) (n : N.toSVec) : tensorMk M N (m ⊗ₜ n) = btmul M N m n := rfl

/-- The quotient map `M ⊗_k N → M ⊗_B N`, as a morphism of `SVec k`. -/
def tensorMkHom : SVec.tensorObj M.toSVec N.toSVec ⟶ (tensor M N).toSVec :=
  SVec.quotMk _ (balanceSub M N).toGradedSubmodule

theorem tensorMkHom_apply (x : SVec.tensorObj M.toSVec N.toSVec) :
    tensorMkHom M N x = tensorMk M N x := rfl

theorem tensorMkHom_mem : tensorMkHom M N ∈ SVec.parityHom _ (tensor M N).toSVec 0 :=
  SVec.quotMk_mem _ _

theorem tensorMk_add (x y : SVec.tensorObj M.toSVec N.toSVec) :
    tensorMk M N (x + y) = tensorMk M N x + tensorMk M N y := rfl

theorem tensorMk_smul (r : k) (x : SVec.tensorObj M.toSVec N.toSVec) :
    tensorMk M N (r • x) = r • tensorMk M N x := rfl

theorem tensorMk_zsmul (n : ℤ) (x : SVec.tensorObj M.toSVec N.toSVec) :
    tensorMk M N (n • x) = n • tensorMk M N x := rfl

theorem tensorMk_zero : tensorMk M N 0 = 0 := rfl

theorem tensorMk_surjective : Function.Surjective (tensorMk M N) :=
  SVec.quotMkFun_surjective _ _

theorem tensorMk_eq_tensorMk {x y : SVec.tensorObj M.toSVec N.toSVec} :
    tensorMk M N x = tensorMk M N y ↔ x - y ∈ balanceRel M N :=
  SVec.quotMkFun_eq_quotMkFun _ _

theorem btmul_add_left (m m' : M.toSVec) (n : N.toSVec) :
    btmul M N (m + m') n = btmul M N m n + btmul M N m' n := by
  rw [← tensorMk_tmul, add_tmul, tensorMk_add]; rfl

theorem btmul_add_right (m : M.toSVec) (n n' : N.toSVec) :
    btmul M N m (n + n') = btmul M N m n + btmul M N m n' := by
  rw [← tensorMk_tmul, tmul_add, tensorMk_add]; rfl

theorem btmul_smul_left (r : k) (m : M.toSVec) (n : N.toSVec) :
    btmul M N (r • m) n = r • btmul M N m n := by
  rw [← tensorMk_tmul, ← smul_tmul', tensorMk_smul]; rfl

theorem btmul_smul_right (r : k) (m : M.toSVec) (n : N.toSVec) :
    btmul M N m (r • n) = r • btmul M N m n := by
  rw [← tensorMk_tmul, tmul_smul, tensorMk_smul]; rfl

theorem btmul_zsmul_left (z : ℤ) (m : M.toSVec) (n : N.toSVec) :
    btmul M N (z • m) n = z • btmul M N m n := by
  rw [← tensorMk_tmul, ← smul_tmul', tensorMk_zsmul]; rfl

theorem btmul_zero_left (n : N.toSVec) : btmul M N 0 n = 0 := by
  rw [← tensorMk_tmul, zero_tmul, tensorMk_zero]

theorem btmul_zero_right (m : M.toSVec) : btmul M N m 0 = 0 := by
  rw [← tensorMk_tmul, tmul_zero, tensorMk_zero]

/-- The balancing relation `(m b) ⊗ n = m ⊗ (b n)` in `M ⊗_B N`. -/
theorem btmul_ract_lact (m : M.toSVec) (b : B) (n : N.toSVec) :
    btmul M N (M.ract b m) n = btmul M N m (N.lact b n) := by
  rw [← tensorMk_tmul, ← tensorMk_tmul, tensorMk_eq_tensorMk]
  exact balance_mem M N m b n

theorem lact_tensorMk (a : A) (x : SVec.tensorObj M.toSVec N.toSVec) :
    (tensor M N).lact a (tensorMk M N x) = tensorMk M N ((tensorK M N).lact a x) := rfl

theorem ract_tensorMk (c : C) (x : SVec.tensorObj M.toSVec N.toSVec) :
    (tensor M N).ract c (tensorMk M N x) = tensorMk M N ((tensorK M N).ract c x) := rfl

/-- `a (m ⊗ n) = (a m) ⊗ n`. -/
theorem lact_btmul (a : A) (m : M.toSVec) (n : N.toSVec) :
    (tensor M N).lact a (btmul M N m n) = btmul M N (M.lact a m) n := rfl

/-- `(m ⊗ n) c = m ⊗ (n c)`. -/
theorem ract_btmul (c : C) (m : M.toSVec) (n : N.toSVec) :
    (tensor M N).ract c (btmul M N m n) = btmul M N m (N.ract c n) := rfl

theorem tensorMk_mem_part {p : ZMod 2} {x : SVec.tensorObj M.toSVec N.toSVec}
    (hx : x ∈ (SVec.tensorObj M.toSVec N.toSVec).part p) : tensorMk M N x ∈ (tensor M N).toSVec.part p :=
  SVec.quotMkFun_mem_part _ _ hx

/-- `m ⊗ n` has parity `|m| + |n|`. -/
theorem btmul_mem_part {p q : ZMod 2} {m : M.toSVec} {n : N.toSVec} (hm : m ∈ M.toSVec.part p)
    (hn : n ∈ N.toSVec.part q) : btmul M N m n ∈ (tensor M N).toSVec.part (p + q) :=
  tensorMk_mem_part M N (SVec.tmul_mem_part hm hn)

theorem proj_tensorMk (p : ZMod 2) (x : SVec.tensorObj M.toSVec N.toSVec) :
    (tensor M N).toSVec.proj p (tensorMk M N x) =
      tensorMk M N ((SVec.tensorObj M.toSVec N.toSVec).proj p x) :=
  SVec.quot_proj_mk _ _ p x

variable {M N}

/-- Induction on `M ⊗_B N`: every element is a sum of classes `m ⊗ n`. -/
theorem tensor_induction_on {P : (tensor M N).toSVec → Prop} (x : (tensor M N).toSVec) (zero : P 0)
    (btmul : ∀ m n, P (btmul M N m n)) (add : ∀ x y, P x → P y → P (x + y)) : P x := by
  induction x using SVec.quot_induction_on with
  | h v =>
    induction v using TensorProduct.induction_on with
    | zero => exact zero
    | tmul m n => exact btmul m n
    | add x y hx hy => exact add _ _ hx hy

/-- Induction on `M ⊗_B N` with homogeneous generators. -/
theorem tensor_induction_on_homogeneous {P : (tensor M N).toSVec → Prop} (x : (tensor M N).toSVec)
    (zero : P 0)
    (btmul : ∀ (p q : ZMod 2) (m : M.toSVec) (n : N.toSVec), m ∈ M.toSVec.part p →
      n ∈ N.toSVec.part q → P (btmul M N m n))
    (add : ∀ x y, P x → P y → P (x + y)) : P x := by
  refine tensor_induction_on x zero (fun m n => ?_) add
  rw [← SVec.proj_apply_add M.toSVec m, ← SVec.proj_apply_add N.toSVec n, btmul_add_left,
    btmul_add_right, btmul_add_right]
  exact add _ _ (add _ _ (btmul 0 0 _ _ (SVec.proj_mem_part _ _ _) (SVec.proj_mem_part _ _ _))
      (btmul 0 1 _ _ (SVec.proj_mem_part _ _ _) (SVec.proj_mem_part _ _ _)))
    (add _ _ (btmul 1 0 _ _ (SVec.proj_mem_part _ _ _) (SVec.proj_mem_part _ _ _))
      (btmul 1 1 _ _ (SVec.proj_mem_part _ _ _) (SVec.proj_mem_part _ _ _)))

variable (M N) in
/-- Linear maps out of `M ⊗_B N` are determined by their values on the classes `m ⊗ n`. -/
theorem tensor_hom_ext {W : SVec k} {f g : (tensor M N).toSVec ⟶ W}
    (h : ∀ m n, f (btmul M N m n) = g (btmul M N m n)) : f = g :=
  SVec.hom_ext fun x => tensor_induction_on (P := fun x => f x = g x) x (by simp) h
    (fun x y hx hy => by dsimp only at hx hy ⊢; rw [map_add, map_add, hx, hy])

variable (M N) in
/-- Linear maps out of `M ⊗_B N` are determined by their values on the classes `m ⊗ n` with `m`,
`n` homogeneous. -/
theorem tensor_hom_ext_homogeneous {W : SVec k} {f g : (tensor M N).toSVec ⟶ W}
    (h : ∀ (p q : ZMod 2) (m : M.toSVec) (n : N.toSVec), m ∈ M.toSVec.part p →
      n ∈ N.toSVec.part q → f (btmul M N m n) = g (btmul M N m n)) : f = g :=
  SVec.hom_ext fun x => tensor_induction_on_homogeneous (P := fun x => f x = g x) x (by simp) h
    (fun x y hx hy => by dsimp only at hx hy ⊢; rw [map_add, map_add, hx, hy])

variable (M N) in
/-- A linear map out of `M ⊗_B N` whose values on homogeneous classes `m ⊗ n` have parity
`|m| + |n| + s` has parity `s`. -/
theorem tensor_mem_parity_of_btmul {W : SVec k} {f : (tensor M N).toSVec ⟶ W} {s : ZMod 2}
    (h : ∀ (p q : ZMod 2) (m : M.toSVec) (n : N.toSVec), m ∈ M.toSVec.part p →
      n ∈ N.toSVec.part q → f (btmul M N m n) ∈ W.part (p + q + s)) :
    f ∈ SVec.parityHom (tensor M N).toSVec W s := by
  intro q
  refine tensor_hom_ext_homogeneous M N fun p r m n hm hn => ?_
  change f ((tensor M N).toSVec.proj q (btmul M N m n)) = W.proj (q + s) (f (btmul M N m n))
  rw [SVec.proj_apply_of_mem_part _ (btmul_mem_part M N hm hn),
    SVec.proj_apply_of_mem_part _ (h p r m n hm hn)]
  by_cases hq : q = p + r
  · rw [if_pos hq, if_pos (by rw [hq])]
  · rw [if_neg hq, if_neg (fun e => hq (add_right_cancel e)), map_zero]

/-! ### The universal property -/

section Lift

variable {W : Type*} [AddCommGroup W] [Module k W] (f : M.toSVec →ₗ[k] N.toSVec →ₗ[k] W)
  (hf : ∀ (m : M.toSVec) (b : B) (n : N.toSVec), f (M.ract b m) n = f m (N.lact b n))

/-- The universal property of `M ⊗_B N`: a balanced bilinear map `f` (`f (m b) n = f m (b n)`)
induces a linear map `M ⊗_B N → W`. -/
def tensorLift : (tensor M N).toSVec →ₗ[k] W :=
  (balanceRel M N).liftQ (TensorProduct.lift f) (balanceRel_le M N fun p q r m b n _ _ _ => by
    rw [LinearMap.mem_ker, balance, map_sub, lift.tmul, lift.tmul, hf, sub_self])

@[simp] theorem tensorLift_btmul (m : M.toSVec) (n : N.toSVec) :
    tensorLift f hf (btmul M N m n) = f m n :=
  lift.tmul m n

theorem tensorLift_tensorMk (x : SVec.tensorObj M.toSVec N.toSVec) :
    tensorLift f hf (tensorMk M N x) = TensorProduct.lift f x := rfl

end Lift

end Tensor


/-! ## Functoriality: the whiskerings `f ⊗ 1` and `1 ⊗ g` -/

section WhiskerRight

variable [GradedAlgebra ℬ] {M M' : SuperBimodule 𝒜 ℬ} (f : M ⟶ M') (N : SuperBimodule ℬ 𝒞)

omit [GradedAlgebra ℬ] in
theorem whiskerRight_balance (m : M.toSVec) (b : B) (n : N.toSVec) :
    SVec.whiskerRight f.1 N.toSVec (balance M N m b n) = balance M' N (f.1 m) b n := by
  have h : f.1 (M.ract b m) = M'.ract b (f.1 m) :=
    congrArg (fun φ : M.toSVec ⟶ M'.toSVec => φ m) (f.2.2 b)
  rw [balance, balance, SVec.hom_map_sub, SVec.whiskerRight_tmul, SVec.whiskerRight_tmul, h]

theorem whiskerRight_mem_balanceSub :
    ∀ x ∈ balanceSub M N, SVec.whiskerRight f.1 N.toSVec x ∈ balanceSub M' N := by
  intro x hx
  refine balanceRel_le M N
    (S := (balanceRel M' N).comap (SVec.toLinearMap (SVec.whiskerRight f.1 N.toSVec)))
    (fun p q r m b n _ _ _ => ?_) hx
  change SVec.whiskerRight f.1 N.toSVec (balance M N m b n) ∈ balanceRel M' N
  rw [whiskerRight_balance]
  exact balance_mem M' N _ b n

omit [GradedAlgebra ℬ] in
theorem isHom_whiskerRight :
    IsHom (tensorK M N) (tensorK M' N) (SVec.whiskerRight f.1 N.toSVec) := by
  refine ⟨fun p a ha => ?_, fun c => ?_⟩
  · change SVec.whiskerRight (M.lact a) N.toSVec ≫ SVec.whiskerRight f.1 N.toSVec =
      twist k p (SVec.whiskerRight f.1 N.toSVec) ≫ SVec.whiskerRight (M'.lact a) N.toSVec
    rw [← SVec.comp_whiskerRight, f.2.1 p a ha, SVec.comp_whiskerRight, SVec.twist_whiskerRight]
  · exact TensorProduct.ext' fun _ _ => rfl

/-- `f ⊗ 1_N : M ⊗_B N → M' ⊗_B N`, `(f ⊗ 1)(m ⊗ n) = f(m) ⊗ n`. -/
def whiskerRight : tensor M N ⟶ tensor M' N :=
  descend ⟨SVec.whiskerRight f.1 N.toSVec, isHom_whiskerRight f N⟩ (whiskerRight_mem_balanceSub f N)

theorem whiskerRight_tensorMk (x : SVec.tensorObj M.toSVec N.toSVec) :
    (whiskerRight f N).1 (tensorMk M N x) = tensorMk M' N (SVec.whiskerRight f.1 N.toSVec x) := rfl

/-- `(f ⊗ 1)(m ⊗ n) = f(m) ⊗ n`. -/
theorem whiskerRight_btmul (m : M.toSVec) (n : N.toSVec) :
    (whiskerRight f N).1 (btmul M N m n) = btmul M' N (f.1 m) n := rfl

variable (M) in
theorem id_whiskerRight : whiskerRight (𝟙 M) N = 𝟙 (tensor M N) :=
  hom_ext (tensor_hom_ext M N fun _ _ => rfl)

theorem comp_whiskerRight {M'' : SuperBimodule 𝒜 ℬ} (f' : M' ⟶ M'') :
    whiskerRight (f ≫ f') N = whiskerRight f N ≫ whiskerRight f' N :=
  hom_ext (tensor_hom_ext M N fun _ _ => rfl)

theorem add_whiskerRight (f' : M ⟶ M') :
    whiskerRight (f + f') N = whiskerRight f N + whiskerRight f' N :=
  hom_ext (tensor_hom_ext M N fun m n => by
    simp only [whiskerRight_btmul, add_val, SVec.add_apply, btmul_add_left])

theorem smul_whiskerRight (r : k) : whiskerRight (r • f) N = r • whiskerRight f N :=
  hom_ext (tensor_hom_ext M N fun m n => by
    simp only [whiskerRight_btmul, smul_val, SVec.smul_apply, btmul_smul_left])

end WhiskerRight

section WhiskerLeft

variable [GradedAlgebra ℬ] [GradedAlgebra 𝒞] (M : SuperBimodule 𝒜 ℬ) {N N' : SuperBimodule ℬ 𝒞}

omit [GradedAlgebra ℬ] [GradedAlgebra 𝒞] in
theorem whiskerLeft_balance_of_mem {q : ZMod 2} {g : N.toSVec ⟶ N'.toSVec} (hg : IsHom N N' g)
    (hgq : g ∈ SVec.parityHom N.toSVec N'.toSVec q) {p : ZMod 2} {m : M.toSVec}
    (hm : m ∈ M.toSVec.part p) {r : ZMod 2} {b : B} (hb : b ∈ ℬ r) (n : N.toSVec) :
    SVec.whiskerLeft M.toSVec g (balance M N m b n) = sign k ((p + r) * q) • balance M N' m b (g n) := by
  have h : g (N.lact b n) = sign k (r * q) • N'.lact b (g n) :=
    congrArg (fun φ : N.toSVec ⟶ N'.toSVec => φ n) (((isHom_iff_of_mem hgq).1 hg).1 r b hb)
  rw [balance, SVec.hom_map_sub, SVec.whiskerLeft_tmul hgq (SVec.apply_mem_part (M.ract_mem r b hb) hm),
    SVec.whiskerLeft_tmul hgq hm, h, tmul_smul, smul_smul, ← sign_add, ← add_mul, balance,
    smul_sub]

omit [GradedAlgebra 𝒞] in
theorem whiskerLeft_mem_balanceRel_of_mem {q : ZMod 2} {g : N.toSVec ⟶ N'.toSVec} (hg : IsHom N N' g)
    (hgq : g ∈ SVec.parityHom N.toSVec N'.toSVec q) :
    ∀ x ∈ balanceRel M N, SVec.whiskerLeft M.toSVec g x ∈ balanceRel M N' := by
  intro x hx
  refine balanceRel_le M N
    (S := (balanceRel M N').comap (SVec.toLinearMap (SVec.whiskerLeft M.toSVec g)))
    (fun p q r m b n hm hb _ => ?_) hx
  change SVec.whiskerLeft M.toSVec g (balance M N m b n) ∈ balanceRel M N'
  rw [whiskerLeft_balance_of_mem M hg hgq hm hb]
  exact Submodule.smul_mem _ _ (balance_mem M N' m b _)

variable (g : N ⟶ N')

theorem whiskerLeft_mem_balanceSub :
    ∀ x ∈ balanceSub M N, SVec.whiskerLeft M.toSVec g.1 x ∈ balanceSub M N' := by
  intro x hx
  have e : SVec.whiskerLeft M.toSVec g.1 =
      SVec.whiskerLeft M.toSVec (proj k 0 g.1) + SVec.whiskerLeft M.toSVec (proj k 1 g.1) := by
    rw [← SVec.whiskerLeft_add, proj_add_proj]
  rw [mem_balanceSub, e, SVec.add_apply]
  exact Submodule.add_mem _
    (whiskerLeft_mem_balanceRel_of_mem M (g.2.proj 0) (proj_mem 0 g.1) x hx)
    (whiskerLeft_mem_balanceRel_of_mem M (g.2.proj 1) (proj_mem 1 g.1) x hx)

omit [GradedAlgebra ℬ] [GradedAlgebra 𝒞] in
theorem lactK_comp_whiskerLeft {p : ZMod 2} {a : A} (ha : a ∈ 𝒜 p) (g : N.toSVec ⟶ N'.toSVec) :
    SVec.whiskerRight (M.lact a) N.toSVec ≫ SVec.whiskerLeft M.toSVec g =
      twist k p (SVec.whiskerLeft M.toSVec g) ≫ SVec.whiskerRight (M.lact a) N'.toSVec := by
  rw [SVec.twist_whiskerLeft]
  refine Supercategory.induction_on (R := k) g ?_ (fun q g hg => ?_) (fun g g' hg hg' => ?_)
  · rw [SVec.whiskerLeft_zero, map_zero, SVec.whiskerLeft_zero, Limits.zero_comp, Limits.comp_zero]
  · rw [SVec.super_interchange (M.lact_mem p a ha) hg, twist_of_mem p hg, SVec.whiskerLeft_smul,
      Linear.smul_comp, koszulSign_smul (R := k)]
  · rw [SVec.whiskerLeft_add, map_add, SVec.whiskerLeft_add, Preadditive.comp_add,
      Preadditive.add_comp, hg, hg']

omit [GradedAlgebra ℬ] [GradedAlgebra 𝒞] in
theorem ractK_comp_whiskerLeft_of_mem {q : ZMod 2} {g : N.toSVec ⟶ N'.toSVec} (hg : IsHom N N' g)
    (hgq : g ∈ SVec.parityHom N.toSVec N'.toSVec q) (c : C) :
    ractK M N c ≫ SVec.whiskerLeft M.toSVec g = SVec.whiskerLeft M.toSVec g ≫ ractK M N' c := by
  rw [SVec.whiskerLeft_of_mem _ hgq, ractK_apply, ractK_apply]
  change map (M.toSVec.sgn q) (SVec.toLinearMap g) ∘ₗ map LinearMap.id (SVec.toLinearMap (N.ract c)) =
    map LinearMap.id (SVec.toLinearMap (N'.ract c)) ∘ₗ map (M.toSVec.sgn q) (SVec.toLinearMap g)
  rw [← map_comp, ← map_comp, LinearMap.comp_id, LinearMap.id_comp, ← SVec.toLinearMap_comp,
    ← SVec.toLinearMap_comp, hg.2 c]

omit [GradedAlgebra ℬ] in
theorem isHom_whiskerLeft : IsHom (tensorK M N) (tensorK M N') (SVec.whiskerLeft M.toSVec g.1) := by
  refine ⟨fun p a ha => lactK_comp_whiskerLeft M ha g.1, fun c => ?_⟩
  have e : SVec.whiskerLeft M.toSVec g.1 =
      SVec.whiskerLeft M.toSVec (proj k 0 g.1) + SVec.whiskerLeft M.toSVec (proj k 1 g.1) := by
    rw [← SVec.whiskerLeft_add, proj_add_proj]
  change ractK M N c ≫ SVec.whiskerLeft M.toSVec g.1 = SVec.whiskerLeft M.toSVec g.1 ≫ ractK M N' c
  rw [e, Preadditive.comp_add, Preadditive.add_comp,
    ractK_comp_whiskerLeft_of_mem M (g.2.proj 0) (proj_mem 0 g.1),
    ractK_comp_whiskerLeft_of_mem M (g.2.proj 1) (proj_mem 1 g.1)]

/-- `1_M ⊗ g : M ⊗_B N → M ⊗_B N'`, `(1 ⊗ g)(m ⊗ n) = (-1)^{|g||m|} m ⊗ g(n)`. -/
def whiskerLeft : tensor M N ⟶ tensor M N' :=
  descend ⟨SVec.whiskerLeft M.toSVec g.1, isHom_whiskerLeft M g⟩ (whiskerLeft_mem_balanceSub M g)

theorem whiskerLeft_tensorMk (x : SVec.tensorObj M.toSVec N.toSVec) :
    (whiskerLeft M g).1 (tensorMk M N x) = tensorMk M N' (SVec.whiskerLeft M.toSVec g.1 x) := rfl

/-- **The Koszul sign rule**: `(1 ⊗ g)(m ⊗ n) = (-1)^{|m||g|} m ⊗ g(n)`. -/
theorem whiskerLeft_btmul {q : ZMod 2} (hg : g ∈ parity (R := k) N N' q) {p : ZMod 2}
    {m : M.toSVec} (hm : m ∈ M.toSVec.part p) (n : N.toSVec) :
    (whiskerLeft M g).1 (btmul M N m n) = sign k (p * q) • btmul M N' m (g.1 n) := by
  rw [← tensorMk_tmul, whiskerLeft_tensorMk, SVec.whiskerLeft_tmul (mem_parity_iff.1 hg) hm,
    tensorMk_smul, tensorMk_tmul]

theorem whiskerLeft_btmul_even (hg : g ∈ parity (R := k) N N' 0) (m : M.toSVec) (n : N.toSVec) :
    (whiskerLeft M g).1 (btmul M N m n) = btmul M N' m (g.1 n) := by
  rw [← tensorMk_tmul, whiskerLeft_tensorMk, SVec.whiskerLeft_even _ (mem_parity_iff.1 hg)]
  rfl

variable (N) in
theorem whiskerLeft_id : whiskerLeft M (𝟙 N) = 𝟙 (tensor M N) :=
  hom_ext (SVec.quot_hom_ext _ _ fun x => by
    change tensorMk M N (SVec.whiskerLeft M.toSVec (𝟙 N.toSVec) x) = tensorMk M N x
    rw [SVec.whiskerLeft_id]; rfl)

theorem whiskerLeft_comp {N'' : SuperBimodule ℬ 𝒞} (g' : N' ⟶ N'') :
    whiskerLeft M (g ≫ g') = whiskerLeft M g ≫ whiskerLeft M g' :=
  hom_ext (SVec.quot_hom_ext _ _ fun x => by
    change tensorMk M N'' (SVec.whiskerLeft M.toSVec (g.1 ≫ g'.1) x) =
      tensorMk M N'' (SVec.whiskerLeft M.toSVec g'.1 (SVec.whiskerLeft M.toSVec g.1 x))
    rw [SVec.whiskerLeft_comp]; rfl)

theorem whiskerLeft_add (g' : N ⟶ N') : whiskerLeft M (g + g') = whiskerLeft M g + whiskerLeft M g' :=
  hom_ext (SVec.quot_hom_ext _ _ fun x => by
    change tensorMk M N' (SVec.whiskerLeft M.toSVec (g.1 + g'.1) x) =
      tensorMk M N' (SVec.whiskerLeft M.toSVec g.1 x) + tensorMk M N' (SVec.whiskerLeft M.toSVec g'.1 x)
    rw [SVec.whiskerLeft_add]; rfl)

theorem whiskerLeft_smul (r : k) : whiskerLeft M (r • g) = r • whiskerLeft M g :=
  hom_ext (SVec.quot_hom_ext _ _ fun x => by
    change tensorMk M N' (SVec.whiskerLeft M.toSVec (r • g.1) x) =
      r • tensorMk M N' (SVec.whiskerLeft M.toSVec g.1 x)
    rw [SVec.whiskerLeft_smul]; rfl)

/-- `1 ⊗ g` has the parity of `g`. -/
theorem whiskerLeft_mem {q : ZMod 2} (hg : g ∈ parity (R := k) N N' q) :
    whiskerLeft M g ∈ parity (R := k) (tensor M N) (tensor M N') q :=
  mem_parity_iff.2 (SVec.quotMap_mem (SVec.whiskerLeft_mem M.toSVec (mem_parity_iff.1 hg))
    (whiskerLeft_mem_balanceSub M g))

/-- `f ⊗ 1` has the parity of `f`. -/
theorem whiskerRight_mem {M' : SuperBimodule 𝒜 ℬ} {p : ZMod 2} {f : M ⟶ M'}
    (hf : f ∈ parity (R := k) M M' p) (N : SuperBimodule ℬ 𝒞) :
    whiskerRight f N ∈ parity (R := k) (tensor M N) (tensor M' N) p :=
  mem_parity_iff.2 (SVec.quotMap_mem (SVec.whiskerRight_mem (mem_parity_iff.1 hf) N.toSVec)
    (whiskerRight_mem_balanceSub f N))

/-- **The super interchange law** for the balanced tensor product:
`(f ⊗ 1) ≫ (1 ⊗ g) = (-1)^{|f||g|} (1 ⊗ g) ≫ (f ⊗ 1)`. -/
theorem super_interchange {M' : SuperBimodule 𝒜 ℬ} {p q : ZMod 2} {f : M ⟶ M'}
    (hf : f ∈ parity (R := k) M M' p) (hg : g ∈ parity (R := k) N N' q) :
    whiskerRight f N ≫ whiskerLeft M' g = koszulSign p q • (whiskerLeft M g ≫ whiskerRight f N') :=
  hom_ext (SVec.quot_hom_ext _ _ fun x => by
    change tensorMk M' N' ((SVec.whiskerRight f.1 N.toSVec ≫ SVec.whiskerLeft M'.toSVec g.1) x) =
      koszulSign p q • tensorMk M' N' ((SVec.whiskerLeft M.toSVec g.1 ≫ SVec.whiskerRight f.1 N'.toSVec) x)
    rw [SVec.super_interchange (mem_parity_iff.1 hf) (mem_parity_iff.1 hg), SVec.zsmul_apply,
      tensorMk_zsmul])

end WhiskerLeft

/-! ## Iterated tensor products -/

section Iterated

variable [GradedAlgebra ℬ] [GradedAlgebra 𝒞] (M : SuperBimodule 𝒜 ℬ) (N : SuperBimodule ℬ 𝒞)
  (P : SuperBimodule 𝒞 𝒟)

/-- Linear maps out of `(M ⊗_B N) ⊗_C P` are determined by their values on the classes
`(m ⊗ n) ⊗ p`. -/
theorem tensor_hom_ext_left {W : SVec k} {f g : (tensor (tensor M N) P).toSVec ⟶ W}
    (h : ∀ m n p, f (btmul _ P (btmul M N m n) p) = g (btmul _ P (btmul M N m n) p)) : f = g := by
  refine tensor_hom_ext _ P fun x p => ?_
  induction x using tensor_induction_on with
  | zero => rw [btmul_zero_left, SVec.hom_map_zero, SVec.hom_map_zero]
  | btmul m n => exact h m n p
  | add x y hx hy => rw [btmul_add_left, SVec.hom_map_add, SVec.hom_map_add, hx, hy]

/-- Linear maps out of `M ⊗_B (N ⊗_C P)` are determined by their values on the classes
`m ⊗ (n ⊗ p)`. -/
theorem tensor_hom_ext_right {W : SVec k} {f g : (tensor M (tensor N P)).toSVec ⟶ W}
    (h : ∀ m n p, f (btmul M _ m (btmul N P n p)) = g (btmul M _ m (btmul N P n p))) : f = g := by
  refine tensor_hom_ext M _ fun m x => ?_
  induction x using tensor_induction_on with
  | zero => rw [btmul_zero_right, SVec.hom_map_zero, SVec.hom_map_zero]
  | btmul n p => exact h m n p
  | add x y hx hy => rw [btmul_add_right, SVec.hom_map_add, SVec.hom_map_add, hx, hy]

/-- Homogeneous version of `tensor_hom_ext_left`. -/
theorem tensor_hom_ext_left_homogeneous {W : SVec k} {f g : (tensor (tensor M N) P).toSVec ⟶ W}
    (h : ∀ (p q r : ZMod 2) (m : M.toSVec) (n : N.toSVec) (x : P.toSVec), m ∈ M.toSVec.part p →
      n ∈ N.toSVec.part q → x ∈ P.toSVec.part r →
      f (btmul _ P (btmul M N m n) x) = g (btmul _ P (btmul M N m n) x)) : f = g := by
  refine tensor_hom_ext_homogeneous _ P fun s r y x hy hx => ?_
  rw [← (SVec.mem_part_iff _).1 hy]
  clear hy
  induction y using tensor_induction_on_homogeneous with
  | zero => rw [map_zero, btmul_zero_left, SVec.hom_map_zero, SVec.hom_map_zero]
  | btmul p q m n hm hn =>
    rw [SVec.proj_apply_of_mem_part _ (btmul_mem_part M N hm hn)]
    split_ifs
    · exact h p q r m n x hm hn hx
    · rw [btmul_zero_left, SVec.hom_map_zero, SVec.hom_map_zero]
  | add y z hy hz => rw [map_add, btmul_add_left, SVec.hom_map_add, SVec.hom_map_add, hy, hz]

/-- A linear map out of `(M ⊗_B N) ⊗_C P` whose values on homogeneous classes have parity
`|m| + |n| + |p| + s` has parity `s`. -/
theorem tensor_mem_parity_of_btmul_left {W : SVec k} {f : (tensor (tensor M N) P).toSVec ⟶ W}
    {s : ZMod 2}
    (h : ∀ (p q r : ZMod 2) (m : M.toSVec) (n : N.toSVec) (x : P.toSVec), m ∈ M.toSVec.part p →
      n ∈ N.toSVec.part q → x ∈ P.toSVec.part r →
      f (btmul _ P (btmul M N m n) x) ∈ W.part (p + q + r + s)) :
    f ∈ SVec.parityHom (tensor (tensor M N) P).toSVec W s := by
  intro t
  refine tensor_hom_ext_left_homogeneous M N P fun p q r m n x hm hn hx => ?_
  change f ((tensor (tensor M N) P).toSVec.proj t (btmul _ P (btmul M N m n) x)) =
    W.proj (t + s) (f (btmul _ P (btmul M N m n) x))
  rw [SVec.proj_apply_of_mem_part _ (btmul_mem_part _ P (btmul_mem_part M N hm hn) hx),
    SVec.proj_apply_of_mem_part _ (h p q r m n x hm hn hx)]
  by_cases ht : t = p + q + r
  · rw [if_pos ht, if_pos (by rw [ht])]
  · rw [if_neg ht, if_neg (fun e => ht (add_right_cancel e)), SVec.hom_map_zero]

/-! ### The associator -/

/-- The trilinear map `(m, n, p) ↦ m ⊗ (n ⊗ p)`. -/
def assocTri : M.toSVec →ₗ[k] N.toSVec →ₗ[k] P.toSVec →ₗ[k] (tensor M (tensor N P)).toSVec :=
  curry (curry (SVec.toLinearMap (tensorMkHom M (tensor N P)) ∘ₗ
    map LinearMap.id (SVec.toLinearMap (tensorMkHom N P)) ∘ₗ
      (TensorProduct.assoc k M.toSVec N.toSVec P.toSVec).toLinearMap))

@[simp] theorem assocTri_apply (m : M.toSVec) (n : N.toSVec) (p : P.toSVec) :
    assocTri M N P m n p = btmul M _ m (btmul N P n p) := rfl

theorem assocTri_balanced (m : M.toSVec) (b : B) (n : N.toSVec) :
    assocTri M N P (M.ract b m) n = assocTri M N P m (N.lact b n) :=
  LinearMap.ext fun p => by rw [assocTri_apply, assocTri_apply, btmul_ract_lact, lact_btmul]

/-- The bilinear map `((m ⊗ n), p) ↦ m ⊗ (n ⊗ p)`. -/
def assocBi : (tensor M N).toSVec →ₗ[k] P.toSVec →ₗ[k] (tensor M (tensor N P)).toSVec :=
  tensorLift (assocTri M N P) (assocTri_balanced M N P)

theorem assocBi_balanced (x : (tensor M N).toSVec) (c : C) (p : P.toSVec) :
    assocBi M N P ((tensor M N).ract c x) p = assocBi M N P x (P.lact c p) := by
  induction x using tensor_induction_on with
  | zero => rw [SVec.hom_map_zero, map_zero, LinearMap.zero_apply, LinearMap.zero_apply]
  | btmul m n =>
    rw [ract_btmul, assocBi, tensorLift_btmul, tensorLift_btmul, assocTri_apply, assocTri_apply,
      btmul_ract_lact]
  | add x y hx hy =>
    rw [SVec.hom_map_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hx, hy]

/-- The associator `(M ⊗_B N) ⊗_C P → M ⊗_B (N ⊗_C P)` on underlying superspaces. -/
def assocHom : (tensor (tensor M N) P).toSVec ⟶ (tensor M (tensor N P)).toSVec :=
  SVec.ofHom (tensorLift (assocBi M N P) (assocBi_balanced M N P))

@[simp] theorem assocHom_btmul (m : M.toSVec) (n : N.toSVec) (p : P.toSVec) :
    assocHom M N P (btmul _ P (btmul M N m n) p) = btmul M _ m (btmul N P n p) := by
  rw [assocHom, SVec.ofHom_apply, tensorLift_btmul, assocBi, tensorLift_btmul, assocTri_apply]

/-- The trilinear map `(n, p, m) ↦ (m ⊗ n) ⊗ p`. -/
def assocInvTri : N.toSVec →ₗ[k] P.toSVec →ₗ[k] M.toSVec →ₗ[k] (tensor (tensor M N) P).toSVec :=
  LinearMap.lflip ∘ₗ (curry (curry (SVec.toLinearMap (tensorMkHom (tensor M N) P) ∘ₗ
    map (SVec.toLinearMap (tensorMkHom M N)) LinearMap.id))).flip

@[simp] theorem assocInvTri_apply (n : N.toSVec) (p : P.toSVec) (m : M.toSVec) :
    assocInvTri M N P n p m = btmul _ P (btmul M N m n) p := rfl

theorem assocInvTri_balanced (n : N.toSVec) (c : C) (p : P.toSVec) :
    assocInvTri M N P (N.ract c n) p = assocInvTri M N P n (P.lact c p) :=
  LinearMap.ext fun m => by
    rw [assocInvTri_apply, assocInvTri_apply, ← ract_btmul, btmul_ract_lact]

/-- The bilinear map `((n ⊗ p), m) ↦ (m ⊗ n) ⊗ p`. -/
def assocInvBi : (tensor N P).toSVec →ₗ[k] M.toSVec →ₗ[k] (tensor (tensor M N) P).toSVec :=
  tensorLift (assocInvTri M N P) (assocInvTri_balanced M N P)

theorem assocInvBi_balanced (m : M.toSVec) (b : B) (y : (tensor N P).toSVec) :
    (assocInvBi M N P).flip (M.ract b m) y = (assocInvBi M N P).flip m ((tensor N P).lact b y) := by
  induction y using tensor_induction_on with
  | zero =>
    rw [LinearMap.flip_apply, LinearMap.flip_apply, SVec.hom_map_zero, map_zero]
    rfl
  | btmul n p =>
    rw [LinearMap.flip_apply, LinearMap.flip_apply, lact_btmul, assocInvBi, tensorLift_btmul,
      tensorLift_btmul, assocInvTri_apply, assocInvTri_apply, btmul_ract_lact]
  | add y z hy hz =>
    simp only [LinearMap.flip_apply, SVec.hom_map_add, map_add, LinearMap.add_apply] at hy hz ⊢
    rw [hy, hz]

/-- The inverse associator `M ⊗_B (N ⊗_C P) → (M ⊗_B N) ⊗_C P` on underlying superspaces. -/
def assocInv : (tensor M (tensor N P)).toSVec ⟶ (tensor (tensor M N) P).toSVec :=
  SVec.ofHom (tensorLift (assocInvBi M N P).flip (assocInvBi_balanced M N P))

@[simp] theorem assocInv_btmul (m : M.toSVec) (n : N.toSVec) (p : P.toSVec) :
    assocInv M N P (btmul M _ m (btmul N P n p)) = btmul _ P (btmul M N m n) p := by
  rw [assocInv, SVec.ofHom_apply, tensorLift_btmul, LinearMap.flip_apply, assocInvBi,
    tensorLift_btmul, assocInvTri_apply]

/-- The associator as an isomorphism of superspaces. -/
def assocSVecIso : (tensor (tensor M N) P).toSVec ≅ (tensor M (tensor N P)).toSVec where
  hom := assocHom M N P
  inv := assocInv M N P
  hom_inv_id := tensor_hom_ext_left M N P fun m n p => by
    rw [SVec.comp_apply, assocHom_btmul, assocInv_btmul, SVec.id_apply]
  inv_hom_id := tensor_hom_ext_right M N P fun m n p => by
    rw [SVec.comp_apply, assocInv_btmul, assocHom_btmul, SVec.id_apply]

theorem assocHom_mem :
    assocHom M N P ∈ SVec.parityHom (tensor (tensor M N) P).toSVec (tensor M (tensor N P)).toSVec 0 :=
  tensor_mem_parity_of_btmul_left M N P fun p q r m n x hm hn hx => by
    rw [assocHom_btmul, add_zero, add_assoc]
    exact btmul_mem_part M _ hm (btmul_mem_part N P hn hx)

theorem assocInv_mem :
    assocInv M N P ∈ SVec.parityHom (tensor M (tensor N P)).toSVec (tensor (tensor M N) P).toSVec 0 :=
  inv_mem (assocSVecIso M N P) (assocHom_mem M N P)

theorem isHom_assocHom : IsHom (tensor (tensor M N) P) (tensor M (tensor N P)) (assocHom M N P) :=
  isHom_of_even (assocHom_mem M N P)
    (fun a => tensor_hom_ext_left M N P fun m n p => by
      rw [SVec.comp_apply, SVec.comp_apply, lact_btmul, lact_btmul, assocHom_btmul, assocHom_btmul,
        lact_btmul])
    (fun d => tensor_hom_ext_left M N P fun m n p => by
      rw [SVec.comp_apply, SVec.comp_apply, ract_btmul, assocHom_btmul, assocHom_btmul, ract_btmul,
        ract_btmul])

theorem isHom_assocInv : IsHom (tensor M (tensor N P)) (tensor (tensor M N) P) (assocInv M N P) :=
  isHom_of_even (assocInv_mem M N P)
    (fun a => tensor_hom_ext_right M N P fun m n p => by
      rw [SVec.comp_apply, SVec.comp_apply, lact_btmul, assocInv_btmul, assocInv_btmul, lact_btmul,
        lact_btmul])
    (fun d => tensor_hom_ext_right M N P fun m n p => by
      rw [SVec.comp_apply, SVec.comp_apply, ract_btmul, ract_btmul, assocInv_btmul, assocInv_btmul,
        ract_btmul])

/-- **The associator** `(M ⊗_B N) ⊗_C P ≅ M ⊗_B (N ⊗_C P)`, an even isomorphism of
`(A, D)`-superbimodules, `(m ⊗ n) ⊗ p ↦ m ⊗ (n ⊗ p)`. -/
def assoc : tensor (tensor M N) P ≅ tensor M (tensor N P) where
  hom := ⟨assocHom M N P, isHom_assocHom M N P⟩
  inv := ⟨assocInv M N P, isHom_assocInv M N P⟩
  hom_inv_id := hom_ext (assocSVecIso M N P).hom_inv_id
  inv_hom_id := hom_ext (assocSVecIso M N P).inv_hom_id

@[simp] theorem assoc_hom_btmul (m : M.toSVec) (n : N.toSVec) (p : P.toSVec) :
    (assoc M N P).hom.1 (btmul _ P (btmul M N m n) p) = btmul M _ m (btmul N P n p) :=
  assocHom_btmul M N P m n p

@[simp] theorem assoc_inv_btmul (m : M.toSVec) (n : N.toSVec) (p : P.toSVec) :
    (assoc M N P).inv.1 (btmul M _ m (btmul N P n p)) = btmul _ P (btmul M N m n) p :=
  assocInv_btmul M N P m n p

theorem assoc_hom_mem [GradedAlgebra 𝒟] :
    (assoc M N P).hom ∈ parity (R := k) (tensor (tensor M N) P) (tensor M (tensor N P)) 0 :=
  mem_parity_iff.2 (assocHom_mem M N P)

theorem assoc_inv_mem [GradedAlgebra 𝒟] :
    (assoc M N P).inv ∈ parity (R := k) (tensor M (tensor N P)) (tensor (tensor M N) P) 0 :=
  mem_parity_iff.2 (assocInv_mem M N P)

end Iterated

/-! ### Naturality of the associator and the pentagon identity -/

section Naturality

variable [GradedAlgebra ℬ] [GradedAlgebra 𝒞] (M : SuperBimodule 𝒜 ℬ) (N : SuperBimodule ℬ 𝒞)
  (P : SuperBimodule 𝒞 𝒟)

theorem whiskerLeft_zero {N' : SuperBimodule ℬ 𝒞} : whiskerLeft M (0 : N ⟶ N') = 0 :=
  hom_ext (SVec.quot_hom_ext _ _ fun x => by
    change tensorMk M N' (SVec.whiskerLeft M.toSVec (0 : N.toSVec ⟶ N'.toSVec) x) = 0
    rw [SVec.whiskerLeft_zero]; rfl)

omit [GradedAlgebra 𝒞] in
theorem zero_whiskerRight {M' : SuperBimodule 𝒜 ℬ} : whiskerRight (0 : M ⟶ M') N = 0 :=
  hom_ext (SVec.quot_hom_ext _ _ fun x => by
    change tensorMk M' N (SVec.whiskerRight (0 : M.toSVec ⟶ M'.toSVec) N.toSVec x) = 0
    rw [SVec.whiskerRight_zero]; rfl)

theorem assoc_naturality_left {M' : SuperBimodule 𝒜 ℬ} (f : M ⟶ M') :
    whiskerRight (whiskerRight f N) P ≫ (assoc M' N P).hom =
      (assoc M N P).hom ≫ whiskerRight f (tensor N P) :=
  hom_ext (tensor_hom_ext_left M N P fun m n p => by
    rw [comp_val, comp_val, SVec.comp_apply, SVec.comp_apply, whiskerRight_btmul,
      whiskerRight_btmul, assoc_hom_btmul, assoc_hom_btmul, whiskerRight_btmul])

theorem assoc_naturality_middle [GradedAlgebra 𝒟] {N' : SuperBimodule ℬ 𝒞} (g : N ⟶ N') :
    whiskerRight (whiskerLeft M g) P ≫ (assoc M N' P).hom =
      (assoc M N P).hom ≫ whiskerLeft M (whiskerRight g P) := by
  refine Supercategory.induction_on (R := k) g ?_ (fun q g hg => ?_) (fun g g' hg hg' => ?_)
  · rw [whiskerLeft_zero, zero_whiskerRight, zero_whiskerRight, whiskerLeft_zero,
      Limits.zero_comp, Limits.comp_zero]
  · refine hom_ext (tensor_hom_ext_left_homogeneous M N P fun p r s m n x hm hn _ => ?_)
    rw [comp_val, comp_val, SVec.comp_apply, SVec.comp_apply, whiskerRight_btmul,
      whiskerLeft_btmul M g hg hm, btmul_smul_left, SVec.hom_map_smul, assoc_hom_btmul,
      assoc_hom_btmul, whiskerLeft_btmul M _ (whiskerRight_mem _ hg P) hm, whiskerRight_btmul]
  · rw [whiskerLeft_add, add_whiskerRight, Preadditive.add_comp, hg, hg', add_whiskerRight,
      whiskerLeft_add, Preadditive.comp_add]

theorem assoc_naturality_right [GradedAlgebra 𝒟] {P' : SuperBimodule 𝒞 𝒟} (h : P ⟶ P') :
    whiskerLeft (tensor M N) h ≫ (assoc M N P').hom =
      (assoc M N P).hom ≫ whiskerLeft M (whiskerLeft N h) := by
  refine Supercategory.induction_on (R := k) h ?_ (fun r h hh => ?_) (fun h h' hh hh' => ?_)
  · rw [whiskerLeft_zero, whiskerLeft_zero, whiskerLeft_zero, Limits.zero_comp, Limits.comp_zero]
  · refine hom_ext (tensor_hom_ext_left_homogeneous M N P fun p q s m n x hm hn hx => ?_)
    rw [comp_val, comp_val, SVec.comp_apply, SVec.comp_apply,
      whiskerLeft_btmul _ h hh (btmul_mem_part M N hm hn), SVec.hom_map_smul, assoc_hom_btmul,
      assoc_hom_btmul, whiskerLeft_btmul M _ (whiskerLeft_mem N h hh) hm,
      whiskerLeft_btmul N h hh hn, btmul_smul_right, smul_smul, ← sign_add, ← add_mul]
  · rw [whiskerLeft_add, whiskerLeft_add, whiskerLeft_add, Preadditive.add_comp, hh, hh',
      Preadditive.comp_add]

variable {E : Type w} [Ring E] [Algebra k E] {ℰ : ZMod 2 → Submodule k E}

/-- **The pentagon identity** for the associators of balanced tensor products. -/
theorem pentagon [GradedAlgebra 𝒟] [GradedAlgebra ℰ] (Q : SuperBimodule 𝒟 ℰ) :
    whiskerRight (assoc M N P).hom Q ≫ (assoc M (tensor N P) Q).hom ≫
        whiskerLeft M (assoc N P Q).hom =
      (assoc (tensor M N) P Q).hom ≫ (assoc M N (tensor P Q)).hom := by
  refine hom_ext (tensor_hom_ext_left (tensor M N) P Q fun x p q => ?_)
  induction x using tensor_induction_on with
  | zero => rw [btmul_zero_left, btmul_zero_left, SVec.hom_map_zero, SVec.hom_map_zero]
  | btmul m n =>
    simp only [comp_val, SVec.comp_apply]
    rw [whiskerRight_btmul, assoc_hom_btmul, assoc_hom_btmul,
      whiskerLeft_btmul_even M _ (assoc_hom_mem N P Q), assoc_hom_btmul, assoc_hom_btmul,
      assoc_hom_btmul]
  | add x y hx hy =>
    rw [btmul_add_left, btmul_add_left, SVec.hom_map_add, SVec.hom_map_add, hx, hy]

/-- The pentagon identity for the inverse associators. -/
theorem pentagon_inv [GradedAlgebra 𝒟] [GradedAlgebra ℰ] (Q : SuperBimodule 𝒟 ℰ) :
    whiskerLeft M (assoc N P Q).inv ≫ (assoc M (tensor N P) Q).inv ≫
        whiskerRight (assoc M N P).inv Q =
      (assoc M N (tensor P Q)).inv ≫ (assoc (tensor M N) P Q).inv := by
  refine hom_ext (tensor_hom_ext_right M N (tensor P Q) fun m n x => ?_)
  induction x using tensor_induction_on with
  | zero => rw [btmul_zero_right, btmul_zero_right, SVec.hom_map_zero, SVec.hom_map_zero]
  | btmul p q =>
    simp only [comp_val, SVec.comp_apply]
    rw [whiskerLeft_btmul_even M _ (assoc_inv_mem N P Q), assoc_inv_btmul, assoc_inv_btmul,
      whiskerRight_btmul, assoc_inv_btmul, assoc_inv_btmul, assoc_inv_btmul]
  | add x y hx hy =>
    rw [btmul_add_right, btmul_add_right, SVec.hom_map_add, SVec.hom_map_add, hx, hy]

end Naturality

end SuperBimodule

/-! ## The regular superbimodule and the unitors -/

namespace SuperBimodule

variable {A : Type u} [Ring A] [Algebra k A] {B : Type u} [Ring B] [Algebra k B] {C : Type u}
  [Ring C] [Algebra k C] {𝒜 : ZMod 2 → Submodule k A} {ℬ : ZMod 2 → Submodule k B}
  {𝒞 : ZMod 2 → Submodule k C}

section Regular

variable (𝒜) [GradedAlgebra 𝒜]

/-- The superspace underlying a superalgebra `A`. -/
abbrev regularSVec : SVec k where
  carrier := A
  odd := algProj 𝒜 1
  odd_comp_odd := LinearMap.ext fun a =>
    proj_proj (R := k) (C := SuperalgebraCat 𝒜) (X := SuperalgebraCat.star 𝒜)
      (Y := SuperalgebraCat.star 𝒜) 1 a

theorem regularSVec_proj (p : ZMod 2) : (regularSVec 𝒜).proj p = algProj 𝒜 p := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [SVec.proj_zero]
    ext a
    rw [LinearMap.sub_apply, LinearMap.id_apply]
    exact (eq_sub_of_add_eq (algProj_add_algProj 𝒜 a)).symm
  · rfl

theorem mem_regularSVec_part_iff {p : ZMod 2} {a : A} : a ∈ (regularSVec 𝒜).part p ↔ a ∈ 𝒜 p := by
  rw [SVec.mem_part_iff, regularSVec_proj]
  exact (mem_iff_proj (R := k) (C := SuperalgebraCat 𝒜) (X := SuperalgebraCat.star 𝒜)
    (Y := SuperalgebraCat.star 𝒜)).symm

/-- **Brundan–Ellis, Example 1.5(i).** The regular `(A, A)`-superbimodule `A`, the unit object
of `A-SMod-A`. -/
def regular : SuperBimodule 𝒜 𝒜 where
  toSVec := regularSVec 𝒜
  lact :=
    { toFun := fun a => SVec.ofHom (LinearMap.mulLeft k a)
      map_add' := fun a a' => SVec.hom_ext fun x => add_mul a a' x
      map_smul' := fun r a => SVec.hom_ext fun x => smul_mul_assoc r a x }
  ract :=
    { toFun := fun b => SVec.ofHom (LinearMap.mulRight k b)
      map_add' := fun b b' => SVec.hom_ext fun x => mul_add x b b'
      map_smul' := fun r b => SVec.hom_ext fun x => mul_smul_comm r x b }
  lact_one := SVec.hom_ext fun x => one_mul x
  lact_mul a a' := SVec.hom_ext fun x => mul_assoc a a' x
  ract_one := SVec.hom_ext fun x => mul_one x
  ract_mul b b' := SVec.hom_ext fun x => (mul_assoc x b b').symm
  lact_ract a b := SVec.hom_ext fun x => mul_assoc a x b
  lact_mem p a ha := SVec.mem_parityHom_of_apply_mem fun q x hx =>
    (mem_regularSVec_part_iff 𝒜).2 (by
      rw [add_comm]; exact SetLike.GradedMul.mul_mem ha ((mem_regularSVec_part_iff 𝒜).1 hx))
  ract_mem p b hb := SVec.mem_parityHom_of_apply_mem fun q x hx =>
    (mem_regularSVec_part_iff 𝒜).2 (SetLike.GradedMul.mul_mem ((mem_regularSVec_part_iff 𝒜).1 hx) hb)

theorem regular_lact_apply (a x : A) : (regular 𝒜).lact a x = a * x := rfl

theorem regular_ract_apply (b x : A) : (regular 𝒜).ract b x = x * b := rfl

end Regular

section LeftUnitor

variable [GradedAlgebra 𝒜] (M : SuperBimodule 𝒜 ℬ)

/-! ### The left unitor `A ⊗_A M ≅ M` -/

theorem lact_regular_ract (a b : A) (m : M.toSVec) :
    M.lact ((regular 𝒜).ract b a) m = M.lact a (M.lact b m) := by
  rw [regular_ract_apply, M.lact_mul]; rfl

/-- The bilinear map `(a, m) ↦ a m`. -/
def leftUnitorBi : (regular 𝒜).toSVec →ₗ[k] M.toSVec →ₗ[k] M.toSVec := M.lact

/-- `A ⊗_A M → M`, `a ⊗ m ↦ a m`. -/
def leftUnitorHom : (tensor (regular 𝒜) M).toSVec ⟶ M.toSVec :=
  SVec.ofHom (tensorLift (leftUnitorBi M) (lact_regular_ract M))

@[simp] theorem leftUnitorHom_btmul (a : A) (m : M.toSVec) :
    leftUnitorHom M (btmul (regular 𝒜) M a m) = M.lact a m :=
  tensorLift_btmul (leftUnitorBi M) (lact_regular_ract M) a m

/-- `M → A ⊗_A M`, `m ↦ 1 ⊗ m`. -/
def leftUnitorInv : M.toSVec ⟶ (tensor (regular 𝒜) M).toSVec :=
  SVec.ofHom
    { toFun := fun m => btmul (regular 𝒜) M (1 : A) m
      map_add' := btmul_add_right (regular 𝒜) M (1 : A)
      map_smul' := fun r m => btmul_smul_right (regular 𝒜) M r (1 : A) m }

@[simp] theorem leftUnitorInv_apply (m : M.toSVec) :
    leftUnitorInv M m = btmul (regular 𝒜) M (1 : A) m :=
  rfl

/-- The left unitor on underlying superspaces. -/
def leftUnitorSVecIso : (tensor (regular 𝒜) M).toSVec ≅ M.toSVec where
  hom := leftUnitorHom M
  inv := leftUnitorInv M
  hom_inv_id := tensor_hom_ext (regular 𝒜) M fun a m => by
    rw [SVec.comp_apply, leftUnitorHom_btmul, leftUnitorInv_apply, ← btmul_ract_lact,
      regular_ract_apply, one_mul, SVec.id_apply]
  inv_hom_id := SVec.hom_ext fun m => by
    rw [SVec.comp_apply, leftUnitorInv_apply, leftUnitorHom_btmul, M.lact_one]

theorem leftUnitorHom_mem :
    leftUnitorHom M ∈ SVec.parityHom (tensor (regular 𝒜) M).toSVec M.toSVec 0 :=
  tensor_mem_parity_of_btmul (regular 𝒜) M fun p q a m ha hm => by
    rw [leftUnitorHom_btmul, add_zero, add_comm]
    exact SVec.apply_mem_part (M.lact_mem p a ((mem_regularSVec_part_iff 𝒜).1 ha)) hm

theorem isHom_leftUnitorHom : IsHom (tensor (regular 𝒜) M) M (leftUnitorHom M) :=
  isHom_of_even (leftUnitorHom_mem M)
    (fun a => tensor_hom_ext (regular 𝒜) M fun a' m => by
      rw [SVec.comp_apply, SVec.comp_apply, lact_btmul, leftUnitorHom_btmul, leftUnitorHom_btmul,
        regular_lact_apply, M.lact_mul, SVec.comp_apply])
    (fun b => tensor_hom_ext (regular 𝒜) M fun a' m => by
      have h := congrArg (fun φ : M.toSVec ⟶ M.toSVec => φ m) (M.lact_ract a' b)
      simp only [SVec.comp_apply] at h
      rw [SVec.comp_apply, SVec.comp_apply, ract_btmul, leftUnitorHom_btmul, leftUnitorHom_btmul, h])

theorem isHom_leftUnitorInv : IsHom M (tensor (regular 𝒜) M) (leftUnitorInv M) :=
  isHom_of_even (inv_mem (leftUnitorSVecIso M) (leftUnitorHom_mem M))
    (fun a => SVec.hom_ext fun m => by
      rw [SVec.comp_apply, SVec.comp_apply, leftUnitorInv_apply, leftUnitorInv_apply, lact_btmul,
        ← btmul_ract_lact, regular_ract_apply, regular_lact_apply, one_mul, mul_one])
    (fun b => SVec.hom_ext fun m => by
      rw [SVec.comp_apply, SVec.comp_apply, leftUnitorInv_apply, leftUnitorInv_apply, ract_btmul])

/-- **The left unitor** `A ⊗_A M ≅ M`, `a ⊗ m ↦ a m`, an even isomorphism of
superbimodules. -/
def leftUnitor : tensor (regular 𝒜) M ≅ M where
  hom := ⟨leftUnitorHom M, isHom_leftUnitorHom M⟩
  inv := ⟨leftUnitorInv M, isHom_leftUnitorInv M⟩
  hom_inv_id := hom_ext (leftUnitorSVecIso M).hom_inv_id
  inv_hom_id := hom_ext (leftUnitorSVecIso M).inv_hom_id

@[simp] theorem leftUnitor_hom_btmul (a : A) (m : M.toSVec) :
    (leftUnitor M).hom.1 (btmul (regular 𝒜) M a m) = M.lact a m :=
  leftUnitorHom_btmul M a m

@[simp] theorem leftUnitor_inv_apply (m : M.toSVec) :
    (leftUnitor M).inv.1 m = btmul (regular 𝒜) M (1 : A) m := rfl

end LeftUnitor

section RightUnitor

variable [GradedAlgebra ℬ] (M : SuperBimodule 𝒜 ℬ)

/-! ### The right unitor `M ⊗_B B ≅ M` -/

/-- The bilinear map `(m, b) ↦ m b`. -/
def rightUnitorBi : M.toSVec →ₗ[k] (regular ℬ).toSVec →ₗ[k] M.toSVec :=
  (M.ract : B →ₗ[k] (M.toSVec →ₗ[k] M.toSVec)).flip

theorem rightUnitorBi_apply (m : M.toSVec) (b : B) : rightUnitorBi M m b = M.ract b m := rfl

theorem rightUnitorBi_balanced (m : M.toSVec) (b b' : B) :
    rightUnitorBi M (M.ract b m) b' = rightUnitorBi M m ((regular ℬ).lact b b') := by
  rw [rightUnitorBi_apply, rightUnitorBi_apply, regular_lact_apply, M.ract_mul]; rfl

/-- `M ⊗_B B → M`, `m ⊗ b ↦ m b`. -/
def rightUnitorHom : (tensor M (regular ℬ)).toSVec ⟶ M.toSVec :=
  SVec.ofHom (tensorLift (rightUnitorBi M) (rightUnitorBi_balanced M))

@[simp] theorem rightUnitorHom_btmul (m : M.toSVec) (b : B) :
    rightUnitorHom M (btmul M (regular ℬ) m b) = M.ract b m :=
  tensorLift_btmul (rightUnitorBi M) (rightUnitorBi_balanced M) m b

/-- `M → M ⊗_B B`, `m ↦ m ⊗ 1`. -/
def rightUnitorInv : M.toSVec ⟶ (tensor M (regular ℬ)).toSVec :=
  SVec.ofHom
    { toFun := fun m => btmul M (regular ℬ) m (1 : B)
      map_add' := fun m m' => btmul_add_left M (regular ℬ) m m' (1 : B)
      map_smul' := fun r m => btmul_smul_left M (regular ℬ) r m (1 : B) }

@[simp] theorem rightUnitorInv_apply (m : M.toSVec) :
    rightUnitorInv M m = btmul M (regular ℬ) m (1 : B) := rfl

/-- The right unitor on underlying superspaces. -/
def rightUnitorSVecIso : (tensor M (regular ℬ)).toSVec ≅ M.toSVec where
  hom := rightUnitorHom M
  inv := rightUnitorInv M
  hom_inv_id := tensor_hom_ext M (regular ℬ) fun m b => by
    rw [SVec.comp_apply, rightUnitorHom_btmul, rightUnitorInv_apply, btmul_ract_lact,
      regular_lact_apply, mul_one, SVec.id_apply]
  inv_hom_id := SVec.hom_ext fun m => by
    rw [SVec.comp_apply, rightUnitorInv_apply, rightUnitorHom_btmul, M.ract_one]

theorem rightUnitorHom_mem :
    rightUnitorHom M ∈ SVec.parityHom (tensor M (regular ℬ)).toSVec M.toSVec 0 :=
  tensor_mem_parity_of_btmul M (regular ℬ) fun p q m b hm hb => by
    rw [rightUnitorHom_btmul, add_zero]
    exact SVec.apply_mem_part (M.ract_mem q b ((mem_regularSVec_part_iff ℬ).1 hb)) hm

theorem isHom_rightUnitorHom : IsHom (tensor M (regular ℬ)) M (rightUnitorHom M) :=
  isHom_of_even (rightUnitorHom_mem M)
    (fun a => tensor_hom_ext M (regular ℬ) fun m b => by
      have h := congrArg (fun φ : M.toSVec ⟶ M.toSVec => φ m) (M.lact_ract a b)
      simp only [SVec.comp_apply] at h
      rw [SVec.comp_apply, SVec.comp_apply, lact_btmul, rightUnitorHom_btmul, rightUnitorHom_btmul, h])
    (fun b' => tensor_hom_ext M (regular ℬ) fun m b => by
      rw [SVec.comp_apply, SVec.comp_apply, ract_btmul, rightUnitorHom_btmul, rightUnitorHom_btmul,
        regular_ract_apply, M.ract_mul, SVec.comp_apply])

theorem isHom_rightUnitorInv : IsHom M (tensor M (regular ℬ)) (rightUnitorInv M) :=
  isHom_of_even (inv_mem (rightUnitorSVecIso M) (rightUnitorHom_mem M))
    (fun a => SVec.hom_ext fun m => by
      rw [SVec.comp_apply, SVec.comp_apply, rightUnitorInv_apply, rightUnitorInv_apply, lact_btmul])
    (fun b => SVec.hom_ext fun m => by
      rw [SVec.comp_apply, SVec.comp_apply, rightUnitorInv_apply, rightUnitorInv_apply, ract_btmul,
        btmul_ract_lact, regular_lact_apply, regular_ract_apply, one_mul, mul_one])

/-- **The right unitor** `M ⊗_B B ≅ M`, `m ⊗ b ↦ m b`, an even isomorphism of
superbimodules. -/
def rightUnitor : tensor M (regular ℬ) ≅ M where
  hom := ⟨rightUnitorHom M, isHom_rightUnitorHom M⟩
  inv := ⟨rightUnitorInv M, isHom_rightUnitorInv M⟩
  hom_inv_id := hom_ext (rightUnitorSVecIso M).hom_inv_id
  inv_hom_id := hom_ext (rightUnitorSVecIso M).inv_hom_id

@[simp] theorem rightUnitor_hom_btmul (m : M.toSVec) (b : B) :
    (rightUnitor M).hom.1 (btmul M (regular ℬ) m b) = M.ract b m :=
  rightUnitorHom_btmul M m b

@[simp] theorem rightUnitor_inv_apply (m : M.toSVec) :
    (rightUnitor M).inv.1 m = btmul M (regular ℬ) m (1 : B) := rfl

theorem rightUnitor_hom_mem : (rightUnitor M).hom ∈ parity (R := k) (tensor M (regular ℬ)) M 0 :=
  mem_parity_iff.2 (rightUnitorHom_mem M)

end RightUnitor

section UnitorProps

variable [GradedAlgebra 𝒜] [GradedAlgebra ℬ] (M : SuperBimodule 𝒜 ℬ)

theorem leftUnitor_hom_mem : (leftUnitor M).hom ∈ parity (R := k) (tensor (regular 𝒜) M) M 0 :=
  mem_parity_iff.2 (leftUnitorHom_mem M)

/-! ### Naturality of the unitors and the triangle identity -/

theorem leftUnitor_naturality {M' : SuperBimodule 𝒜 ℬ} (f : M ⟶ M') :
    whiskerLeft (regular 𝒜) f ≫ (leftUnitor M').hom = (leftUnitor M).hom ≫ f := by
  refine Supercategory.induction_on (R := k) f ?_ (fun q f hf => ?_) (fun f f' hf hf' => ?_)
  · rw [whiskerLeft_zero, Limits.zero_comp, Limits.comp_zero]
  · refine hom_ext (tensor_hom_ext_homogeneous (regular 𝒜) M fun p r a m ha _ => ?_)
    have h := congrArg (fun φ : M.toSVec ⟶ M'.toSVec => φ m)
      (((isHom_iff_of_mem (mem_parity_iff.1 hf)).1 f.2).1 p a ((mem_regularSVec_part_iff 𝒜).1 ha))
    simp only [SVec.comp_apply, SVec.smul_apply] at h
    rw [comp_val, comp_val, SVec.comp_apply, SVec.comp_apply, whiskerLeft_btmul _ f hf ha,
      SVec.hom_map_smul, leftUnitor_hom_btmul, leftUnitor_hom_btmul, h]
  · rw [whiskerLeft_add, Preadditive.add_comp, hf, hf', Preadditive.comp_add]

omit [GradedAlgebra 𝒜] in
theorem rightUnitor_naturality {M' : SuperBimodule 𝒜 ℬ} (f : M ⟶ M') :
    whiskerRight f (regular ℬ) ≫ (rightUnitor M').hom = (rightUnitor M).hom ≫ f :=
  hom_ext (tensor_hom_ext M (regular ℬ) fun m b => by
    have h := congrArg (fun φ : M.toSVec ⟶ M'.toSVec => φ m) (f.2.2 b)
    simp only [SVec.comp_apply] at h
    rw [comp_val, comp_val, SVec.comp_apply, SVec.comp_apply, whiskerRight_btmul,
      rightUnitor_hom_btmul, rightUnitor_hom_btmul, h])

omit [GradedAlgebra 𝒜] in
/-- **The triangle identity** for balanced tensor products. -/
theorem triangle [GradedAlgebra 𝒞] (N : SuperBimodule ℬ 𝒞) :
    (assoc M (regular ℬ) N).hom ≫ whiskerLeft M (leftUnitor N).hom =
      whiskerRight (rightUnitor M).hom N :=
  hom_ext (tensor_hom_ext_left M (regular ℬ) N fun m b n => by
    rw [comp_val, SVec.comp_apply, assoc_hom_btmul, whiskerLeft_btmul_even M _ (leftUnitor_hom_mem N),
      leftUnitor_hom_btmul, whiskerRight_btmul, rightUnitor_hom_btmul, btmul_ract_lact])

end UnitorProps

end SuperBimodule

end StringDiagrams

end
