import StringDiagrams.Super.Superalgebra
import StringDiagrams.Super.Pi

/-!
# Superbimodules

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Example 1.2(iii) and Example 1.8.

Let `A`, `B` be superalgebras (`k`-algebras graded by `ZMod 2`, Mathlib's `GradedAlgebra`).
An `(A, B)`-superbimodule is a superspace `V` with an even linear map `A ⊗ V ⊗ B → V` making
`V` an `(A, B)`-bimodule. We record it by the left and right actions
`lact : A → End(V)`, `ract : B → End(V)` (`lact (a a') = lact a ∘ lact a'`,
`ract (b b') = ract b' ∘ ract b`, commuting with each other), where evenness of the action map
says that `lact a` and `ract b` have the parities of `a` and `b` (`SuperBimodule`).

A superbimodule homomorphism is a linear map `f : V → W` with
`m_W ∘ (1_A ⊗ f ⊗ 1_B) = f ∘ m_V`; with the Koszul sign rule this says
`f(a v b) = (-1)^{|f||a|} a f(v) b` for homogeneous `f` and `a`. For inhomogeneous `f` it says
`f ∘ lact a = lact a ∘ (f₀ + (-1)^{|a|} f₁)` for homogeneous `a`, and `f ∘ ract b = ract b ∘ f`
(`SuperBimodule.IsHom`, with `Supercategory.twist`).

## Main results

* `SuperBimodule.instSupercategory`: **Example 1.2(iii)**, `A-SMod-B` is a supercategory (the
  parity components of a superbimodule homomorphism are superbimodule homomorphisms:
  `IsHom.proj`).
* `SuperBimodule.instPiSupercategory`: **Example 1.8**, `A-SMod-B` is a Π-supercategory, with
  `Π V` the superspace `V` with the opposite grading and actions `a · v · b := (-1)^{|a|} a v b`
  (`piObj`, `piObj_lact_of_mem`), and `ζ_V : Π V → V` the identity function (`ζIso`).

The monoidal structure on `A-SMod-A` of Examples 1.5(i) and 1.13(i) (tensor product over `A`)
is formalized only for `A = k`, where `k-SMod-k` is `SVec k`
(`StringDiagrams.Super.SVec`): Mathlib's tensor product of modules is over a commutative ring,
and the balanced tensor product of bimodules over a noncommutative superalgebra is not
available.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory

universe u v v'

variable {k : Type u} [CommRing k] {A : Type v} [Ring A] [Algebra k A] {B : Type v'} [Ring B]
  [Algebra k B]

variable (𝒜 : ZMod 2 → Submodule k A) (ℬ : ZMod 2 → Submodule k B)

/-- An `(A, B)`-superbimodule (Brundan–Ellis, Example 1.2(iii)): a superspace with left and
right actions whose action maps are even. -/
structure SuperBimodule where
  /-- The underlying superspace. -/
  toSVec : SVec k
  /-- The left action `v ↦ a v`. -/
  lact : A →ₗ[k] (toSVec ⟶ toSVec)
  /-- The right action `v ↦ v b`. -/
  ract : B →ₗ[k] (toSVec ⟶ toSVec)
  lact_one : lact 1 = 𝟙 toSVec
  lact_mul : ∀ a a' : A, lact (a * a') = lact a' ≫ lact a
  ract_one : ract 1 = 𝟙 toSVec
  ract_mul : ∀ b b' : B, ract (b * b') = ract b ≫ ract b'
  lact_ract : ∀ (a : A) (b : B), lact a ≫ ract b = ract b ≫ lact a
  lact_mem : ∀ (p : ZMod 2) (a : A), a ∈ 𝒜 p → lact a ∈ parity (R := k) toSVec toSVec p
  ract_mem : ∀ (p : ZMod 2) (b : B), b ∈ ℬ p → ract b ∈ parity (R := k) toSVec toSVec p

namespace SuperBimodule

variable {𝒜 ℬ}

/-- A linear map `f : V → W` is a superbimodule homomorphism:
`f(a v b) = (-1)^{|f||a|} a f(v) b`, i.e. `f ∘ lact a = lact a ∘ (f₀ + (-1)^{|a|} f₁)` for
homogeneous `a`, and `f ∘ ract b = ract b ∘ f`. -/
def IsHom (V W : SuperBimodule 𝒜 ℬ) (f : V.toSVec ⟶ W.toSVec) : Prop :=
  (∀ (p : ZMod 2) (a : A), a ∈ 𝒜 p → V.lact a ≫ f = twist k p f ≫ W.lact a) ∧
    ∀ b : B, V.ract b ≫ f = f ≫ W.ract b

/-- For homogeneous `f`, the condition is `f(a v b) = (-1)^{|f||a|} a f(v) b`. -/
theorem isHom_iff_of_mem {V W : SuperBimodule 𝒜 ℬ} {q : ZMod 2} {f : V.toSVec ⟶ W.toSVec}
    (hf : f ∈ parity (R := k) V.toSVec W.toSVec q) :
    IsHom V W f ↔ (∀ (p : ZMod 2) (a : A), a ∈ 𝒜 p →
      V.lact a ≫ f = sign k (p * q) • (f ≫ W.lact a)) ∧
      ∀ b : B, V.ract b ≫ f = f ≫ W.ract b := by
  simp only [IsHom, twist_of_mem _ hf, Linear.smul_comp]

variable (V W : SuperBimodule 𝒜 ℬ)

/-- The superbimodule homomorphisms, a submodule of all linear maps. -/
def homSubmodule : Submodule k (V.toSVec ⟶ W.toSVec) where
  carrier := {f | IsHom V W f}
  add_mem' {f g} hf hg := ⟨fun p a ha => by
      rw [Preadditive.comp_add, hf.1 p a ha, hg.1 p a ha, map_add, Preadditive.add_comp],
    fun b => by rw [Preadditive.comp_add, hf.2, hg.2, Preadditive.add_comp]⟩
  zero_mem' := ⟨fun p a _ => by simp, fun b => by simp⟩
  smul_mem' r f hf := ⟨fun p a ha => by
      rw [Linear.comp_smul, hf.1 p a ha, map_smul, Linear.smul_comp],
    fun b => by rw [Linear.comp_smul, hf.2, Linear.smul_comp]⟩

variable {V W}

theorem isHom_id (V : SuperBimodule 𝒜 ℬ) : IsHom V V (𝟙 V.toSVec) :=
  ⟨fun p a _ => by rw [twist_id, Category.comp_id, Category.id_comp],
    fun b => by rw [Category.comp_id, Category.id_comp]⟩

theorem IsHom.comp {U V W : SuperBimodule 𝒜 ℬ} {f : U.toSVec ⟶ V.toSVec}
    {g : V.toSVec ⟶ W.toSVec} (hf : IsHom U V f) (hg : IsHom V W g) : IsHom U W (f ≫ g) :=
  ⟨fun p a ha => by
      rw [← Category.assoc, hf.1 p a ha, Category.assoc, hg.1 p a ha, twist_comp,
        Category.assoc],
    fun b => by rw [← Category.assoc, hf.2, Category.assoc, hg.2, Category.assoc]⟩

/-! ## The supercategory `A-SMod-B` -/

instance : Category (SuperBimodule 𝒜 ℬ) where
  Hom V W := homSubmodule V W
  id V := ⟨𝟙 _, isHom_id V⟩
  comp f g := ⟨f.1 ≫ g.1, IsHom.comp f.2 g.2⟩
  id_comp f := Subtype.ext (Category.id_comp f.1)
  comp_id f := Subtype.ext (Category.comp_id f.1)
  assoc f g h := Subtype.ext (Category.assoc f.1 g.1 h.1)

@[ext] theorem hom_ext {V W : SuperBimodule 𝒜 ℬ} {f g : V ⟶ W} (h : f.1 = g.1) : f = g :=
  Subtype.ext h

@[simp] theorem id_val (V : SuperBimodule 𝒜 ℬ) : (𝟙 V : V ⟶ V).1 = 𝟙 V.toSVec := rfl

@[simp] theorem comp_val {U V W : SuperBimodule 𝒜 ℬ} (f : U ⟶ V) (g : V ⟶ W) :
    (f ≫ g).1 = f.1 ≫ g.1 := rfl

instance : Preadditive (SuperBimodule 𝒜 ℬ) where
  homGroup V W := inferInstanceAs (AddCommGroup (homSubmodule V W))
  add_comp _ _ _ f f' g := Subtype.ext (Preadditive.add_comp _ _ _ f.1 f'.1 g.1)
  comp_add _ _ _ f g g' := Subtype.ext (Preadditive.comp_add _ _ _ f.1 g.1 g'.1)

instance : Linear k (SuperBimodule 𝒜 ℬ) where
  homModule V W := inferInstanceAs (Module k (homSubmodule V W))
  smul_comp _ _ _ r f g := Subtype.ext (Linear.smul_comp _ _ _ r f.1 g.1)
  comp_smul _ _ _ f r g := Subtype.ext (Linear.comp_smul _ _ _ f.1 r g.1)

@[simp] theorem add_val {V W : SuperBimodule 𝒜 ℬ} (f g : V ⟶ W) : (f + g).1 = f.1 + g.1 := rfl

@[simp] theorem smul_val {V W : SuperBimodule 𝒜 ℬ} (r : k) (f : V ⟶ W) : (r • f).1 = r • f.1 :=
  rfl

section

variable [GradedAlgebra ℬ]

/-- The right action commutes with the parity components of a homomorphism. -/
theorem IsHom.ract_comp_proj {f : V.toSVec ⟶ W.toSVec} (hf : IsHom V W f) (q : ZMod 2) (b : B) :
    V.ract b ≫ proj k q f = proj k q f ≫ W.ract b := by
  refine DirectSum.Decomposition.inductionOn ℬ (motive := fun b => V.ract b ≫ proj k q f =
    proj k q f ≫ W.ract b) (by simp) (fun {r} b => ?_) (fun b b' h h' => ?_) b
  · have h := congrArg (proj k (r + q)) (hf.2 b)
    rwa [proj_comp_of_mem_left q (V.ract_mem r b b.2), add_comm,
      proj_comp_of_mem_right q f (W.ract_mem r b b.2)] at h
  · simp only [map_add, Preadditive.add_comp, Preadditive.comp_add, h, h']

/-- The parity components of a superbimodule homomorphism are superbimodule homomorphisms. -/
theorem IsHom.proj {f : V.toSVec ⟶ W.toSVec} (hf : IsHom V W f) (q : ZMod 2) :
    IsHom V W (proj k q f) := by
  refine ⟨fun p a ha => ?_, hf.ract_comp_proj q⟩
  have h := congrArg (Supercategory.proj k (p + q)) (hf.1 p a ha)
  rwa [proj_comp_of_mem_left q (V.lact_mem p a ha), add_comm,
    proj_comp_of_mem_right q _ (W.lact_mem p a ha), proj_twist,
    ← twist_of_mem p (proj_mem q f)] at h

end

section

variable [GradedAlgebra ℬ]

/-- **Brundan–Ellis, Example 1.2(iii).** `A-SMod-B` is a supercategory: a superbimodule
homomorphism has parity `p` if its underlying linear map does. -/
instance instSupercategory : Supercategory k (SuperBimodule 𝒜 ℬ) where
  parity V W p := (parity (R := k) V.toSVec W.toSVec p).comap (homSubmodule V W).subtype
  isInternal V W := by
    rw [DirectSum.isInternal_submodule_iff_isCompl _ (i := 0) (j := 1) (by decide)
      (by ext p; rcases parity_eq_zero_or_one p with rfl | rfl <;> simp)]
    constructor
    · rw [Submodule.disjoint_def]
      intro f h0 h1
      apply Subtype.ext
      have h0' : f.1 ∈ parity (R := k) V.toSVec W.toSVec 0 := h0
      have h1' : f.1 ∈ parity (R := k) V.toSVec W.toSVec 1 := h1
      rw [← proj_of_mem h0', proj_of_mem_ne h1' (by decide)]
      rfl
    · rw [codisjoint_iff, eq_top_iff]
      intro f _
      have e : f = ⟨proj k 0 f.1, f.2.proj 0⟩ + ⟨proj k 1 f.1, f.2.proj 1⟩ :=
        Subtype.ext (proj_add_proj f.1).symm
      rw [e]
      exact Submodule.add_mem_sup (Submodule.mem_comap.2 (proj_mem 0 f.1))
        (Submodule.mem_comap.2 (proj_mem 1 f.1))
  id_mem V := Submodule.mem_comap.2 (Supercategory.id_mem (C := SVec k) V.toSVec)
  comp_mem hf hg := Submodule.mem_comap.2
    (Supercategory.comp_mem (C := SVec k) (Submodule.mem_comap.1 hf) (Submodule.mem_comap.1 hg))

theorem mem_parity_iff {V W : SuperBimodule 𝒜 ℬ} {p : ZMod 2} {f : V ⟶ W} :
    f ∈ parity (R := k) V W p ↔ f.1 ∈ parity (R := k) V.toSVec W.toSVec p := by
  exact Submodule.mem_comap

end

variable [GradedAlgebra 𝒜]

/-! ## The parity shift (Example 1.8) -/

theorem twist_lact_comp_ract (V : SuperBimodule 𝒜 ℬ) (a : A) (b : B) :
    twist k 1 (V.lact a) ≫ V.ract b = V.ract b ≫ twist k 1 (V.lact a) := by
  refine DirectSum.Decomposition.inductionOn 𝒜 (motive := fun a =>
    twist k 1 (V.lact a) ≫ V.ract b = V.ract b ≫ twist k 1 (V.lact a)) (by simp)
    (fun {r} a => ?_) (fun a a' h h' => ?_) a
  · dsimp only
    rw [twist_one_of_mem (V.lact_mem r a a.2), Linear.smul_comp, Linear.comp_smul, V.lact_ract]
  · simp only [map_add, Preadditive.add_comp, Preadditive.comp_add, h, h']

/-- **Brundan–Ellis, Example 1.8.** The superbimodule `Π V`: the superspace `V` with the
opposite grading, with actions `a · v · b := (-1)^{|a|} a v b`. -/
def piObj (V : SuperBimodule 𝒜 ℬ) : SuperBimodule 𝒜 ℬ where
  toSVec := SVec.piObj V.toSVec
  lact := SVec.piHom ∘ₗ twist k 1 ∘ₗ V.lact
  ract := SVec.piHom ∘ₗ V.ract
  lact_one := by simp [V.lact_one]
  lact_mul a a' := by simp [V.lact_mul, twist_comp]
  ract_one := by simp [V.ract_one]
  ract_mul b b' := by simp [V.ract_mul]
  lact_ract a b := by
    simp only [LinearMap.coe_comp, Function.comp_apply, ← SVec.piHom_comp]
    rw [twist_lact_comp_ract]
  lact_mem p a ha := SVec.piHom_mem_iff.2 (twist_mem 1 (V.lact_mem p a ha))
  ract_mem p b hb := SVec.piHom_mem_iff.2 (V.ract_mem p b hb)

/-- **Example 1.8.** In `Π V`, `a · v = (-1)^{|a|} a v`. -/
theorem piObj_lact_of_mem (V : SuperBimodule 𝒜 ℬ) {p : ZMod 2} {a : A} (ha : a ∈ 𝒜 p) :
    (piObj V).lact a = SVec.piHom (sign k p • V.lact a) := by
  change SVec.piHom (twist k 1 (V.lact a)) = _
  rw [twist_one_of_mem (V.lact_mem p a ha)]

theorem piObj_ract (V : SuperBimodule 𝒜 ℬ) (b : B) : (piObj V).ract b = SVec.piHom (V.ract b) :=
  rfl

theorem isHom_ζ (V : SuperBimodule 𝒜 ℬ) : IsHom (piObj V) V (SVec.ζIso V.toSVec).hom := by
  refine ⟨fun p a ha => ?_, fun b => rfl⟩
  have hζ : (SVec.ζIso V.toSVec).hom ∈ parity (R := k) (piObj V).toSVec V.toSVec 1 :=
    SVec.ζIso_hom_mem _
  rw [piObj_lact_of_mem V ha, twist_of_mem p hζ, mul_one, Linear.smul_comp, map_smul]
  rfl

theorem isHom_ζ_inv (V : SuperBimodule 𝒜 ℬ) : IsHom V (piObj V) (SVec.ζIso V.toSVec).inv := by
  refine ⟨fun p a ha => ?_, fun b => rfl⟩
  have hζ : (SVec.ζIso V.toSVec).inv ∈ parity (R := k) V.toSVec (piObj V).toSVec 1 :=
    inv_mem _ (SVec.ζIso_hom_mem _)
  rw [piObj_lact_of_mem V ha, twist_of_mem p hζ, mul_one,
    Linear.smul_comp, map_smul, Linear.comp_smul, smul_smul, sign_mul_self, one_smul]
  rfl

/-- The odd isomorphism `ζ_V : Π V → V`, the identity function. -/
def ζIso (V : SuperBimodule 𝒜 ℬ) : piObj V ≅ V where
  hom := ⟨(SVec.ζIso V.toSVec).hom, isHom_ζ V⟩
  inv := ⟨(SVec.ζIso V.toSVec).inv, isHom_ζ_inv V⟩
  hom_inv_id := Subtype.ext (SVec.ζIso V.toSVec).hom_inv_id
  inv_hom_id := Subtype.ext (SVec.ζIso V.toSVec).inv_hom_id

variable [GradedAlgebra ℬ]

theorem ζIso_hom_mem (V : SuperBimodule 𝒜 ℬ) :
    (ζIso V).hom ∈ parity (R := k) (piObj V) V 1 :=
  SVec.ζIso_hom_mem V.toSVec

/-- **Brundan–Ellis, Example 1.8.** `A-SMod-B` is a Π-supercategory, with `ζ_V : Π V → V` the
identity function. -/
instance instPiSupercategory : PiSupercategory k (SuperBimodule 𝒜 ℬ) :=
  PiSupercategory.ofIso piObj ζIso ζIso_hom_mem

/-- **Example 1.8.** `Π f = (-1)^{|f|} f` on underlying linear maps. -/
theorem pi_map_of_mem {V W : SuperBimodule 𝒜 ℬ} {p : ZMod 2} {f : V ⟶ W}
    (hf : f ∈ parity (R := k) V W p) :
    SVec.toLinearMap ((PiSupercategory.pi (R := k)).map f).1 = sign k p • SVec.toLinearMap f.1 := by
  change SVec.toLinearMap (twist k 1 f).1 = _
  rw [twist_of_mem 1 hf, one_mul]
  rfl

/-- **Example 1.8.** `ξ_V : Π² V → V` is minus the identity function. -/
theorem ξ_hom (V : SuperBimodule 𝒜 ℬ) :
    SVec.toLinearMap (PiSupercategory.ξ (R := k) V).hom.1 =
      (-LinearMap.id : V.toSVec.carrier →ₗ[k] V.toSVec.carrier) := by
  rw [PiSupercategory.ξ_hom_eq_neg]
  rfl

end SuperBimodule

end StringDiagrams
