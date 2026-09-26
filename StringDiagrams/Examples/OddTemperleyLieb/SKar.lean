import StringDiagrams.Examples.OddTemperleyLieb.Decomposition
import StringDiagrams.Examples.OddTemperleyLieb.Splitting
import StringDiagrams.Super.SKarMonoidal

/-!
# The super Karoubi envelope of `STL(δ)` (Theorem A.3 = Theorem 1.18)

J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, Theorem A.3.

Let `k` be a field, `q ∈ k^×` not a root of unity and `δ = -(q - q⁻¹)`. In
`SKar(STL(δ)) = Kar(Mat(STL(δ)̲_π))` let `P n a := (f_n)^a_a` be the object given by the
Jones–Wenzl projector `f_n` on `Πᵃ n` (`jwObj`).

* `hom_jwObj_eq_zero`, `jwObj_isSchur`, `id_jwObj_ne_zero`: `Hom(P m a, P n b) = 0` unless
  `(m, a) = (n, b)`, and `End(P n a) = k · 1 ≠ 0`. So the `P n a` are pairwise non-isomorphic
  simple objects in the sense that their endomorphism algebras are `k`.
* `exists_iso_bsum_jwObj`: **every object of `SKar(STL(δ))` is isomorphic to a finite direct
  sum of objects `P n a`.**

These two facts are the semisimplicity of `SKar(STL(δ))` as an additive category: it is a
Krull–Schmidt category whose indecomposable objects are the `P n a`, all of which have
endomorphism algebra `k`, with no nonzero morphisms between non-isomorphic ones. (Mathlib has
no notion of a semisimple abelian category, and no abelian structure on idempotent
completions, so the statement "`SKar(STL(δ))` is a semisimple abelian category" is not
formalized as such; see the module `KZero` for the Grothendieck ring.)
-/

noncomputable section

namespace StringDiagrams.OddTemperleyLieb

open CategoryTheory Limits Idempotents Supercategory
open Rep (delta)

instance instSupercategory (R : Type*) [CommRing R] (δ : R) : Supercategory R (STL R δ) :=
  supercategory R δ

instance instMonoidalSupercategory (R : Type*) [CommRing R] (δ : R) :
    MonoidalSupercategory R (STL R δ) :=
  monoidalSupercategory R δ

variable {k : Type*} [Field k] (q : kˣ)

local notation "δq" => delta q

/-- The underlying category of the Π-envelope of `STL(δ)`. -/
abbrev DD : Type _ := Underlying k (Envelope k (STL k δq))

/-- The object `Πᵃ n`. -/
def genD (a : ZMod 2) (n : ℕ) : DD q := ⟨⟨a, X k δq n⟩⟩

theorem parity_X (m n : ℕ) (p : ZMod 2) :
    parity (R := k) (X k δq m) (X k δq n) p =
      (pres k δq).homDeg (Presentation.parityDeg sig) (strands m) (strands n) p := rfl

variable {q} in
/-- The even morphism `Πᵃ m → Πᵇ n` given by a morphism of parity `a + b`. -/
def homD {a b : ZMod 2} {m n : ℕ} (f : X k δq m ⟶ X k δq n)
    (hf : f ∈ (pres k δq).homDeg (Presentation.parityDeg sig) (strands m) (strands n) (a + b)) :
    genD q a m ⟶ genD q b n :=
  ⟨Envelope.ofHom f, by
    show f ∈ parity (R := k) (X k δq m) (X k δq n) (0 + (a + b))
    rwa [zero_add]⟩

@[simp] theorem homD_val {a b : ZMod 2} {m n : ℕ} (f : X k δq m ⟶ X k δq n) (hf) :
    Envelope.toHom (homD (q := q) (a := a) (b := b) f hf).1 = f := rfl

theorem homD_comp {a b c : ZMod 2} {l m n : ℕ} (f : X k δq l ⟶ X k δq m) (g : X k δq m ⟶ X k δq n)
    (hf : f ∈ (pres k δq).homDeg (Presentation.parityDeg sig) (strands l) (strands m) (a + b))
    (hg : g ∈ (pres k δq).homDeg (Presentation.parityDeg sig) (strands m) (strands n) (b + c))
    (hfg : f ≫ g ∈ (pres k δq).homDeg (Presentation.parityDeg sig) (strands l) (strands n) (a + c)) :
    homD f hf ≫ homD g hg = homD (q := q) (f ≫ g) hfg := rfl

theorem homD_ext {a b : ZMod 2} {m n : ℕ} {f g : genD q a m ⟶ genD q b n}
    (h : Envelope.toHom f.1 = Envelope.toHom g.1) : f = g :=
  Underlying.hom_ext h

/-- The parity of the underlying morphism of a morphism `Πᵃ m → Πᵇ n`. -/
theorem val_mem_parity {a b : ZMod 2} {m n : ℕ} (f : genD q a m ⟶ genD q b n) :
    Envelope.toHom f.1 ∈
      (pres k δq).homDeg (Presentation.parityDeg sig) (strands m) (strands n) (a + b) := by
  have := f.2
  change Envelope.toHom f.1 ∈ parity (R := k) (X k δq m) (X k δq n) (0 + (a + b)) at this
  rwa [zero_add] at this

theorem jw_mem_parity (n : ℕ) (a : ZMod 2) :
    jw q n ∈ (pres k δq).homDeg (Presentation.parityDeg sig) (strands n) (strands n) (a + a) := by
  rw [ZModModule.add_self a, show (0 : ZMod 2) = 0 from rfl]
  exact evenSpan_le_parity _ _ (jw_mem_evenSpan q n)

variable (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1)
include hq

/-- The object `P n a = (f_n)^a_a` of `SKar(STL(δ))`. -/
def jwObj (n : ℕ) (a : ZMod 2) : SKar k (STL k δq) where
  X := (Mat_.embedding (DD q)).obj (genD q a n)
  p := (Mat_.embedding (DD q)).map (homD (jw q n) (jw_mem_parity q n a))
  idem := by
    rw [← Functor.map_comp]
    congr 1
    exact Underlying.hom_ext (jw_idem hq n)

omit hq in
/-- A morphism in both parities is zero. -/
theorem eq_zero_of_mem_both {m n : ℕ} {f : X k δq m ⟶ X k δq n}
    (h0 : f ∈ (pres k δq).homDeg (Presentation.parityDeg sig) (strands m) (strands n) 0)
    (h1 : f ∈ (pres k δq).homDeg (Presentation.parityDeg sig) (strands m) (strands n) 1) :
    f = 0 := by
  have e1 := proj_of_mem (R := k) (C := STL k δq) (X := X k δq m) (Y := X k δq n) h1
  have e0 := proj_of_mem_ne (R := k) (C := STL k δq) (X := X k δq m) (Y := X k δq n) h0
    (p := 1) (by decide)
  rw [← e1, e0]

variable {q} in
/-- The morphism of `STL(δ)` underlying a morphism `P m a ⟶ P n b`. -/
def mor {m n : ℕ} {a b : ZMod 2} (φ : jwObj q hq m a ⟶ jwObj q hq n b) : X k δq m ⟶ X k δq n :=
  Envelope.toHom (φ.f PUnit.unit PUnit.unit).1

omit hq in
theorem mat_comp_single {x y z : DD q} (f : (Mat_.embedding (DD q)).obj x ⟶ (Mat_.embedding (DD q)).obj y)
    (g : (Mat_.embedding (DD q)).obj y ⟶ (Mat_.embedding (DD q)).obj z) :
    (f ≫ g) PUnit.unit PUnit.unit = f PUnit.unit PUnit.unit ≫ g PUnit.unit PUnit.unit := by
  rw [Mat_.comp_apply]
  simp

theorem mor_comp {l m n : ℕ} {a b c : ZMod 2} (φ : jwObj q hq l a ⟶ jwObj q hq m b)
    (ψ : jwObj q hq m b ⟶ jwObj q hq n c) : mor hq (φ ≫ ψ) = mor hq φ ≫ mor hq ψ := by
  simp only [mor, Karoubi.comp_f, mat_comp_single, Underlying.comp_val, Envelope.toHom_comp]

theorem mor_id (n : ℕ) (a : ZMod 2) : mor hq (𝟙 (jwObj q hq n a)) = jw q n := rfl

theorem mor_eq {m n : ℕ} {a b : ZMod 2} (φ : jwObj q hq m a ⟶ jwObj q hq n b) :
    mor hq φ = jw q m ≫ mor hq φ ≫ jw q n := by
  have := congrArg (fun f => Envelope.toHom (f PUnit.unit PUnit.unit).1) φ.comm
  simpa only [mat_comp_single, Underlying.comp_val, Envelope.toHom_comp] using this

theorem mor_mem_parity {m n : ℕ} {a b : ZMod 2} (φ : jwObj q hq m a ⟶ jwObj q hq n b) :
    mor hq φ ∈ (pres k δq).homDeg (Presentation.parityDeg sig) (strands m) (strands n) (a + b) :=
  val_mem_parity q (φ.f PUnit.unit PUnit.unit)

theorem jwObj_hom_ext {m n : ℕ} {a b : ZMod 2} {φ ψ : jwObj q hq m a ⟶ jwObj q hq n b}
    (h : mor hq φ = mor hq ψ) : φ = ψ := by
  apply Karoubi.hom_ext
  apply Mat_.hom_ext
  rintro ⟨⟩ ⟨⟩
  exact Underlying.hom_ext h

theorem mor_zero {m n : ℕ} {a b : ZMod 2} : mor hq (0 : jwObj q hq m a ⟶ jwObj q hq n b) = 0 := rfl

theorem mor_smul {m n : ℕ} {a b : ZMod 2} (c : k) (φ : jwObj q hq m a ⟶ jwObj q hq n b) :
    mor hq (c • φ) = c • mor hq φ := rfl

/-- **`Hom(P m a, P n b) = 0` unless `(m, a) = (n, b)`.** -/
theorem hom_jwObj_eq_zero {m n : ℕ} {a b : ZMod 2} (h : m ≠ n ∨ a ≠ b)
    (φ : jwObj q hq m a ⟶ jwObj q hq n b) : φ = 0 := by
  apply jwObj_hom_ext
  rw [mor_zero]
  rcases eq_or_ne m n with rfl | hmn
  · have hab : a ≠ b := h.resolve_left (not_not.mpr rfl)
    obtain ⟨c, hc⟩ := jw_comp_comp_jw_self hq (mor hq φ)
    rw [← mor_eq] at hc
    refine eq_zero_of_mem_both q ?_ ?_
    · rw [hc]; exact Submodule.smul_mem _ _ (by simpa using jw_mem_parity q m 0)
    · have hab1 : a + b = 1 := by
        clear hc h φ
        revert a b; decide
      have := mor_mem_parity q hq φ
      rwa [hab1] at this
  · rw [mor_eq]; exact jw_comp_comp_jw_of_ne hq hmn _

/-- **`End(P n a) = k`.** -/
theorem jwObj_isSchur (n : ℕ) (a : ZMod 2) : IsSchur (k := k) (jwObj q hq n a) := by
  intro φ
  obtain ⟨c, hc⟩ := jw_comp_comp_jw_self hq (mor hq φ)
  rw [← mor_eq] at hc
  exact ⟨c, jwObj_hom_ext q hq (by rw [hc, mor_smul, mor_id])⟩

/-- `P n a ≠ 0`. -/
theorem id_jwObj_ne_zero (n : ℕ) (a : ZMod 2) : 𝟙 (jwObj q hq n a) ≠ 0 := by
  intro h
  have := congrArg (mor hq) h
  rw [mor_id, mor_zero] at this
  exact jw_ne_zero hq n this

/-! ## Decomposing the objects `Πᵃ m` -/

omit hq in
theorem wR1_mem_homDeg {m n : ℕ} {p : ZMod 2} {f : X k δq m ⟶ X k δq n}
    (hf : f ∈ (pres k δq).homDeg (Presentation.parityDeg sig) (strands m) (strands n) p) :
    wR1 k δq f ∈ (pres k δq).homDeg (Presentation.parityDeg sig) (strands (m + 1))
      (strands (n + 1)) p := by
  have h := Presentation.comp_mem_homDeg (Presentation.eqToHom_mem_homDeg (P := pres k δq)
    (Presentation.parityDeg sig) (congrArg (pres k δq).obj (strands_tensor_one m).symm))
    (Presentation.comp_mem_homDeg ((pres k δq).wR_mem (Presentation.parityDeg sig) hf (strands 1))
      (Presentation.eqToHom_mem_homDeg (P := pres k δq) (Presentation.parityDeg sig)
        (congrArg (pres k δq).obj (strands_tensor_one n))))
  simpa using h

variable {q} in
/-- A piece of `m`: a Jones–Wenzl projector `f_n` with maps `α : m → n`, `β : n → m` of parity
`b`, absorbed by `f_n`. -/
structure DPiece (m : ℕ) where
  n : ℕ
  b : ZMod 2
  α : X k δq m ⟶ X k δq n
  β : X k δq n ⟶ X k δq m
  hα : α ∈ (pres k δq).homDeg (Presentation.parityDeg sig) (strands m) (strands n) b
  hβ : β ∈ (pres k δq).homDeg (Presentation.parityDeg sig) (strands n) (strands m) b
  hαj : α ≫ jw q n = α
  hjβ : jw q n ≫ β = β

/-- Splitting a piece of `m` into pieces of `m + 1`: `f_n ⊗ 1 = f_{n+1} + g_{n+1}` with
`g_{n+1} ≅ Π f_{n-1}`. -/
def splitPiece {m : ℕ} : DPiece (q := q) m → List (DPiece (q := q) (m + 1))
  | ⟨0, b, α, β, hα, hβ, hαj, hjβ⟩ =>
    [⟨1, b, wR1 k δq α, wR1 k δq β, wR1_mem_homDeg q hα, wR1_mem_homDeg q hβ,
      by rw [jw_one, Category.comp_id], by rw [jw_one, Category.id_comp]⟩]
  | ⟨N + 1, b, α, β, hα, hβ, hαj, hjβ⟩ =>
    [⟨N + 2, b, wR1 k δq α ≫ jw q (N + 2), jw q (N + 2) ≫ wR1 k δq β,
      by simpa using Presentation.comp_mem_homDeg (wR1_mem_homDeg q hα) (jw_mem_parity q (N + 2) 0),
      by simpa using Presentation.comp_mem_homDeg (jw_mem_parity q (N + 2) 0) (wR1_mem_homDeg q hβ),
      by rw [Category.assoc, jw_idem hq], by rw [← Category.assoc, jw_idem hq]⟩,
     ⟨N, b + 1, wR1 k δq α ≫ vDec q N, uDec q N ≫ wR1 k δq β,
      Presentation.comp_mem_homDeg (wR1_mem_homDeg q hα) (vDec_mem_parity N),
      by simpa [add_comm] using Presentation.comp_mem_homDeg (uDec_mem_parity N) (wR1_mem_homDeg q hβ),
      by rw [Category.assoc, vDec_comp_jw hq], by rw [← Category.assoc, jw_comp_uDec hq]⟩]

/-- The pieces of `m`. -/
def pieces : (m : ℕ) → List (DPiece (q := q) m)
  | 0 => [⟨0, 0, 𝟙 _, 𝟙 _, by simpa using jw_mem_parity q 0 0, by simpa using jw_mem_parity q 0 0,
      by rw [jw_zero, Category.comp_id], by rw [jw_zero, Category.id_comp]⟩]
  | m + 1 => (pieces m).flatMap (splitPiece q hq)

omit hq in
theorem wR1_list_sum {a b : ℕ} (l : List (X k δq a ⟶ X k δq b)) :
    wR1 k δq l.sum = (l.map (wR1 k δq)).sum := by
  induction l with
  | nil => simp [wR1_zero]
  | cons x l ih => simp [wR1_add, ih]

theorem splitPiece_sum {m : ℕ} (p : DPiece (q := q) m) :
    ((splitPiece q hq p).map fun p' => p'.α ≫ p'.β).sum = wR1 k δq (p.α ≫ p.β) := by
  obtain ⟨n, b, α, β, hα, hβ, hαj, hjβ⟩ := p
  cases n with
  | zero => simp [splitPiece, wR1_comp]
  | succ N =>
    simp only [splitPiece, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    have e : (wR1 k δq α ≫ jw q (N + 2)) ≫ jw q (N + 2) ≫ wR1 k δq β +
        (wR1 k δq α ≫ vDec q N) ≫ uDec q N ≫ wR1 k δq β =
        wR1 k δq α ≫ (jw q (N + 2) + gDec q N) ≫ wR1 k δq β := by
      rw [← vDec_comp_uDec]
      simp only [Category.assoc, Preadditive.add_comp, Preadditive.comp_add]
      rw [← Category.assoc (jw q (N + 2)) (jw q (N + 2)), jw_idem hq]
    rw [e, ← wR1_jw_eq, ← wR1_comp, ← wR1_comp, ← Category.assoc, hαj]

/-- **The pieces of `m` resolve the identity**: `Σ α ≫ β = 1_m`. -/
theorem pieces_sum (m : ℕ) : ((pieces q hq m).map fun p => p.α ≫ p.β).sum = 𝟙 (X k δq m) := by
  induction m with
  | zero => simp [pieces]
  | succ m ih =>
    have key : ∀ L : List (DPiece (q := q) m),
        ((L.flatMap (splitPiece q hq)).map fun p => p.α ≫ p.β).sum =
          wR1 k δq ((L.map fun p => p.α ≫ p.β).sum) := by
      intro L
      induction L with
      | nil => simp [wR1_zero]
      | cons p L ihL =>
        rw [List.flatMap_cons, List.map_append, List.sum_append, ihL, splitPiece_sum,
          List.map_cons, List.sum_cons, wR1_add]
    rw [pieces, key, ih, wR1_id]

/-! ## Every object is a direct sum of the `P n a` -/

/-- `Z` is a retract of a finite direct sum of objects `P n a`. -/
def IsRetractJw (Z : SKar k (STL k δq)) : Prop :=
  ∃ L : List (SKar k (STL k δq)), (∀ P ∈ L, ∃ n a, P = jwObj q hq n a) ∧
    ∃ (σ : Z ⟶ bsum L) (τ : bsum L ⟶ Z), σ ≫ τ = 𝟙 Z

theorem IsRetractJw.of_retract {Z Y : SKar k (STL k δq)} (hY : IsRetractJw q hq Y) (σ : Z ⟶ Y)
    (τ : Y ⟶ Z) (h : σ ≫ τ = 𝟙 Z) : IsRetractJw q hq Z := by
  obtain ⟨L, hL, σ', τ', h'⟩ := hY
  refine ⟨L, hL, σ ≫ σ', τ' ≫ τ, ?_⟩
  rw [Category.assoc, ← Category.assoc σ', h', Category.id_comp, h]

theorem IsRetractJw.of_iso {Z Y : SKar k (STL k δq)} (hY : IsRetractJw q hq Y) (e : Z ≅ Y) :
    IsRetractJw q hq Z :=
  hY.of_retract q hq e.hom e.inv e.hom_inv_id

theorem isRetractJw_zero : IsRetractJw q hq (bsum []) :=
  ⟨[], by simp, 𝟙 _, 𝟙 _, Category.comp_id _⟩

theorem IsRetractJw.biprodObj {Y₁ Y₂ : SKar k (STL k δq)} (h₁ : IsRetractJw q hq Y₁)
    (h₂ : IsRetractJw q hq Y₂) : IsRetractJw q hq (Y₁ ⊞ Y₂) := by
  obtain ⟨L₁, hL₁, σ₁, τ₁, e₁⟩ := h₁
  obtain ⟨L₂, hL₂, σ₂, τ₂, e₂⟩ := h₂
  refine ⟨L₁ ++ L₂, fun P hP => ?_, biprod.map σ₁ σ₂ ≫ (bsumAppendIso L₁ L₂).inv,
    (bsumAppendIso L₁ L₂).hom ≫ biprod.map τ₁ τ₂, ?_⟩
  · rcases List.mem_append.mp hP with h | h
    · exact hL₁ P h
    · exact hL₂ P h
  · rw [Category.assoc, Iso.inv_hom_id_assoc]
    apply biprod.hom_ext' <;> simp [reassoc_of% e₁, reassoc_of% e₂]

theorem isRetractJw_bsum (l : List (SKar k (STL k δq))) (h : ∀ Y ∈ l, IsRetractJw q hq Y) :
    IsRetractJw q hq (bsum l) := by
  induction l with
  | nil => exact isRetractJw_zero q hq
  | cons Y l ih =>
    exact IsRetractJw.biprodObj q hq (h Y (by simp)) (ih fun Z hZ => h Z (by simp [hZ]))

omit hq in
/-- The underlying morphism of an endomorphism of `Πᵃ m` in `SKar`, additively. -/
def endG (a : ZMod 2) (m : ℕ) :
    ((SKar.of k (STL k δq)).obj (genD q a m) ⟶ (SKar.of k (STL k δq)).obj (genD q a m)) →+
      (X k δq m ⟶ X k δq m) where
  toFun f := Envelope.toHom (f.f PUnit.unit PUnit.unit).1
  map_zero' := rfl
  map_add' _ _ := rfl

omit hq in
theorem endG_injective (a : ZMod 2) (m : ℕ) : Function.Injective (endG q a m) := by
  intro f g h
  apply Karoubi.hom_ext
  apply Mat_.hom_ext
  rintro ⟨⟩ ⟨⟩
  exact Underlying.hom_ext h

omit hq in
theorem parity_shift {a b : ZMod 2} {m n : ℕ} {f : X k δq m ⟶ X k δq n}
    (hf : f ∈ (pres k δq).homDeg (Presentation.parityDeg sig) (strands m) (strands n) b) :
    f ∈ (pres k δq).homDeg (Presentation.parityDeg sig) (strands m) (strands n) (a + (a + b)) := by
  rwa [← add_assoc, ZModModule.add_self, zero_add]

/-- The piece of `SKar` given by a piece of `m`. -/
def skarPiece (a : ZMod 2) {m : ℕ} (p : DPiece (q := q) m) :
    Piece ((SKar.of k (STL k δq)).obj (genD q a m)) where
  obj := jwObj q hq p.n (a + p.b)
  a := ⟨(Mat_.embedding (DD q)).map (homD p.α (parity_shift q p.hα)), by
    show _ = 𝟙 _ ≫ _ ≫ _
    dsimp only [jwObj]
    rw [Category.id_comp, ← Functor.map_comp]
    congr 1
    exact Underlying.hom_ext p.hαj.symm⟩
  b := ⟨(Mat_.embedding (DD q)).map (homD p.β (by simpa [add_comm] using parity_shift q p.hβ)), by
    show _ = _ ≫ _ ≫ 𝟙 _
    dsimp only [jwObj]
    rw [Category.comp_id, ← Functor.map_comp]
    congr 1
    exact Underlying.hom_ext p.hjβ.symm⟩

theorem isRetractJw_gen (a : ZMod 2) (m : ℕ) :
    IsRetractJw q hq ((SKar.of k (STL k δq)).obj (genD q a m)) := by
  set l := (pieces q hq m).map (skarPiece q hq a)
  refine ⟨l.map Piece.obj, ?_, toBsum l, fromBsum l, retract_bsum_of_sum_eq_id l ?_⟩
  · intro P hP
    simp only [l, List.map_map, List.mem_map] at hP
    obtain ⟨p, -, rfl⟩ := hP
    exact ⟨p.n, a + p.b, rfl⟩
  · apply endG_injective q a m
    rw [map_list_sum, List.map_map, List.map_map]
    have : ((endG q a m) ∘ (fun p : Piece ((SKar.of k (STL k δq)).obj (genD q a m)) => p.a ≫ p.b)) ∘
        (skarPiece q hq a) = fun p => p.α ≫ p.β := by
      funext p
      simp only [Function.comp, endG, AddMonoidHom.coe_mk, ZeroHom.coe_mk, skarPiece,
        Karoubi.comp_f, mat_comp_single]
      rfl
    rw [this, pieces_sum]
    show 𝟙 (X k δq m) = Envelope.toHom ((𝟙 ((Mat_.embedding (DD q)).obj (genD q a m))) PUnit.unit
      PUnit.unit).1
    simp [Mat_.id_apply]
    rfl

theorem isRetractJw_of (x : DD q) : IsRetractJw q hq ((SKar.of k (STL k δq)).obj x) := by
  obtain ⟨⟨a, lam⟩⟩ := x
  have e : lam = X k δq (lam.as.word.length) := by
    conv_lhs => rw [← (pres k δq).obj_toObj lam]
    exact congrArg _ (eq_strands _)
  have hx : (⟨⟨a, lam⟩⟩ : DD q) = genD q a (lam.as.word.length) := by
    rw [genD, ← e]
  rw [hx]
  exact isRetractJw_gen q hq a _

theorem isRetractJw (Z : SKar k (STL k δq)) : IsRetractJw q hq Z := by
  -- `Z` is a retract of `Z.X`, which is a direct sum of objects `Πᵃ m`
  refine IsRetractJw.of_retract q hq ?_ (Karoubi.decompId_i Z) (Karoubi.decompId_p Z)
    (Karoubi.decompId Z).symm
  set M := Z.X
  set e := Mat_.isoBiproductEmbedding M
  set F : M.ι → Mat_ (DD q) := fun i => (Mat_.embedding (DD q)).obj (M.X i)
  let piece : M.ι → Piece ((toKaroubi _).obj M) := fun i =>
    ⟨(SKar.of k (STL k δq)).obj (M.X i),
      (toKaroubi _).map (e.hom ≫ biproduct.π F i),
      (toKaroubi _).map (biproduct.ι F i ≫ e.inv)⟩
  set l := (Finset.univ : Finset M.ι).toList.map piece
  have hsum : (l.map fun p => p.a ≫ p.b).sum = 𝟙 _ := by
    simp only [l, List.map_map]
    have : ((fun p : Piece ((toKaroubi _).obj M) => p.a ≫ p.b) ∘ piece) =
        fun i => (toKaroubi _).map (e.hom ≫ biproduct.π F i ≫ biproduct.ι F i ≫ e.inv) := by
      funext i
      simp only [Function.comp, piece, ← Functor.map_comp, Category.assoc]
    rw [this, Finset.sum_map_toList (f := fun i => (toKaroubi (Mat_ (DD q))).map
      (e.hom ≫ biproduct.π F i ≫ biproduct.ι F i ≫ e.inv))]
    rw [← Functor.map_sum]
    simp only [← Preadditive.comp_sum, ← Preadditive.sum_comp, ← Category.assoc]
    have ht : ∑ j, (e.hom ≫ biproduct.π F j) ≫ biproduct.ι F j = e.hom := by
      simp only [Category.assoc, ← Preadditive.comp_sum, biproduct.total, Category.comp_id]
    rw [ht, e.hom_inv_id, CategoryTheory.Functor.map_id]
  refine IsRetractJw.of_retract q hq (isRetractJw_bsum q hq _ ?_) (toBsum l) (fromBsum l)
    (retract_bsum_of_sum_eq_id l hsum)
  intro Y hY
  simp only [l, List.map_map, List.mem_map] at hY
  obtain ⟨i, -, rfl⟩ := hY
  exact isRetractJw_of q hq (M.X i)

/-- **Semisimplicity of `SKar(STL(δ))`.** Every object is isomorphic to a finite direct sum of
objects `P n a = (f_n)^a_a`. -/
theorem exists_iso_bsum_jwObj (Z : SKar k (STL k δq)) :
    ∃ L : List (SKar k (STL k δq)), (∀ P ∈ L, ∃ n a, P = jwObj q hq n a) ∧ Nonempty (Z ≅ bsum L) := by
  obtain ⟨L, hL, σ, τ, h⟩ := isRetractJw q hq Z
  obtain ⟨L', hL', e⟩ := iso_bsum_of_retract (k := k) L (fun P hP => by
    obtain ⟨n, a, rfl⟩ := hL P hP
    exact jwObj_isSchur q hq n a) Z σ τ h
  exact ⟨L', fun P hP => hL P (hL'.subset hP), e⟩

end StringDiagrams.OddTemperleyLieb

end
