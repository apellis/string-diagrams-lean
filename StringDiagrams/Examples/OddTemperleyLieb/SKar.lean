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

end StringDiagrams.OddTemperleyLieb

end
