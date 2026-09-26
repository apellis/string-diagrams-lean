import StringDiagrams.Examples.OddTemperleyLieb.KZero

/-!
# The ring `K₀(SKar(STL(δ)))`

J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, Theorem A.3 (last
paragraph).

* `unitIso`: the unit object of `SKar(STL(δ))` is `P 0 0 = (f_0)^0_0`;
* `piIso`: `Π (P n 0) ≅ P n 1`, so `[P n 1] = π [P n 0]` (`classJw_one`);
* `tensorIso`: `P (N+1) 0 ⊗ P 1 0 ≅ P (N+2) 0 ⊞ P N 1`, from `f_{N+1} ⊗ 1 = f_{N+2} + g_{N+2}` with
  `g_{N+2} ≅ Π f_N` (`Decomposition`); so
  `[P (N+1) 0] [P 1 0] = [P (N+2) 0] + π [P N 0]` (`classJw_mul_one`).
-/

noncomputable section

namespace StringDiagrams.OddTemperleyLieb

open CategoryTheory Limits Idempotents MonoidalCategory Supercategory
open Rep (delta)

variable {k : Type*} [Field k] (q : kˣ)

local notation "δq" => delta q

variable (hq : ∀ n : ℕ, 0 < n → q ^ n ≠ 1)
include hq

omit hq in
theorem mat_comp_unique {D : Type*} [Category D] [Preadditive D] {M N K : Mat_ D} [Unique N.ι]
    (f : M ⟶ N) (g : N ⟶ K) (i : M.ι) (l : K.ι) : (f ≫ g) i l = f i default ≫ g default l := by
  rw [Mat_.comp_apply, Fintype.sum_unique]

/-! ## The unit -/

omit hq in
theorem homD_one (a : ZMod 2) (n : ℕ) (h) : homD (q := q) (a := a) (b := a) (𝟙 (X k δq n)) h =
    𝟙 (genD q a n) := Underlying.hom_ext rfl

theorem jwObj_zero_p (a : ZMod 2) :
    (jwObj q hq 0 a).p = 𝟙 ((Mat_.embedding (DD q)).obj (genD q a 0)) := by
  show (Mat_.embedding (DD q)).map _ = _
  rw [← CategoryTheory.Functor.map_id]
  congr 1

/-- The unit object of `SKar(STL(δ))` is `P 0 0`. -/
theorem unit_eq : 𝟙_ (SKar k (STL k δq)) = jwObj q hq 0 0 := by
  refine Karoubi.ext rfl ?_
  rw [jwObj_zero_p, eqToHom_refl, Category.comp_id, Category.id_comp]
  rfl

theorem one_eq_classJw : (1 : K₀ (SKar k (STL k δq))) = classJw q hq (0, 0) := by
  rw [K₀.one_def, classJw, unit_eq q hq]

/-! ## The parity shift -/

/-- `Π (P n 0) = P n 1`. -/
theorem pi_jwObj (n : ℕ) : (PiCategory.pi (R := k)).obj (jwObj q hq n 0) = jwObj q hq n 1 := by
  refine Karoubi.ext rfl ?_
  rw [eqToHom_refl, Category.comp_id, Category.id_comp]
  apply Mat_.hom_ext
  rintro ⟨⟩ ⟨⟩
  apply Underlying.hom_ext
  apply Envelope.hom_ext
  erw [Envelope.toHom_pi_map, twist_of_mem (R := k) 1 (jw_mem_parity q n 0)]
  rw [zmod2_add_self, sign_zero, one_smul, show (1 : ZMod 2) * (0 + 0) = 0 from rfl, sign_zero,
    one_smul]
  rfl

theorem classJw_one (n : ℕ) : classJw q hq (n, 1) = Zπ.π • classJw q hq (n, 0) := by
  rw [classJw, classJw, SKar.π_smul_mk_algebra, pi_jwObj]

/-! ## The tensor product with the generating object -/

omit hq in
theorem X_tensor_one (m : ℕ) :
    X k δq m ⊗ X k δq 1 = X k δq (m + 1) := X_tensor k δq m 1

omit hq in
/-- Right whiskering in `STL(δ)` is `wR1` up to the identification `m ⊗ 1 = m + 1`. -/
theorem whiskerRight_eq_wR1 {a b : ℕ} (x : X k δq a ⟶ X k δq b) :
    x ▷ X k δq 1 = eqToHom (X_tensor_one q a) ≫ wR1 k δq x ≫ eqToHom (X_tensor_one q b).symm := by
  rw [wR1]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl, Category.comp_id,
    Category.id_comp]
  rfl

omit hq in
theorem eqToHom_tensor_mem (m : ℕ) :
    (eqToHom (X_tensor_one q m) : X k δq m ⊗ X k δq 1 ⟶ X k δq (m + 1)) ∈
      (pres k δq).homDeg (Presentation.parityDeg sig) ((strands m).tensor (strands 1))
        (strands (m + 1)) 0 :=
  Presentation.eqToHom_mem_homDeg (P := pres k δq) _ _

omit hq in
theorem eqToHom_tensor_mem' (m : ℕ) :
    (eqToHom (X_tensor_one q m).symm : X k δq (m + 1) ⟶ X k δq m ⊗ X k δq 1) ∈
      (pres k δq).homDeg (Presentation.parityDeg sig) (strands (m + 1))
        ((strands m).tensor (strands 1)) 0 :=
  Presentation.eqToHom_mem_homDeg (P := pres k δq) _ _

variable {q} in
/-- The object `(Π⁰ m) ⊗ (Π⁰ 1)` of the underlying category of the Π-envelope. -/
abbrev tensD (m : ℕ) : DD q := genD q 0 m ⊗ genD q 0 1

omit hq in
/-- A morphism out of `(Π⁰ m) ⊗ (Π⁰ 1)`, given by `φ : m + 1 → n` of parity `b`. -/
def homOut {m n : ℕ} {b : ZMod 2} (φ : X k δq (m + 1) ⟶ X k δq n)
    (hφ : φ ∈ (pres k δq).homDeg (Presentation.parityDeg sig) (strands (m + 1)) (strands n) b) :
    tensD (q := q) m ⟶ genD q b n :=
  ⟨Envelope.ofHom (eqToHom (X_tensor_one q m) ≫ φ), by
    have := Presentation.comp_mem_homDeg (eqToHom_tensor_mem q m) hφ
    show _ ∈ parity (R := k) (X k δq m ⊗ X k δq 1) (X k δq n) (0 + (0 + 0 + b))
    simpa using this⟩

omit hq in
/-- A morphism into `(Π⁰ m) ⊗ (Π⁰ 1)`, given by `ψ : n → m + 1` of parity `b`. -/
def homIn {m n : ℕ} {b : ZMod 2} (ψ : X k δq n ⟶ X k δq (m + 1))
    (hψ : ψ ∈ (pres k δq).homDeg (Presentation.parityDeg sig) (strands n) (strands (m + 1)) b) :
    genD q b n ⟶ tensD (q := q) m :=
  ⟨Envelope.ofHom (ψ ≫ eqToHom (X_tensor_one q m).symm), by
    have := Presentation.comp_mem_homDeg hψ (eqToHom_tensor_mem' q m)
    show _ ∈ parity (R := k) (X k δq n) (X k δq m ⊗ X k δq 1) (0 + (b + (0 + 0)))
    simpa using this⟩

/-- The underlying morphism of the idempotent of `P m 0 ⊗ P 1 0`. -/
theorem tensor_p_val (m : ℕ) (x y : PUnit × PUnit) :
    Envelope.toHom ((jwObj q hq m 0 ⊗ jwObj q hq 1 0).p x y).1 =
      eqToHom (X_tensor_one q m) ≫ wR1 k δq (jw q m) ≫ eqToHom (X_tensor_one q m).symm := by
  show Envelope.toHom ((homD (jw q m) (jw_mem_parity q m 0)).1 ⊗
    (homD (jw q 1) (jw_mem_parity q 1 0)).1) = _
  rw [Envelope.tensorHom_def', Envelope.toHom_comp, Envelope.toHom_whiskerRight_of_par_zero _ _ rfl,
    Envelope.toHom_whiskerLeft_of_par_zero _ rfl]
  simp only [homD_val, jw_one]
  show jw q m ▷ X k δq 1 ≫ X k δq m ◁ 𝟙 (X k δq 1) = _
  erw [MonoidalSupercategory.whiskerLeft_id (R := k), Category.comp_id, whiskerRight_eq_wR1]

instance (n : ℕ) (a : ZMod 2) : Unique (jwObj q hq n a).X.ι := inferInstanceAs (Unique PUnit)

instance (m : ℕ) : Unique (jwObj q hq m 0 ⊗ jwObj q hq 1 0).X.ι where
  default := (PUnit.unit, PUnit.unit)
  uniq := fun ⟨⟨⟩, ⟨⟩⟩ => rfl

omit hq in
theorem karoubi_add_f {C : Type*} [Category C] [Preadditive C] {P Q : Karoubi C} (f g : P ⟶ Q) :
    (f + g).f = f.f + g.f := rfl

omit hq in
@[simp] theorem homOut_val {m n : ℕ} {b : ZMod 2} (φ : X k δq (m + 1) ⟶ X k δq n) (hφ) :
    Envelope.toHom (homOut q (b := b) φ hφ).1 = eqToHom (X_tensor_one q m) ≫ φ := rfl

omit hq in
@[simp] theorem homIn_val {m n : ℕ} {b : ZMod 2} (ψ : X k δq n ⟶ X k δq (m + 1)) (hψ) :
    Envelope.toHom (homIn q (b := b) ψ hψ).1 = ψ ≫ eqToHom (X_tensor_one q m).symm := rfl

@[simp] theorem jwObj_p_val (n : ℕ) (a : ZMod 2) (x y : PUnit) :
    Envelope.toHom ((jwObj q hq n a).p x y).1 = jw q n := rfl

variable {q hq} in
/-- A morphism `P m 0 ⊗ P 1 0 ⟶ P n b` given by `φ : m + 1 → n` absorbing the projectors. -/
def kOut {m n : ℕ} {b : ZMod 2} (φ : X k δq (m + 1) ⟶ X k δq n)
    (hφ : φ ∈ (pres k δq).homDeg (Presentation.parityDeg sig) (strands (m + 1)) (strands n) b)
    (h1 : wR1 k δq (jw q m) ≫ φ = φ) (h2 : φ ≫ jw q n = φ) :
    jwObj q hq m 0 ⊗ jwObj q hq 1 0 ⟶ jwObj q hq n b :=
  ⟨fun _ _ => homOut q φ hφ, by
    apply Mat_.hom_ext
    intro x y
    rw [mat_comp_unique, mat_comp_unique]
    apply Underlying.hom_ext
    apply Envelope.hom_ext
    simp only [Underlying.comp_val, Envelope.toHom_comp, tensor_p_val, homOut_val, jwObj_p_val,
      Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [h2, h1]⟩

variable {q hq} in
/-- A morphism `P n b ⟶ P m 0 ⊗ P 1 0` given by `ψ : n → m + 1` absorbing the projectors. -/
def kIn {m n : ℕ} {b : ZMod 2} (ψ : X k δq n ⟶ X k δq (m + 1))
    (hψ : ψ ∈ (pres k δq).homDeg (Presentation.parityDeg sig) (strands n) (strands (m + 1)) b)
    (h1 : ψ ≫ wR1 k δq (jw q m) = ψ) (h2 : jw q n ≫ ψ = ψ) :
    jwObj q hq n b ⟶ jwObj q hq m 0 ⊗ jwObj q hq 1 0 :=
  ⟨fun _ _ => homIn q ψ hψ, by
    apply Mat_.hom_ext
    intro x y
    rw [mat_comp_unique, mat_comp_unique]
    apply Underlying.hom_ext
    apply Envelope.hom_ext
    simp only [Underlying.comp_val, Envelope.toHom_comp, tensor_p_val, homIn_val, jwObj_p_val,
      Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [← Category.assoc ψ, h1, ← Category.assoc, h2]⟩

theorem mor_kIn_kOut {m n n' : ℕ} {b b' : ZMod 2} (ψ : X k δq n ⟶ X k δq (m + 1)) (hψ h1 h2)
    (φ : X k δq (m + 1) ⟶ X k δq n') (hφ h1' h2') :
    mor hq (kIn (q := q) (hq := hq) (b := b) ψ hψ h1 h2 ≫ kOut (b := b') φ hφ h1' h2') = ψ ≫ φ := by
  simp only [mor, Karoubi.comp_f]
  rw [mat_comp_unique]
  simp [kIn, kOut]

/-- **`P (N+1) 0 ⊗ P 1 0 ≅ P (N+2) 0 ⊞ P N 1`.** -/
def tensorIso (N : ℕ) :
    jwObj q hq (N + 1) 0 ⊗ jwObj q hq 1 0 ≅ bsum [jwObj q hq (N + 2) 0, jwObj q hq N 1] := by
  have hw : wR1 k δq (jw q (N + 1)) ≫ wR1 k δq (jw q (N + 1)) = wR1 k δq (jw q (N + 1)) := by
    rw [← wR1_comp, jw_idem hq]
  let a₁ := kOut (q := q) (hq := hq) (b := 0) (jw q (N + 2)) (by simpa using jw_mem_parity q (N + 2) 0)
    (wR1_comp_jw hq (N + 1)) (jw_idem hq _)
  let b₁ := kIn (q := q) (hq := hq) (b := 0) (jw q (N + 2)) (by simpa using jw_mem_parity q (N + 2) 0)
    (jw_comp_wR1 hq (N + 1)) (jw_idem hq _)
  let a₂ := kOut (q := q) (hq := hq) (b := 1) (vDec q N) (vDec_mem_parity N)
    (by rw [vDec, ← Category.assoc, hw]) (vDec_comp_jw hq N)
  let b₂ := kIn (q := q) (hq := hq) (b := 1) (uDec q N) (uDec_mem_parity N)
    (by rw [uDec, Linear.smul_comp, Category.assoc, hw]) (jw_comp_uDec hq N)
  let l : List (Piece (jwObj q hq (N + 1) 0 ⊗ jwObj q hq 1 0)) :=
    [⟨jwObj q hq (N + 2) 0, a₁, b₁⟩, ⟨jwObj q hq N 1, a₂, b₂⟩]
  refine isoBsum l ?_ ?_
  · -- `f_{N+1} ⊗ 1 = f_{N+2} + g_{N+2}`
    simp only [l, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    apply Karoubi.hom_ext
    apply Mat_.hom_ext
    intro x y
    simp only [karoubi_add_f, Karoubi.comp_f, Karoubi.id_f, Mat_.add_apply]
    rw [mat_comp_unique, mat_comp_unique]
    apply Underlying.hom_ext
    apply Envelope.hom_ext
    simp only [Underlying.add_val, Underlying.comp_val, Envelope.toHom_add, Envelope.toHom_comp,
      tensor_p_val, a₁, b₁, a₂, b₂, kOut, kIn, homOut_val, homIn_val, Category.assoc]
    rw [← Category.assoc (jw q (N + 2)) (jw q (N + 2)), jw_idem hq,
      ← Category.assoc (vDec q N), vDec_comp_uDec, ← Preadditive.comp_add, ← Preadditive.add_comp,
      ← wR1_jw_eq]
  · refine ⟨?_, ?_, ?_, ?_, trivial⟩
    · apply jwObj_hom_ext
      rw [mor_kIn_kOut, jw_idem hq, mor_id]
    · intro p hp
      simp only [List.mem_singleton] at hp
      subst hp
      exact ⟨hom_jwObj_eq_zero q hq (Or.inr (by decide)) _,
        hom_jwObj_eq_zero q hq (Or.inr (by decide)) _⟩
    · apply jwObj_hom_ext
      rw [mor_kIn_kOut, uDec_comp_vDec hq, mor_id]
    · intro p hp; simp at hp

/-- **`[P (N+1) 0] [P 1 0] = [P (N+2) 0] + π [P N 0]`.** -/
theorem classJw_mul_one (N : ℕ) :
    classJw q hq (N + 1, 0) * classJw q hq (1, 0) =
      classJw q hq (N + 2, 0) + Zπ.π • classJw q hq (N, 0) := by
  rw [classJw, classJw, K₀.mk_mul_mk, K₀.mk_eq_mk_of_iso (tensorIso q hq N), mk_bsum,
    ← classJw_one]
  simp [classJw]

end StringDiagrams.OddTemperleyLieb

end
