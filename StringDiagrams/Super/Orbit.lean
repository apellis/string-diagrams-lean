import StringDiagrams.Super.QPi

/-!
# The orbit supercategory of an auto-equivalence

This file provides the construction behind the associated graded `(Q, Π)`-supercategory of a
`(Q, Π)`-category (J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
§6, proof of Theorem 6.13).

Let `S` be a supercategory with an adjoint auto-equivalence `(Q, Q⁻¹)` by superfunctors with
even unit and counit (`StringDiagrams.ShiftData`). Its powers `Qⁱ`, `i ∈ ℤ`
(`ShiftData.pow`), come with even isomorphisms `Q Qⁱ ≅ Qⁱ⁺¹` (`ShiftData.succ`) and
`Qⁱ Q ≅ Qⁱ⁺¹` (`ShiftData.comm`). The *orbit supercategory* `Orbit d` has the objects of `S`,
and its morphisms `λ → μ` of degree `m` are the families
`(f_{i,j} : Qⁱ λ → Qʲ μ)_{i - j = m}` compatible with `Q`, i.e.
`f_{i+1,j+1} = Q f_{i,j}` up to the isomorphisms `Q Qⁱ ≅ Qⁱ⁺¹` (`ShiftData.Fam`). Such a
family is determined by any one of its entries (as `Q` is faithful), e.g. by
`f_{0,-m} : λ → Q⁻ᵐ μ`; thus the morphisms of degree `m` are `Hom_S(λ, Q⁻ᵐ μ)`, and
composition is `g ∘ f = (g_{j,k} ∘ f_{i,j})`. Using compatible families rather than
`Hom_S(λ, Q⁻ᵐ μ)` itself makes composition strictly associative without the coherence
isomorphisms `Qᵐ Qⁿ ≅ Qᵐ⁺ⁿ`.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory

universe w v u

variable (R : Type w) [CommRing R]

/-- An adjoint auto-equivalence of a supercategory by superfunctors, with even unit and
counit. -/
structure ShiftData (S : Type u) [Category.{v} S] [Preadditive S] [Linear R S]
    [Supercategory R S] where
  /-- The adjoint equivalence `(Q, Q⁻¹)`. -/
  e : S ≌ S
  [functor_additive : e.functor.Additive]
  [functor_linear : e.functor.Linear R]
  [functor_isSuperfunctor : IsSuperfunctor R e.functor]
  [inverse_additive : e.inverse.Additive]
  [inverse_linear : e.inverse.Linear R]
  [inverse_isSuperfunctor : IsSuperfunctor R e.inverse]
  unit_mem : ∀ X : S, e.unitIso.hom.app X ∈ parity (R := R) X (e.inverse.obj (e.functor.obj X)) 0
  counit_mem : ∀ X : S, e.counitIso.hom.app X ∈ parity (R := R) (e.functor.obj (e.inverse.obj X)) X 0

attribute [instance] ShiftData.functor_additive ShiftData.functor_linear
  ShiftData.functor_isSuperfunctor ShiftData.inverse_additive ShiftData.inverse_linear
  ShiftData.inverse_isSuperfunctor

namespace ShiftData

variable {R} {S : Type u} [Category.{v} S] [Preadditive S] [Linear R S] [Supercategory R S]
  (d : ShiftData R S)

/-- `Q`. -/
abbrev Q : S ⥤ S := d.e.functor

/-- `Q⁻¹`. -/
abbrev Qi : S ⥤ S := d.e.inverse

theorem unit_inv_mem (X : S) :
    d.e.unitIso.inv.app X ∈ parity (R := R) (d.Qi.obj (d.Q.obj X)) X 0 :=
  inv_mem (d.e.unitIso.app X) (d.unit_mem X)

theorem counit_inv_mem (X : S) :
    d.e.counitIso.inv.app X ∈ parity (R := R) X (d.Q.obj (d.Qi.obj X)) 0 :=
  inv_mem (d.e.counitIso.app X) (d.counit_mem X)

/-! ## Powers of `Q` -/

/-- `Qⁿ`, `n ∈ ℕ` (with `Qⁿ⁺¹ = Qⁿ ⋙ Q`, i.e. `Q` applied last). -/
def powNat : ℕ → S ⥤ S
  | 0 => 𝟭 S
  | n + 1 => powNat n ⋙ d.Q

/-- `Q⁻ⁿ`, `n ∈ ℕ` (with `Q⁻ⁿ⁻¹ = Q⁻ⁿ ⋙ Q⁻¹`). -/
def powNeg : ℕ → S ⥤ S
  | 0 => 𝟭 S
  | n + 1 => powNeg n ⋙ d.Qi

/-- `Qⁱ`, `i ∈ ℤ`. -/
def pow : ℤ → S ⥤ S
  | Int.ofNat n => d.powNat n
  | Int.negSucc n => d.powNeg (n + 1)

instance powNat_additive : ∀ n, (d.powNat n).Additive
  | 0 => inferInstanceAs (𝟭 S).Additive
  | n + 1 => by haveI := powNat_additive n; exact inferInstanceAs (d.powNat n ⋙ d.Q).Additive

instance powNat_linear : ∀ n, (d.powNat n).Linear R
  | 0 => inferInstanceAs ((𝟭 S).Linear R)
  | n + 1 => by haveI := powNat_linear n; exact inferInstanceAs ((d.powNat n ⋙ d.Q).Linear R)

instance powNat_isSuperfunctor : ∀ n, IsSuperfunctor R (d.powNat n)
  | 0 => inferInstanceAs (IsSuperfunctor R (𝟭 S))
  | n + 1 => by
    haveI := powNat_isSuperfunctor n; exact inferInstanceAs (IsSuperfunctor R (d.powNat n ⋙ d.Q))

instance powNeg_additive : ∀ n, (d.powNeg n).Additive
  | 0 => inferInstanceAs (𝟭 S).Additive
  | n + 1 => by haveI := powNeg_additive n; exact inferInstanceAs (d.powNeg n ⋙ d.Qi).Additive

instance powNeg_linear : ∀ n, (d.powNeg n).Linear R
  | 0 => inferInstanceAs ((𝟭 S).Linear R)
  | n + 1 => by haveI := powNeg_linear n; exact inferInstanceAs ((d.powNeg n ⋙ d.Qi).Linear R)

instance powNeg_isSuperfunctor : ∀ n, IsSuperfunctor R (d.powNeg n)
  | 0 => inferInstanceAs (IsSuperfunctor R (𝟭 S))
  | n + 1 => by
    haveI := powNeg_isSuperfunctor n
    exact inferInstanceAs (IsSuperfunctor R (d.powNeg n ⋙ d.Qi))

instance pow_additive : ∀ i, (d.pow i).Additive
  | Int.ofNat n => d.powNat_additive n
  | Int.negSucc n => d.powNeg_additive (n + 1)

instance pow_linear : ∀ i, (d.pow i).Linear R
  | Int.ofNat n => d.powNat_linear n
  | Int.negSucc n => d.powNeg_linear (n + 1)

instance pow_isSuperfunctor : ∀ i, IsSuperfunctor R (d.pow i)
  | Int.ofNat n => d.powNat_isSuperfunctor n
  | Int.negSucc n => d.powNeg_isSuperfunctor (n + 1)

@[simp] theorem pow_zero : d.pow 0 = 𝟭 S := rfl

/-! ## The isomorphisms `Q Qⁱ ≅ Qⁱ⁺¹` -/

/-- `Q Qⁱ ≅ Qⁱ⁺¹` (in diagrammatic order `Qⁱ ⋙ Q ≅ Qⁱ⁺¹`): the identity for `i ≥ 0`, the
counit for `i < 0`. -/
def succ : ∀ i : ℤ, d.pow i ⋙ d.Q ≅ d.pow (i + 1)
  | Int.ofNat _ => Iso.refl _
  | Int.negSucc 0 => d.e.counitIso
  | Int.negSucc (n + 1) => Functor.associator _ _ _ ≪≫ isoWhiskerLeft (d.powNeg (n + 1)) d.e.counitIso ≪≫
      Functor.rightUnitor _

theorem succ_hom_mem (i : ℤ) (X : S) :
    (d.succ i).hom.app X ∈ parity (R := R) (d.Q.obj ((d.pow i).obj X)) ((d.pow (i + 1)).obj X) 0 := by
  rcases i with n | (_ | n)
  · exact id_mem _
  · exact d.counit_mem X
  · convert d.counit_mem ((d.powNeg (n + 1)).obj X) using 1
    show 𝟙 _ ≫ _ ≫ 𝟙 _ = _
    rw [Category.id_comp, Category.comp_id]; rfl

theorem succ_inv_mem (i : ℤ) (X : S) :
    (d.succ i).inv.app X ∈ parity (R := R) ((d.pow (i + 1)).obj X) (d.Q.obj ((d.pow i).obj X)) 0 :=
  inv_mem ((d.succ i).app X) (d.succ_hom_mem i X)

/-! ## The isomorphisms `Qⁱ Q ≅ Qⁱ⁺¹` -/

/-- `Qⁿ Q ≅ Qⁿ⁺¹` for `n ∈ ℕ`. -/
def commNat : ∀ n : ℕ, d.Q ⋙ d.powNat n ≅ d.powNat (n + 1)
  | 0 => Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm
  | n + 1 => (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (commNat n) d.Q

/-- `Q⁻ⁿ⁻¹ Q ≅ Q⁻ⁿ` for `n ∈ ℕ`. -/
def commNeg : ∀ n : ℕ, d.Q ⋙ d.powNeg (n + 1) ≅ d.powNeg n
  | 0 => isoWhiskerLeft d.Q (Functor.leftUnitor _) ≪≫ d.e.unitIso.symm
  | n + 1 => (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (commNeg n) d.Qi

/-- `Qⁱ Q ≅ Qⁱ⁺¹` (in diagrammatic order `Q ⋙ Qⁱ ≅ Qⁱ⁺¹`): built from identities for
`i ≥ 0` and from the unit for `i < 0`. -/
def comm : ∀ i : ℤ, d.Q ⋙ d.pow i ≅ d.pow (i + 1)
  | Int.ofNat n => d.commNat n
  | Int.negSucc 0 => d.commNeg 0
  | Int.negSucc (n + 1) => d.commNeg (n + 1)

theorem commNat_hom_mem (n : ℕ) (X : S) :
    (d.commNat n).hom.app X ∈ parity (R := R) ((d.powNat n).obj (d.Q.obj X)) ((d.powNat (n + 1)).obj X) 0 := by
  induction n with
  | zero => simpa [commNat] using id_mem (R := R) (d.Q.obj X)
  | succ n ih =>
    convert map_mem d.Q ih using 1
    exact Category.id_comp _

theorem commNeg_hom_mem (n : ℕ) (X : S) :
    (d.commNeg n).hom.app X ∈ parity (R := R) ((d.powNeg (n + 1)).obj (d.Q.obj X)) ((d.powNeg n).obj X) 0 := by
  induction n with
  | zero =>
    convert d.unit_inv_mem X using 1
    exact Category.id_comp _
  | succ n ih =>
    convert map_mem d.Qi ih using 1
    exact Category.id_comp _

theorem comm_hom_mem (i : ℤ) (X : S) :
    (d.comm i).hom.app X ∈ parity (R := R) ((d.pow i).obj (d.Q.obj X)) ((d.pow (i + 1)).obj X) 0 := by
  rcases i with n | (_ | n)
  · exact d.commNat_hom_mem n X
  · exact d.commNeg_hom_mem 0 X
  · exact d.commNeg_hom_mem (n + 1) X

theorem comm_inv_mem (i : ℤ) (X : S) :
    (d.comm i).inv.app X ∈ parity (R := R) ((d.pow (i + 1)).obj X) ((d.pow i).obj (d.Q.obj X)) 0 :=
  inv_mem ((d.comm i).app X) (d.comm_hom_mem i X)

theorem succ_negSucc_succ_hom_app (n : ℕ) (X : S) :
    (d.succ (Int.negSucc (n + 1))).hom.app X = d.e.counitIso.hom.app ((d.powNeg (n + 1)).obj X) := by
  show 𝟙 _ ≫ _ ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]; rfl

theorem succ_negSucc_succ_inv_app (n : ℕ) (X : S) :
    (d.succ (Int.negSucc (n + 1))).inv.app X = d.e.counitIso.inv.app ((d.powNeg (n + 1)).obj X) := by
  rw [← cancel_mono ((d.succ (Int.negSucc (n + 1))).hom.app X), Iso.inv_hom_id_app,
    succ_negSucc_succ_hom_app]
  exact (Iso.inv_hom_id_app d.e.counitIso _).symm

theorem commNeg_succ_hom_app (n : ℕ) (X : S) :
    (d.commNeg (n + 1)).hom.app X = d.Qi.map ((d.commNeg n).hom.app X) := by
  show 𝟙 _ ≫ _ = _
  rw [Category.id_comp]; rfl

/-- The compatibility of `comm` with `succ`: `Qⁱ⁺¹ Q ≅ Qⁱ⁺²` is obtained from `Qⁱ Q ≅ Qⁱ⁺¹` by
applying `Q` and the isomorphisms `succ`. For `i = -1` this is the triangle identity of the
adjoint equivalence. -/
theorem comm_succ (i : ℤ) (X : S) :
    (d.comm (i + 1)).hom.app X =
      (d.succ i).inv.app (d.Q.obj X) ≫ d.Q.map ((d.comm i).hom.app X) ≫ (d.succ (i + 1)).hom.app X := by
  rcases i with n | (_ | n)
  · show (d.commNat (n + 1)).hom.app X = 𝟙 _ ≫ d.Q.map ((d.commNat n).hom.app X) ≫ 𝟙 _
    rw [Category.comp_id]; rfl
  · show 𝟙 _ ≫ 𝟙 _ = (d.e.counitIso.inv.app (d.Q.obj X)) ≫
      d.Q.map (𝟙 _ ≫ d.e.unitIso.inv.app X) ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
    exact (d.e.counitInv_functor_comp X).symm
  · rcases n with _ | n
    · show (d.commNeg 0).hom.app X = (d.succ (Int.negSucc 1)).inv.app (d.Q.obj X) ≫
        d.Q.map ((d.commNeg 1).hom.app X) ≫ d.e.counitIso.hom.app X
      rw [succ_negSucc_succ_inv_app, commNeg_succ_hom_app]
      symm
      exact (Iso.inv_comp_eq (d.e.counitIso.app _)).2 (d.e.counitIso.hom.naturality _)
    · show (d.commNeg (n + 1)).hom.app X = (d.succ (Int.negSucc (n + 2))).inv.app (d.Q.obj X) ≫
        d.Q.map ((d.commNeg (n + 2)).hom.app X) ≫ (d.succ (Int.negSucc (n + 1))).hom.app X
      rw [succ_negSucc_succ_inv_app, succ_negSucc_succ_hom_app, commNeg_succ_hom_app d (n + 1)]
      symm
      exact (Iso.inv_comp_eq (d.e.counitIso.app _)).2 (d.e.counitIso.hom.naturality _)

/-! ## Compatible families -/

/-- All families of morphisms `Qⁱ X ⟶ Qʲ Y`. -/
def FamAll (X Y : S) := ∀ i j : ℤ, (d.pow i).obj X ⟶ (d.pow j).obj Y

instance (X Y : S) : CoeFun (d.FamAll X Y) fun _ => ∀ i j : ℤ, (d.pow i).obj X ⟶ (d.pow j).obj Y :=
  ⟨fun f => f⟩

instance (X Y : S) : AddCommGroup (d.FamAll X Y) :=
  inferInstanceAs (AddCommGroup (∀ i j : ℤ, (d.pow i).obj X ⟶ (d.pow j).obj Y))

instance (X Y : S) : Module R (d.FamAll X Y) :=
  inferInstanceAs (Module R (∀ i j : ℤ, (d.pow i).obj X ⟶ (d.pow j).obj Y))

variable {d}

@[simp] theorem FamAll.add_apply {X Y : S} (f g : d.FamAll X Y) (i j : ℤ) :
    (f + g) i j = f i j + g i j := rfl

@[simp] theorem FamAll.smul_apply {X Y : S} (r : R) (f : d.FamAll X Y) (i j : ℤ) :
    (r • f) i j = r • f i j := rfl

@[simp] theorem FamAll.zero_apply {X Y : S} (i j : ℤ) : (0 : d.FamAll X Y) i j = 0 := rfl

@[simp] theorem FamAll.neg_apply {X Y : S} (f : d.FamAll X Y) (i j : ℤ) : (-f) i j = -f i j :=
  rfl

@[ext] theorem FamAll.ext {X Y : S} {f g : d.FamAll X Y} (h : ∀ i j, f i j = g i j) : f = g :=
  funext fun i => funext fun j => h i j

variable (d)

/-- A family is compatible with `Q`: `f_{i+1,j+1} = Q f_{i,j}` up to the isomorphisms
`Q Qⁱ ≅ Qⁱ⁺¹`. -/
def IsCompat {X Y : S} (f : d.FamAll X Y) : Prop :=
  ∀ i j, f (i + 1) (j + 1) = (d.succ i).inv.app X ≫ d.Q.map (f i j) ≫ (d.succ j).hom.app Y

variable (R) in
/-- The compatible families of degree `m`: those supported on `i - j = m`. -/
def Fam (m : ℤ) (X Y : S) : Submodule R (d.FamAll X Y) where
  carrier := {f | (∀ i j, i - j ≠ m → f i j = 0) ∧ d.IsCompat f}
  add_mem' := by
    rintro f g ⟨hf0, hf⟩ ⟨hg0, hg⟩
    refine ⟨fun i j h => by simp [hf0 i j h, hg0 i j h], fun i j => ?_⟩
    simp only [FamAll.add_apply, hf i j, hg i j, Functor.map_add, Preadditive.add_comp,
      Preadditive.comp_add]
  zero_mem' := ⟨fun _ _ _ => rfl, fun i j => by simp⟩
  smul_mem' := by
    rintro r f ⟨hf0, hf⟩
    refine ⟨fun i j h => by simp [hf0 i j h], fun i j => ?_⟩
    simp only [FamAll.smul_apply, hf i j, Functor.map_smul, Linear.smul_comp, Linear.comp_smul]

variable {d}

theorem Fam.eq_zero {m : ℤ} {X Y : S} {f : d.FamAll X Y} (hf : f ∈ d.Fam R m X Y) {i j : ℤ}
    (h : i - j ≠ m) : f i j = 0 := hf.1 i j h

theorem Fam.compat {m : ℤ} {X Y : S} {f : d.FamAll X Y} (hf : f ∈ d.Fam R m X Y) (i j : ℤ) :
    f (i + 1) (j + 1) = (d.succ i).inv.app X ≫ d.Q.map (f i j) ≫ (d.succ j).hom.app Y :=
  hf.2 i j

variable (d)

/-- The composite of a family of degree `m` with a family: `(g ∘ f)_{i,k} = g_{i-m,k} ∘ f_{i,i-m}`. -/
def famComp (m : ℤ) {X Y Z : S} (f : d.FamAll X Y) (g : d.FamAll Y Z) : d.FamAll X Z :=
  fun i k => f i (i - m) ≫ g (i - m) k

variable {d}

theorem famComp_mem {m n : ℤ} {X Y Z : S} {f : d.FamAll X Y} {g : d.FamAll Y Z}
    (hf : f ∈ d.Fam R m X Y) (hg : g ∈ d.Fam R n Y Z) : d.famComp m f g ∈ d.Fam R (m + n) X Z := by
  refine ⟨fun i k h => ?_, fun i k => ?_⟩
  · rw [famComp, Fam.eq_zero hg (by omega), Limits.comp_zero]
  · simp only [famComp]
    rw [show i + 1 - m = i - m + 1 by ring, Fam.compat hf, Fam.compat hg]
    simp [Category.assoc]

variable (d)

/-- The identity family: `1_{i,i} = 1`. -/
def idFam (X : S) : d.FamAll X X :=
  fun i j => if h : i = j then eqToHom (congrArg (fun k => (d.pow k).obj X) h) else 0

theorem idFam_self (X : S) (i : ℤ) : d.idFam X i i = 𝟙 _ := by simp [idFam]

theorem idFam_mem (X : S) : d.idFam X ∈ d.Fam R 0 X X := by
  refine ⟨fun i j h => ?_, fun i j => ?_⟩
  · rw [idFam, dif_neg (by omega)]
  · by_cases h : i = j
    · subst h; simp [idFam_self]
    · rw [idFam, idFam, dif_neg h, dif_neg (by omega)]; simp

theorem famComp_idFam_left {X Y : S} (f : d.FamAll X Y) : d.famComp 0 (d.idFam X) f = f := by
  ext i k
  simp only [famComp]
  rw [show i - 0 = i by ring, idFam_self, Category.id_comp]

theorem famComp_idFam_right {m : ℤ} {X Y : S} {f : d.FamAll X Y} (hf : f ∈ d.Fam R m X Y) :
    d.famComp m f (d.idFam Y) = f := by
  ext i k
  simp only [famComp, idFam]
  by_cases h : i - m = k
  · subst h; simp
  · rw [dif_neg h, Limits.comp_zero, Fam.eq_zero hf (by omega)]

theorem famComp_assoc (m n : ℤ) {W X Y Z : S} (f : d.FamAll W X) (g : d.FamAll X Y)
    (h : d.FamAll Y Z) :
    d.famComp (m + n) (d.famComp m f g) h = d.famComp m f (d.famComp n g h) := by
  ext i l
  simp only [famComp]
  rw [show i - (m + n) = i - m - n by ring, Category.assoc]

/-! ## Morphisms of the orbit supercategory -/

/-- The composite as a bilinear map on families of degrees `m` and `n`. -/
def famCompₗ (m n : ℤ) (X Y Z : S) :
    d.Fam R m X Y →ₗ[R] d.Fam R n Y Z →ₗ[R] d.Fam R (m + n) X Z :=
  LinearMap.mk₂ R (fun (f : d.Fam R m X Y) (g : d.Fam R n Y Z) =>
      (⟨d.famComp m f.1 g.1, famComp_mem f.2 g.2⟩ : d.Fam R (m + n) X Z))
    (fun f f' g => Subtype.ext (FamAll.ext fun i k => by
      simp [famComp, Preadditive.add_comp]))
    (fun r f g => Subtype.ext (FamAll.ext fun i k => by simp [famComp]))
    (fun f g g' => Subtype.ext (FamAll.ext fun i k => by
      simp [famComp, Preadditive.comp_add]))
    (fun r f g => Subtype.ext (FamAll.ext fun i k => by simp [famComp]))

@[simp] theorem famCompₗ_apply (m n : ℤ) {X Y Z : S} (f : d.Fam R m X Y) (g : d.Fam R n Y Z) :
    ((d.famCompₗ m n X Y Z f g : d.Fam R (m + n) X Z) : d.FamAll X Z) = d.famComp m f.1 g.1 := rfl

/-- The morphisms `X → Y` of the orbit supercategory: `⨁ₘ` compatible families of degree `m`. -/
def Hom (X Y : S) : Type _ := DirectSum ℤ fun m => d.Fam R m X Y

instance (m : ℤ) (X Y : S) : AddCommGroup (d.Fam R m X Y) := Submodule.addCommGroup _

instance (m : ℤ) (X Y : S) : Module R (d.Fam R m X Y) := Submodule.module _

instance (X Y : S) : AddCommGroup (d.Hom X Y) :=
  inferInstanceAs (AddCommGroup (DirectSum ℤ fun m => d.Fam R m X Y))

instance (X Y : S) : Module R (d.Hom X Y) :=
  inferInstanceAs (Module R (DirectSum ℤ fun m => d.Fam R m X Y))

/-- The inclusion of the families of degree `m`. -/
def lof (m : ℤ) (X Y : S) : d.Fam R m X Y →ₗ[R] d.Hom X Y :=
  DirectSum.lof R ℤ (fun m => d.Fam R m X Y) m

/-- The degree-`m` component of a morphism. -/
def component (m : ℤ) (X Y : S) : d.Hom X Y →ₗ[R] d.Fam R m X Y :=
  DirectSum.component R ℤ (fun m => d.Fam R m X Y) m

@[simp] theorem component_lof_self (m : ℤ) {X Y : S} (f : d.Fam R m X Y) :
    d.component m X Y (d.lof m X Y f) = f :=
  DirectSum.component.lof_self (M := fun m => d.Fam R m X Y) R m f

theorem component_lof_of_ne {m n : ℤ} {X Y : S} (f : d.Fam R m X Y) (h : m ≠ n) :
    d.component n X Y (d.lof m X Y f) = 0 :=
  (DirectSum.component.of (M := fun m => d.Fam R m X Y) R n m f).trans (dif_neg h)

variable {d}

@[ext] theorem Hom.ext {X Y : S} {x y : d.Hom X Y}
    (h : ∀ m, d.component m X Y x = d.component m X Y y) : x = y :=
  DirectSum.ext (β := fun m => d.Fam R m X Y) h

@[elab_as_elim]
theorem Hom.induction_on {X Y : S} {motive : d.Hom X Y → Prop} (x : d.Hom X Y) (zero : motive 0)
    (lof : ∀ m f, motive (d.lof m X Y f)) (add : ∀ x y, motive x → motive y → motive (x + y)) :
    motive x :=
  DirectSum.induction_on (β := fun m => d.Fam R m X Y) x zero
    (fun m f => by
      have h := lof m f
      rw [ShiftData.lof] at h
      exact h) add

/-- Linear maps out of `Hom X Y` agree if they agree on homogeneous families. -/
theorem Hom.linearMap_ext {X Y : S} {N : Type*} [AddCommGroup N] [Module R N]
    {φ ψ : d.Hom X Y →ₗ[R] N} (h : ∀ m f, φ (d.lof m X Y f) = ψ (d.lof m X Y f)) : φ = ψ :=
  DirectSum.linearMap_ext R fun m => LinearMap.ext fun f => h m f

variable (d)

theorem lof_congr {X Y : S} {i j : ℤ} (h : i = j) {a : d.Fam R i X Y} {b : d.Fam R j X Y}
    (hab : (a : d.FamAll X Y) = b) : d.lof i X Y a = d.lof j X Y b := by
  subst h; congr 1; exact Subtype.ext hab

/-- Composition of morphisms, bilinearly extended from `famComp`. -/
def compL (X Y Z : S) : d.Hom X Y →ₗ[R] d.Hom Y Z →ₗ[R] d.Hom X Z :=
  DirectSum.toModule R ℤ (d.Hom Y Z →ₗ[R] d.Hom X Z) fun m =>
    LinearMap.flip (DirectSum.toModule R ℤ (d.Fam R m X Y →ₗ[R] d.Hom X Z) fun n =>
      ((d.famCompₗ m n X Y Z).flip).compr₂ (d.lof (m + n) X Z))

theorem compL_lof_lof {m n : ℤ} {X Y Z : S} (f : d.Fam R m X Y) (g : d.Fam R n Y Z) :
    d.compL X Y Z (d.lof m X Y f) (d.lof n Y Z g) = d.lof (m + n) X Z (d.famCompₗ m n X Y Z f g) := by
  simp only [compL, lof]
  erw [DirectSum.toModule_lof, LinearMap.flip_apply, DirectSum.toModule_lof]
  rfl

/-- The identity morphism. -/
def idHom (X : S) : d.Hom X X := d.lof 0 X X ⟨d.idFam X, d.idFam_mem X⟩

theorem id_compL {X Y : S} (x : d.Hom X Y) : d.compL X X Y (d.idHom X) x = x := by
  induction x using Hom.induction_on with
  | zero => simp
  | lof m f =>
    rw [idHom, compL_lof_lof]
    exact d.lof_congr (zero_add m) (by simp [famComp_idFam_left])
  | add x y hx hy => rw [map_add, hx, hy]

theorem compL_id {X Y : S} (x : d.Hom X Y) : d.compL X Y Y x (d.idHom Y) = x := by
  induction x using Hom.induction_on with
  | zero => simp
  | lof m f =>
    rw [idHom, compL_lof_lof]
    exact d.lof_congr (add_zero m) (by simp [famComp_idFam_right d f.2])
  | add x y hx hy => rw [map_add, LinearMap.add_apply, hx, hy]

theorem compL_assoc {W X Y Z : S} (x : d.Hom W X) (y : d.Hom X Y) (z : d.Hom Y Z) :
    d.compL W Y Z (d.compL W X Y x y) z = d.compL W X Z x (d.compL X Y Z y z) := by
  induction x using Hom.induction_on with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | lof m f =>
    induction y using Hom.induction_on with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']
    | lof n g =>
      induction z using Hom.induction_on with
      | zero => simp
      | add z z' hz hz' => simp only [map_add, hz, hz']
      | lof p h =>
        simp only [compL_lof_lof]
        exact d.lof_congr (add_assoc m n p) (by simp [famComp_assoc])

theorem compL_lof_lof' {m n : ℤ} {X Y Z : S} (f : d.Fam R m X Y) (g : d.Fam R n Y Z) :
    d.compL X Y Z (d.lof m X Y f) (d.lof n Y Z g) =
      d.lof (m + n) X Z ⟨d.famComp m f.1 g.1, famComp_mem f.2 g.2⟩ :=
  d.compL_lof_lof f g

/-! ## Parity projections of families -/

variable (R) in
/-- The parity-`p` part of a family, entrywise. -/
def famProj (p : ZMod 2) (m : ℤ) (X Y : S) : d.Fam R m X Y →ₗ[R] d.Fam R m X Y where
  toFun f := ⟨fun i j => proj R p (f.1 i j), fun i j h => by
      show proj R p (f.1 i j) = 0
      rw [Fam.eq_zero f.2 h, map_zero],
    fun i j => by
      show proj R p (f.1 (i + 1) (j + 1)) = _ ≫ d.Q.map (proj R p (f.1 i j)) ≫ _
      rw [Fam.compat f.2]
      have h1 := proj_comp_of_mem_left (R := R) p (d.succ_inv_mem i X)
        (d.Q.map (f.1 i j) ≫ (d.succ j).hom.app Y)
      have h2 := proj_comp_of_mem_right (R := R) p (d.Q.map (f.1 i j)) (d.succ_hom_mem j Y)
      rw [zero_add] at h1
      rw [add_zero] at h2
      rw [h1, h2, map_proj]⟩
  map_add' f g := Subtype.ext (FamAll.ext fun i j => map_add _ _ _)
  map_smul' r f := Subtype.ext (FamAll.ext fun i j => map_smul _ _ _)

@[simp] theorem famProj_apply (p : ZMod 2) {m : ℤ} {X Y : S} (f : d.Fam R m X Y) (i j : ℤ) :
    (d.famProj R p m X Y f).1 i j = proj R p (f.1 i j) := rfl

variable (R) in
/-- The parity-`p` part of a morphism. -/
def projHom (p : ZMod 2) (X Y : S) : d.Hom X Y →ₗ[R] d.Hom X Y :=
  DirectSum.toModule R ℤ (d.Hom X Y) fun m => d.lof m X Y ∘ₗ d.famProj R p m X Y

theorem projHom_lof (p : ZMod 2) {m : ℤ} {X Y : S} (f : d.Fam R m X Y) :
    d.projHom R p X Y (d.lof m X Y f) = d.lof m X Y (d.famProj R p m X Y f) := by
  rw [projHom, lof]
  erw [DirectSum.toModule_lof]
  rfl

theorem component_projHom (p : ZMod 2) (m : ℤ) {X Y : S} (x : d.Hom X Y) :
    d.component m X Y (d.projHom R p X Y x) = d.famProj R p m X Y (d.component m X Y x) := by
  induction x using Hom.induction_on with
  | zero => simp
  | lof n f =>
    rw [projHom_lof]
    by_cases h : n = m
    · subst h; simp
    · rw [d.component_lof_of_ne _ h, d.component_lof_of_ne _ h, map_zero]
  | add x y hx hy => simp [hx, hy]

variable (R) in
/-- The morphisms of parity `p`: all entries of all components have parity `p`. -/
def parityHom (X Y : S) (p : ZMod 2) : Submodule R (d.Hom X Y) where
  carrier := {x | ∀ m i j, (d.component m X Y x).1 i j ∈ parity (R := R) _ _ p}
  add_mem' hx hy m i j := by
    simp only [map_add, Submodule.coe_add, FamAll.add_apply]
    exact Submodule.add_mem _ (hx m i j) (hy m i j)
  zero_mem' m i j := by simp only [map_zero, Submodule.coe_zero, FamAll.zero_apply]; exact Submodule.zero_mem _
  smul_mem' r x hx m i j := by
    simp only [map_smul, Submodule.coe_smul, FamAll.smul_apply]
    exact Submodule.smul_mem _ _ (hx m i j)

theorem projHom_mem (p : ZMod 2) {X Y : S} (x : d.Hom X Y) : d.projHom R p X Y x ∈ d.parityHom R X Y p :=
  fun m i j => by rw [component_projHom, famProj_apply]; exact proj_mem _ _

theorem projHom_of_mem {p : ZMod 2} {X Y : S} {x : d.Hom X Y} (hx : x ∈ d.parityHom R X Y p) :
    d.projHom R p X Y x = x :=
  Hom.ext fun m => Subtype.ext (FamAll.ext fun i j => by
    rw [component_projHom, famProj_apply, proj_of_mem (hx m i j)])

theorem projHom_add_projHom {X Y : S} (x : d.Hom X Y) :
    d.projHom R 0 X Y x + d.projHom R 1 X Y x = x :=
  Hom.ext fun m => Subtype.ext (FamAll.ext fun i j => by
    rw [map_add, component_projHom, component_projHom]
    exact proj_add_proj _)

theorem compL_projHom_mem (p q : ZMod 2) {X Y Z : S} (x : d.Hom X Y) (y : d.Hom Y Z) :
    d.compL X Y Z (d.projHom R p X Y x) (d.projHom R q Y Z y) ∈ d.parityHom R X Z (p + q) := by
  induction x using Hom.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply]; exact Submodule.add_mem _ hx hx'
  | lof m f =>
    induction y using Hom.induction_on with
    | zero => simp only [map_zero]; exact Submodule.zero_mem _
    | add y y' hy hy' => simp only [map_add]; exact Submodule.add_mem _ hy hy'
    | lof n g =>
      rw [projHom_lof, projHom_lof, compL_lof_lof']
      intro k i l
      by_cases h : m + n = k
      · subst h
        simp only [component_lof_self, famComp]
        exact comp_mem (proj_mem _ _) (proj_mem _ _)
      · rw [d.component_lof_of_ne _ h]; exact Submodule.zero_mem _

theorem compL_mem {p q : ZMod 2} {X Y Z : S} {x : d.Hom X Y} {y : d.Hom Y Z}
    (hx : x ∈ d.parityHom R X Y p) (hy : y ∈ d.parityHom R Y Z q) :
    d.compL X Y Z x y ∈ d.parityHom R X Z (p + q) := by
  rw [← d.projHom_of_mem hx, ← d.projHom_of_mem hy]
  exact d.compL_projHom_mem p q x y

/-! ## Degrees -/

variable (R) in
/-- The morphisms of degree `n`: the families of degree `n`. -/
def degreeHom (X Y : S) (n : ℤ) : Submodule R (d.Hom X Y) := LinearMap.range (d.lof n X Y)

theorem isInternal_degreeHom (X Y : S) : DirectSum.IsInternal (d.degreeHom R X Y) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · rw [iSupIndep_def]
    intro n
    rw [Submodule.disjoint_def]
    intro x hx hx'
    obtain ⟨f, rfl⟩ := hx
    have h0 : d.component n X Y (d.lof n X Y f) = 0 := by
      have hle : (⨆ j, ⨆ (_ : j ≠ n), d.degreeHom R X Y j) ≤ LinearMap.ker (d.component n X Y) := by
        refine iSup_le fun j => iSup_le fun hj => ?_
        rintro _ ⟨g, rfl⟩
        exact d.component_lof_of_ne _ hj
      exact hle hx'
    rw [component_lof_self] at h0
    rw [h0, map_zero]
  · rw [eq_top_iff]
    rintro x -
    induction x using Hom.induction_on with
    | zero => exact Submodule.zero_mem _
    | lof m f => exact Submodule.mem_iSup_of_mem m ⟨f, rfl⟩
    | add x y hx hy => exact Submodule.add_mem _ hx hy

end ShiftData

end StringDiagrams

end
