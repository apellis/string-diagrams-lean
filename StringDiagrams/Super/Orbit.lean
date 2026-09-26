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

universe w v u v₁ u₁

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

theorem comm_zero_hom_app (X : S) : (d.comm 0).hom.app X = 𝟙 (d.Q.obj X) := by
  show 𝟙 _ ≫ 𝟙 _ = _
  exact Category.id_comp _

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

/-! ## Diagonal families -/

/-- The diagonal family with entries `φ i : Qⁱ X ⟶ Qⁱ Y`. -/
def diagFam {X Y : S} (φ : ∀ i : ℤ, (d.pow i).obj X ⟶ (d.pow i).obj Y) : d.FamAll X Y :=
  fun i j => if h : i = j then φ i ≫ eqToHom (congrArg (fun k => (d.pow k).obj Y) h) else 0

theorem diagFam_self {X Y : S} (φ : ∀ i : ℤ, (d.pow i).obj X ⟶ (d.pow i).obj Y) (i : ℤ) :
    d.diagFam φ i i = φ i := by simp [diagFam]

theorem diagFam_mem {X Y : S} {φ : ∀ i : ℤ, (d.pow i).obj X ⟶ (d.pow i).obj Y}
    (hφ : ∀ i, φ (i + 1) = (d.succ i).inv.app X ≫ d.Q.map (φ i) ≫ (d.succ i).hom.app Y) :
    d.diagFam φ ∈ d.Fam R 0 X Y := by
  refine ⟨fun i j h => ?_, fun i j => ?_⟩
  · rw [diagFam, dif_neg (by omega)]
  · by_cases h : i = j
    · subst h; rw [diagFam_self, diagFam_self, hφ]
    · rw [diagFam, diagFam, dif_neg h, dif_neg (by omega)]; simp

theorem famComp_diagFam {X Y Z : S} (φ : ∀ i : ℤ, (d.pow i).obj X ⟶ (d.pow i).obj Y)
    (ψ : ∀ i : ℤ, (d.pow i).obj Y ⟶ (d.pow i).obj Z) :
    d.famComp 0 (d.diagFam φ) (d.diagFam ψ) = d.diagFam fun i => φ i ≫ ψ i := by
  ext i k
  simp only [famComp]
  rw [show i - 0 = i by ring, diagFam_self]
  by_cases h : i = k
  · subst h; simp [diagFam_self]
  · simp [diagFam, h]

/-- The family `(Qⁱ g)ᵢ` of a morphism `g` of `S`. -/
def mapFam {X Y : S} (g : X ⟶ Y) : d.Fam R 0 X Y :=
  ⟨d.diagFam fun i => (d.pow i).map g, d.diagFam_mem fun i => by
    have := (d.succ i).hom.naturality g
    simp only [Functor.comp_map] at this
    rw [this, Iso.inv_hom_id_app_assoc]⟩

/-! ## Families are determined by one entry -/

variable {d} in
theorem FamAll.congr_entry {X Y : S} {f g : d.FamAll X Y} {i j i' j' : ℤ} (hi : i = i')
    (hj : j = j') (h : f i j = g i j) : f i' j' = g i' j' := by
  subst hi hj; exact h

variable {d} in
theorem Fam.eq_of_entry {m : ℤ} {X Y : S} {f g : d.FamAll X Y} (hf : f ∈ d.Fam R m X Y)
    (hg : g ∈ d.Fam R m X Y) {i₀ j₀ : ℤ} (h₀ : i₀ - j₀ = m) (h : f i₀ j₀ = g i₀ j₀) : f = g := by
  have key : ∀ k : ℤ, f (i₀ + k) (j₀ + k) = g (i₀ + k) (j₀ + k) := by
    intro k
    induction k using Int.induction_on with
    | hz => exact FamAll.congr_entry (by ring) (by ring) h
    | hp k ih =>
      have e := FamAll.congr_entry (f := f) (g := g) (i' := i₀ + (k + 1)) (j' := j₀ + (k + 1))
        (by ring) (by ring) (show f (i₀ + k + 1) (j₀ + k + 1) = g (i₀ + k + 1) (j₀ + k + 1) by
          rw [Fam.compat hf, Fam.compat hg, ih])
      exact e
    | hn k ih =>
      have e := FamAll.congr_entry (f := f) (g := g)
        (i' := i₀ + (-(k : ℤ) - 1) + 1) (j' := j₀ + (-(k : ℤ) - 1) + 1) (by ring) (by ring) ih
      rw [Fam.compat hf, Fam.compat hg] at e
      have e3 := (cancel_mono _).1 ((cancel_epi _).1 e)
      exact d.Q.map_injective e3
  ext i j
  by_cases hij : i - j = m
  · exact FamAll.congr_entry (by ring) (by omega) (key (i - i₀))
  · rw [Fam.eq_zero hf hij, Fam.eq_zero hg hij]

/-! ## The families `σ` -/

/-- The family `σ_{i,i+1} : Qⁱ(Q X) ≅ Qⁱ⁺¹ X` (degree `-1`). -/
def famσ (X : S) : d.FamAll (d.Q.obj X) X :=
  fun i j => if h : j = i + 1 then
    (d.comm i).hom.app X ≫ eqToHom (congrArg (fun k => (d.pow k).obj X) h.symm) else 0

/-- The inverse family (degree `1`). -/
def famσinv (X : S) : d.FamAll X (d.Q.obj X) :=
  fun i j => if h : i = j + 1 then
    eqToHom (congrArg (fun k => (d.pow k).obj X) h) ≫ (d.comm j).inv.app X else 0

theorem famσ_succ (X : S) (i : ℤ) : d.famσ X i (i + 1) = (d.comm i).hom.app X := by
  simp [famσ]

theorem famσinv_succ (X : S) (j : ℤ) : d.famσinv X (j + 1) j = (d.comm j).inv.app X := by
  simp [famσinv]

theorem famσ_mem (X : S) : d.famσ X ∈ d.Fam R (-1) (d.Q.obj X) X := by
  refine ⟨fun i j h => ?_, fun i j => ?_⟩
  · rw [famσ, dif_neg (by omega)]
  · by_cases h : j = i + 1
    · subst h
      rw [famσ_succ, famσ_succ, d.comm_succ]
    · rw [famσ, famσ, dif_neg h, dif_neg (by omega)]; simp

theorem famσinv_mem (X : S) : d.famσinv X ∈ d.Fam R 1 X (d.Q.obj X) := by
  refine ⟨fun i j h => ?_, fun i j => ?_⟩
  · rw [famσinv, dif_neg (by omega)]
  · by_cases h : i = j + 1
    · subst h
      rw [famσinv_succ, famσinv_succ, ← cancel_epi ((d.comm (j + 1)).hom.app X),
        Iso.hom_inv_id_app, d.comm_succ]
      simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
      rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
      erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app]
      rfl
    · rw [famσinv, famσinv, dif_neg h, dif_neg (by omega)]; simp

theorem famComp_famσ_famσinv (X : S) :
    d.famComp (-1) (d.famσ X) (d.famσinv X) = d.idFam (d.Q.obj X) := by
  ext i k
  simp only [famComp]
  rw [show i - -1 = i + 1 by ring, famσ_succ]
  by_cases h : i = k
  · subst h; rw [famσinv_succ, Iso.hom_inv_id_app, idFam_self]; rfl
  · rw [famσinv, dif_neg (by omega), Limits.comp_zero, idFam, dif_neg h]

theorem famComp_famσinv_famσ (X : S) :
    d.famComp 1 (d.famσinv X) (d.famσ X) = d.idFam X := by
  ext i k
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by ring⟩
  simp only [famComp]
  rw [show j + 1 - 1 = j by ring, famσinv_succ]
  by_cases h : k = j + 1
  · subst h; rw [famσ_succ, Iso.inv_hom_id_app, idFam_self]
  · rw [famσ, dif_neg h, Limits.comp_zero, idFam, dif_neg (Ne.symm h)]

end ShiftData

/-! ## The orbit supercategory -/

/-- The orbit supercategory of `d`: the objects of `S`; see the module documentation. -/
@[ext]
structure Orbit {R : Type w} [CommRing R] {S : Type u} [Category.{v} S] [Preadditive S]
    [Linear R S] [Supercategory R S] (d : ShiftData R S) where
  /-- The object of `S`. -/
  obj : S

namespace Orbit

open ShiftData GradedSupercategory

variable {R} {S : Type u} [Category.{v} S] [Preadditive S] [Linear R S] [Supercategory R S]
  {d : ShiftData R S}

instance : Category (Orbit d) where
  Hom X Y := d.Hom X.obj Y.obj
  id X := d.idHom X.obj
  comp f g := d.compL _ _ _ f g
  id_comp f := d.id_compL f
  comp_id f := d.compL_id f
  assoc f g h := d.compL_assoc f g h

theorem comp_def {X Y Z : Orbit d} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ g = d.compL X.obj Y.obj Z.obj f g := rfl

theorem id_def (X : Orbit d) : 𝟙 X = d.idHom X.obj := rfl

instance : Preadditive (Orbit d) where
  homGroup X Y := inferInstanceAs (AddCommGroup (d.Hom X.obj Y.obj))
  add_comp X Y Z f f' g := LinearMap.map_add₂ (d.compL X.obj Y.obj Z.obj) f f' g
  comp_add X Y Z f g g' := LinearMap.map_add (d.compL X.obj Y.obj Z.obj f) g g'

instance : Linear R (Orbit d) where
  homModule X Y := inferInstanceAs (Module R (d.Hom X.obj Y.obj))
  smul_comp X Y Z r f g := LinearMap.map_smul₂ (d.compL X.obj Y.obj Z.obj) r f g
  comp_smul X Y Z f r g := LinearMap.map_smul (d.compL X.obj Y.obj Z.obj f) r g

/-- The orbit supercategory is a supercategory: a morphism has parity `p` if all entries of all
its families do. -/
instance : Supercategory R (Orbit d) where
  parity X Y p := d.parityHom R X.obj Y.obj p
  isInternal X Y := by
    rw [DirectSum.isInternal_submodule_iff_isCompl _ (i := 0) (j := 1) (by decide)
      (by ext p; rcases parity_eq_zero_or_one p with rfl | rfl <;> simp)]
    constructor
    · rw [Submodule.disjoint_def]
      intro x h0 h1
      refine Hom.ext fun m => Subtype.ext (FamAll.ext fun i j => ?_)
      have e := proj_of_mem (R := R) (h0 m i j)
      rw [proj_of_mem_ne (h1 m i j) (by decide)] at e
      simpa using e.symm
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      rw [← d.projHom_add_projHom x]
      exact Submodule.add_mem_sup (d.projHom_mem 0 x) (d.projHom_mem 1 x)
  id_mem X m i j := by
    by_cases h : m = 0
    · subst h
      simp only [id_def, idHom, component_lof_self, idFam]
      split_ifs with hij
      · subst hij; simpa using id_mem (R := R) _
      · exact Submodule.zero_mem _
    · rw [id_def, idHom, d.component_lof_of_ne _ (Ne.symm h)]; exact Submodule.zero_mem _
  comp_mem hf hg := d.compL_mem hf hg

theorem mem_parity_iff {X Y : Orbit d} {p : ZMod 2} {f : X ⟶ Y} :
    f ∈ parity (R := R) X Y p ↔ f ∈ d.parityHom R X.obj Y.obj p := Iff.rfl

theorem proj_eq {X Y : Orbit d} (p : ZMod 2) (f : X ⟶ Y) :
    proj R p f = d.projHom R p X.obj Y.obj f :=
  proj_eq_of_add (h := d.projHom R (p + 1) X.obj Y.obj f)
    (by
      rcases parity_eq_zero_or_one p with rfl | rfl
      · exact (d.projHom_add_projHom f).symm
      · rw [add_comm]; exact (d.projHom_add_projHom f).symm)
    (d.projHom_mem p f) (d.projHom_mem (p + 1) f)

/-- The orbit supercategory is graded: the families of degree `m` have degree `m`. -/
instance : GradedSupercategory R (Orbit d) where
  degree X Y n := d.degreeHom R X.obj Y.obj n
  isInternal_degree X Y := d.isInternal_degreeHom X.obj Y.obj
  proj_mem_degree p {X Y n f} hf := by
    obtain ⟨g, rfl⟩ := hf
    rw [proj_eq, projHom_lof]
    exact ⟨_, rfl⟩
  id_mem_degree X := ⟨_, rfl⟩
  comp_mem_degree {X Y Z m n f g} hf hg := by
    obtain ⟨f, rfl⟩ := hf
    obtain ⟨g, rfl⟩ := hg
    exact ⟨_, (d.compL_lof_lof f g).symm⟩

theorem mem_degree_iff {X Y : Orbit d} {n : ℤ} {f : X ⟶ Y} :
    f ∈ GradedSupercategory.degree (R := R) X Y n ↔ ∃ g, d.lof n X.obj Y.obj g = f := Iff.rfl

theorem lof_mem_degree {X Y : Orbit d} {n : ℤ} (g : d.Fam R n X.obj Y.obj) :
    (d.lof n X.obj Y.obj g : X ⟶ Y) ∈ GradedSupercategory.degree (R := R) X Y n := ⟨g, rfl⟩

/-! ## The inclusion of `S` in degree zero -/

variable (d) in
/-- The inclusion `ι : S ⥤ Orbit d`, `g ↦ (Qⁱ g)ᵢ` in degree `0`. -/
@[simps obj]
def ι : S ⥤ Orbit d where
  obj X := ⟨X⟩
  map {X Y} g := d.lof 0 X Y (d.mapFam g)
  map_id X := by
    show d.lof 0 X X _ = d.lof 0 X X _
    congr 1
    refine Subtype.ext (FamAll.ext fun i j => ?_)
    simp [mapFam, diagFam, idFam]
  map_comp {X Y Z} f g := by
    show d.lof 0 X Z _ = d.compL X Y Z (d.lof 0 X Y _) (d.lof 0 Y Z _)
    rw [compL_lof_lof]
    refine d.lof_congr (add_zero 0).symm ?_
    rw [famCompₗ_apply]
    simp only [mapFam]
    rw [famComp_diagFam]
    simp

theorem ι_map (d : ShiftData R S) {X Y : S} (g : X ⟶ Y) :
    ((ι d).map g : (⟨X⟩ : Orbit d) ⟶ ⟨Y⟩) = d.lof 0 X Y (d.mapFam g) := rfl

instance : (ι d).Additive where
  map_add {X Y f g} := by
    show d.lof 0 X Y _ = d.lof 0 X Y _ + d.lof 0 X Y _
    rw [← map_add]; congr 1
    exact Subtype.ext (FamAll.ext fun i j => by
      simp only [mapFam, diagFam, Functor.map_add, Submodule.coe_add, FamAll.add_apply]
      split_ifs <;> simp [Preadditive.add_comp])

instance : (ι d).Linear R where
  map_smul {X Y} f r := by
    show d.lof 0 X Y _ = r • d.lof 0 X Y _
    rw [← map_smul]; congr 1
    exact Subtype.ext (FamAll.ext fun i j => by
      simp only [mapFam, diagFam, Functor.map_smul, Submodule.coe_smul, FamAll.smul_apply]
      split_ifs <;> simp)

instance : IsSuperfunctor R (ι d) where
  map_mem {X Y p f} hf m i j := by
    show (d.component m X Y (d.lof 0 X Y (d.mapFam f))).1 i j ∈ _
    by_cases h : m = 0
    · subst h
      simp only [component_lof_self, mapFam, diagFam]
      split_ifs with hij
      · subst hij; simpa using map_mem (d.pow i) hf
      · exact Submodule.zero_mem _
    · rw [d.component_lof_of_ne _ (Ne.symm h)]; exact Submodule.zero_mem _

theorem ι_map_mem_degree {X Y : S} (g : X ⟶ Y) :
    (ι d).map g ∈ GradedSupercategory.degree (R := R) ((ι d).obj X) ((ι d).obj Y) 0 :=
  ⟨_, rfl⟩

/-! ## The degree-zero part of the orbit supercategory is `S` -/

variable (d) in
/-- `ι` as a functor into the morphisms of degree zero. -/
@[simps obj]
def ιZ : S ⥤ DegreeZero R (Orbit d) where
  obj X := ⟨⟨X⟩⟩
  map g := ⟨(ι d).map g, ι_map_mem_degree g⟩
  map_id X := DegreeZero.hom_ext ((ι d).map_id X)
  map_comp f g := DegreeZero.hom_ext ((ι d).map_comp f g)

instance : (ιZ d).Additive where
  map_add := DegreeZero.hom_ext (ι d).map_add

instance : (ιZ d).Linear R where
  map_smul f r := DegreeZero.hom_ext (Functor.Linear.map_smul (F := ι d) f r)

instance : IsSuperfunctor R (ιZ d) where
  map_mem hf := map_mem (R := R) (ι d) hf

theorem _root_.StringDiagrams.ShiftData.component_zero_compL {X Y Z : S} {x : d.Hom X Y}
    {y : d.Hom Y Z} (hx : x ∈ d.degreeHom R X Y 0) (hy : y ∈ d.degreeHom R Y Z 0) :
    d.component 0 X Z (d.compL X Y Z x y) =
      ⟨d.famComp 0 (d.component 0 X Y x).1 (d.component 0 Y Z y).1,
        by simpa using famComp_mem (d.component 0 X Y x).2 (d.component 0 Y Z y).2⟩ := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  rw [compL_lof_lof, show d.lof (0 + 0) X Z (d.famCompₗ 0 0 X Y Z a b) =
    d.lof 0 X Z ⟨d.famComp 0 a.1 b.1, by simpa using famComp_mem a.2 b.2⟩ from
      d.lof_congr (add_zero 0) rfl]
  simp only [component_lof_self]

theorem degreeZero_eq_lof {X Y : Orbit d} (x : (⟨X⟩ : DegreeZero R (Orbit d)) ⟶ ⟨Y⟩) :
    x.1 = d.lof 0 X.obj Y.obj (d.component 0 X.obj Y.obj x.1) := by
  obtain ⟨f, hf⟩ := x.2
  rw [← hf, component_lof_self]

variable (d) in
/-- The entry `(0, 0)` of a morphism of degree zero. -/
@[simps obj]
def π₀ : DegreeZero R (Orbit d) ⥤ S where
  obj X := X.obj.obj
  map {X Y} x := (d.component 0 X.obj.obj Y.obj.obj x.1).1 0 0
  map_id X := by
    show (d.component 0 _ _ (d.idHom X.obj.obj)).1 0 0 = _
    simp [idHom, idFam_self]
  map_comp {X Y Z} x y := by
    show (d.component 0 _ _ (d.compL _ _ _ x.1 y.1)).1 0 0 = _
    rw [d.component_zero_compL x.2 y.2]
    rfl

theorem π₀_comp_ιZ_map {X Y : Orbit d} (x : (⟨X⟩ : DegreeZero R (Orbit d)) ⟶ ⟨Y⟩) :
    (ιZ d).map ((π₀ d).map x) = x := by
  apply DegreeZero.hom_ext
  show d.lof 0 _ _ (d.mapFam _) = x.1
  rw [degreeZero_eq_lof x]
  congr 1
  refine Subtype.ext (Fam.eq_of_entry (d.mapFam _).2 (d.component 0 _ _ x.1).2
    (i₀ := 0) (j₀ := 0) rfl ?_)
  simp [mapFam, diagFam_self]; rfl

theorem ιZ_comp_π₀_map {X Y : S} (g : X ⟶ Y) : (π₀ d).map ((ιZ d).map g) = g := by
  show (d.component 0 _ _ (d.lof 0 _ _ (d.mapFam g))).1 0 0 = g
  rw [component_lof_self]
  simp [mapFam, diagFam_self]

theorem ιZ_comp_π₀ : ιZ d ⋙ π₀ d = 𝟭 S :=
  CategoryTheory.Functor.ext (fun _ => rfl) fun X Y g => by simpa using ιZ_comp_π₀_map g

theorem π₀_comp_ιZ : π₀ d ⋙ ιZ d = 𝟭 _ :=
  CategoryTheory.Functor.ext (fun _ => rfl) fun X Y x => by simpa using π₀_comp_ιZ_map x

instance : (π₀ d).Additive where
  map_add {X Y x y} := by
    show (d.component 0 _ _ (x.1 + y.1)).1 0 0 = _
    rw [map_add]; rfl

instance : (π₀ d).Linear R where
  map_smul {X Y} x r := by
    show (d.component 0 _ _ (r • x.1)).1 0 0 = _
    rw [map_smul]; rfl

instance : IsSuperfunctor R (π₀ d) where
  map_mem hx := hx 0 0 0

/-! ## The Π-structure -/

section Pi

variable [PiSupercategory R S]

/-- The odd isomorphisms `ζ_X : Π X ≅ X` of `S`, in degree `0`. -/
def ζIso (X : Orbit d) : (⟨(PiSupercategory.pi (R := R)).obj X.obj⟩ : Orbit d) ≅ X :=
  (ι d).mapIso (PiSupercategory.ζ (R := R) X.obj)

theorem ζIso_hom_mem (X : Orbit d) :
    (ζIso X).hom ∈ parity (R := R) (⟨(PiSupercategory.pi (R := R)).obj X.obj⟩ : Orbit d) X 1 :=
  map_mem (ι d) (PiSupercategory.ζ_hom_mem X.obj)

/-- The orbit supercategory of a Π-supercategory is a Π-supercategory, with `Π` and `ζ`
induced from `S`. -/
instance instPiSupercategory : PiSupercategory R (Orbit d) :=
  PiSupercategory.ofIso (fun X => ⟨(PiSupercategory.pi (R := R)).obj X.obj⟩) ζIso ζIso_hom_mem

theorem ζ_eq (X : Orbit d) : PiSupercategory.ζ (R := R) X = ζIso X := rfl

@[simp] theorem pi_obj (X : Orbit d) :
    (PiSupercategory.pi (R := R)).obj X = ⟨(PiSupercategory.pi (R := R)).obj X.obj⟩ := rfl

/-- `Π` commutes with `ι`. -/
theorem pi_map_ι {X Y : S} (g : X ⟶ Y) :
    (PiSupercategory.pi (R := R)).map ((ι d).map g) =
      (ι d).map ((PiSupercategory.pi (R := R)).map g) := by
  show (ζIso _).hom ≫ twist R 1 ((ι d).map g) ≫ (ζIso _).inv = _
  rw [← map_twist (ι d), ζIso, ζIso, Functor.mapIso_hom, Functor.mapIso_inv, ← Functor.map_comp,
    ← Functor.map_comp, PiSupercategory.pi_map_eq (R := R) g]
  rfl

/-- `ξ = ζζ` of the orbit supercategory is `ξ` of `S`. -/
theorem ξ_hom_eq (X : S) :
    (PiSupercategory.ξ (R := R) (⟨X⟩ : Orbit d)).hom = (ι d).map (PiSupercategory.ξ (R := R) X).hom := by
  rw [PiSupercategory.ξ_hom, PiSupercategory.ξ_hom, ζ_eq, ζIso, Functor.mapIso_hom]
  erw [pi_map_ι]
  rw [← Functor.map_comp]

end Pi

/-! ## The `Q`-structure -/

/-- The even isomorphism `σ_X : Q X ≅ X` of degree `-1`. -/
def σIso (X : Orbit d) : (⟨d.Q.obj X.obj⟩ : Orbit d) ≅ X where
  hom := d.lof (-1) _ _ ⟨d.famσ X.obj, d.famσ_mem X.obj⟩
  inv := d.lof 1 _ _ ⟨d.famσinv X.obj, d.famσinv_mem X.obj⟩
  hom_inv_id := by
    show d.compL _ _ _ _ _ = d.idHom _
    rw [compL_lof_lof]
    exact d.lof_congr (by norm_num) (by rw [famCompₗ_apply]; exact d.famComp_famσ_famσinv _)
  inv_hom_id := by
    show d.compL _ _ _ _ _ = d.idHom _
    rw [compL_lof_lof]
    exact d.lof_congr (by norm_num) (by rw [famCompₗ_apply]; exact d.famComp_famσinv_famσ _)

theorem σIso_hom_mem (X : Orbit d) :
    (σIso X).hom ∈ parity (R := R) (⟨d.Q.obj X.obj⟩ : Orbit d) X 0 := by
  intro m i j
  show (d.component m _ _ (d.lof (-1) _ _ _)).1 i j ∈ _
  by_cases h : m = -1
  · subst h
    simp only [component_lof_self, famσ]
    split_ifs with hij
    · subst hij; simpa using d.comm_hom_mem i X.obj
    · exact Submodule.zero_mem _
  · rw [d.component_lof_of_ne _ (Ne.symm h)]; exact Submodule.zero_mem _

theorem σIso_hom_mem_degree (X : Orbit d) :
    (σIso X).hom ∈ GradedSupercategory.degree (R := R) (⟨d.Q.obj X.obj⟩ : Orbit d) X (-1) :=
  ⟨_, rfl⟩

/-- `σ` is natural with respect to the morphisms of `S`: `σ_Y ∘ ι(Q g) = ι(g) ∘ σ_X`. -/
theorem σIso_hom_naturality {X Y : S} (g : X ⟶ Y) :
    (σIso ((ι d).obj X)).hom ≫ (ι d).map g = (ι d).map (d.Q.map g) ≫ (σIso ((ι d).obj Y)).hom := by
  show d.compL _ _ _ (d.lof (-1) _ _ _) (d.lof 0 _ _ _) = d.compL _ _ _ (d.lof 0 _ _ _) (d.lof (-1) _ _ _)
  rw [compL_lof_lof, compL_lof_lof]
  refine d.lof_congr (by norm_num) ?_
  rw [famCompₗ_apply, famCompₗ_apply]
  ext i k
  simp only [famComp, mapFam]
  rw [show i - -1 = i + 1 by ring, show i - 0 = i by ring, diagFam_self]
  by_cases h : k = i + 1
  · subst h
    rw [famσ_succ, famσ_succ, diagFam_self]
    exact ((d.comm i).hom.naturality g).symm
  · rw [famσ_succ, diagFam, dif_neg (Ne.symm h), Limits.comp_zero, famσ, dif_neg h,
      Limits.comp_zero]

/-- The even isomorphism `σ̄_X : Q⁻¹ X ≅ X` of degree `1`: `σ_{Q⁻¹X}⁻¹` followed by the counit. -/
def σbarIso (X : Orbit d) : (⟨d.Qi.obj X.obj⟩ : Orbit d) ≅ X :=
  (σIso (⟨d.Qi.obj X.obj⟩ : Orbit d)).symm ≪≫ (ι d).mapIso (d.e.counitIso.app X.obj)

theorem σbarIso_hom_mem (X : Orbit d) :
    (σbarIso X).hom ∈ parity (R := R) (⟨d.Qi.obj X.obj⟩ : Orbit d) X 0 := by
  have := comp_mem (inv_mem _ (σIso_hom_mem (⟨d.Qi.obj X.obj⟩ : Orbit d)))
    (map_mem (ι d) (d.counit_mem X.obj))
  simpa [σbarIso] using this

theorem σbarIso_hom_mem_degree (X : Orbit d) :
    (σbarIso X).hom ∈ GradedSupercategory.degree (R := R) (⟨d.Qi.obj X.obj⟩ : Orbit d) X 1 := by
  have := GradedSupercategory.comp_mem_degree
    (GradedSupercategory.inv_mem_degree _ (σIso_hom_mem_degree (⟨d.Qi.obj X.obj⟩ : Orbit d)))
    (ι_map_mem_degree (d := d) (d.e.counitIso.hom.app X.obj))
  simpa [σbarIso] using this

/-- **The orbit supercategory of a Π-supercategory is a graded `(Q, Π)`-supercategory**, with
`Q X = Q X` and `σ` of degree `-1` given by the isomorphisms `Qⁱ Q ≅ Qⁱ⁺¹`, and
`Q⁻¹ X = Q⁻¹ X` with `σ̄ = σ⁻¹` followed by the counit. -/
instance instQPiSupercategory [PiSupercategory R S] : QPiSupercategory R (Orbit d) :=
  QPiSupercategory.ofIso (fun X => ι_map_mem_degree (d := d) (PiSupercategory.ζ (R := R) X.obj).hom)
    (fun X => ⟨d.Q.obj X.obj⟩) σIso σIso_hom_mem σIso_hom_mem_degree
    (fun X => ⟨d.Qi.obj X.obj⟩) σbarIso σbarIso_hom_mem σbarIso_hom_mem_degree

theorem Q_map_ι [PiSupercategory R S] {X Y : S} (g : X ⟶ Y) :
    (QPiSupercategory.Q (R := R) (C := Orbit d)).map ((ι d).map g) = (ι d).map (d.Q.map g) := by
  show (σIso _).hom ≫ (ι d).map g ≫ (σIso _).inv = _
  rw [reassoc_of% (σIso_hom_naturality g), Iso.hom_inv_id, Category.comp_id]

@[simp] theorem Q_obj [PiSupercategory R S] (X : Orbit d) :
    (QPiSupercategory.Q (R := R) (C := Orbit d)).obj X = ⟨d.Q.obj X.obj⟩ := rfl

theorem σ_eq [PiSupercategory R S] (X : Orbit d) : QPiSupercategory.σ (R := R) X = σIso X := rfl

end Orbit


/-! ## Functoriality of the orbit supercategory -/

/-- A morphism of shift data: a superfunctor `F : S ⥤ S'` with an even natural isomorphism
`γ : Q' F ≅ F Q` (in diagrammatic order `F ⋙ Q' ≅ Q ⋙ F`). -/
structure ShiftFunctor {S : Type u} [Category.{v} S] [Preadditive S] [Linear R S]
    [Supercategory R S] {S' : Type u₁} [Category.{v₁} S'] [Preadditive S'] [Linear R S']
    [Supercategory R S'] (d : ShiftData R S) (d' : ShiftData R S') where
  /-- The superfunctor. -/
  F : S ⥤ S'
  [additive : F.Additive]
  [linear : F.Linear R]
  [isSuperfunctor : IsSuperfunctor R F]
  /-- `γ : F ⋙ Q' ≅ Q ⋙ F`. -/
  γ : F ⋙ d'.Q ≅ d.Q ⋙ F
  γ_mem : ∀ X : S, γ.hom.app X ∈ parity (R := R) (d'.Q.obj (F.obj X)) (F.obj (d.Q.obj X)) 0

attribute [instance] ShiftFunctor.additive ShiftFunctor.linear ShiftFunctor.isSuperfunctor

namespace ShiftFunctor

variable {R} {S : Type u} [Category.{v} S] [Preadditive S] [Linear R S] [Supercategory R S]
  {S' : Type u₁} [Category.{v₁} S'] [Preadditive S'] [Linear R S'] [Supercategory R S']
  {d : ShiftData R S} {d' : ShiftData R S'} (Φ : ShiftFunctor R d d')

open ShiftData

/-- `Γⁿ : Q'ⁿ F ≅ F Qⁿ` for `n ∈ ℕ`. -/
def ΓNat : ∀ n : ℕ, Φ.F ⋙ d'.powNat n ≅ d.powNat n ⋙ Φ.F
  | 0 => Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm
  | n + 1 => (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (ΓNat n) d'.Q ≪≫
      Functor.associator _ _ _ ≪≫ isoWhiskerLeft (d.powNat n) Φ.γ ≪≫ (Functor.associator _ _ _).symm

theorem ΓNat_succ_hom_app (n : ℕ) (X : S) :
    (Φ.ΓNat (n + 1)).hom.app X = d'.Q.map ((Φ.ΓNat n).hom.app X) ≫ Φ.γ.hom.app ((d.powNat n).obj X) := by
  show 𝟙 _ ≫ _ ≫ 𝟙 _ ≫ _ ≫ 𝟙 _ = _
  simp

/-- The isomorphism `Q'⁻ⁿ⁻¹ F ≅ F Q⁻ⁿ⁻¹` determined by the compatibility with `Γ⁻ⁿ`, using that
`Q'` is fully faithful. -/
def ΓNegAux (n : ℕ) (Γ' : Φ.F ⋙ d'.pow (Int.negSucc n + 1) ≅ d.pow (Int.negSucc n + 1) ⋙ Φ.F) :
    Φ.F ⋙ d'.powNeg (n + 1) ≅ d.powNeg (n + 1) ⋙ Φ.F :=
  NatIso.ofComponents (fun X => d'.Q.preimageIso (((d'.succ (Int.negSucc n)).app (Φ.F.obj X)) ≪≫
      Γ'.app X ≪≫ Φ.F.mapIso ((d.succ (Int.negSucc n)).app X).symm ≪≫
        (Φ.γ.app ((d.pow (Int.negSucc n)).obj X)).symm))
    (fun {X Y} f => d'.Q.map_injective (by
      simp only [Functor.comp_obj, Functor.comp_map, Iso.trans_hom, Iso.app_hom,
        Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv, Functor.map_comp,
        Functor.preimageIso_hom, Functor.map_preimage, Category.assoc]
      have n1 := (d'.succ (Int.negSucc n)).hom.naturality (Φ.F.map f)
      have n2 := Γ'.hom.naturality f
      have n3 := (d.succ (Int.negSucc n)).inv.naturality f
      have n4 := Φ.γ.inv.naturality ((d.pow (Int.negSucc n)).map f)
      simp only [Functor.comp_obj, Functor.comp_map] at n1 n2 n3 n4
      erw [reassoc_of% n1, reassoc_of% n2, ← Φ.F.map_comp_assoc, n3, Φ.F.map_comp_assoc, n4]
      rfl))

/-- `Γⁿ : Q'ⁿ F ≅ F Qⁿ` for `n < 0`. -/
def ΓNeg : ∀ n : ℕ, Φ.F ⋙ d'.powNeg (n + 1) ≅ d.powNeg (n + 1) ⋙ Φ.F
  | 0 => Φ.ΓNegAux 0 (Φ.ΓNat 0)
  | n + 1 => Φ.ΓNegAux (n + 1) (ΓNeg n)

/-- `Γⁱ : Q'ⁱ F ≅ F Qⁱ`, `i ∈ ℤ` (the paper's `γ_F^i`). -/
def Γ : ∀ i : ℤ, Φ.F ⋙ d'.pow i ≅ d.pow i ⋙ Φ.F
  | Int.ofNat n => Φ.ΓNat n
  | Int.negSucc n => Φ.ΓNeg n

theorem Γ_negSucc (n : ℕ) : Φ.Γ (Int.negSucc n) = Φ.ΓNegAux n (Φ.Γ (Int.negSucc n + 1)) := by
  rcases n with _ | n <;> rfl

/-- The recursion (the paper's definition of `γ_F^n`):
`Γⁱ⁺¹ = F(Q Qⁱ ≅ Qⁱ⁺¹) ∘ γ_{Qⁱ} ∘ Q' Γⁱ ∘ (Q' Q'ⁱ ≅ Q'ⁱ⁺¹)⁻¹`. -/
theorem Γ_succ_hom_app (i : ℤ) (X : S) :
    (Φ.Γ (i + 1)).hom.app X = (d'.succ i).inv.app (Φ.F.obj X) ≫ d'.Q.map ((Φ.Γ i).hom.app X) ≫
      Φ.γ.hom.app ((d.pow i).obj X) ≫ Φ.F.map ((d.succ i).hom.app X) := by
  rcases i with n | n
  · show (Φ.ΓNat (n + 1)).hom.app X = 𝟙 _ ≫ d'.Q.map ((Φ.ΓNat n).hom.app X) ≫ _ ≫ Φ.F.map (𝟙 _)
    rw [ΓNat_succ_hom_app, Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id]
    rfl
  · rw [Γ_negSucc]
    simp only [ΓNegAux, NatIso.ofComponents_hom_app, Functor.preimageIso_hom, Functor.map_preimage,
      Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv, Category.assoc,
      Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, Category.comp_id]
    rw [← Φ.F.map_comp, Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]

theorem Γ_succ_inv_app (i : ℤ) (X : S) :
    (Φ.Γ (i + 1)).inv.app X = Φ.F.map ((d.succ i).inv.app X) ≫ Φ.γ.inv.app ((d.pow i).obj X) ≫
      d'.Q.map ((Φ.Γ i).inv.app X) ≫ (d'.succ i).hom.app (Φ.F.obj X) := by
  rw [← cancel_epi ((Φ.Γ (i + 1)).hom.app X), Iso.hom_inv_id_app, Γ_succ_hom_app]
  simp only [Category.assoc]
  rw [← Φ.F.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [Iso.hom_inv_id_app_assoc, ← d'.Q.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app]
  rfl

theorem ΓNat_hom_mem (n : ℕ) (X : S) : (Φ.ΓNat n).hom.app X ∈ parity (R := R) _ _ 0 := by
  induction n with
  | zero => show 𝟙 _ ≫ 𝟙 _ ∈ _; simpa using id_mem (R := R) (Φ.F.obj X)
  | succ n ih =>
    rw [ΓNat_succ_hom_app]
    simpa using comp_mem (map_mem d'.Q ih) (Φ.γ_mem _)

theorem Γ_hom_mem (i : ℤ) (X : S) : (Φ.Γ i).hom.app X ∈ parity (R := R) _ _ 0 := by
  have step : ∀ (n : ℕ), (Φ.Γ (Int.negSucc n + 1)).hom.app X ∈ parity (R := R) _ _ 0 →
      (Φ.Γ (Int.negSucc n)).hom.app X ∈ parity (R := R) _ _ 0 := by
    intro n h
    rw [Γ_negSucc]
    apply mem_of_map_mem d'.Q
    simp only [ΓNegAux, NatIso.ofComponents_hom_app, Functor.preimageIso_hom, Functor.map_preimage,
      Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv]
    have := comp_mem (d'.succ_hom_mem (Int.negSucc n) (Φ.F.obj X)) (comp_mem h
      (comp_mem (map_mem Φ.F (d.succ_inv_mem (Int.negSucc n) X))
        (inv_mem (Φ.γ.app _) (Φ.γ_mem ((d.pow (Int.negSucc n)).obj X)))))
    simpa using this
  rcases i with n | n
  · exact Φ.ΓNat_hom_mem n X
  · induction n with
    | zero => exact step 0 (Φ.ΓNat_hom_mem 0 X)
    | succ n ih => exact step (n + 1) ih

theorem Γ_inv_mem (i : ℤ) (X : S) : (Φ.Γ i).inv.app X ∈ parity (R := R) _ _ 0 :=
  inv_mem ((Φ.Γ i).app X) (Φ.Γ_hom_mem i X)

/-! ### The functor on families -/

/-- The family `Γʲ ∘ F(f_{i,j}) ∘ (Γⁱ)⁻¹`. -/
def famMap {X Y : S} (f : d.FamAll X Y) : d'.FamAll (Φ.F.obj X) (Φ.F.obj Y) :=
  fun i j => (Φ.Γ i).hom.app X ≫ Φ.F.map (f i j) ≫ (Φ.Γ j).inv.app Y

theorem famMap_mem {m : ℤ} {X Y : S} {f : d.FamAll X Y} (hf : f ∈ d.Fam R m X Y) :
    Φ.famMap f ∈ d'.Fam R m (Φ.F.obj X) (Φ.F.obj Y) := by
  refine ⟨fun i j h => by rw [famMap, Fam.eq_zero hf h]; simp, fun i j => ?_⟩
  simp only [famMap]
  rw [Γ_succ_hom_app, Γ_succ_inv_app, Fam.compat hf]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Φ.F.map_comp_assoc ((d.succ i).hom.app X), Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← Φ.F.map_comp_assoc ((d.succ j).hom.app Y), Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  have hγ := Φ.γ.hom.naturality (f i j)
  simp only [Functor.comp_obj, Functor.comp_map] at hγ
  rw [← reassoc_of% hγ, Iso.hom_inv_id_app_assoc]

variable (m : ℤ) (X Y : S) in
/-- `famMap` on families of degree `m`, as a linear map. -/
def famMapₗ : d.Fam R m X Y →ₗ[R] d'.Fam R m (Φ.F.obj X) (Φ.F.obj Y) where
  toFun f := ⟨Φ.famMap f.1, Φ.famMap_mem f.2⟩
  map_add' f g := Subtype.ext (FamAll.ext fun i j => by
    simp [famMap, Preadditive.add_comp, Preadditive.comp_add])
  map_smul' r f := Subtype.ext (FamAll.ext fun i j => by simp [famMap])

theorem famMap_famComp (m : ℤ) {X Y Z : S} (f : d.FamAll X Y) (g : d.FamAll Y Z) :
    Φ.famMap (d.famComp m f g) = d'.famComp m (Φ.famMap f) (Φ.famMap g) := by
  ext i k
  simp [famMap, famComp]

theorem famMap_idFam (X : S) : Φ.famMap (d.idFam X) = d'.idFam (Φ.F.obj X) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [famMap, idFam_self]
  · simp [famMap, idFam, h]

theorem famMap_mapFam {X Y : S} (g : X ⟶ Y) :
    Φ.famMap (d.mapFam g).1 = (d'.mapFam (Φ.F.map g)).1 := by
  ext i j
  by_cases h : i = j
  · subst h
    simp only [famMap, mapFam, diagFam_self]
    have := (Φ.Γ i).hom.naturality g
    simp only [Functor.comp_obj, Functor.comp_map] at this
    rw [← Category.assoc, ← this, Category.assoc, Iso.hom_inv_id_app]
    exact Category.comp_id _
  · simp [famMap, mapFam, diagFam, h]

variable (X Y : S) in
/-- The functor on morphisms of the orbit supercategories. -/
def mapL : d.Hom X Y →ₗ[R] d'.Hom (Φ.F.obj X) (Φ.F.obj Y) :=
  DirectSum.toModule R ℤ (d'.Hom (Φ.F.obj X) (Φ.F.obj Y)) fun m =>
    d'.lof m (Φ.F.obj X) (Φ.F.obj Y) ∘ₗ Φ.famMapₗ m X Y

theorem mapL_lof {m : ℤ} {X Y : S} (f : d.Fam R m X Y) :
    Φ.mapL X Y (d.lof m X Y f) = d'.lof m (Φ.F.obj X) (Φ.F.obj Y) (Φ.famMapₗ m X Y f) := by
  rw [mapL, ShiftData.lof]
  erw [DirectSum.toModule_lof]
  rfl

end ShiftFunctor

namespace Orbit

open ShiftData ShiftFunctor GradedSupercategory

variable {R} {S : Type u} [Category.{v} S] [Preadditive S] [Linear R S] [Supercategory R S]
  {S' : Type u₁} [Category.{v₁} S'] [Preadditive S'] [Linear R S'] [Supercategory R S']
  {d : ShiftData R S} {d' : ShiftData R S'}

/-- The graded superfunctor `Orbit d ⥤ Orbit d'` induced by a morphism of shift data. -/
@[simps obj]
def map (Φ : ShiftFunctor R d d') : Orbit d ⥤ Orbit d' where
  obj X := ⟨Φ.F.obj X.obj⟩
  map {X Y} x := Φ.mapL X.obj Y.obj x
  map_id X := by
    show Φ.mapL _ _ (d.lof 0 _ _ _) = d'.lof 0 _ _ _
    rw [mapL_lof]
    congr 1
    exact Subtype.ext (Φ.famMap_idFam X.obj)
  map_comp {X Y Z} x y := by
    show Φ.mapL _ _ (d.compL _ _ _ x y) = d'.compL _ _ _ (Φ.mapL _ _ x) (Φ.mapL _ _ y)
    induction x using Hom.induction_on with
    | zero => simp
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
    | lof m f =>
      induction y using Hom.induction_on with
      | zero => simp
      | add y y' hy hy' => simp only [map_add, hy, hy']
      | lof n g =>
        rw [compL_lof_lof, mapL_lof, mapL_lof, mapL_lof, compL_lof_lof]
        congr 1
        exact Subtype.ext (Φ.famMap_famComp m f.1 g.1)

theorem map_map_lof (Φ : ShiftFunctor R d d') {X Y : Orbit d} {m : ℤ} (f : d.Fam R m X.obj Y.obj) :
    (map Φ).map (d.lof m X.obj Y.obj f : X ⟶ Y) = d'.lof m _ _ (Φ.famMapₗ m X.obj Y.obj f) :=
  Φ.mapL_lof f

instance (Φ : ShiftFunctor R d d') : (map Φ).Additive where
  map_add {X Y x y} := LinearMap.map_add (Φ.mapL X.obj Y.obj) x y

instance (Φ : ShiftFunctor R d d') : (map Φ).Linear R where
  map_smul {X Y} x r := LinearMap.map_smul (Φ.mapL X.obj Y.obj) r x

instance (Φ : ShiftFunctor R d d') : IsGradedSuperfunctor R (map Φ) where
  map_mem {X Y p x} hx := by
    rw [mem_parity_iff, ← d.projHom_of_mem hx]
    clear hx
    induction x using Hom.induction_on with
    | zero => simp only [map_zero]; exact Submodule.zero_mem _
    | add x x' hx hx' =>
      rw [map_add, Functor.map_add]; exact Submodule.add_mem _ hx hx'
    | lof m f =>
      rw [projHom_lof]
      erw [map_map_lof]
      intro k i j
      by_cases h : m = k
      · subst h
        erw [component_lof_self]
        show (Φ.Γ i).hom.app _ ≫ Φ.F.map (proj R p (f.1 i j)) ≫ (Φ.Γ j).inv.app _ ∈ _
        simpa using comp_mem (comp_mem (Φ.Γ_hom_mem i _) (map_mem Φ.F (proj_mem p _)))
          (Φ.Γ_inv_mem j _)
      · erw [d'.component_lof_of_ne _ h]; exact Submodule.zero_mem _
  map_mem_degree {X Y n x} hx := by
    obtain ⟨f, rfl⟩ := hx
    exact ⟨_, (map_map_lof Φ f).symm⟩

/-- `map Φ` extends `F`: `F̃ ∘ ι = ι ∘ F`. -/
theorem ι_comp_map (Φ : ShiftFunctor R d d') : ι d ⋙ map Φ = Φ.F ⋙ ι d' :=
  CategoryTheory.Functor.ext (fun _ => rfl) fun X Y g => by
    simp only [Functor.comp_map, eqToHom_refl, Category.comp_id, Category.id_comp]
    show Φ.mapL X Y (d.lof 0 X Y _) = d'.lof 0 _ _ _
    rw [mapL_lof]
    congr 1
    exact Subtype.ext (Φ.famMap_mapFam g)

end Orbit

end StringDiagrams

end
