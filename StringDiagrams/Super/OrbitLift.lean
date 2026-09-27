import StringDiagrams.Super.OrbitFunctorial
import StringDiagrams.Super.Graded

/-!
# Evaluating an orbit supercategory

Let `d = (Q, Q⁻¹)` be a shift datum on a graded supercategory `C` (`StringDiagrams.ShiftData`)
which is *trivialized* by even isomorphisms `σ_X : Q X ≅ X` of degree `-1`, natural in `X`, with
counit of degree zero (`ShiftData.Trivialization`); e.g. `Q` the degree shift of a graded
`(Q, Π)`-supercategory (J. Brundan, A. P. Ellis, *Monoidal supercategories*,
arXiv:1603.05928v3, Definition 6.4), or `- q_μ` on a morphism supercategory of a graded
`(Q, Π)`-2-supercategory. Iterating `σ` gives even isomorphisms `τ_i : Qⁱ X ≅ X` of degree `-i`
(`Orbit.Eval.τ`), and the *evaluation* `Orbit.eval t : Orbit d ⥤ C` sends a family `(f_{i,j})`
of degree `m` to `τ_{-m} ∘ f_{0,-m}`. It is a superfunctor, the identity on `C` in degree zero
(`Orbit.eval_ι_map`), carries `σ` of the orbit supercategory to `σ` (`Orbit.eval_σIso_hom`), and
is natural with respect to morphisms of trivialized shift data (`Orbit.eval_map_map`).

For a morphism of shift data `Φ : d' → d` whose functor takes values in degree zero, the
*lift* `Orbit.lift t Φ := Orbit.map Φ ⋙ Orbit.eval t : Orbit d' ⥤ C` is a graded superfunctor
(`Orbit.lift_map_mem_degree`), bijective on morphisms when `Φ.F` is faithful with image all the
morphisms of degree zero (`Orbit.lift_map_injective`, `Orbit.lift_map_surjective`). This is
the construction of `T` in the proof of Theorem 6.13 (for one object; compare
`QAssociated.T`) and of its 2-categorical analogue (`StringDiagrams.Super.QAssociatedTwoT`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory GradedSupercategory

universe w v u v₁ u₁ v₂ u₂

namespace ShiftData

variable {R : Type w} [CommRing R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  [Supercategory R C] [GradedSupercategory R C]

/-- A trivialization of a shift datum on a graded supercategory: even isomorphisms
`σ_X : Q X ≅ X` of degree `-1`, natural in `X`, such that the counit has degree zero. -/
structure Trivialization (d : ShiftData R C) where
  /-- The isomorphisms `σ_X : Q X ≅ X`. -/
  σ : ∀ X : C, d.Q.obj X ≅ X
  σ_mem : ∀ X : C, (σ X).hom ∈ parity (R := R) (d.Q.obj X) X 0
  σ_mem_degree : ∀ X : C, (σ X).hom ∈ degree (R := R) (d.Q.obj X) X (-1)
  σ_naturality : ∀ {X Y : C} (f : X ⟶ Y), d.Q.map f ≫ (σ Y).hom = (σ X).hom ≫ f
  counit_mem_degree : ∀ X : C, d.e.counitIso.hom.app X ∈ degree (R := R) (d.Q.obj (d.Qi.obj X)) X 0

namespace Trivialization

variable {d : ShiftData R C} (t : d.Trivialization)

theorem σ_inv_mem (X : C) : (t.σ X).inv ∈ parity (R := R) X (d.Q.obj X) 0 :=
  inv_mem _ (t.σ_mem X)

theorem σ_inv_mem_degree (X : C) : (t.σ X).inv ∈ degree (R := R) X (d.Q.obj X) 1 := by
  simpa using inv_mem_degree _ (t.σ_mem_degree X)

theorem Q_map_eq {X Y : C} (f : X ⟶ Y) : d.Q.map f = (t.σ X).hom ≫ f ≫ (t.σ Y).inv := by
  rw [← reassoc_of% (t.σ_naturality f), Iso.hom_inv_id, Category.comp_id]

include t in
theorem succ_hom_mem_degree (i : ℤ) (X : C) :
    (d.succ i).hom.app X ∈ degree (R := R) _ _ 0 := by
  rcases i with n | (_ | n)
  · exact id_mem_degree _
  · exact t.counit_mem_degree X
  · rw [succ_negSucc_succ_hom_app]
    exact t.counit_mem_degree _

include t in
theorem succ_inv_mem_degree (i : ℤ) (X : C) :
    (d.succ i).inv.app X ∈ degree (R := R) _ _ 0 := by
  simpa using inv_mem_degree ((d.succ i).app X) (t.succ_hom_mem_degree i X)

end Trivialization

end ShiftData

namespace Orbit

open ShiftData ShiftFunctor

/-! ## The isomorphisms `τ_i : Qⁱ X ≅ X` and the evaluation -/

namespace Eval

variable {R : Type w} [CommRing R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  [Supercategory R C] [GradedSupercategory R C] {d : ShiftData R C} (t : d.Trivialization)

/-- `τ_n : Qⁿ X ≅ X`, `n ∈ ℕ`: iterated `σ`. -/
def τNat : ∀ (n : ℕ) (X : C), (d.powNat n).obj X ≅ X
  | 0, _ => Iso.refl _
  | n + 1, X => t.σ ((d.powNat n).obj X) ≪≫ τNat n X

/-- `τ_{-n-1} : Q⁻ⁿ⁻¹ X ≅ X`: `σ⁻¹` followed by the counit. -/
def τNeg : ∀ (n : ℕ) (X : C), (d.powNeg (n + 1)).obj X ≅ X
  | 0, X => (t.σ (d.Qi.obj X)).symm ≪≫ d.e.counitIso.app X
  | n + 1, X => (t.σ (d.Qi.obj ((d.powNeg (n + 1)).obj X))).symm ≪≫
      d.e.counitIso.app ((d.powNeg (n + 1)).obj X) ≪≫ τNeg n X

/-- `τ_i : Qⁱ X ≅ X`, `i ∈ ℤ`, even of degree `-i`. -/
def τ : ∀ (i : ℤ) (X : C), (d.pow i).obj X ≅ X
  | Int.ofNat n, X => τNat t n X
  | Int.negSucc n, X => τNeg t n X

theorem τ_zero (X : C) : τ t 0 X = Iso.refl _ := rfl

/-- The recursion of `τ`: `τ_{i+1} = τ_i ∘ σ ∘ (Q Qⁱ ≅ Qⁱ⁺¹)⁻¹`. -/
theorem τ_succ (i : ℤ) (X : C) :
    (τ t (i + 1) X).hom = (d.succ i).inv.app X ≫ (t.σ ((d.pow i).obj X)).hom ≫ (τ t i X).hom := by
  rcases i with n | (_ | n)
  · show (τNat t (n + 1) X).hom = 𝟙 _ ≫ _ ≫ _
    rw [Category.id_comp]; rfl
  · show 𝟙 _ = d.e.counitIso.inv.app X ≫ (t.σ (d.Qi.obj X)).hom ≫
      ((t.σ (d.Qi.obj X)).inv ≫ d.e.counitIso.hom.app X)
    rw [Iso.hom_inv_id_assoc, Iso.inv_hom_id_app]
  · rw [succ_negSucc_succ_inv_app]
    show (τ t (Int.negSucc n) X).hom = d.e.counitIso.inv.app ((d.powNeg (n + 1)).obj X) ≫
      (t.σ (d.Qi.obj ((d.powNeg (n + 1)).obj X))).hom ≫
        ((t.σ (d.Qi.obj ((d.powNeg (n + 1)).obj X))).inv ≫
          d.e.counitIso.hom.app ((d.powNeg (n + 1)).obj X) ≫ (τNeg t n X).hom)
    rw [Iso.hom_inv_id_assoc, Iso.inv_hom_id_app_assoc]
    rcases n with _ | n <;> rfl

theorem τNat_hom_mem (n : ℕ) (X : C) :
    (τNat t n X).hom ∈ parity (R := R) _ _ 0 ∧ (τNat t n X).hom ∈ degree (R := R) _ _ (-n) := by
  induction n with
  | zero => exact ⟨id_mem _, id_mem_degree _⟩
  | succ n ih =>
    refine ⟨by simpa using! comp_mem (t.σ_mem _) ih.1, ?_⟩
    have := comp_mem_degree (t.σ_mem_degree _) ih.2
    rwa [show (-1 + -(n : ℤ)) = -((n + 1 : ℕ) : ℤ) by push_cast; ring] at this

theorem τNeg_hom_mem (n : ℕ) (X : C) :
    (τNeg t n X).hom ∈ parity (R := R) _ _ 0 ∧
      (τNeg t n X).hom ∈ degree (R := R) _ _ ((n : ℤ) + 1) := by
  induction n with
  | zero =>
    show (t.σ _).inv ≫ d.e.counitIso.hom.app X ∈ _ ∧ (t.σ _).inv ≫ d.e.counitIso.hom.app X ∈ _
    refine ⟨?_, ?_⟩
    · simpa using! comp_mem (t.σ_inv_mem (d.Qi.obj X)) (d.counit_mem X)
    · simpa using! comp_mem_degree (t.σ_inv_mem_degree (d.Qi.obj X)) (t.counit_mem_degree X)
  | succ n ih =>
    show (t.σ _).inv ≫ d.e.counitIso.hom.app _ ≫ (τNeg t n X).hom ∈ _ ∧
      (t.σ _).inv ≫ d.e.counitIso.hom.app _ ≫ (τNeg t n X).hom ∈ _
    refine ⟨?_, ?_⟩
    · simpa using! comp_mem (t.σ_inv_mem (d.Qi.obj ((d.powNeg (n + 1)).obj X)))
        (comp_mem (d.counit_mem ((d.powNeg (n + 1)).obj X)) ih.1)
    · have := comp_mem_degree (t.σ_inv_mem_degree (d.Qi.obj ((d.powNeg (n + 1)).obj X)))
        (comp_mem_degree (t.counit_mem_degree ((d.powNeg (n + 1)).obj X)) ih.2)
      rwa [show (1 + (0 + ((n : ℤ) + 1))) = ((n + 1 : ℕ) : ℤ) + 1 by push_cast; ring] at this

/-- `τ_i` is even of degree `-i`. -/
theorem τ_hom_mem (i : ℤ) (X : C) :
    (τ t i X).hom ∈ parity (R := R) _ _ 0 ∧ (τ t i X).hom ∈ degree (R := R) _ _ (-i) := by
  rcases i with n | n
  · exact τNat_hom_mem t n X
  · refine ⟨(τNeg_hom_mem t n X).1, ?_⟩
    have := (τNeg_hom_mem t n X).2
    rwa [show ((n : ℤ) + 1) = -Int.negSucc n by rw [Int.neg_negSucc]; push_cast; ring] at this

theorem τ_inv_mem (i : ℤ) (X : C) :
    (τ t i X).inv ∈ parity (R := R) _ _ 0 ∧ (τ t i X).inv ∈ degree (R := R) _ _ i := by
  refine ⟨inv_mem _ (τ_hom_mem t i X).1, ?_⟩
  simpa using inv_mem_degree (R := R) _ (τ_hom_mem t i X).2

theorem τ_succ_inv (i : ℤ) (X : C) :
    (τ t (i + 1) X).inv = (τ t i X).inv ≫ (t.σ ((d.pow i).obj X)).inv ≫ (d.succ i).hom.app X := by
  rw [← cancel_epi (τ t (i + 1) X).hom, Iso.hom_inv_id, τ_succ]
  simp

variable {t} {X Y : C}

/-- The morphism `τ_j ∘ f_{i,j} ∘ τ_i⁻¹ : X → Y` given by an entry of a family. -/
def val (t : d.Trivialization) (f : d.FamAll X Y) (i j : ℤ) : X ⟶ Y :=
  (τ t i X).inv ≫ f i j ≫ (τ t j Y).hom

/-- All entries of a compatible family give the same morphism. -/
theorem val_succ {m : ℤ} {f : d.FamAll X Y} (hf : f ∈ d.Fam R m X Y) (i j : ℤ) :
    val t f (i + 1) (j + 1) = val t f i j := by
  rw [val, val, τ_succ_inv, τ_succ, Fam.compat hf, t.Q_map_eq]
  simp

theorem val_eq {m : ℤ} {f : d.FamAll X Y} (hf : f ∈ d.Fam R m X Y) {i j : ℤ}
    (h : i - j = m) : val t f i j = val t f 0 (-m) := by
  have key : ∀ k : ℤ, val t f (0 + k) (-m + k) = val t f 0 (-m) := by
    intro k
    induction k using Int.induction_on with
    | zero => simp
    | succ k ih => rw [← ih, ← add_assoc, ← add_assoc, val_succ hf]
    | pred k ih =>
      rw [← ih, show (0 : ℤ) + -(k : ℤ) = 0 + (-(k : ℤ) - 1) + 1 by ring,
        show -m + -(k : ℤ) = -m + (-(k : ℤ) - 1) + 1 by ring, val_succ hf]
  rw [← key i, show 0 + i = i by ring, show -m + i = j by omega]

theorem val_zero (f : d.FamAll X Y) (j : ℤ) : val t f 0 j = f 0 j ≫ (τ t j Y).hom := by
  rw [val, τ_zero]; simp

theorem val_famComp (m : ℤ) {Z : C} (f : d.FamAll X Y) (g : d.FamAll Y Z) (i k : ℤ) :
    val t (d.famComp m f g) i k = val t f i (i - m) ≫ val t g (i - m) k := by
  rw [val, val, val, famComp]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

variable (t)

/-- The evaluation on families of degree `m`: `f ↦ τ_{-m} ∘ f_{0,-m}`. -/
def evalFam (m : ℤ) (X Y : C) : d.Fam R m X Y →ₗ[R] (X ⟶ Y) where
  toFun f := val t f.1 0 (-m)
  map_add' f g := by
    simp only [val, Submodule.coe_add, FamAll.add_apply, Preadditive.add_comp,
      Preadditive.comp_add]
  map_smul' r f := by
    simp only [val, Submodule.coe_smul, FamAll.smul_apply, Linear.smul_comp, Linear.comp_smul,
      RingHom.id_apply]

/-- The evaluation on morphisms, as a linear map. -/
def evalL (X Y : C) : d.Hom X Y →ₗ[R] (X ⟶ Y) :=
  DirectSum.toModule R ℤ (X ⟶ Y) fun m => evalFam t m X Y

theorem evalL_lof {m : ℤ} (f : d.Fam R m X Y) :
    evalL t X Y (d.lof m X Y f) = val t f.1 0 (-m) := by
  rw [evalL, ShiftData.lof]
  erw [DirectSum.toModule_lof]
  rfl

variable {t}

theorem val_mem {p : ZMod 2} {f : d.FamAll X Y} (i j : ℤ)
    (hf : f i j ∈ parity (R := R) _ _ p) : val t f i j ∈ parity (R := R) _ _ p := by
  have := comp_mem (comp_mem (τ_inv_mem t i X).1 hf) (τ_hom_mem t j Y).1
  rw [zero_add, add_zero, Category.assoc] at this
  exact this

theorem val_mem_degree {f : d.FamAll X Y} {n : ℤ} (i j : ℤ) (hf : f i j ∈ degree (R := R) _ _ n) :
    val t f i j ∈ degree (R := R) X Y (i + n - j) := by
  have := comp_mem_degree (comp_mem_degree (τ_inv_mem t i X).2 hf) (τ_hom_mem t j Y).2
  rw [show i + n + -j = i + n - j by ring, Category.assoc] at this
  exact this

end Eval

section Eval

open Eval

variable {R : Type w} [CommRing R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  [Supercategory R C] [GradedSupercategory R C] {d : ShiftData R C} (t : d.Trivialization)

/-- **The evaluation of an orbit supercategory.** A family of degree `m` goes to
`τ_{-m} ∘ f_{0,-m}`, where `τ_{-m} : Q⁻ᵐ Y ≅ Y` is built from `σ`. -/
def eval : Orbit d ⥤ C where
  obj X := X.obj
  map {X Y} x := evalL t X.obj Y.obj x
  map_id X := by
    show evalL t _ _ (d.lof 0 _ _ _) = _
    rw [evalL_lof]
    show val t (d.idFam X.obj) 0 (-0) = 𝟙 _
    rw [neg_zero, val, d.idFam_self, τ_zero]
    simp
  map_comp {X Y Z} x y := by
    show evalL t _ _ (d.compL _ _ _ x y) = evalL t _ _ x ≫ evalL t _ _ y
    induction x using Hom.induction_on with
    | zero => simp
    | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx', Preadditive.add_comp]
    | lof m f =>
      induction y using Hom.induction_on with
      | zero => simp
      | add y y' hy hy' => simp only [map_add, hy, hy', Preadditive.comp_add]
      | lof n g =>
        rw [compL_lof_lof, evalL_lof, evalL_lof, evalL_lof, famCompₗ_apply, val_famComp,
          val_eq g.2 (show 0 - m - -(m + n) = n by ring), zero_sub]

@[simp] theorem eval_obj (X : Orbit d) : (eval t).obj X = X.obj := rfl

theorem eval_map_lof {X Y : Orbit d} {m : ℤ} (f : d.Fam R m X.obj Y.obj) :
    (eval t).map (d.lof m X.obj Y.obj f : X ⟶ Y) = val t f.1 0 (-m) :=
  evalL_lof t f

instance : (eval t).Additive where
  map_add {X Y x y} := LinearMap.map_add (evalL t X.obj Y.obj) x y

instance : (eval t).Linear R where
  map_smul {X Y} x r := LinearMap.map_smul (evalL t X.obj Y.obj) r x

instance : IsSuperfunctor R (eval t) where
  map_mem {X Y p x} hx := by
    rw [← d.projHom_of_mem hx]
    clear hx
    induction x using Hom.induction_on with
    | zero => simp only [map_zero]; exact Submodule.zero_mem _
    | add x x' hx hx' =>
      rw [map_add, Functor.map_add]; exact Submodule.add_mem _ hx hx'
    | lof m f =>
      rw [projHom_lof, eval_map_lof]
      exact val_mem 0 (-m) (proj_mem _ _)

/-- The evaluation is the identity on `C` in degree zero. -/
theorem eval_ι_map {X Y : C} (f : X ⟶ Y) : (eval t).map ((ι d).map f) = f := by
  rw [ι_map]
  refine (eval_map_lof t (X := (⟨X⟩ : Orbit _)) (Y := ⟨Y⟩) _).trans ?_
  rw [neg_zero, val, τ_zero, τ_zero]
  simp [mapFam, diagFam_self]

set_option backward.isDefEq.respectTransparency false in
/-- The evaluation carries `σ` of the orbit supercategory to `σ`. -/
theorem eval_σIso_hom (X : Orbit d) : (eval t).map (σIso X).hom = (t.σ X.obj).hom := by
  show (eval t).map (d.lof (-1) _ _ _) = _
  rw [eval_map_lof, neg_neg, val_zero]
  show d.famσ X.obj 0 (0 + 1) ≫ (τ t (0 + 1) X.obj).hom = _
  rw [famσ_succ, comm_zero_hom_app, τ_succ, τ_zero]
  simp only [succ_zero_inv_app, Iso.refl_hom, Category.comp_id]
  erw [Category.id_comp, Category.id_comp]
  rfl

/-! ### Naturality -/

section Naturality

variable {C' : Type u₁} [Category.{v₁} C'] [Preadditive C'] [Linear R C'] [Supercategory R C']
  [GradedSupercategory R C'] {d' : ShiftData R C'} (t' : d'.Trivialization)
  (Ψ : ShiftFunctor R d d')

/-- The compatibility of a morphism of shift data with trivializations:
`σ'_{F X} ∘ γ⁻¹ = F σ_X`. -/
def IsTrivCompatible : Prop :=
  ∀ X : C, Ψ.γ.inv.app X ≫ (t'.σ (Ψ.F.obj X)).hom = Ψ.F.map (t.σ X).hom

variable {t t' Ψ}

theorem Γ_inv_τ (h : IsTrivCompatible t t' Ψ) (i : ℤ) (Z : C) :
    (Ψ.Γ i).inv.app Z ≫ (τ t' i (Ψ.F.obj Z)).hom = Ψ.F.map (τ t i Z).hom := by
  refine Int.forall_of_step (P := fun i => (Ψ.Γ i).inv.app Z ≫ (τ t' i (Ψ.F.obj Z)).hom =
    Ψ.F.map (τ t i Z).hom) ?_ (fun i => ?_) i
  · rw [Γ_zero_inv_app, τ_zero, τ_zero]; simp
  · have h1 : (Ψ.Γ (i + 1)).inv.app Z ≫ (τ t' (i + 1) (Ψ.F.obj Z)).hom =
        Ψ.F.map ((d.succ i).inv.app Z ≫ (t.σ ((d.pow i).obj Z)).hom) ≫
          (Ψ.Γ i).inv.app Z ≫ (τ t' i (Ψ.F.obj Z)).hom := by
      rw [ShiftFunctor.Γ_succ_inv_app, τ_succ]
      simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Functor.map_comp]
      rw [reassoc_of% (t'.σ_naturality ((Ψ.Γ i).inv.app Z)), ← h]
      simp only [Category.assoc]
    have h2 : Ψ.F.map (τ t (i + 1) Z).hom = Ψ.F.map ((d.succ i).inv.app Z ≫
        (t.σ ((d.pow i).obj Z)).hom) ≫ Ψ.F.map (τ t i Z).hom := by
      rw [τ_succ, ← Functor.map_comp, Category.assoc]
    have hK : IsIso (Ψ.F.map ((d.succ i).inv.app Z ≫ (t.σ ((d.pow i).obj Z)).hom)) :=
      inferInstance
    show _ = _ ↔ _ = _
    rw [h1, h2]
    exact ⟨fun e => (cancel_epi _).1 e, fun e => by rw [e]⟩

set_option backward.isDefEq.respectTransparency false in
/-- **Naturality of the evaluation** with respect to morphisms of trivialized shift data. -/
theorem eval_map_map (h : IsTrivCompatible t t' Ψ) {X Y : Orbit d} (x : X ⟶ Y) :
    (eval t').map ((map Ψ).map x) = Ψ.F.map ((eval t).map x) := by
  induction x using Hom.induction_on with
  | zero => simp
  | add x y hx hy => rw [(map _).map_add, (eval t').map_add, hx, hy, (eval t).map_add, Ψ.F.map_add]
  | lof m f =>
    rw [map_map_lof]
    erw [eval_map_lof, eval_map_lof]
    rw [val_zero, val_zero]
    simp only [famMapₗ_apply, famMap, Γ_zero_hom_app, Category.assoc,
      Functor.map_comp]
    erw [Category.id_comp, Γ_inv_τ h]

end Naturality

end Eval

/-! ## Lifts -/

section Lift

open Eval

variable {R : Type w} [CommRing R] {S : Type u₂} [Category.{v₂} S] [Preadditive S] [Linear R S]
  [Supercategory R S] {d' : ShiftData R S}
  {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  [Supercategory R C] [GradedSupercategory R C] {d : ShiftData R C} (t : d.Trivialization)

/-- The superfunctor `Orbit d' ⥤ C` induced by a morphism of shift data `Φ : d' → d` to a
trivialized shift datum: `Orbit.map Φ` followed by the evaluation. -/
def lift (Φ : ShiftFunctor R d' d) : Orbit d' ⥤ C :=
  map Φ ⋙ eval t

variable (Φ : ShiftFunctor R d' d)

@[simp] theorem lift_obj (X : Orbit d') : (lift t Φ).obj X = Φ.F.obj X.obj := rfl

theorem lift_map {X Y : Orbit d'} (x : X ⟶ Y) :
    (lift t Φ).map x = (eval t).map ((map Φ).map x) := rfl

instance : (lift t Φ).Additive := inferInstanceAs (map Φ ⋙ eval t).Additive

instance : (lift t Φ).Linear R := inferInstanceAs ((map Φ ⋙ eval t).Linear R)

instance : IsSuperfunctor R (lift t Φ) := inferInstanceAs (IsSuperfunctor R (map Φ ⋙ eval t))

set_option backward.isDefEq.respectTransparency false in
theorem lift_ι_map {X Y : S} (f : X ⟶ Y) : (lift t Φ).map ((ι d').map f) = Φ.F.map f := by
  rw [lift_map, map_ι_map, eval_ι_map]

set_option backward.isDefEq.respectTransparency false in
theorem lift_σIso_hom (X : Orbit d') :
    (lift t Φ).map (σIso X).hom = Φ.γ.inv.app X.obj ≫ (t.σ (Φ.F.obj X.obj)).hom := by
  rw [lift_map, map_σIso_hom, Functor.map_comp, eval_ι_map]
  erw [eval_σIso_hom]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem lift_map_lof {X Y : Orbit d'} {m : ℤ} (f : d'.Fam R m X.obj Y.obj) :
    (lift t Φ).map (d'.lof m X.obj Y.obj f : X ⟶ Y) =
      Φ.F.map (f.1 0 (-m)) ≫ (Φ.Γ (-m)).inv.app Y.obj ≫ (τ t (-m) (Φ.F.obj Y.obj)).hom := by
  rw [lift_map, map_map_lof]
  erw [eval_map_lof]
  rw [val_zero]
  simp only [famMapₗ_apply, famMap, Γ_zero_hom_app, Category.assoc]
  erw [Category.id_comp]
  rfl

variable {Φ}

include t in
/-- If `Φ.F` takes values in degree zero and `γ` has degree zero, so do the `Γⁱ`. -/
theorem Γ_hom_mem_degree (hP : ∀ {X Y : S} (f : X ⟶ Y), Φ.F.map f ∈ degree (R := R) _ _ 0)
    (hγ : ∀ X : S, Φ.γ.hom.app X ∈ degree (R := R) _ _ 0) (i : ℤ) (X : S) :
    (Φ.Γ i).hom.app X ∈ degree (R := R) _ _ 0 := by
  refine Int.forall_of_step (P := fun i => (Φ.Γ i).hom.app X ∈ degree (R := R) _ _ 0) ?_
    (fun i => ?_) i
  · rw [Γ_zero_hom_app]; exact id_mem_degree _
  · show _ ∈ _ ↔ _ ∈ _
    rw [Γ_succ_hom_app]
    constructor
    · intro h
      have h1 := comp_mem_degree (comp_mem_degree (t.succ_hom_mem_degree i _) h)
        (comp_mem_degree (hP ((d'.succ i).inv.app X))
          (inv_mem_degree (Φ.γ.app ((d'.pow i).obj X)) (hγ ((d'.pow i).obj X))))
      simp only [Category.assoc, Iso.hom_inv_id_app_assoc, zero_add, add_zero,
        Iso.app_inv] at h1
      rw [← Φ.F.map_comp_assoc, Iso.hom_inv_id_app] at h1
      erw [CategoryTheory.Functor.map_id, Category.id_comp] at h1
      rw [Iso.hom_inv_id_app] at h1
      erw [Category.comp_id] at h1
      rw [t.Q_map_eq] at h1
      have h2 := comp_mem_degree (comp_mem_degree (t.σ_inv_mem_degree _) h1)
        (t.σ_mem_degree _)
      simpa using h2
    · intro h
      have hQ : d.Q.map ((Φ.Γ i).hom.app X) ∈ degree (R := R) _ _ 0 := by
        rw [t.Q_map_eq]
        simpa using comp_mem_degree (comp_mem_degree (t.σ_mem_degree _) h)
          (t.σ_inv_mem_degree _)
      have := comp_mem_degree (comp_mem_degree (comp_mem_degree
        (t.succ_inv_mem_degree i _) hQ) (hγ ((d'.pow i).obj X))) (hP ((d'.succ i).hom.app X))
      simpa using this

include t in
theorem Γ_inv_mem_degree (hP : ∀ {X Y : S} (f : X ⟶ Y), Φ.F.map f ∈ degree (R := R) _ _ 0)
    (hγ : ∀ X : S, Φ.γ.hom.app X ∈ degree (R := R) _ _ 0) (i : ℤ) (X : S) :
    (Φ.Γ i).inv.app X ∈ degree (R := R) _ _ 0 := by
  simpa using inv_mem_degree ((Φ.Γ i).app X) (Γ_hom_mem_degree t hP hγ i X)

theorem lift_map_lof_mem_degree (hP : ∀ {X Y : S} (f : X ⟶ Y), Φ.F.map f ∈ degree (R := R) _ _ 0)
    (hγ : ∀ X : S, Φ.γ.hom.app X ∈ degree (R := R) _ _ 0) {X Y : Orbit d'} {m : ℤ}
    (f : d'.Fam R m X.obj Y.obj) :
    (lift t Φ).map (d'.lof m X.obj Y.obj f : X ⟶ Y) ∈ degree (R := R) _ _ m := by
  rw [lift_map_lof]
  have := comp_mem_degree (hP (f.1 0 (-m))) (comp_mem_degree
    (Γ_inv_mem_degree t hP hγ (-m) Y.obj) (τ_hom_mem t (-m) (Φ.F.obj Y.obj)).2)
  simpa using! this

/-- **The lift is graded** when `Φ.F` takes values in degree zero and `γ` has degree zero. -/
theorem lift_map_mem_degree (hP : ∀ {X Y : S} (f : X ⟶ Y), Φ.F.map f ∈ degree (R := R) _ _ 0)
    (hγ : ∀ X : S, Φ.γ.hom.app X ∈ degree (R := R) _ _ 0) {X Y : Orbit d'} {n : ℤ} {x : X ⟶ Y}
    (hx : x ∈ degree (R := R) X Y n) : (lift t Φ).map x ∈ degree (R := R) _ _ n := by
  obtain ⟨f, rfl⟩ := hx
  exact lift_map_lof_mem_degree t hP hγ f

theorem dproj_lift_map (hP : ∀ {X Y : S} (f : X ⟶ Y), Φ.F.map f ∈ degree (R := R) _ _ 0)
    (hγ : ∀ X : S, Φ.γ.hom.app X ∈ degree (R := R) _ _ 0) {X Y : Orbit d'} (n : ℤ)
    (x : X ⟶ Y) :
    dproj R n ((lift t Φ).map x) =
      (lift t Φ).map (d'.lof n X.obj Y.obj (d'.component n X.obj Y.obj x) : X ⟶ Y) := by
  induction x using Hom.induction_on with
  | zero =>
    rw [Functor.map_zero, map_zero, map_zero, map_zero]
    exact ((lift t Φ).map_zero _ _).symm
  | add x y hx hy =>
    rw [Functor.map_add, map_add, hx, hy, map_add, map_add]
    exact ((lift t Φ).map_add).symm
  | lof m f =>
    by_cases h : m = n
    · subst h
      rw [component_lof_self, dproj_of_mem (lift_map_lof_mem_degree t hP hγ f)]
    · rw [d'.component_lof_of_ne _ h, dproj_of_mem_ne (lift_map_lof_mem_degree t hP hγ f) h,
        map_zero]
      exact ((lift t Φ).map_zero _ _).symm

/-- **The lift is faithful** when `Φ.F` is. -/
theorem lift_map_injective [Φ.F.Faithful]
    (hP : ∀ {X Y : S} (f : X ⟶ Y), Φ.F.map f ∈ degree (R := R) _ _ 0)
    (hγ : ∀ X : S, Φ.γ.hom.app X ∈ degree (R := R) _ _ 0) {X Y : Orbit d'} {x y : X ⟶ Y}
    (h : (lift t Φ).map x = (lift t Φ).map y) : x = y := by
  refine Hom.ext fun n => ?_
  have h1 := dproj_lift_map t hP hγ n x
  rw [h, dproj_lift_map t hP hγ n y, lift_map_lof, lift_map_lof] at h1
  have h2 := (cancel_mono ((Φ.Γ (-n)).inv.app Y.obj ≫ (τ t (-n) (Φ.F.obj Y.obj)).hom)).1
    (by simpa only [Category.assoc] using! h1)
  exact Subtype.ext (Fam.eq_of_entry (d'.component n X.obj Y.obj x).2
    (d'.component n X.obj Y.obj y).2 (i₀ := 0) (j₀ := -n) (by ring) (Φ.F.map_injective h2.symm))

omit [GradedSupercategory R C] in
theorem F_map_Q_map {X Y : S} (f : X ⟶ Y) :
    Φ.F.map (d'.Q.map f) = Φ.γ.inv.app X ≫ d.Q.map (Φ.F.map f) ≫ Φ.γ.hom.app Y := by
  have n := Φ.γ.hom.naturality f
  simp only [Functor.comp_obj, Functor.comp_map] at n
  rw [← cancel_epi (Φ.γ.hom.app X), Iso.hom_inv_id_app_assoc, n]

/-- The conjugate `Γ_i⁻¹ τ_i g τ_j⁻¹ Γ_j : F Qⁱ X → F Qʲ Y` of a morphism `g : F X → F Y`. -/
def conj (Φ : ShiftFunctor R d' d) {X Y : S} (g : Φ.F.obj X ⟶ Φ.F.obj Y) (i j : ℤ) :
    Φ.F.obj ((d'.pow i).obj X) ⟶ Φ.F.obj ((d'.pow j).obj Y) :=
  (Φ.Γ i).inv.app X ≫ (τ t i (Φ.F.obj X)).hom ≫ g ≫ (τ t j (Φ.F.obj Y)).inv ≫ (Φ.Γ j).hom.app Y

theorem conj_mem_degree (Φ : ShiftFunctor R d' d)
    (hP : ∀ {X Y : S} (f : X ⟶ Y), Φ.F.map f ∈ degree (R := R) _ _ 0)
    (hγ : ∀ X : S, Φ.γ.hom.app X ∈ degree (R := R) _ _ 0) {X Y : S}
    {g : Φ.F.obj X ⟶ Φ.F.obj Y} {n : ℤ} (hg : g ∈ degree (R := R) _ _ n) {i j : ℤ}
    (h : i - j = n) : conj t Φ g i j ∈ degree (R := R) _ _ 0 := by
  have := comp_mem_degree (Γ_inv_mem_degree t hP hγ i X) (comp_mem_degree
    (τ_hom_mem t i (Φ.F.obj X)).2 (comp_mem_degree hg (comp_mem_degree
      (τ_inv_mem t j (Φ.F.obj Y)).2 (Γ_hom_mem_degree t hP hγ j Y))))
  rwa [show 0 + (-i + (n + (j + 0))) = 0 by omega] at this

variable (hP : ∀ {X Y : S} (f : X ⟶ Y), Φ.F.map f ∈ degree (R := R) _ _ 0)
  (hγ : ∀ X : S, Φ.γ.hom.app X ∈ degree (R := R) _ _ 0)
  (hsurj : ∀ {X Y : S} (g : Φ.F.obj X ⟶ Φ.F.obj Y), g ∈ degree (R := R) _ _ 0 →
    ∃ f : X ⟶ Y, Φ.F.map f = g)

set_option backward.isDefEq.respectTransparency false in
include hP hγ hsurj in
/-- **The lift is full** when `Φ.F` is faithful with image all the morphisms of degree zero. -/
theorem lift_map_surjective [Φ.F.Faithful] {X Y : Orbit d'}
    (g : Φ.F.obj X.obj ⟶ Φ.F.obj Y.obj) : ∃ x : X ⟶ Y, (lift t Φ).map x = g := by
  refine induction_on_degree (R := R) g ⟨0, Functor.map_zero _ _ _⟩ (fun n g hg => ?_)
    (fun g h ⟨x, hx⟩ ⟨y, hy⟩ => ⟨x + y, by rw [Functor.map_add, hx, hy]⟩)
  classical
  let fam : d'.FamAll X.obj Y.obj := fun i j =>
    if h : i - j = n then (hsurj _ (conj_mem_degree t Φ hP hγ hg h)).choose else 0
  have hfam : ∀ i j (h : i - j = n), Φ.F.map (fam i j) = conj t Φ g i j := fun i j h => by
    simp only [fam, dite_eq_left h]
    exact (hsurj _ (conj_mem_degree t Φ hP hγ hg h)).choose_spec
  have hmem : fam ∈ d'.Fam R n X.obj Y.obj := by
    refine ⟨fun i j h => by simp only [fam, dite_eq_right h], fun i j => ?_⟩
    by_cases h : i - j = n
    · apply Φ.F.map_injective
      rw [hfam _ _ (by omega), Functor.map_comp, Functor.map_comp, F_map_Q_map, hfam i j h]
      simp only [conj, Γ_succ_inv_app, Γ_succ_hom_app, τ_succ, τ_succ_inv, t.Q_map_eq,
        Category.assoc, Iso.hom_inv_id_app_assoc,
        Iso.inv_hom_id_assoc,
        Functor.comp_obj]
    · simp only [fam, dite_eq_right h, dite_eq_right (show ¬(i + 1 - (j + 1) = n) by omega),
        Functor.map_zero, Limits.zero_comp, Limits.comp_zero]
  refine ⟨d'.lof n X.obj Y.obj ⟨fam, hmem⟩, ?_⟩
  rw [lift_map_lof]
  change Φ.F.map (fam 0 (-n)) ≫ _ ≫ _ = g
  rw [hfam 0 (-n) (by ring), conj, Γ_zero_inv_app, τ_zero]
  simp

end Lift

end Orbit

end StringDiagrams

end
