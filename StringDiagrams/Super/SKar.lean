import StringDiagrams.Super.K0
import StringDiagrams.Super.Underlying
import StringDiagrams.Super.Envelope
import Mathlib.CategoryTheory.Preadditive.Mat
import Mathlib.CategoryTheory.Idempotents.Biproducts

/-!
# The super Karoubi envelope

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §1.5.

For a category `A`, the additive Karoubi envelope `Kar(A)` is the idempotent completion of the
additive envelope of `A`; we use Mathlib's additive envelope `Mat_` and idempotent completion
`Idempotents.Karoubi`. For a supercategory `A`, the *super Karoubi envelope* is
`SKar(A) := Kar(A̲_π)`: first the Π-envelope `A_π`, then its underlying category of even
morphisms, then the additive Karoubi envelope.

## Main definitions and results

* `Linear R (Mat_ C)`, `Linear R (Karoubi C)`: the additive envelope and the idempotent
  completion of an `R`-linear category are `R`-linear.
* `Mat_.instPiCategory`, `Karoubi.instPiCategory`: a Π-category structure `(C, Π, ξ)` extends to
  `Mat_ C` (entrywise) and to `Karoubi C` (`Π(X, p) = (Π X, Π p)`).
* `SKar R C := Karoubi (Mat_ (Underlying R (Envelope R C)))`: an `R`-linear additive,
  idempotent complete Π-category (`SKar.instPiCategory`), with the embedding
  `SKar.of : A̲_π ⥤ SKar(A)`.
* `K₀ (SKar R C)` is a `Zπ`-module with `π [V] = [Π V]` (`SKar.moduleZπ`, `SKar.π_smul_mk`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Limits Idempotents

universe w v u

variable {R : Type w} [CommRing R]

/-! ## Linear structures -/

namespace Mat_

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]

instance (M N : Mat_ C) : Module R (M ⟶ N) := by
  change Module R (∀ i j, M.X i ⟶ N.X j)
  infer_instance

@[simp] theorem smul_apply {M N : Mat_ C} (r : R) (f : M ⟶ N) (i j) : (r • f) i j = r • f i j :=
  rfl

instance instLinear : Linear R (Mat_ C) where
  smul_comp M N K r f g := by
    ext i k
    simp [Finset.smul_sum, Linear.smul_comp]
  comp_smul M N K f r g := by
    ext i k
    simp [Finset.smul_sum, Linear.comp_smul]

/-- A diagonal matrix of morphisms. -/
def diag {ι : Type} [Fintype ι] {X Y : ι → C} (φ : ∀ i, X i ⟶ Y i) :
    (⟨ι, X⟩ : Mat_ C) ⟶ ⟨ι, Y⟩ := by
  classical
  exact fun i j => if h : i = j then φ i ≫ eqToHom (congrArg Y h) else 0

theorem diag_apply_self {ι : Type} [Fintype ι] {X Y : ι → C} (φ : ∀ i, X i ⟶ Y i) (i : ι) :
    diag φ i i = φ i := by
  simp [diag]

theorem diag_apply_of_ne {ι : Type} [Fintype ι] {X Y : ι → C} (φ : ∀ i, X i ⟶ Y i) {i j : ι}
    (h : i ≠ j) : diag φ i j = 0 := by
  simp [diag, h]

@[simp] theorem diag_comp_apply {ι : Type} [Fintype ι] {X Y : ι → C} (φ : ∀ i, X i ⟶ Y i)
    {N : Mat_ C} (f : (⟨ι, Y⟩ : Mat_ C) ⟶ N) (i : ι) (k : N.ι) :
    (diag φ ≫ f) i k = φ i ≫ f i k := by
  classical
  rw [CategoryTheory.Mat_.comp_apply, Finset.sum_eq_single i]
  · rw [diag_apply_self]
  · intro j _ hj; rw [diag_apply_of_ne φ (Ne.symm hj), zero_comp]
  · intro h; exact absurd (Finset.mem_univ i) h

@[simp] theorem comp_diag_apply {ι : Type} [Fintype ι] {X Y : ι → C} (φ : ∀ i, X i ⟶ Y i)
    {M : Mat_ C} (f : M ⟶ (⟨ι, X⟩ : Mat_ C)) (i : M.ι) (k : ι) :
    (f ≫ diag φ) i k = f i k ≫ φ k := by
  classical
  rw [CategoryTheory.Mat_.comp_apply, Finset.sum_eq_single k]
  · rw [diag_apply_self]
  · intro j _ hj; rw [diag_apply_of_ne φ hj, comp_zero]
  · intro h; exact absurd (Finset.mem_univ k) h

theorem diag_comp_diag {ι : Type} [Fintype ι] {X Y Z : ι → C} (φ : ∀ i, X i ⟶ Y i)
    (ψ : ∀ i, Y i ⟶ Z i) : diag φ ≫ diag ψ = diag (fun i => φ i ≫ ψ i) := by
  ext i k
  rw [diag_comp_apply]
  by_cases h : i = k
  · subst h; rw [diag_apply_self, diag_apply_self]
  · rw [diag_apply_of_ne _ h, diag_apply_of_ne _ h, comp_zero]

theorem diag_id {ι : Type} [Fintype ι] (X : ι → C) :
    diag (fun i => 𝟙 (X i)) = 𝟙 (⟨ι, X⟩ : Mat_ C) := by
  ext i k
  by_cases h : i = k
  · subst h; rw [diag_apply_self, CategoryTheory.Mat_.id_apply_self]
  · rw [diag_apply_of_ne _ h, CategoryTheory.Mat_.id_apply_of_ne _ _ _ h]

/-- A diagonal isomorphism. -/
@[simps]
def diagIso {ι : Type} [Fintype ι] {X Y : ι → C} (φ : ∀ i, X i ≅ Y i) :
    (⟨ι, X⟩ : Mat_ C) ≅ ⟨ι, Y⟩ where
  hom := diag fun i => (φ i).hom
  inv := diag fun i => (φ i).inv
  hom_inv_id := by rw [diag_comp_diag]; simp only [Iso.hom_inv_id]; exact diag_id X
  inv_hom_id := by rw [diag_comp_diag]; simp only [Iso.inv_hom_id]; exact diag_id Y

/-! ### Π-categories -/

instance {D : Type*} [Category.{v} D] [Preadditive D] (F : C ⥤ D) [F.Additive] :
    F.mapMat_.Additive where
  map_add := by
    intros
    ext
    simp

variable [PiCategory R C]

instance : (PiCategory.pi (R := R) (C := C)).mapMat_.Linear R where
  map_smul f r := by
    ext i j
    simp

/-- **The Π-category structure on the additive envelope.** `Π` acts entrywise, and
`ξ_M` is the diagonal matrix of the `ξ_{M_i}`. -/
instance instPiCategory : PiCategory R (Mat_ C) where
  pi := (PiCategory.pi (R := R) (C := C)).mapMat_
  ξ := NatIso.ofComponents (fun M => diagIso (X := fun i => (PiCategory.pi (R := R)).obj
      ((PiCategory.pi (R := R)).obj (M.X i))) (Y := M.X)
      fun i => PiCategory.ξApp (R := R) (M.X i))
    (fun {M N} f => by
      ext i k
      simp only [Functor.comp_map, Functor.mapMat__map, diagIso_hom, Functor.id_map]
      rw [comp_diag_apply, diag_comp_apply]
      exact PiCategory.ξApp_naturality (R := R) (f i k))
  ξ_pi M := by
    ext i k
    simp only [NatIso.ofComponents_hom_app, diagIso_hom, Functor.mapMat__map]
    by_cases h : i = k
    · subst h
      rw [diag_apply_self, diag_apply_self]
      exact PiCategory.ξApp_pi (R := R) (M.X i)
    · rw [diag_apply_of_ne _ h, diag_apply_of_ne _ h, Functor.map_zero]

theorem pi_obj (M : Mat_ C) :
    (PiCategory.pi (R := R)).obj M = ⟨M.ι, fun i => (PiCategory.pi (R := R)).obj (M.X i)⟩ := rfl

end Mat_

namespace Karoubi

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]

instance {P Q : Karoubi C} : SMul R (P ⟶ Q) where
  smul r f := ⟨r • f.f, by rw [Linear.smul_comp, Linear.comp_smul, ← f.comm]⟩

@[simp] theorem smul_f {P Q : Karoubi C} (r : R) (f : P ⟶ Q) : (r • f).f = r • f.f := rfl

instance (P Q : Karoubi C) : Module R (P ⟶ Q) :=
  Function.Injective.module R (Karoubi.inclusionHom P Q) (fun f g h => Karoubi.hom_ext f g h)
    (fun _ _ => rfl)

instance instLinear : Linear R (Karoubi C) where
  smul_comp _ _ _ r f g := Karoubi.hom_ext _ _ (by simp [Linear.smul_comp])
  comp_smul _ _ _ f r g := Karoubi.hom_ext _ _ (by simp [Linear.comp_smul])

/-! ### Π-categories -/

variable [PiCategory R C]

/-- The functor `Π(X, p) = (Π X, Π p)` on the idempotent completion. -/
@[simps]
def piFunctor : Karoubi C ⥤ Karoubi C where
  obj P := ⟨(PiCategory.pi (R := R)).obj P.X, (PiCategory.pi (R := R)).map P.p,
    by rw [← Functor.map_comp, P.idem]⟩
  map {P Q} f := ⟨(PiCategory.pi (R := R)).map f.f, by
    show _ = (PiCategory.pi (R := R)).map P.p ≫ (PiCategory.pi (R := R)).map f.f ≫
      (PiCategory.pi (R := R)).map Q.p
    rw [← Functor.map_comp, ← Functor.map_comp, ← f.comm]⟩
  map_id P := rfl
  map_comp f g := Karoubi.hom_ext _ _ (Functor.map_comp _ _ _)

instance : (piFunctor (R := R) (C := C)).Additive where
  map_add := Karoubi.hom_ext _ _ (Functor.map_add _)

instance : (piFunctor (R := R) (C := C)).Linear R where
  map_smul _ _ := Karoubi.hom_ext _ _ (Functor.map_smul _ _ _)

@[reassoc]
theorem ξ_hom_naturality {X Y : C} (f : X ⟶ Y) :
    (PiCategory.pi (R := R)).map ((PiCategory.pi (R := R)).map f) ≫
      (PiCategory.ξ (R := R)).hom.app Y = (PiCategory.ξ (R := R)).hom.app X ≫ f :=
  (PiCategory.ξ (R := R)).hom.naturality f

@[reassoc]
theorem ξ_inv_naturality {X Y : C} (f : X ⟶ Y) :
    f ≫ (PiCategory.ξ (R := R)).inv.app Y =
      (PiCategory.ξ (R := R)).inv.app X ≫ (PiCategory.pi (R := R)).map
        ((PiCategory.pi (R := R)).map f) :=
  (PiCategory.ξ (R := R)).inv.naturality f

/-- The isomorphism `ξ_{(X, p)} : Π²(X, p) ≅ (X, p)`, with components `ξ_X ∘ p` and
`p ∘ ξ_X⁻¹`. -/
@[simps]
def ξIso (P : Karoubi C) : (piFunctor (R := R)).obj ((piFunctor (R := R)).obj P) ≅ P where
  hom := ⟨(PiCategory.ξ (R := R)).hom.app P.X ≫ P.p, by
    simp only [piFunctor_obj_p, Category.assoc, P.idem, ξ_hom_naturality_assoc]⟩
  inv := ⟨P.p ≫ (PiCategory.ξ (R := R)).inv.app P.X, by
    simp only [piFunctor_obj_p, Category.assoc, ← ξ_inv_naturality, P.idem_assoc]⟩
  hom_inv_id := Idempotents.Karoubi.hom_ext _ _ (by
    simp only [Idempotents.Karoubi.comp_f, Idempotents.Karoubi.id_f, piFunctor_obj_p,
      Category.assoc]
    rw [P.idem_assoc, ξ_inv_naturality, Iso.hom_inv_id_app_assoc])
  inv_hom_id := Idempotents.Karoubi.hom_ext _ _ (by
    simp only [Idempotents.Karoubi.comp_f, Idempotents.Karoubi.id_f, Category.assoc,
      Iso.inv_hom_id_app_assoc, P.idem])

/-- **The Π-category structure on the idempotent completion.** -/
instance instPiCategory : PiCategory R (Karoubi C) where
  pi := piFunctor (R := R)
  ξ := NatIso.ofComponents (fun P => ξIso (R := R) P) (fun {P Q} f =>
    Idempotents.Karoubi.hom_ext _ _ (by
      simp only [Functor.comp_map, piFunctor_map_f, Idempotents.Karoubi.comp_f, ξIso_hom_f,
        Functor.id_map, ξ_hom_naturality_assoc, Idempotents.Karoubi.comp_p, Category.assoc,
        Idempotents.Karoubi.p_comp]))
  ξ_pi P := Idempotents.Karoubi.hom_ext _ _ (by
    simp only [NatIso.ofComponents_hom_app, ξIso_hom_f, piFunctor_obj_X, piFunctor_obj_p,
      piFunctor_map_f, Functor.map_comp]
    rw [PiCategory.ξ_pi])

theorem pi_obj (P : Karoubi C) : (PiCategory.pi (R := R)).obj P = (piFunctor (R := R)).obj P :=
  rfl

end Karoubi

instance {D : Type u} [Category.{v} D] [Preadditive D] [HasFiniteBiproducts D] :
    HasBinaryBiproducts (Karoubi D) :=
  hasBinaryBiproducts_of_finite_biproducts _

/-! ## The super Karoubi envelope -/

variable (R) in
/-- **Brundan–Ellis, §1.5.** The super Karoubi envelope `SKar(A) := Kar(A̲_π)`: the additive
Karoubi envelope (idempotent completion of the additive envelope) of the underlying category of
the Π-envelope. -/
abbrev SKar (C : Type u) [Category.{v} C] [Preadditive C] [Linear R C] [Supercategory R C] :=
  Karoubi (Mat_ (Underlying R (Envelope R C)))

namespace SKar

variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear R C] [Supercategory R C]

example : Linear R (SKar R C) := inferInstance
example : HasFiniteBiproducts (SKar R C) := inferInstance
example : IsIdempotentComplete (SKar R C) := inferInstance

/-- **Brundan–Ellis, §1.5.** `SKar(A)` is a Π-category. -/
instance instPiCategory : PiCategory R (SKar R C) := Karoubi.instPiCategory

variable (R) in
/-- The embedding `A̲_π ⥤ SKar(A)`. -/
def of : Underlying R (Envelope R C) ⥤ SKar R C := Mat_.embedding _ ⋙ toKaroubi _

instance : (of R C).Additive where
  map_add := by intros; rfl

instance : (of R C).Full := Functor.Full.comp _ _

instance : (of R C).Faithful := Functor.Faithful.comp _ _

variable (R) in
/-- **Brundan–Ellis, §1.5.** `K₀(SKar(A))` is a module over `Zπ = ℤ[π]/(π² − 1)`, with `π`
acting by `[V] ↦ [Π V]`. -/
def moduleZπ : Module Zπ (K₀ (SKar R C)) := K₀.moduleZπ R (SKar R C)

theorem π_smul_mk (V : SKar R C) :
    letI := moduleZπ R C
    Zπ.π • K₀.mk V = K₀.mk ((PiCategory.pi (R := R)).obj V) :=
  K₀.π_smul_mk R (SKar R C) V

end SKar

end StringDiagrams
