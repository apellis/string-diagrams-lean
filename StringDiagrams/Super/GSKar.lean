import StringDiagrams.Super.QPiCategory
import StringDiagrams.Super.QEnvelope
import StringDiagrams.Super.SKar
import Mathlib.Algebra.Polynomial.Laurent

/-!
# The graded super Karoubi envelope and its Grothendieck group

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §6, the
end of the section.

* A `(Q, Π)`-category structure extends to the additive envelope `Mat_` and to the idempotent
  completion `Karoubi` (`Mat_.instQPiCategory`, `Karoubi.instQPiCategory`), extending the
  Π-category structures of `StringDiagrams.Super.SKar`.
* For a graded supercategory `A`, `GSKar R A := Kar(A̲_{q,π})`, the additive Karoubi envelope
  of the underlying category of the `(Q, Π)`-envelope, is an additive, idempotent complete
  `(Q, Π)`-category (`GSKar.instQPiCategory`).
* Its split Grothendieck group `K₀(GSKar(A))` is a module over `Zπ[q, q⁻¹]`
  (`LaurentPolynomial Zπ`, `GSKar.moduleLaurent`) with `π` acting as `[Π]` and `q` acting as
  `[Q]` (`K₀.C_π_smul_mk`, `K₀.T_smul_mk`, `K₀.T_neg_one_smul_mk`).

The 2-categorical version (`GSKAR(𝔄)`, the Grothendieck ring `K₀(GSKAR(𝔄))` as a locally unital
`Zπ[q, q⁻¹]`-algebra) is not formalized: it requires the additive Karoubi envelope of a
bicategory, with horizontal composition extended to formal direct sums and idempotents.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Limits Idempotents

universe w v u

variable {R : Type w} [CommRing R]

/-! ## The additive envelope -/

namespace Mat_

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]

theorem mapMat_diag {D : Type*} [Category D] [Preadditive D] (F : C ⥤ D) [F.Additive]
    {ι : Type} [Fintype ι] {X Y : ι → C} (φ : ∀ i, X i ⟶ Y i) :
    F.mapMat_.map (diag (X := X) (Y := Y) φ) = diag (X := fun i => F.obj (X i))
      (Y := fun i => F.obj (Y i)) (fun i => F.map (φ i)) := by
  classical
  ext i j
  by_cases h : i = j
  · subst h; simp [diag_apply_self]
  · simp only [Functor.mapMat__map]
    rw [diag_apply_of_ne _ h, diag_apply_of_ne _ h, F.map_zero]

theorem diag_congr {ι : Type} [Fintype ι] {X Y : ι → C} {φ ψ : ∀ i, X i ⟶ Y i}
    (h : ∀ i, φ i = ψ i) : diag φ = diag ψ := by
  rw [funext h]

/-- A natural isomorphism of additive functors, entrywise on the additive envelope. -/
def mapMatIso {D : Type*} [Category D] [Preadditive D] {F G : C ⥤ D} [F.Additive] [G.Additive]
    (α : F ≅ G) : F.mapMat_ ≅ G.mapMat_ :=
  NatIso.ofComponents (fun M => diagIso (X := fun i => F.obj (M.X i)) (Y := fun i => G.obj (M.X i))
    fun i => α.app (M.X i))
    (fun {M N} f => by
      ext i k
      simp only [Functor.mapMat__map, diagIso_hom]
      rw [comp_diag_apply, diag_comp_apply]
      exact α.hom.naturality (f i k))

@[simp] theorem mapMatIso_hom_app {D : Type*} [Category D] [Preadditive D] {F G : C ⥤ D}
    [F.Additive] [G.Additive] (α : F ≅ G) (M : Mat_ C) :
    (mapMatIso α).hom.app M = diag (X := fun i => F.obj (M.X i)) (Y := fun i => G.obj (M.X i))
      fun i => α.hom.app (M.X i) := rfl

@[simp] theorem mapMatIso_inv_app {D : Type*} [Category D] [Preadditive D] {F G : C ⥤ D}
    [F.Additive] [G.Additive] (α : F ≅ G) (M : Mat_ C) :
    (mapMatIso α).inv.app M = diag (X := fun i => G.obj (M.X i)) (Y := fun i => F.obj (M.X i))
      fun i => α.inv.app (M.X i) := rfl

theorem ξ_hom_app_eq [PiCategory R C] (M : Mat_ C) :
    (PiCategory.ξ (R := R) (C := Mat_ C)).hom.app M =
      diag (X := fun i => (PiCategory.pi (R := R)).obj ((PiCategory.pi (R := R)).obj (M.X i)))
        (Y := M.X) fun i => (PiCategory.ξ (R := R)).hom.app (M.X i) := rfl

theorem ξ_inv_app_eq [PiCategory R C] (M : Mat_ C) :
    (PiCategory.ξ (R := R) (C := Mat_ C)).inv.app M =
      diag (X := M.X)
        (Y := fun i => (PiCategory.pi (R := R)).obj ((PiCategory.pi (R := R)).obj (M.X i)))
        fun i => (PiCategory.ξ (R := R)).inv.app (M.X i) := rfl

variable [QPiCategory R C]

instance : (QPiCategory.Q (R := R) (C := C)).mapMat_.Linear R where
  map_smul f r := by ext i j; simp

instance : (QPiCategory.Qinv (R := R) (C := C)).mapMat_.Linear R where
  map_smul f r := by ext i j; simp

/-- **The `(Q, Π)`-category structure on the additive envelope**, entrywise. -/
instance instQPiCategory : QPiCategory R (Mat_ C) where
  Q := (QPiCategory.Q (R := R) (C := C)).mapMat_
  Qinv := (QPiCategory.Qinv (R := R) (C := C)).mapMat_
  ii := mapMatIso (F := QPiCategory.Q (R := R) (C := C) ⋙ QPiCategory.Qinv (R := R))
    (G := 𝟭 C) (QPiCategory.ii (R := R) (C := C))
  jj := mapMatIso (F := QPiCategory.Qinv (R := R) (C := C) ⋙ QPiCategory.Q (R := R))
    (G := 𝟭 C) (QPiCategory.jj (R := R) (C := C))
  left_triangle M := by
    rw [mapMatIso_inv_app, mapMatIso_hom_app]
    erw [mapMat_diag, diag_comp_diag]
    exact (diag_congr fun i => QPiCategory.left_triangle (M.X i)).trans (diag_id _)
  right_triangle M := by
    rw [mapMatIso_inv_app, mapMatIso_hom_app]
    erw [mapMat_diag, diag_comp_diag]
    exact (diag_congr fun i => QPiCategory.right_triangle (M.X i)).trans (diag_id _)
  Q_pi :=
    { β := mapMatIso (F := QPiCategory.Q (R := R) (C := C) ⋙ PiCategory.pi (R := R))
        (G := PiCategory.pi (R := R) ⋙ QPiCategory.Q (R := R))
        (QPiCategory.Q_pi (R := R) (C := C)).β
      comm := fun M => by
        rw [ξ_hom_app_eq, ξ_inv_app_eq, mapMatIso_hom_app, mapMatIso_hom_app]
        erw [mapMat_diag, mapMat_diag, diag_comp_diag, diag_comp_diag]
        exact diag_congr fun i => (QPiCategory.Q_pi (R := R) (C := C)).comm (M.X i) }

end Mat_

/-! ## The idempotent completion -/

namespace Karoubi

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]

/-- The functor `F(X, p) = (F X, F p)` on idempotent completions. -/
@[simps]
def mapFunctor {D : Type*} [Category D] (F : C ⥤ D) : Karoubi C ⥤ Karoubi D where
  obj P := ⟨F.obj P.X, F.map P.p, by rw [← F.map_comp, P.idem]⟩
  map {P Q} f := ⟨F.map f.f, by
    show _ = F.map P.p ≫ F.map f.f ≫ F.map Q.p
    rw [← F.map_comp, ← F.map_comp, ← f.comm]⟩
  map_id P := rfl
  map_comp f g := Karoubi.hom_ext _ _ (F.map_comp _ _)

instance {D : Type*} [Category D] [Preadditive D] (F : C ⥤ D) [F.Additive] :
    (mapFunctor F).Additive where
  map_add := Karoubi.hom_ext _ _ (F.map_add)

instance {D : Type*} [Category D] [Preadditive D] [Linear R D] (F : C ⥤ D) [F.Additive]
    [F.Linear R] : (mapFunctor F).Linear R where
  map_smul _ _ := Karoubi.hom_ext _ _ (F.map_smul _ _)

/-- A natural isomorphism `F ≅ G` induces `mapFunctor F ≅ mapFunctor G`, with components
`α_X ∘ F p = G p ∘ α_X`. -/
@[simps!]
def mapIso {D : Type*} [Category D] {F G : C ⥤ D} (α : F ≅ G) : mapFunctor F ≅ mapFunctor G :=
  NatIso.ofComponents (fun P =>
    { hom := ⟨α.hom.app P.X ≫ G.map P.p, by
        simp only [mapFunctor_obj_p, Category.assoc, ← G.map_comp, P.idem]
        rw [α.hom.naturality_assoc, ← G.map_comp, P.idem]⟩
      inv := ⟨α.inv.app P.X ≫ F.map P.p, by
        simp only [mapFunctor_obj_p, Category.assoc, ← F.map_comp, P.idem]
        rw [α.inv.naturality_assoc, ← F.map_comp, P.idem]⟩
      hom_inv_id := Karoubi.hom_ext _ _ (by
        simp only [Karoubi.comp_f, Category.assoc, Karoubi.id_f, mapFunctor_obj_p]
        rw [α.inv.naturality_assoc, ← F.map_comp, P.idem, α.hom_inv_id_app_assoc])
      inv_hom_id := Karoubi.hom_ext _ _ (by
        simp only [Karoubi.comp_f, Category.assoc, Karoubi.id_f, mapFunctor_obj_p]
        rw [α.hom.naturality_assoc, ← G.map_comp, P.idem, α.inv_hom_id_app_assoc]) })
    (fun {P Q} f => Karoubi.hom_ext _ _ (by
      simp only [Functor.comp_map, mapFunctor_map_f, Karoubi.comp_f]
      rw [α.hom.naturality_assoc, ← G.map_comp, Karoubi.comp_p, Category.assoc, ← G.map_comp,
        Karoubi.p_comp]))

/-- A natural isomorphism `F ≅ 𝟭` induces `mapFunctor F ≅ 𝟭`. -/
def mapIsoId {F : C ⥤ C} (α : F ≅ 𝟭 C) : mapFunctor F ≅ 𝟭 (Karoubi C) :=
  mapIso α ≪≫ NatIso.ofComponents (fun P => Iso.refl _) (fun f => by simp)

omit [Preadditive C] in
theorem mapIsoId_hom_app_f {F : C ⥤ C} (α : F ≅ 𝟭 C) (P : Karoubi C) :
    ((mapIsoId α).hom.app P).f = α.hom.app P.X ≫ P.p := by
  simp [mapIsoId]

omit [Preadditive C] in
theorem mapIsoId_inv_app_f {F : C ⥤ C} (α : F ≅ 𝟭 C) (P : Karoubi C) :
    ((mapIsoId α).inv.app P).f = P.p ≫ α.inv.app P.X ≫ F.map P.p := by
  simp [mapIsoId]

variable [QPiCategory R C]

/-- **The `(Q, Π)`-category structure on the idempotent completion**:
`Q(X, p) = (Q X, Q p)`, `Q⁻¹(X, p) = (Q⁻¹ X, Q⁻¹ p)`. -/
instance instQPiCategory : QPiCategory R (Karoubi C) where
  Q := mapFunctor (QPiCategory.Q (R := R) (C := C))
  Qinv := mapFunctor (QPiCategory.Qinv (R := R) (C := C))
  ii := mapIsoId (F := QPiCategory.Q (R := R) (C := C) ⋙ QPiCategory.Qinv (R := R))
    (QPiCategory.ii (R := R) (C := C))
  jj := mapIsoId (F := QPiCategory.Qinv (R := R) (C := C) ⋙ QPiCategory.Q (R := R))
    (QPiCategory.jj (R := R) (C := C))
  left_triangle P := Karoubi.hom_ext _ _ (by
    simp only [Karoubi.comp_f, mapFunctor_map_f, mapIsoId_hom_app_f, mapIsoId_inv_app_f,
      Karoubi.id_f, mapFunctor_obj_p, Functor.map_comp, Category.assoc, Functor.comp_map]
    have n := (QPiCategory.jj (R := R) (C := C)).hom.naturality ((QPiCategory.Q (R := R)).map P.p)
    simp only [Functor.comp_map, Functor.id_map] at n
    erw [reassoc_of% n, reassoc_of% (QPiCategory.left_triangle (R := R) P.X)]
    rw [← (QPiCategory.Q (R := R)).map_comp, P.idem, ← (QPiCategory.Q (R := R)).map_comp, P.idem])
  right_triangle P := Karoubi.hom_ext _ _ (by
    simp only [Karoubi.comp_f, mapFunctor_map_f, mapIsoId_hom_app_f, mapIsoId_inv_app_f,
      Karoubi.id_f, mapFunctor_obj_p, Functor.map_comp, Category.assoc, Functor.comp_map]
    have n := (QPiCategory.jj (R := R) (C := C)).hom.naturality P.p
    simp only [Functor.comp_map, Functor.id_map] at n
    rw [← Functor.map_comp_assoc (QPiCategory.Qinv (R := R)) _ ((QPiCategory.jj (R := R)).hom.app P.X), n,
      Functor.map_comp_assoc]
    erw [reassoc_of% (QPiCategory.right_triangle (R := R) P.X)]
    rw [← (QPiCategory.Qinv (R := R)).map_comp, P.idem, ← (QPiCategory.Qinv (R := R)).map_comp, P.idem])
  Q_pi :=
    { β := mapIso (F := QPiCategory.Q (R := R) (C := C) ⋙ PiCategory.pi (R := R))
        (G := PiCategory.pi (R := R) ⋙ QPiCategory.Q (R := R)) (QPiCategory.Q_pi (R := R) (C := C)).β
      comm := fun P => Karoubi.hom_ext _ _ (by
        show ((PiCategory.ξ (R := R)).hom.app _ ≫ (QPiCategory.Q (R := R)).map P.p) ≫
            (QPiCategory.Q (R := R)).map (P.p ≫ (PiCategory.ξ (R := R)).inv.app P.X) =
          (PiCategory.pi (R := R)).map ((QPiCategory.Q_pi (R := R) (C := C)).β.hom.app P.X ≫
            (QPiCategory.Q (R := R)).map ((PiCategory.pi (R := R)).map P.p)) ≫
            ((QPiCategory.Q_pi (R := R) (C := C)).β.hom.app ((PiCategory.pi (R := R)).obj P.X) ≫
              (QPiCategory.Q (R := R)).map ((PiCategory.pi (R := R)).map
                ((PiCategory.pi (R := R)).map P.p)))
        have n1 := (PiCategory.ξ (R := R) (C := C)).inv.naturality P.p
        have n2 := (QPiCategory.Q_pi (R := R) (C := C)).β.hom.naturality
          ((PiCategory.pi (R := R)).map P.p)
        simp only [Functor.id_map, Functor.comp_map] at n1 n2
        have c := (QPiCategory.Q_pi (R := R) (C := C)).comm P.X
        simp only [Category.assoc]
        rw [← Functor.map_comp (QPiCategory.Q (R := R)) P.p, P.idem_assoc, n1, Functor.map_comp,
          reassoc_of% c, Functor.map_comp (PiCategory.pi (R := R))
            ((QPiCategory.Q_pi (R := R) (C := C)).β.hom.app P.X), Category.assoc,
          reassoc_of% n2, ← Functor.map_comp (QPiCategory.Q (R := R)),
          ← Functor.map_comp (PiCategory.pi (R := R)), ← Functor.map_comp (PiCategory.pi (R := R)),
          P.idem]) }

end Karoubi

/-! ## `K₀` of a `(Q, Π)`-category as a `Zπ[q, q⁻¹]`-module -/

namespace K₀

open Polynomial LaurentPolynomial

variable (R) (A : Type u) [Category.{v} A] [Preadditive A] [Linear R A] [QPiCategory R A]
  [HasBinaryBiproducts A]

/-- `q[V] := [Q V]`. -/
def qEnd : AddMonoid.End (K₀ A) := map (QPiCategory.Q (R := R) (C := A))

/-- `q⁻¹[V] := [Q⁻¹ V]`. -/
def qinvEnd : AddMonoid.End (K₀ A) := map (QPiCategory.Qinv (R := R) (C := A))

theorem qEnd_mul_qinvEnd : qEnd R A * qinvEnd R A = 1 := by
  show (map _).comp (map _) = AddMonoidHom.id _
  rw [← map_comp, map_eq_of_iso (QPiCategory.jj (R := R) (C := A)), map_id]

theorem qinvEnd_mul_qEnd : qinvEnd R A * qEnd R A = 1 := by
  show (map _).comp (map _) = AddMonoidHom.id _
  rw [← map_comp, map_eq_of_iso (QPiCategory.ii (R := R) (C := A)), map_id]

/-- `q` as a unit of `End(K₀ A)`. -/
def qUnit : (AddMonoid.End (K₀ A))ˣ :=
  ⟨qEnd R A, qinvEnd R A, qEnd_mul_qinvEnd R A, qinvEnd_mul_qEnd R A⟩

theorem piInvolution_commute :
    Commute (show AddMonoid.End (K₀ A) from piInvolution R A) (qEnd R A) := by
  show (map _).comp (map _) = (map _).comp (map _)
  rw [← map_comp, ← map_comp, map_eq_of_iso (QPiCategory.Q_pi (R := R) (C := A)).β]

theorem toEnd_commute (r : Zπ) :
    Commute (Zπ.toEnd (piInvolution R A) (piInvolution_piInvolution R A) r) (qEnd R A) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective r
  show Commute (Polynomial.eval₂ (Int.castRingHom _)
    (show AddMonoid.End (K₀ A) from piInvolution R A) p) _
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.eval₂_add]; exact hp.add_left hq
  | monomial n a =>
    rw [Polynomial.eval₂_monomial]
    exact (Int.cast_commute a _).mul_left ((piInvolution_commute R A).pow_left n)

/-- The ring homomorphism `Zπ[q, q⁻¹] → End(K₀ A)`: `π ↦ [Π]`, `q ↦ [Q]`. -/
def laurentEnd : LaurentPolynomial Zπ →+* AddMonoid.End (K₀ A) :=
  AddMonoidAlgebra.liftNCRingHom (Zπ.toEnd (piInvolution R A) (piInvolution_piInvolution R A))
    ((Units.coeHom _).comp (zpowersHom _ (qUnit R A))) fun r n => by
      simp only [MonoidHom.comp_apply, Units.coeHom_apply, zpowersHom_apply]
      exact ((toEnd_commute R A r).units_zpow_right (u := qUnit R A) _)

/-- **Brundan–Ellis, §6.** `K₀` of a `(Q, Π)`-category with biproducts is a module over
`Zπ[q, q⁻¹]`, with `π` acting as `[Π]` and `q` acting as `[Q]`. -/
def moduleLaurent : Module (LaurentPolynomial Zπ) (K₀ A) := Module.compHom (K₀ A) (laurentEnd R A)

theorem laurentEnd_C (r : Zπ) : laurentEnd R A (C r) =
    Zπ.toEnd (piInvolution R A) (piInvolution_piInvolution R A) r := by
  rw [laurentEnd, ← single_eq_C]
  erw [AddMonoidAlgebra.liftNC_single]
  simp

theorem laurentEnd_T (n : ℤ) : laurentEnd R A (T n) = ((qUnit R A ^ n : (AddMonoid.End (K₀ A))ˣ) :
    AddMonoid.End (K₀ A)) := by
  rw [laurentEnd, T]
  erw [AddMonoidAlgebra.liftNC_single]
  simp

theorem C_π_smul_mk (V : A) :
    letI := moduleLaurent R A
    (C Zπ.π : LaurentPolynomial Zπ) • mk V = mk ((PiCategory.pi (R := R)).obj V) := by
  show laurentEnd R A (C Zπ.π) (mk V) = _
  rw [laurentEnd_C, Zπ.toEnd_π, piInvolution_mk]

theorem T_smul_mk (V : A) :
    letI := moduleLaurent R A
    (T 1 : LaurentPolynomial Zπ) • mk V = mk ((QPiCategory.Q (R := R)).obj V) := by
  show laurentEnd R A (T 1) (mk V) = _
  rw [laurentEnd_T, zpow_one]
  exact map_mk _ V

theorem T_neg_one_smul_mk (V : A) :
    letI := moduleLaurent R A
    (T (-1) : LaurentPolynomial Zπ) • mk V = mk ((QPiCategory.Qinv (R := R)).obj V) := by
  show laurentEnd R A (T (-1)) (mk V) = _
  rw [laurentEnd_T, zpow_neg_one]
  exact map_mk _ V

end K₀

/-! ## The graded super Karoubi envelope -/

open GradedSupercategory

variable (R) in
/-- **Brundan–Ellis, §6.** The graded super Karoubi envelope `GSKar(A) := Kar(A̲_{q,π})`: the
additive Karoubi envelope of the underlying category of the `(Q, Π)`-envelope. -/
abbrev GSKar (C : Type u) [Category.{v} C] [Preadditive C] [Linear R C] [Supercategory R C]
    [GradedSupercategory R C] :=
  Karoubi (Mat_ (GUnderlying R (QPiEnvelope R C)))

namespace GSKar

variable (C : Type u) [Category.{v} C] [Preadditive C] [Linear R C] [Supercategory R C]
  [GradedSupercategory R C]

example : Linear R (GSKar R C) := inferInstance
example : HasFiniteBiproducts (GSKar R C) := inferInstance
example : IsIdempotentComplete (GSKar R C) := inferInstance

/-- **Brundan–Ellis, §6.** `GSKar(A)` is a `(Q, Π)`-category (additive and idempotent
complete). -/
instance instQPiCategory : QPiCategory R (GSKar R C) := Karoubi.instQPiCategory

variable (R) in
/-- **Brundan–Ellis, §6.** `K₀(GSKar(A))` is a `Zπ[q, q⁻¹]`-module with `π` acting as `[Π]` and
`q` acting as `[Q]`. -/
def moduleLaurent : Module (LaurentPolynomial Zπ) (K₀ (GSKar R C)) := K₀.moduleLaurent R (GSKar R C)

end GSKar

end StringDiagrams

end
