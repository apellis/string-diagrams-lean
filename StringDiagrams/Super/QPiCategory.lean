import StringDiagrams.Super.QPi

/-!
# (Q, Π)-categories and the underlying (Q, Π)-category of a graded (Q, Π)-supercategory

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §6,
Definition 6.12 and the strict 2-functor `𝔼` of (6.3).

* A `(Q, Π)`-category (`StringDiagrams.QPiCategory`, Definition 6.12(i)) is a Π-category
  `(A, Π, ξ)` (Definition 1.6) with endofunctors `Q`, `Q⁻¹`, natural isomorphisms
  `ii : Q⁻¹Q ≅ I`, `jj : QQ⁻¹ ≅ I` such that `ii⁻¹` and `jj` are the unit and counit of an
  adjunction (the triangle identities `left_triangle`, `right_triangle`, equivalently
  `Q ii = jj Q` and `ii Q⁻¹ = Q⁻¹ jj`: `Q_map_ii`, `ii_Qinv`), and a Π-functor structure
  `β_Q : ΠQ ≅ QΠ` on `Q` (the condition `ξQξ⁻¹ = β_QΠ ∘ Πβ_Q` is the axiom of
  `StringDiagrams.PiFunctor`).
* A `(Q, Π)`-functor (`StringDiagrams.QPiFunctor`, Definition 6.12(ii)) is a Π-functor
  `(F, β_F)` with a natural isomorphism `γ_F : Q'F ≅ FQ`. The identity, `Π` (with
  `β_Π = -1`, `γ_Π = β_Q⁻¹`) and `Q` (with `β_Q`, `γ_Q = 1`) are `(Q, Π)`-functors
  (`QPiFunctor.id`, `QPiFunctor.pi`, `QPiFunctor.Q`), and they compose (`QPiFunctor.comp`).
* A `(Q, Π)`-natural transformation (`QPiFunctor.IsQPiNatural`, Definition 6.12(iii)).
* The strict 2-functor `𝔼 : (Q,Π)-GSCat → (Q,Π)-Cat` of (6.3): the underlying category
  `GUnderlying R A` (even morphisms of degree zero) of a graded `(Q, Π)`-supercategory is a
  `(Q, Π)`-category (instance `GradedSupercategory.GUnderlying.instQPiCategory`), with
  `ξ = ζζ`, `ii = σ̄σ`, `jj = σσ̄`, and `β_Q` as in Corollary 6.7; a graded superfunctor gives
  a `(Q, Π)`-functor (`GUnderlying.qpiFunctor`), and a supernatural transformation that is
  even of degree zero gives a `(Q, Π)`-natural transformation (`GUnderlying.natTrans`,
  `GUnderlying.isQPiNatural`). Compatibility with composition: `GUnderlying.map_comp`,
  `GUnderlying.qpiFunctor_comp_β`, `GUnderlying.qpiFunctor_comp_γ`.

Along the way, the morphisms of degree zero of a graded `(Q, Π)`-supercategory form a
Π-supercategory (instance `GradedSupercategory.DegreeZero.instPiSupercategory`).

Compositions are written in diagrammatic order.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory GradedSupercategory

universe w w₁ w₂ w₃ w₄ w₅ w₆

variable (R : Type w) [CommRing R]

/-- A `(Q, Π)`-category (Brundan–Ellis, Definition 6.12(i)): a Π-category with an adjoint pair
of auto-equivalences `(Q, Q⁻¹)` with unit `ii⁻¹` and counit `jj`, and a Π-functor structure
`β_Q : ΠQ ≅ QΠ` on `Q`. -/
class QPiCategory (C : Type w₁) [Category.{w₂} C] [Preadditive C] [Linear R C] extends
    PiCategory R C where
  /-- The functor `Q`. -/
  Q : C ⥤ C
  [Q_additive : Q.Additive]
  [Q_linear : Q.Linear R]
  /-- The functor `Q⁻¹`. -/
  Qinv : C ⥤ C
  [Qinv_additive : Qinv.Additive]
  [Qinv_linear : Qinv.Linear R]
  /-- `ii : Q⁻¹Q ≅ I`. -/
  ii : Q ⋙ Qinv ≅ 𝟭 C
  /-- `jj : QQ⁻¹ ≅ I`. -/
  jj : Qinv ⋙ Q ≅ 𝟭 C
  /-- The triangle identity `jj Q ∘ Q ii⁻¹ = 1_Q`. -/
  left_triangle : ∀ X : C, Q.map (ii.inv.app X) ≫ jj.hom.app (Q.obj X) = 𝟙 (Q.obj X)
  /-- The triangle identity `Q⁻¹ jj ∘ ii⁻¹ Q⁻¹ = 1_{Q⁻¹}`. -/
  right_triangle : ∀ X : C, ii.inv.app (Qinv.obj X) ≫ Qinv.map (jj.hom.app X) = 𝟙 (Qinv.obj X)
  /-- The isomorphism `β_Q : ΠQ ≅ QΠ` with `ξQξ⁻¹ = β_QΠ ∘ Πβ_Q`. -/
  Q_pi : PiFunctor R Q

attribute [instance] QPiCategory.Q_additive QPiCategory.Q_linear QPiCategory.Qinv_additive
  QPiCategory.Qinv_linear

namespace QPiCategory

variable {R} {C : Type w₁} [Category.{w₂} C] [Preadditive C] [Linear R C] [QPiCategory R C]

/-- The triangle identities say `Q ii = jj Q`. -/
theorem Q_map_ii (X : C) :
    (Q (R := R)).map ((ii (R := R)).hom.app X) = (jj (R := R)).hom.app ((Q (R := R)).obj X) := by
  rw [← cancel_epi ((Q (R := R)).map ((ii (R := R)).inv.app X)), ← Functor.map_comp,
    Iso.inv_hom_id_app, left_triangle]
  exact (Q (R := R)).map_id _

/-- The triangle identities say `ii Q⁻¹ = Q⁻¹ jj`. -/
theorem ii_Qinv (X : C) :
    (ii (R := R)).hom.app ((Qinv (R := R)).obj X) = (Qinv (R := R)).map ((jj (R := R)).hom.app X) := by
  rw [← cancel_epi ((ii (R := R)).inv.app ((Qinv (R := R)).obj X)), Iso.inv_hom_id_app,
    right_triangle]
  rfl

variable (R C) in
/-- The adjoint equivalence `(Q, Q⁻¹)` with unit `ii⁻¹` and counit `jj`. -/
def qEquivalence : C ≌ C where
  functor := Q (R := R)
  inverse := Qinv (R := R)
  unitIso := (ii (R := R)).symm
  counitIso := jj (R := R)
  functor_unitIso_comp X := left_triangle X

end QPiCategory

open QPiCategory PiCategory

variable {R} {C : Type w₁} [Category.{w₂} C] [Preadditive C] [Linear R C] [QPiCategory R C]
  {D : Type w₃} [Category.{w₄} D] [Preadditive D] [Linear R D] [QPiCategory R D]
  {E : Type w₅} [Category.{w₆} E] [Preadditive E] [Linear R E] [QPiCategory R E]

variable (R) in
/-- A `(Q, Π)`-functor (Brundan–Ellis, Definition 6.12(ii)): a Π-functor `(F, β_F)` with a
natural isomorphism `γ_F : Q'F ≅ FQ`. -/
structure QPiFunctor (F : C ⥤ D) extends PiFunctor R F where
  /-- The isomorphism `γ_F : Q'F ≅ FQ`. -/
  γ : F ⋙ QPiCategory.Q (R := R) ≅ QPiCategory.Q (R := R) ⋙ F

namespace QPiFunctor

variable (R C) in
/-- **Definition 6.12(ii).** The identity functor, with `β_I = 1` and `γ_I = 1`. -/
@[simps!]
def id : QPiFunctor R (𝟭 C) where
  toPiFunctor := PiFunctor.id R C
  γ := Iso.refl _

variable (R C) in
/-- **Definition 6.12(ii).** `Π`, with `β_Π = -1` and `γ_Π = β_Q⁻¹`. -/
@[simps!]
def pi : QPiFunctor R (PiCategory.pi (R := R) (C := C)) where
  toPiFunctor := PiFunctor.pi
  γ := (QPiCategory.Q_pi (R := R) (C := C)).β.symm

variable (R C) in
/-- **Definition 6.12(ii).** `Q`, with `β_Q` and `γ_Q = 1`. -/
def Q : QPiFunctor R (QPiCategory.Q (R := R) (C := C)) where
  toPiFunctor := QPiCategory.Q_pi
  γ := Iso.refl _

/-- The composite of `(Q, Π)`-functors, with `β_{GF} = Gβ_F ∘ β_G F` and
`γ_{GF} = Gγ_F ∘ γ_G F`. -/
@[simps!]
def comp {F : C ⥤ D} {G : D ⥤ E} (hF : QPiFunctor R F) (hG : QPiFunctor R G) :
    QPiFunctor R (F ⋙ G) where
  toPiFunctor := hF.toPiFunctor.comp hG.toPiFunctor
  γ := NatIso.ofComponents (fun X => hG.γ.app (F.obj X) ≪≫ G.mapIso (hF.γ.app X)) (fun f => by
    have n1 := hF.γ.hom.naturality f
    have n2 := hG.γ.hom.naturality (F.map f)
    simp only [Functor.comp_obj, Functor.comp_map] at n1 n2 ⊢
    simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
    rw [reassoc_of% n2, ← G.map_comp, ← G.map_comp, n1])

variable (R) in
/-- A `(Q, Π)`-natural transformation (Brundan–Ellis, Definition 6.12(iii)):
`xΠ ∘ β_F = β_G ∘ Π'x` and `xQ ∘ γ_F = γ_G ∘ Q'x`. -/
def IsQPiNatural {F G : C ⥤ D} (hF : QPiFunctor R F) (hG : QPiFunctor R G) (x : F ⟶ G) : Prop :=
  PiFunctor.IsPiNatural R hF.toPiFunctor hG.toPiFunctor x ∧
    ∀ X : C, hF.γ.hom.app X ≫ x.app ((QPiCategory.Q (R := R)).obj X) =
      (QPiCategory.Q (R := R)).map (x.app X) ≫ hG.γ.hom.app X

variable (R) in
/-- The compatibility of `γ_F` with `β` (needed for Theorem 6.13, see the erratum in
`StringDiagrams.Super.QAssociated`): `γ_F` is a Π-natural transformation between the
Π-functors `Q' F` and `F Q`, i.e. `γ_F Π ∘ Q' β_F ∘ β_{Q'} F = F β_Q ∘ β_F Q ∘ Π' γ_F` in
`Hom(Π' Q' F, F Q Π)`. -/
def IsCompatible {F : C ⥤ D} (hF : QPiFunctor R F) : Prop :=
  PiFunctor.IsPiNatural R (hF.toPiFunctor.comp (QPiCategory.Q_pi (R := R) (C := D)))
    ((QPiCategory.Q_pi (R := R) (C := C)).comp hF.toPiFunctor) hF.γ.hom

theorem IsCompatible.iff {F : C ⥤ D} (hF : QPiFunctor R F) :
    hF.IsCompatible R ↔ ∀ X : C,
      (QPiCategory.Q_pi (R := R) (C := D)).β.hom.app (F.obj X) ≫
        (QPiCategory.Q (R := R)).map (hF.β.hom.app X) ≫
          hF.γ.hom.app ((PiCategory.pi (R := R)).obj X) =
      (PiCategory.pi (R := R)).map (hF.γ.hom.app X) ≫ hF.β.hom.app ((QPiCategory.Q (R := R)).obj X) ≫
        F.map ((QPiCategory.Q_pi (R := R) (C := C)).β.hom.app X) := by
  unfold IsCompatible PiFunctor.IsPiNatural
  simp only [PiFunctor.comp_β, NatIso.ofComponents_hom_app, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Category.assoc]

/-- Compatibility is invariant under `(Q, Π)`-natural isomorphisms. -/
theorem IsCompatible.of_iso {F G : C ⥤ D} {hF : QPiFunctor R F} {hG : QPiFunctor R G}
    (x : F ≅ G) (hx : IsQPiNatural R hF hG x.hom) (hc : hG.IsCompatible R) :
    hF.IsCompatible R := by
  rw [IsCompatible.iff] at hc ⊢
  intro X
  rw [← cancel_mono (x.hom.app ((QPiCategory.Q (R := R)).obj ((PiCategory.pi (R := R)).obj X)))]
  have h1 := hx.2 ((PiCategory.pi (R := R)).obj X)
  have h2 := hx.1 X
  have h3 := hx.1 ((QPiCategory.Q (R := R)).obj X)
  have h4 := hx.2 X
  have n1 := (QPiCategory.Q_pi (R := R) (C := D)).β.hom.naturality (x.hom.app X)
  have n2 := x.hom.naturality ((QPiCategory.Q_pi (R := R) (C := C)).β.hom.app X)
  simp only [Functor.comp_obj, Functor.comp_map] at n1 n2
  simp only [Category.assoc]
  rw [h1, ← Functor.map_comp_assoc, h2, Functor.map_comp_assoc, ← reassoc_of% n1, hc X, n2,
    reassoc_of% h3, ← Functor.map_comp_assoc (PiCategory.pi (R := R)) (hF.γ.hom.app X), h4,
    Functor.map_comp_assoc]

theorem isQPiNatural_id {F : C ⥤ D} (hF : QPiFunctor R F) : IsQPiNatural R hF hF (𝟙 F) :=
  ⟨PiFunctor.isPiNatural_id hF.toPiFunctor, fun X => by simp⟩

theorem IsQPiNatural.comp {F G H : C ⥤ D} {hF : QPiFunctor R F} {hG : QPiFunctor R G}
    {hH : QPiFunctor R H} {x : F ⟶ G} {y : G ⟶ H} (hx : IsQPiNatural R hF hG x)
    (hy : IsQPiNatural R hG hH y) : IsQPiNatural R hF hH (x ≫ y) :=
  ⟨hx.1.comp hy.1, fun X => by
    simp only [NatTrans.comp_app, Functor.map_comp, Category.assoc]
    rw [reassoc_of% (hx.2 X), hy.2 X]⟩

end QPiFunctor

/-! ## The strict 2-functor `𝔼` of (6.3) -/

namespace GradedSupercategory

variable {A : Type w₁} [Category.{w₂} A] [Preadditive A] [Linear R A] [Supercategory R A]
  [GradedSupercategory R A] [QPiSupercategory R A]
  {B : Type w₃} [Category.{w₄} B] [Preadditive B] [Linear R B] [Supercategory R B]
  [GradedSupercategory R B] [QPiSupercategory R B]
  {B' : Type w₅} [Category.{w₆} B'] [Preadditive B'] [Linear R B'] [Supercategory R B']
  [GradedSupercategory R B'] [QPiSupercategory R B']

namespace DegreeZero

/-- The morphisms of degree zero of a graded `(Q, Π)`-supercategory form a Π-supercategory:
`ζ` has degree zero. -/
instance instPiSupercategory : PiSupercategory R (DegreeZero R A) where
  pi := map (R := R) (PiSupercategory.pi (R := R) (C := A))
  ζ X := isoMk (PiSupercategory.ζ (R := R) X.obj) (QPiSupercategory.ζ_hom_mem_degree X.obj)
  ζ_isSupernatural :=
    { mem := fun X => PiSupercategory.ζ_hom_mem (R := R) X.obj
      naturality := fun hf => Subtype.ext
        ((PiSupercategory.ζ_isSupernatural (R := R) (C := A)).naturality hf) }

@[simp] theorem pi_obj (X : DegreeZero R A) :
    (PiSupercategory.pi (R := R)).obj X = ⟨(PiSupercategory.pi (R := R)).obj X.obj⟩ := rfl

@[simp] theorem pi_map_val {X Y : DegreeZero R A} (f : X ⟶ Y) :
    ((PiSupercategory.pi (R := R)).map f).1 = (PiSupercategory.pi (R := R)).map f.1 := rfl

@[simp] theorem ζ_hom_val (X : DegreeZero R A) :
    (PiSupercategory.ζ (R := R) X).hom.1 = (PiSupercategory.ζ (R := R) X.obj).hom := rfl

@[simp] theorem ζ_inv_val (X : DegreeZero R A) :
    (PiSupercategory.ζ (R := R) X).inv.1 = (PiSupercategory.ζ (R := R) X.obj).inv := rfl

theorem ξ_hom_val (X : DegreeZero R A) :
    (PiSupercategory.ξ (R := R) X).hom.1 = (PiSupercategory.ξ (R := R) X.obj).hom := rfl

theorem β_hom_val (F : A ⥤ B) [F.Additive] [F.Linear R] [IsGradedSuperfunctor R F]
    (X : DegreeZero R A) :
    (PiSupercategory.β R (map (R := R) F) X).hom.1 = (PiSupercategory.β R F X.obj).hom := rfl

end DegreeZero

namespace GUnderlying

open QPiSupercategory

/-- The functor `Q` on the underlying category. -/
abbrev QU : GUnderlying R A ⥤ GUnderlying R A :=
  Underlying.map (R := R) (DegreeZero.map (R := R) (QPiSupercategory.Q (R := R) (C := A)))

/-- The functor `Q⁻¹` on the underlying category. -/
abbrev QinvU : GUnderlying R A ⥤ GUnderlying R A :=
  Underlying.map (R := R) (DegreeZero.map (R := R) (QPiSupercategory.Qinv (R := R) (C := A)))

/-- An isomorphism of `A` that is even of degree zero, as an isomorphism of the underlying
category. -/
def isoU {X Y : A} (e : X ≅ Y) (h0 : e.hom ∈ parity (R := R) X Y 0)
    (hd : e.hom ∈ degree (R := R) X Y 0) : (⟨⟨X⟩⟩ : GUnderlying R A) ≅ ⟨⟨Y⟩⟩ :=
  Underlying.isoMk (DegreeZero.isoMk e hd) h0

/-- `ii = σ̄σ` on the underlying category. -/
def iiU : QU (R := R) (A := A) ⋙ QinvU (R := R) ≅ 𝟭 (GUnderlying R A) :=
  NatIso.ofComponents (fun X => isoU (ii (R := R) X.obj.obj) (ii_hom_mem _) (ii_hom_mem_degree _))
    fun f => Underlying.hom_ext (DegreeZero.hom_ext (ii_naturality f.1.1))

/-- `jj = σσ̄` on the underlying category. -/
def jjU : QinvU (R := R) (A := A) ⋙ QU (R := R) ≅ 𝟭 (GUnderlying R A) :=
  NatIso.ofComponents (fun X => isoU (jj (R := R) X.obj.obj) (jj_hom_mem _) (jj_hom_mem_degree _))
    fun f => Underlying.hom_ext (DegreeZero.hom_ext (jj_naturality f.1.1))

/-- **(6.3), `𝔼` on objects.** The underlying category of a graded `(Q, Π)`-supercategory is a
`(Q, Π)`-category (Brundan–Ellis, Corollary 6.7(i)–(ii)). -/
instance instQPiCategory : QPiCategory R (GUnderlying R A) where
  Q := QU
  Qinv := QinvU
  ii := iiU
  jj := jjU
  left_triangle X := by
    apply Underlying.hom_ext; apply DegreeZero.hom_ext
    show (QPiSupercategory.Q (R := R)).map (ii (R := R) X.obj.obj).inv ≫
      (jj (R := R) ((QPiSupercategory.Q (R := R)).obj X.obj.obj)).hom = 𝟙 _
    rw [← QPiSupercategory.Q_map_ii, ← Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id]
  right_triangle X := by
    apply Underlying.hom_ext; apply DegreeZero.hom_ext
    show (ii (R := R) ((QPiSupercategory.Qinv (R := R)).obj X.obj.obj)).inv ≫
      (QPiSupercategory.Qinv (R := R)).map (jj (R := R) X.obj.obj).hom = 𝟙 _
    rw [← QPiSupercategory.ii_Qinv, Iso.inv_hom_id]
  Q_pi := Underlying.piFunctor (R := R) (DegreeZero.map (R := R) (QPiSupercategory.Q (R := R)))

@[simp] theorem Q_obj (X : GUnderlying R A) :
    (QPiCategory.Q (R := R)).obj X = ⟨⟨(QPiSupercategory.Q (R := R)).obj X.obj.obj⟩⟩ := rfl

@[simp] theorem Q_map_val {X Y : GUnderlying R A} (f : X ⟶ Y) :
    ((QPiCategory.Q (R := R)).map f).1.1 = (QPiSupercategory.Q (R := R)).map f.1.1 := rfl

@[simp] theorem ii_hom_app_val (X : GUnderlying R A) :
    ((QPiCategory.ii (R := R)).hom.app X).1.1 = (ii (R := R) X.obj.obj).hom := rfl

@[simp] theorem jj_hom_app_val (X : GUnderlying R A) :
    ((QPiCategory.jj (R := R)).hom.app X).1.1 = (jj (R := R) X.obj.obj).hom := rfl

@[simp] theorem β_Q_hom_app_val (X : GUnderlying R A) :
    ((QPiCategory.Q_pi (R := R) (C := GUnderlying R A)).β.hom.app X).1.1 =
      (PiSupercategory.β R (QPiSupercategory.Q (R := R) (C := A)) X.obj.obj).hom := rfl

variable (R) in
/-- The restriction `F̲` of a graded superfunctor to the underlying categories. -/
abbrev map (F : A ⥤ B) [F.Additive] [F.Linear R] [IsGradedSuperfunctor R F] :
    GUnderlying R A ⥤ GUnderlying R B :=
  Underlying.map (R := R) (DegreeZero.map (R := R) F)

/-- `γ_F` on the underlying categories. -/
def γU (F : A ⥤ B) [F.Additive] [F.Linear R] [IsGradedSuperfunctor R F] :
    map R F ⋙ QPiCategory.Q (R := R) ≅ QPiCategory.Q (R := R) ⋙ map R F :=
  NatIso.ofComponents (fun X => isoU (γ R F X.obj.obj) (γ_hom_mem F _) (γ_hom_mem_degree F _))
    fun f => Underlying.hom_ext (DegreeZero.hom_ext (γ_naturality F f.1.1))

/-- **(6.3), `𝔼` on 1-morphisms.** A graded superfunctor between graded
`(Q, Π)`-supercategories gives a `(Q, Π)`-functor `(F̲, β_F, γ_F)` between the underlying
`(Q, Π)`-categories (Brundan–Ellis, Corollary 6.7(ii)). -/
def qpiFunctor (F : A ⥤ B) [F.Additive] [F.Linear R] [IsGradedSuperfunctor R F] :
    QPiFunctor R (map R F) where
  toPiFunctor := Underlying.piFunctor (R := R) (DegreeZero.map (R := R) F)
  γ := γU F

@[simp] theorem qpiFunctor_β_hom_app_val (F : A ⥤ B) [F.Additive] [F.Linear R]
    [IsGradedSuperfunctor R F] (X : GUnderlying R A) :
    ((qpiFunctor (R := R) F).β.hom.app X).1.1 = (PiSupercategory.β R F X.obj.obj).hom := rfl

@[simp] theorem qpiFunctor_γ_hom_app_val (F : A ⥤ B) [F.Additive] [F.Linear R]
    [IsGradedSuperfunctor R F] (X : GUnderlying R A) :
    ((qpiFunctor (R := R) F).γ.hom.app X).1.1 = (γ R F X.obj.obj).hom := rfl

/-- **(6.3), `𝔼` on 2-morphisms.** A supernatural transformation that is even of degree zero
gives a natural transformation of the restrictions. -/
def natTrans {F G : A ⥤ B} [F.Additive] [F.Linear R] [IsGradedSuperfunctor R F] [G.Additive]
    [G.Linear R] [IsGradedSuperfunctor R G] {x : ∀ X, F.obj X ⟶ G.obj X}
    (hx : IsGradedSupernatural R 0 0 x) : map R F ⟶ map R G where
  app X := ⟨⟨x X.obj.obj, hx.mem_degree _⟩, hx.mem _⟩
  naturality _ _ f := Underlying.hom_ext (DegreeZero.hom_ext
    (hx.toIsSupernatural.naturality_zero f.1.1))

omit [QPiSupercategory R A] [QPiSupercategory R B] in
@[simp] theorem natTrans_app_val {F G : A ⥤ B} [F.Additive] [F.Linear R]
    [IsGradedSuperfunctor R F] [G.Additive] [G.Linear R] [IsGradedSuperfunctor R G]
    {x : ∀ X, F.obj X ⟶ G.obj X} (hx : IsGradedSupernatural R 0 0 x) (X : GUnderlying R A) :
    ((natTrans (R := R) hx).app X).1.1 = x X.obj.obj := rfl

/-- **(6.3), `𝔼` on 2-morphisms** (Brundan–Ellis, Corollary 6.7(iii)): the natural
transformation is `(Q, Π)`-natural. -/
theorem isQPiNatural {F G : A ⥤ B} [F.Additive] [F.Linear R] [IsGradedSuperfunctor R F]
    [G.Additive] [G.Linear R] [IsGradedSuperfunctor R G] {x : ∀ X, F.obj X ⟶ G.obj X}
    (hx : IsGradedSupernatural R 0 0 x) :
    QPiFunctor.IsQPiNatural R (qpiFunctor (R := R) F) (qpiFunctor (R := R) G) (natTrans (R := R) hx) :=
  ⟨fun X => Underlying.hom_ext (DegreeZero.hom_ext
      (PiSupercategory.β_naturality_supernatural F G hx.toIsSupernatural X.obj.obj).symm),
    fun X => Underlying.hom_ext (DegreeZero.hom_ext
      (γ_naturality_supernatural F G hx.toIsSupernatural X.obj.obj).symm)⟩

/-- The `(Q, Π)`-functors in the image of `𝔼` satisfy the compatibility
`QPiFunctor.IsCompatible` (from `QPiSupercategory.β_γ_compat`). -/
theorem qpiFunctor_isCompatible (F : A ⥤ B) [F.Additive] [F.Linear R] [IsGradedSuperfunctor R F] :
    (qpiFunctor (R := R) F).IsCompatible R := by
  rw [QPiFunctor.IsCompatible.iff]
  intro X
  apply Underlying.hom_ext; apply DegreeZero.hom_ext
  exact QPiSupercategory.β_γ_compat F X.obj.obj

omit [QPiSupercategory R A] [QPiSupercategory R B] [QPiSupercategory R B'] in
/-- **(6.3)**, `𝔼` is a strict 2-functor: it preserves composition of 1-morphisms. -/
theorem map_comp (F : A ⥤ B) [F.Additive] [F.Linear R] [IsGradedSuperfunctor R F]
    (G : B ⥤ B') [G.Additive] [G.Linear R] [IsGradedSuperfunctor R G] :
    map R (F ⋙ G) = map R F ⋙ map R G := rfl

omit [QPiSupercategory R A] in
theorem map_id : map R (𝟭 A) = 𝟭 (GUnderlying R A) := rfl

/-- **(6.3)**, `𝔼` preserves the `β`-isomorphisms of composites. -/
theorem qpiFunctor_comp_β (F : A ⥤ B) [F.Additive] [F.Linear R] [IsGradedSuperfunctor R F]
    (G : B ⥤ B') [G.Additive] [G.Linear R] [IsGradedSuperfunctor R G] (X : GUnderlying R A) :
    (qpiFunctor (R := R) (F ⋙ G)).β.hom.app X = ((qpiFunctor (R := R) F).comp (qpiFunctor (R := R) G)).β.hom.app X :=
  Underlying.hom_ext (DegreeZero.hom_ext (PiSupercategory.β_comp F G X.obj.obj))

/-- **(6.3)**, `𝔼` preserves the `γ`-isomorphisms of composites. -/
theorem qpiFunctor_comp_γ (F : A ⥤ B) [F.Additive] [F.Linear R] [IsGradedSuperfunctor R F]
    (G : B ⥤ B') [G.Additive] [G.Linear R] [IsGradedSuperfunctor R G] (X : GUnderlying R A) :
    (qpiFunctor (R := R) (F ⋙ G)).γ.hom.app X = ((qpiFunctor (R := R) F).comp (qpiFunctor (R := R) G)).γ.hom.app X :=
  Underlying.hom_ext (DegreeZero.hom_ext (γ_comp F G X.obj.obj))

end GUnderlying

end GradedSupercategory

end StringDiagrams

end
