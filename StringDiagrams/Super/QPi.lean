import StringDiagrams.Super.Graded
import StringDiagrams.Super.Pi
import Mathlib.CategoryTheory.Equivalence

/-!
# Graded (Q, Π)-supercategories

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §6,
Definition 6.4 and Corollary 6.7.

A graded `(Q, Π)`-supercategory is a graded supercategory `A` with graded superfunctors
`Q, Q⁻¹, Π : A → A`, an odd supernatural isomorphism `ζ : Π ⇒ I` of degree `0`, and even
supernatural isomorphisms `σ : Q ⇒ I`, `σ̄ : Q⁻¹ ⇒ I` of degrees `-1` and `1`
(`StringDiagrams.QPiSupercategory`). It extends `PiSupercategory`: the `Π`-part is a
Π-supercategory in the sense of Definition 1.7, so all results of `StringDiagrams.Super.Pi`
(`ξ`, `β_F`, Corollary 3.3) apply verbatim.

That `Π`, `Q` and `Q⁻¹` are *graded* superfunctors is not an extra axiom: since `ζ`, `σ`, `σ̄`
are homogeneous isomorphisms, the action of each functor on morphisms is conjugation by them
(`PiSupercategory.pi_map_eq`, `QPiSupercategory.Q_map_eq`, `QPiSupercategory.Qinv_map_eq`),
so it preserves degrees (instances `pi_isGraded`, `Q_isGraded`, `Qinv_isGraded`).

## Main definitions and statements

* `QPiSupercategory R C` (Definition 6.4); `QPiSupercategory.ofIso`: the structure determined
  by objects and homogeneous isomorphisms `ζ_X`, `σ_X`, `σ̄_X`.
* **Corollary 6.7(i).** `ξ = ζζ`, `ii = σ̄σ : Q⁻¹Q ≅ I`, `jj = σσ̄ : QQ⁻¹ ≅ I` are even of degree
  zero (`ξ_hom_mem_degree`, `ii_hom_mem`, `ii_hom_mem_degree`, `jj_hom_mem`,
  `jj_hom_mem_degree`); `ξΠ = Πξ` (`PiSupercategory.ξ_pi`); `Q ii = jj Q` and
  `ii Q⁻¹ = Q⁻¹ jj` (`Q_map_ii`, `ii_Qinv`), so `ii⁻¹` and `jj` are the unit and counit of an
  adjoint equivalence (`QPiSupercategory.qEquivalence`, with functor `Q` and inverse `Q⁻¹`).
* **Corollary 6.7(ii).** For a graded superfunctor `F`, `β_F := -ζ' F ζ⁻¹` and
  `γ_F := σ' F σ⁻¹ : Q' F ≅ F Q` are even of degree zero (`β_hom_mem_degree`, `γ_hom_mem`,
  `γ_hom_mem_degree`), natural (`γ_naturality`), and `γ_Π = β_Q⁻¹` (`γ_pi`); the identity
  `ξ' F ξ⁻¹ = β_F Π ∘ Π' β_F` is `PiSupercategory.β_comm`.
* **Corollary 6.7(iii).** For a supernatural transformation `x : F ⇒ G` of any parity,
  `γ_G ∘ Q' x = x Q ∘ γ_F` (`γ_naturality_supernatural`; see the erratum below); the
  corresponding statement for `β` is `PiSupercategory.β_naturality_supernatural`.
* **Corollary 6.7(iv).** `γ_{GF} = G γ_F ∘ γ_G F`, `γ_I = 1`, `γ_Q = 1` (`γ_comp`, `γ_id`,
  `γ_Q`); the statements for `β` are `PiSupercategory.β_comp`, `β_id`, `β_pi`.
* `qPow m X` and `σPow m X : qPow m X ≅ X` (even of degree `-m`): the powers `Q^m`, `m ∈ ℤ`,
  and the isomorphisms `σ^m` used in the proof of Lemma 6.11.

## Erratum

Corollary 6.7(iii) is printed as `γ_G ∘ Q' x = x Q ∘ γ_G`; the right-hand side must be
`x Q ∘ γ_F` (the composite `x Q ∘ γ_G` is not defined unless `F = G`). This is a misprint.

Compositions are written in diagrammatic order `f ≫ g` (`= g ∘ f`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory GradedSupercategory

universe w w₁ w₂ w₃ w₄ w₅ w₆

variable (R : Type w) [CommRing R]

/-- A graded `(Q, Π)`-supercategory (Brundan–Ellis, Definition 6.4): a graded supercategory
with a Π-supercategory structure whose `ζ` has degree `0`, and superfunctors `Q`, `Q⁻¹` with
even supernatural isomorphisms `σ : Q ⇒ I` of degree `-1` and `σ̄ : Q⁻¹ ⇒ I` of degree `1`.
That `Π`, `Q`, `Q⁻¹` preserve degrees follows (see the module documentation). -/
class QPiSupercategory (C : Type w₁) [Category.{w₂} C] [Preadditive C] [Linear R C]
    [Supercategory R C] [GradedSupercategory R C] extends PiSupercategory R C where
  ζ_mem_degree : ∀ X : C, (ζ X).hom ∈ degree (R := R) (pi.obj X) X 0
  /-- The degree shift functor `Q`. -/
  Q : C ⥤ C
  [Q_additive : Q.Additive]
  [Q_linear : Q.Linear R]
  [Q_isSuperfunctor : IsSuperfunctor R Q]
  /-- The even isomorphisms `σ_X : Q X ≅ X`, of degree `-1`. -/
  σ : ∀ X : C, Q.obj X ≅ X
  σ_isSupernatural : IsSupernatural R 0 (F := Q) (G := 𝟭 C) fun X => (σ X).hom
  σ_mem_degree : ∀ X : C, (σ X).hom ∈ degree (R := R) (Q.obj X) X (-1)
  /-- The degree shift functor `Q⁻¹`. -/
  Qinv : C ⥤ C
  [Qinv_additive : Qinv.Additive]
  [Qinv_linear : Qinv.Linear R]
  [Qinv_isSuperfunctor : IsSuperfunctor R Qinv]
  /-- The even isomorphisms `σ̄_X : Q⁻¹ X ≅ X`, of degree `1`. -/
  σbar : ∀ X : C, Qinv.obj X ≅ X
  σbar_isSupernatural : IsSupernatural R 0 (F := Qinv) (G := 𝟭 C) fun X => (σbar X).hom
  σbar_mem_degree : ∀ X : C, (σbar X).hom ∈ degree (R := R) (Qinv.obj X) X 1

attribute [instance] QPiSupercategory.Q_additive QPiSupercategory.Q_linear
  QPiSupercategory.Q_isSuperfunctor QPiSupercategory.Qinv_additive QPiSupercategory.Qinv_linear
  QPiSupercategory.Qinv_isSuperfunctor

namespace QPiSupercategory

variable {R} {C : Type w₁} [Category.{w₂} C] [Preadditive C] [Linear R C] [Supercategory R C]
  [GradedSupercategory R C]

/-! ## Construction from homogeneous isomorphisms -/

section OfIso

/-- The functor `f ↦ e_X ≫ f ≫ e_Y⁻¹` determined by isomorphisms `e X : obj X ≅ X`. -/
@[simps]
def conjFunctor (obj : C → C) (e : ∀ X, obj X ≅ X) : C ⥤ C where
  obj := obj
  map {X Y} f := (e X).hom ≫ f ≫ (e Y).inv
  map_id X := by simp
  map_comp f g := by simp

instance (obj : C → C) (e : ∀ X, obj X ≅ X) : (conjFunctor obj e).Additive where
  map_add := by simp [Preadditive.add_comp, Preadditive.comp_add]

instance (obj : C → C) (e : ∀ X, obj X ≅ X) : (conjFunctor obj e).Linear R where
  map_smul _ _ := by simp

omit [GradedSupercategory R C] in
theorem conjFunctor_isSuperfunctor (obj : C → C) (e : ∀ X, obj X ≅ X)
    (he : ∀ X, (e X).hom ∈ parity (R := R) (obj X) X 0) :
    IsSuperfunctor R (conjFunctor obj e) where
  map_mem {X Y p f} hf := by
    have := comp_mem (comp_mem (he X) hf) (inv_mem _ (he Y))
    simpa [Category.assoc] using this

omit [GradedSupercategory R C] in
theorem conjFunctor_isSupernatural (obj : C → C) (e : ∀ X, obj X ≅ X)
    (he : ∀ X, (e X).hom ∈ parity (R := R) (obj X) X 0) :
    IsSupernatural R 0 (F := conjFunctor obj e) (G := 𝟭 C) fun X => (e X).hom :=
  IsSupernatural.of_twist he fun f => by simp

variable [PiSupercategory R C]

/-- **Definition 6.4**, construction: given a Π-supercategory structure whose `ζ` has degree
`0`, a graded `(Q, Π)`-supercategory structure is determined by objects `qObj X`, `qinvObj X`
and even isomorphisms `s X : qObj X ≅ X` of degree `-1`, `t X : qinvObj X ≅ X` of degree
`1`. -/
def ofIso (hζ : ∀ X : C, (PiSupercategory.ζ (R := R) X).hom ∈
      degree (R := R) ((PiSupercategory.pi (R := R)).obj X) X 0)
    (qObj : C → C) (s : ∀ X, qObj X ≅ X) (hs : ∀ X, (s X).hom ∈ parity (R := R) (qObj X) X 0)
    (hs' : ∀ X, (s X).hom ∈ degree (R := R) (qObj X) X (-1))
    (qinvObj : C → C) (t : ∀ X, qinvObj X ≅ X)
    (ht : ∀ X, (t X).hom ∈ parity (R := R) (qinvObj X) X 0)
    (ht' : ∀ X, (t X).hom ∈ degree (R := R) (qinvObj X) X 1) : QPiSupercategory R C :=
  letI := conjFunctor_isSuperfunctor (R := R) qObj s hs
  letI := conjFunctor_isSuperfunctor (R := R) qinvObj t ht
  { (inferInstance : PiSupercategory R C) with
    ζ_mem_degree := hζ
    Q := conjFunctor qObj s
    σ := s
    σ_isSupernatural := conjFunctor_isSupernatural qObj s hs
    σ_mem_degree := hs'
    Qinv := conjFunctor qinvObj t
    σbar := t
    σbar_isSupernatural := conjFunctor_isSupernatural qinvObj t ht
    σbar_mem_degree := ht' }

end OfIso

variable [QPiSupercategory R C]

local notation "𝚷" => PiSupercategory.pi (R := R) (C := C)
local notation "𝐐" => QPiSupercategory.Q (R := R) (C := C)
local notation "𝐐⁻" => QPiSupercategory.Qinv (R := R) (C := C)

/-! ## Basic properties -/

theorem ζ_hom_mem_degree (X : C) :
    (PiSupercategory.ζ (R := R) X).hom ∈ degree (R := R) (𝚷.obj X) X 0 :=
  ζ_mem_degree X

theorem ζ_inv_mem_degree (X : C) :
    (PiSupercategory.ζ (R := R) X).inv ∈ degree (R := R) X (𝚷.obj X) 0 := by
  simpa using inv_mem_degree _ (ζ_mem_degree (R := R) X)

theorem σ_hom_mem (X : C) : (σ (R := R) X).hom ∈ parity (R := R) (𝐐.obj X) X 0 :=
  (σ_isSupernatural (R := R)).mem X

theorem σ_inv_mem (X : C) : (σ (R := R) X).inv ∈ parity (R := R) X (𝐐.obj X) 0 :=
  inv_mem _ (σ_hom_mem X)

theorem σ_hom_mem_degree (X : C) : (σ (R := R) X).hom ∈ degree (R := R) (𝐐.obj X) X (-1) :=
  σ_mem_degree X

theorem σ_inv_mem_degree (X : C) : (σ (R := R) X).inv ∈ degree (R := R) X (𝐐.obj X) 1 := by
  simpa using inv_mem_degree _ (σ_mem_degree (R := R) X)

theorem σbar_hom_mem (X : C) : (σbar (R := R) X).hom ∈ parity (R := R) (𝐐⁻.obj X) X 0 :=
  (σbar_isSupernatural (R := R)).mem X

theorem σbar_inv_mem (X : C) : (σbar (R := R) X).inv ∈ parity (R := R) X (𝐐⁻.obj X) 0 :=
  inv_mem _ (σbar_hom_mem X)

theorem σbar_hom_mem_degree (X : C) :
    (σbar (R := R) X).hom ∈ degree (R := R) (𝐐⁻.obj X) X 1 :=
  σbar_mem_degree X

theorem σbar_inv_mem_degree (X : C) :
    (σbar (R := R) X).inv ∈ degree (R := R) X (𝐐⁻.obj X) (-1) :=
  inv_mem_degree _ (σbar_mem_degree (R := R) X)

/-- Naturality of `σ` (for all morphisms, since `σ` is even). -/
@[reassoc]
theorem σ_naturality {X Y : C} (f : X ⟶ Y) :
    𝐐.map f ≫ (σ (R := R) Y).hom = (σ (R := R) X).hom ≫ f :=
  (σ_isSupernatural (R := R)).naturality_zero f

@[reassoc]
theorem σbar_naturality {X Y : C} (f : X ⟶ Y) :
    𝐐⁻.map f ≫ (σbar (R := R) Y).hom = (σbar (R := R) X).hom ≫ f :=
  (σbar_isSupernatural (R := R)).naturality_zero f

/-- The action of `Q` on morphisms is conjugation by `σ`. -/
theorem Q_map_eq {X Y : C} (f : X ⟶ Y) :
    𝐐.map f = (σ (R := R) X).hom ≫ f ≫ (σ (R := R) Y).inv := by
  rw [← σ_naturality_assoc, Iso.hom_inv_id, Category.comp_id]

/-- The action of `Q⁻¹` on morphisms is conjugation by `σ̄`. -/
theorem Qinv_map_eq {X Y : C} (f : X ⟶ Y) :
    𝐐⁻.map f = (σbar (R := R) X).hom ≫ f ≫ (σbar (R := R) Y).inv := by
  rw [← σbar_naturality_assoc, Iso.hom_inv_id, Category.comp_id]

/-! ## `Π`, `Q` and `Q⁻¹` are graded superfunctors -/

instance pi_isGraded : IsGradedSuperfunctor R 𝚷 where
  map_mem_degree {X Y n f} hf := by
    rw [PiSupercategory.pi_map_eq]
    have := comp_mem_degree (comp_mem_degree (ζ_hom_mem_degree (R := R) X)
      (twist_mem_degree 1 hf)) (ζ_inv_mem_degree (R := R) Y)
    simpa using this

instance Q_isGraded : IsGradedSuperfunctor R 𝐐 where
  map_mem_degree {X Y n f} hf := by
    rw [Q_map_eq]
    have := comp_mem_degree (comp_mem_degree (σ_hom_mem_degree (R := R) X) hf)
      (σ_inv_mem_degree (R := R) Y)
    rwa [show -1 + n + 1 = n by ring, Category.assoc] at this

instance Qinv_isGraded : IsGradedSuperfunctor R 𝐐⁻ where
  map_mem_degree {X Y n f} hf := by
    rw [Qinv_map_eq]
    have := comp_mem_degree (comp_mem_degree (σbar_hom_mem_degree (R := R) X) hf)
      (σbar_inv_mem_degree (R := R) Y)
    rwa [show 1 + n + -1 = n by ring, Category.assoc] at this

/-! ## Corollary 6.7(i) -/

theorem ξ_hom_mem_degree (X : C) :
    (PiSupercategory.ξ (R := R) X).hom ∈ degree (R := R) (𝚷.obj (𝚷.obj X)) X 0 := by
  rw [PiSupercategory.ξ_hom]
  simpa using comp_mem_degree (map_mem_degree 𝚷 (ζ_hom_mem_degree (R := R) X))
    (ζ_hom_mem_degree (R := R) X)

/-- **Corollary 6.7(i).** `ii := σ̄σ : Q⁻¹Q ≅ I`, with component
`σ̄_{Q X} ≫ σ_X` (`= Q⁻¹(σ_X) ≫ σ̄_X`, `ii_hom_eq`). -/
def ii (X : C) : 𝐐⁻.obj (𝐐.obj X) ≅ X := σbar (R := R) (𝐐.obj X) ≪≫ σ (R := R) X

/-- **Corollary 6.7(i).** `jj := σσ̄ : QQ⁻¹ ≅ I`, with component
`σ_{Q⁻¹ X} ≫ σ̄_X` (`= Q(σ̄_X) ≫ σ_X`, `jj_hom_eq`). -/
def jj (X : C) : 𝐐.obj (𝐐⁻.obj X) ≅ X := σ (R := R) (𝐐⁻.obj X) ≪≫ σbar (R := R) X

theorem ii_hom (X : C) :
    (ii (R := R) X).hom = (σbar (R := R) (𝐐.obj X)).hom ≫ (σ (R := R) X).hom := rfl

theorem jj_hom (X : C) :
    (jj (R := R) X).hom = (σ (R := R) (𝐐⁻.obj X)).hom ≫ (σbar (R := R) X).hom := rfl

theorem ii_hom_eq (X : C) :
    (ii (R := R) X).hom = 𝐐⁻.map (σ (R := R) X).hom ≫ (σbar (R := R) X).hom :=
  (σbar_naturality _).symm

theorem jj_hom_eq (X : C) :
    (jj (R := R) X).hom = 𝐐.map (σbar (R := R) X).hom ≫ (σ (R := R) X).hom :=
  (σ_naturality _).symm

theorem ii_hom_mem (X : C) : (ii (R := R) X).hom ∈ parity (R := R) _ X 0 := by
  simpa using comp_mem (σbar_hom_mem (R := R) (𝐐.obj X)) (σ_hom_mem (R := R) X)

theorem ii_hom_mem_degree (X : C) : (ii (R := R) X).hom ∈ degree (R := R) _ X 0 := by
  simpa using comp_mem_degree (σbar_hom_mem_degree (R := R) (𝐐.obj X))
    (σ_hom_mem_degree (R := R) X)

theorem jj_hom_mem (X : C) : (jj (R := R) X).hom ∈ parity (R := R) _ X 0 := by
  simpa using comp_mem (σ_hom_mem (R := R) (𝐐⁻.obj X)) (σbar_hom_mem (R := R) X)

theorem jj_hom_mem_degree (X : C) : (jj (R := R) X).hom ∈ degree (R := R) _ X 0 := by
  simpa using comp_mem_degree (σ_hom_mem_degree (R := R) (𝐐⁻.obj X))
    (σbar_hom_mem_degree (R := R) X)

@[reassoc]
theorem ii_naturality {X Y : C} (f : X ⟶ Y) :
    𝐐⁻.map (𝐐.map f) ≫ (ii (R := R) Y).hom = (ii (R := R) X).hom ≫ f := by
  rw [ii_hom, ii_hom, σbar_naturality_assoc, σ_naturality, Category.assoc]

@[reassoc]
theorem jj_naturality {X Y : C} (f : X ⟶ Y) :
    𝐐.map (𝐐⁻.map f) ≫ (jj (R := R) Y).hom = (jj (R := R) X).hom ≫ f := by
  rw [jj_hom, jj_hom, σ_naturality_assoc, σbar_naturality, Category.assoc]

/-- **Corollary 6.7(i).** `Q ii = jj Q`. -/
theorem Q_map_ii (X : C) : 𝐐.map (ii (R := R) X).hom = (jj (R := R) (𝐐.obj X)).hom := by
  rw [Q_map_eq, ii_hom, jj_hom]
  simp

/-- **Corollary 6.7(i).** `ii Q⁻¹ = Q⁻¹ jj`. -/
theorem ii_Qinv (X : C) : (ii (R := R) (𝐐⁻.obj X)).hom = 𝐐⁻.map (jj (R := R) X).hom := by
  rw [Qinv_map_eq, ii_hom, jj_hom]
  simp

/-- **Corollary 6.7(i).** `ii⁻¹` and `jj` are the unit and counit of an adjoint equivalence
`(Q, Q⁻¹)`: the triangle identities are `Q ii = jj Q` and `ii Q⁻¹ = Q⁻¹ jj`. -/
def qEquivalence : C ≌ C where
  functor := 𝐐
  inverse := 𝐐⁻
  unitIso := NatIso.ofComponents (fun X => (ii (R := R) X).symm) fun f => by
    simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Iso.symm_hom,
      Functor.comp_map]
    rw [← cancel_mono (ii (R := R) _).hom, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Category.assoc, ii_naturality, Iso.inv_hom_id_assoc]
  counitIso := NatIso.ofComponents (fun X => jj (R := R) X) fun f => jj_naturality f
  functor_unitIso_comp X := by
    simp only [Functor.id_obj, NatIso.ofComponents_hom_app, Iso.symm_hom]
    rw [← Q_map_ii, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]

@[simp] theorem qEquivalence_functor : (qEquivalence (R := R) (C := C)).functor = 𝐐 := rfl

@[simp] theorem qEquivalence_inverse : (qEquivalence (R := R) (C := C)).inverse = 𝐐⁻ := rfl

/-- The adjunction `Q ⊣ Q⁻¹` with unit `ii⁻¹` and counit `jj` (Corollary 6.7(i)). -/
def qAdjunction : 𝐐 ⊣ 𝐐⁻ := (qEquivalence (R := R) (C := C)).toAdjunction

/-! ## Corollary 6.7(ii)–(iv) -/

variable {D : Type w₃} [Category.{w₄} D] [Preadditive D] [Linear R D] [Supercategory R D]
  [GradedSupercategory R D] [QPiSupercategory R D]
  {E : Type w₅} [Category.{w₆} E] [Preadditive E] [Linear R E] [Supercategory R E]
  [GradedSupercategory R E] [QPiSupercategory R E]

/-- **Corollary 6.7(ii).** `β_F` is even of degree zero. -/
theorem β_hom_mem_degree (F : C ⥤ D) [F.Additive] [F.Linear R] [IsGradedSuperfunctor R F]
    (X : C) :
    (PiSupercategory.β R F X).hom ∈ degree (R := R) _ _ 0 := by
  rw [PiSupercategory.β_hom]
  simpa using comp_mem_degree (ζ_hom_mem_degree (R := R) (F.obj X))
    (map_mem_degree F (ζ_inv_mem_degree (R := R) X))

variable (R) in
/-- **Corollary 6.7(ii).** `γ_F := σ' F σ⁻¹ : Q' F ≅ F Q`, with component `σ'_{F X} ≫ F(σ_X⁻¹)`
(the horizontal composite of even transformations, computed as for `β`). -/
def γ (F : C ⥤ D) (X : C) : (Q (R := R)).obj (F.obj X) ≅ F.obj ((Q (R := R)).obj X) :=
  σ (R := R) (F.obj X) ≪≫ F.mapIso (σ (R := R) X).symm

theorem γ_hom (F : C ⥤ D) (X : C) :
    (γ R F X).hom = (σ (R := R) (F.obj X)).hom ≫ F.map (σ (R := R) X).inv := rfl

theorem γ_inv (F : C ⥤ D) (X : C) :
    (γ R F X).inv = F.map (σ (R := R) X).hom ≫ (σ (R := R) (F.obj X)).inv := rfl

/-- The literal formula `γ_F = σ' F σ⁻¹`: its component is `Q'(F(σ_X⁻¹)) ≫ σ'_{F Q X}`. -/
theorem γ_hom_eq (F : C ⥤ D) (X : C) :
    (γ R F X).hom = (Q (R := R)).map (F.map (σ (R := R) X).inv) ≫
      (σ (R := R) (F.obj ((Q (R := R)).obj X))).hom := by
  rw [σ_naturality, γ_hom]

theorem γ_hom_mem (F : C ⥤ D) [F.Additive] [F.Linear R] [IsSuperfunctor R F] (X : C) :
    (γ R F X).hom ∈ parity (R := R) _ _ 0 := by
  simpa using comp_mem (σ_hom_mem (R := R) (F.obj X)) (map_mem F (σ_inv_mem (R := R) X))

theorem γ_hom_mem_degree (F : C ⥤ D) [F.Additive] [F.Linear R] [IsGradedSuperfunctor R F]
    (X : C) : (γ R F X).hom ∈ degree (R := R) _ _ 0 := by
  simpa using comp_mem_degree (σ_hom_mem_degree (R := R) (F.obj X))
    (map_mem_degree F (σ_inv_mem_degree (R := R) X))

/-- **Corollary 6.7(ii).** `γ_F` is natural. -/
@[reassoc]
theorem γ_naturality (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) :
    (Q (R := R)).map (F.map f) ≫ (γ R F Y).hom = (γ R F X).hom ≫ F.map ((Q (R := R)).map f) := by
  rw [γ_hom, γ_hom, σ_naturality_assoc, Category.assoc, Q_map_eq (R := R) f, ← F.map_comp,
    ← F.map_comp, Iso.inv_hom_id_assoc]

/-- The natural isomorphism `γ_F : F ⋙ Q' ≅ Q ⋙ F`. -/
def γIso (F : C ⥤ D) : F ⋙ Q (R := R) ≅ Q (R := R) ⋙ F :=
  NatIso.ofComponents (fun X => γ R F X) fun f => γ_naturality F f

/-- **Corollary 6.7(ii).** `γ_Π = β_Q⁻¹`. -/
theorem γ_pi (X : C) :
    (γ R (PiSupercategory.pi (R := R)) X).hom = (PiSupercategory.β R 𝐐 X).inv := by
  rw [← cancel_mono (PiSupercategory.β R 𝐐 X).hom, Iso.inv_hom_id, γ_hom,
    PiSupercategory.β_hom, Category.assoc, PiSupercategory.ζ_naturality_assoc,
    twist_one_of_mem (σ_inv_mem (R := R) X), sign_zero, one_smul, Q_map_eq]
  simp

/-- **Corollary 6.7(iii)** (with the misprint corrected, see the module documentation): for a
supernatural transformation `x : F ⇒ G` of parity `p`, `γ_G ∘ Q' x = x Q ∘ γ_F`. -/
theorem γ_naturality_supernatural (F G : C ⥤ D) [F.Additive] [G.Additive] [G.Linear R]
    {p : ZMod 2} {x : ∀ X, F.obj X ⟶ G.obj X} (hx : IsSupernatural R p x) (X : C) :
    (Q (R := R)).map (x X) ≫ (γ R G X).hom = (γ R F X).hom ≫ x ((Q (R := R)).obj X) := by
  rw [γ_hom, γ_hom, σ_naturality_assoc, Category.assoc, hx.naturality (σ_inv_mem (R := R) X),
    mul_zero, sign_zero, one_smul]

/-- **Corollary 6.7(iv).** `γ_{GF} = G γ_F ∘ γ_G F`. -/
theorem γ_comp (F : C ⥤ D) (G : D ⥤ E) (X : C) :
    (γ R (F ⋙ G) X).hom = (γ R G (F.obj X)).hom ≫ G.map (γ R F X).hom := by
  simp [γ_hom]

/-- **Corollary 6.7(iv).** `γ_I = 1`. -/
theorem γ_id (X : C) : (γ R (𝟭 C) X).hom = 𝟙 _ := by
  simp [γ_hom]

/-- **Corollary 6.7(iv).** `γ_Q = 1`. -/
theorem γ_Q (X : C) : (γ R 𝐐 X).hom = 𝟙 _ := by
  rw [γ_hom, Q_map_eq]
  simp

/-! ## Powers of `Q` -/

variable (R) in
/-- `Qⁿ X` for `n : ℕ`. -/
def qPowNat : ℕ → C → C
  | 0, X => X
  | n + 1, X => 𝐐.obj (qPowNat n X)

variable (R) in
/-- `Q⁻ⁿ X` for `n : ℕ`. -/
def qinvPowNat : ℕ → C → C
  | 0, X => X
  | n + 1, X => 𝐐⁻.obj (qinvPowNat n X)

variable (R) in
/-- `σⁿ : Qⁿ X ≅ X`, even of degree `-n`. -/
def σPowNat : ∀ (n : ℕ) (X : C), qPowNat R n X ≅ X
  | 0, X => Iso.refl X
  | n + 1, X => σ (R := R) (qPowNat R n X) ≪≫ σPowNat n X

variable (R) in
/-- `σ̄ⁿ : Q⁻ⁿ X ≅ X`, even of degree `n`. -/
def σbarPowNat : ∀ (n : ℕ) (X : C), qinvPowNat R n X ≅ X
  | 0, X => Iso.refl X
  | n + 1, X => σbar (R := R) (qinvPowNat R n X) ≪≫ σbarPowNat n X

variable (R) in
/-- `Q^m X` for `m : ℤ` (Brundan–Ellis, proof of Lemma 6.11). -/
def qPow : ℤ → C → C
  | Int.ofNat n => qPowNat R n
  | Int.negSucc n => qinvPowNat R (n + 1)

variable (R) in
/-- `σ^m : Q^m X ≅ X`: `σⁿ` if `m = n ≥ 0`, `σ̄⁻ᵐ` if `m < 0`; even of degree `-m`. -/
def σPow : ∀ (m : ℤ) (X : C), qPow R m X ≅ X
  | Int.ofNat n => σPowNat R n
  | Int.negSucc n => σbarPowNat R (n + 1)

theorem σPowNat_hom_mem (n : ℕ) (X : C) :
    (σPowNat R n X).hom ∈ parity (R := R) _ X 0 := by
  induction n with
  | zero => exact id_mem X
  | succ n ih => simpa using comp_mem (σ_hom_mem (R := R) _) ih

theorem σPowNat_hom_mem_degree (n : ℕ) (X : C) :
    (σPowNat R n X).hom ∈ degree (R := R) _ X (-n) := by
  induction n with
  | zero => exact id_mem_degree X
  | succ n ih =>
    have := comp_mem_degree (σ_hom_mem_degree (R := R) (qPowNat R n X)) ih
    rwa [show (-1 + -(n : ℤ)) = -((n + 1 : ℕ) : ℤ) by push_cast; ring] at this

theorem σbarPowNat_hom_mem (n : ℕ) (X : C) :
    (σbarPowNat R n X).hom ∈ parity (R := R) _ X 0 := by
  induction n with
  | zero => exact id_mem X
  | succ n ih => simpa using comp_mem (σbar_hom_mem (R := R) _) ih

theorem σbarPowNat_hom_mem_degree (n : ℕ) (X : C) :
    (σbarPowNat R n X).hom ∈ degree (R := R) _ X n := by
  induction n with
  | zero => exact id_mem_degree X
  | succ n ih =>
    have := comp_mem_degree (σbar_hom_mem_degree (R := R) (qinvPowNat R n X)) ih
    rwa [show (1 + (n : ℤ)) = ((n + 1 : ℕ) : ℤ) by push_cast; ring] at this

theorem σPow_hom_mem (m : ℤ) (X : C) : (σPow R m X).hom ∈ parity (R := R) _ X 0 := by
  cases m with
  | ofNat n => exact σPowNat_hom_mem n X
  | negSucc n => exact σbarPowNat_hom_mem (n + 1) X

theorem σPow_inv_mem (m : ℤ) (X : C) : (σPow R m X).inv ∈ parity (R := R) X _ 0 :=
  inv_mem _ (σPow_hom_mem m X)

theorem σPow_hom_mem_degree (m : ℤ) (X : C) : (σPow R m X).hom ∈ degree (R := R) _ X (-m) := by
  cases m with
  | ofNat n => exact σPowNat_hom_mem_degree n X
  | negSucc n =>
    have := σbarPowNat_hom_mem_degree (R := R) (n + 1) X
    rwa [show ((n + 1 : ℕ) : ℤ) = -Int.negSucc n by rw [Int.neg_negSucc]] at this

theorem σPow_inv_mem_degree (m : ℤ) (X : C) : (σPow R m X).inv ∈ degree (R := R) X _ m := by
  simpa using inv_mem_degree _ (σPow_hom_mem_degree (R := R) m X)

@[simp] theorem qPow_zero (X : C) : qPow R 0 X = X := rfl

@[simp] theorem σPow_zero (X : C) : σPow R 0 X = Iso.refl X := rfl

end QPiSupercategory

end StringDiagrams

end
