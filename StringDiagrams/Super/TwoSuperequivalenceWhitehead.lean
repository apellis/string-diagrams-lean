import StringDiagrams.Super.TwoHom
import StringDiagrams.Super.MonoidalSuperequivalenceInverse
import StringDiagrams.Biadjunction.ConjPseudofunctor

/-!
# Local 2-superequivalences are 2-superequivalences

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Definition 2.2: the two formulations of a 2-superequivalence agree. The implication from the
first to the second is `TwoSuperfunctor.IsTwoSuperequivalence.isLocalTwoSuperequivalence`
(`StringDiagrams.Super.TwoHom`); this file proves the converse, the super version of the
bicategorical Whitehead theorem (cf. Johnson–Yau, *2-Dimensional Categories*, Theorem 7.4.1):

* `TwoSuperfunctor.IsLocalTwoSuperequivalence.isTwoSuperequivalence`: a 2-superfunctor
  `ℝ : 𝔄 → 𝔅` which is a superequivalence on morphism supercategories and essentially
  surjective up to superequivalence is a 2-superequivalence;
* `TwoSuperfunctor.isTwoSuperequivalence_iff_isLocalTwoSuperequivalence`,
  `TwoSuperfunctor.twoSuperequivalent_iff_localTwoSuperequivalent`.

## Construction

For each object `ν` of `𝔅` choose `𝕊ν` and a superequivalence `e_ν : ℝ(𝕊ν) → ν`, upgraded to
an adjoint equivalence of the underlying bicategory (even unit and counit, triangle
identities). On 1-morphisms `𝕊k` is a lift of `e_ν ≫ k ≫ e'_ν'` along the superequivalence
`ℋom(𝕊ν, 𝕊ν') → ℋom(ℝ𝕊ν, ℝ𝕊ν')`, with an even isomorphism `ℓ_k : ℝ(𝕊k) ≅ e_ν ≫ k ≫ e'_ν'`,
and on 2-morphisms (of either parity) `𝕊η` is the preimage of `ℓ ∘ (e_ν ◁ η ▷ e'_ν') ∘ ℓ⁻¹`
(`IsLocalTwoSuperequivalence.inverse`). The coherence maps of `𝕊` are even, so they and
their coherence axioms are obtained in the underlying bicategory: conjugation by the adjoint
equivalences is a pseudofunctor (`ConjPseudofunctor.pseudofunctor`), its 1-morphisms are
replaced by the isomorphic `ℝ(𝕊k)` (`PseudofunctorCopy.copy`), and the result is lifted along
`ℝ` (`PseudofunctorLift.lift`). Naturality of the coherence maps with respect to odd
2-morphisms is proved directly (`nu_naturality`, `mu_naturality_left`, `mu_naturality_right`),
using that the coherence data is even and the super interchange law has no sign for even
2-morphisms.

The counit `ℝ ∘ 𝕊 ⇒ 𝕀` (components `e_ν`) and `𝕀 ⇒ ℝ ∘ 𝕊` (components `e'_ν`) come from the
corresponding oplax transformations of conjugation (`ConjPseudofunctor.counitTrans`,
`ConjPseudofunctor.unitTrans`) and are inverse up to even invertible supermodifications
(`counit_isSuperequivalence`). The transformation `𝕊 ∘ ℝ ⇒ 𝕀` has components lifts of
`e_{ℝλ}`: it and its quasi-inverse are the lifts along `ℝ` (`OplaxTransLift.lift`) of the
counit and unit whiskered by `ℝ`, and the invertible supermodifications are lifted likewise
(`OplaxTransLift.liftCompIso`, `invCounit_isSuperequivalence`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory

universe w₁ v₁ u₁ w₂ v₂ u₂ w

variable {R : Type w} [CommRing R]
  {B : Type u₁} [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]
  {C : Type u₂} [BicategoryStruct.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ a b : C, Supercategory R (a ⟶ b)] [TwoSupercategory R C]

/-! ## Superequivalences as adjoint equivalences of the underlying bicategory -/

namespace TwoSupercategory

open Bicategory in
/-- Superequivalent objects of a 2-supercategory are equivalent in the underlying bicategory
(of even 2-morphisms), by an adjoint equivalence. -/
theorem Superequivalent.nonempty_equivalence {a b : C} (h : Superequivalent R a b) :
    Nonempty ((⟨a⟩ : Underlying2 R C) ≌ ⟨b⟩) := by
  obtain ⟨f, g, e₁, e₂, h₁, h₂⟩ := h
  exact ⟨Equivalence.mkOfAdjointifyCounit (f := Underlying2.hom1 f) (g := Underlying2.hom1 g)
    (Underlying.isoMk e₁ h₁).symm (Underlying.isoMk e₂ h₂)⟩

end TwoSupercategory

namespace TwoSuperfunctor

/-- A 2-superfunctor as a pseudofunctor of the underlying bicategories, with
`mapComp f g := c⁻¹` and `mapId a := i⁻¹`. -/
def toPseudo (F : TwoSuperfunctor R B C) :
    Pseudofunctor (Underlying2 R B) (Underlying2 R C) :=
  Pseudofunctor.mkOfOplax F.toOplax
    { mapIdIso a :=
        { hom := F.toOplax.mapId a
          inv := ⟨(F.mapId a.obj).hom, F.mapId_hom_mem a.obj⟩
          hom_inv_id := Subtype.ext (F.mapId a.obj).inv_hom_id
          inv_hom_id := Subtype.ext (F.mapId a.obj).hom_inv_id }
      mapCompIso f g :=
        { hom := F.toOplax.mapComp f g
          inv := ⟨(F.mapComp f.obj g.obj).hom, F.mapComp_hom_mem f.obj g.obj⟩
          hom_inv_id := Subtype.ext (F.mapComp f.obj g.obj).inv_hom_id
          inv_hom_id := Subtype.ext (F.mapComp f.obj g.obj).hom_inv_id }
      mapIdIso_hom := rfl
      mapCompIso_hom _ _ := rfl }

variable (F : TwoSuperfunctor R B C)

@[simp] theorem toPseudo_obj (a : Underlying2 R B) : F.toPseudo.obj a = ⟨F.obj a.obj⟩ := rfl

@[simp] theorem toPseudo_map_obj {a b : Underlying2 R B} (f : a ⟶ b) :
    (F.toPseudo.map f).obj = F.map f.obj := rfl

@[simp] theorem toPseudo_map₂_val {a b : Underlying2 R B} {f g : a ⟶ b} (η : f ⟶ g) :
    (F.toPseudo.map₂ η).1 = F.map₂ η.1 := rfl

@[simp] theorem toPseudo_mapComp_hom_val {a b c : Underlying2 R B} (f : a ⟶ b) (g : b ⟶ c) :
    (F.toPseudo.mapComp f g).hom.1 = (F.mapComp f.obj g.obj).inv := rfl

@[simp] theorem toPseudo_mapComp_inv_val {a b c : Underlying2 R B} (f : a ⟶ b) (g : b ⟶ c) :
    (F.toPseudo.mapComp f g).inv.1 = (F.mapComp f.obj g.obj).hom := rfl

@[simp] theorem toPseudo_mapId_hom_val (a : Underlying2 R B) :
    (F.toPseudo.mapId a).hom.1 = (F.mapId a.obj).inv := rfl

@[simp] theorem toPseudo_mapId_inv_val (a : Underlying2 R B) :
    (F.toPseudo.mapId a).inv.1 = (F.mapId a.obj).hom := rfl

namespace IsLocalTwoSuperequivalence

variable {F} (hF : F.IsLocalTwoSuperequivalence)
include hF

/-! ## Local data: preimages of 2-morphisms and lifts of 1-morphisms -/

/-- The chosen superequivalence `ℋom(λ, μ) → ℋom(ℝλ, ℝμ)`. -/
def se (a b : B) : Superequivalence R (F.mapFunctor a b) := (hF.hom a b).some

/-- The preimage of a 2-morphism `ℝF ⇒ ℝG`. -/
def pre {a b : B} {f g : a ⟶ b} (x : F.map f ⟶ F.map g) : f ⟶ g :=
  (hF.se a b).fullyFaithful.preimage x

omit [TwoSupercategory R B] [TwoSupercategory R C] in
@[simp] theorem map₂_pre {a b : B} {f g : a ⟶ b} (x : F.map f ⟶ F.map g) :
    F.map₂ (hF.pre x) = x :=
  (hF.se a b).fullyFaithful.map_preimage x

omit [TwoSupercategory R B] [TwoSupercategory R C] in
theorem map₂_injective {a b : B} {f g : a ⟶ b} :
    Function.Injective (F.map₂ : (f ⟶ g) → (F.map f ⟶ F.map g)) :=
  fun _ _ h => (hF.se a b).fullyFaithful.map_injective h

omit [TwoSupercategory R B] [TwoSupercategory R C] in
theorem pre_mem {a b : B} {f g : a ⟶ b} {p : ZMod 2} {x : F.map f ⟶ F.map g}
    (hx : x ∈ parity (R := R) (F.map f) (F.map g) p) : hF.pre x ∈ parity (R := R) f g p := by
  have := (hF.se a b).fullyFaithful.faithful
  refine mem_of_map_mem (F.mapFunctor a b) ?_
  change F.map₂ (hF.pre x) ∈ _
  rw [map₂_pre]
  exact hx

/-- A lift of a 1-morphism `ℝλ → ℝμ` to a 1-morphism `λ → μ`. -/
def lift {a b : B} (k : F.obj a ⟶ F.obj b) : a ⟶ b := (hF.se a b).inverse.obj k

/-- The even isomorphism `ℝ(lift k) ≅ k`. -/
def liftIso {a b : B} (k : F.obj a ⟶ F.obj b) : F.map (hF.lift k) ≅ k :=
  (hF.se a b).counitIso.app k

omit [TwoSupercategory R B] [TwoSupercategory R C] in
theorem liftIso_hom_mem {a b : B} (k : F.obj a ⟶ F.obj b) :
    (hF.liftIso k).hom ∈ parity (R := R) _ _ 0 :=
  (hF.se a b).counitIso_mem k

/-- The object `𝕊ν` chosen by essential surjectivity. -/
def obj (c : C) : B := (hF.essSurj c).choose

open Bicategory in
/-- The chosen adjoint equivalence `ℝ(𝕊ν) ≌ ν` of the underlying bicategory. -/
def equiv (c : C) : (⟨F.obj (hF.obj c)⟩ : Underlying2 R C) ≌ ⟨c⟩ :=
  (hF.essSurj c).choose_spec.nonempty_equivalence.some

/-! ## The quasi-inverse on the underlying bicategories -/

section Underlying

open Bicategory

/-- The objects `ℝ(𝕊ν)`. -/
abbrev X (c : Underlying2 R C) : Underlying2 R C := ⟨F.obj (hF.obj c.obj)⟩

/-- The adjoint equivalences `ℝ(𝕊ν) ≌ ν`. -/
abbrev E (c : Underlying2 R C) : hF.X c ≌ c := hF.equiv c.obj

/-- Conjugation by the `E`: `k ↦ e_ν ≫ k ≫ e'_ν'`. -/
abbrev Q : Pseudofunctor (Underlying2 R C) (Underlying2 R C) := ConjPseudofunctor.pseudofunctor hF.E

/-- The lifts `𝕊k := lift (e_ν ≫ k ≫ e'_ν')`. -/
abbrev mapU {c d : Underlying2 R C} (k : c ⟶ d) :
    (⟨hF.obj c.obj⟩ : Underlying2 R B) ⟶ ⟨hF.obj d.obj⟩ :=
  ⟨hF.lift (hF.Q.map k).obj⟩

/-- `κ_k : ℝ(𝕊k) ≅ e_ν ≫ k ≫ e'_ν'`. -/
def κ {c d : Underlying2 R C} (k : c ⟶ d) : F.toPseudo.map (hF.mapU k) ≅ hF.Q.map k :=
  { hom := ⟨(hF.liftIso _).hom, hF.liftIso_hom_mem _⟩
    inv := ⟨(hF.liftIso _).inv, inv_mem _ (hF.liftIso_hom_mem _)⟩
    hom_inv_id := Subtype.ext (hF.liftIso _).hom_inv_id
    inv_hom_id := Subtype.ext (hF.liftIso _).inv_hom_id }

/-- The conjugation pseudofunctor with 1-morphisms replaced by `ℝ(𝕊k)`. -/
abbrev Qc : Pseudofunctor (Underlying2 R C) (Underlying2 R C) :=
  PseudofunctorCopy.copy hF.Q (fun k => F.toPseudo.map (hF.mapU k)) hF.κ

/-- Preimages of even 2-morphisms under `ℝ`. -/
def preU {a b : Underlying2 R B} {f g : a ⟶ b} (x : F.toPseudo.map f ⟶ F.toPseudo.map g) :
    f ⟶ g :=
  ⟨hF.pre x.1, hF.pre_mem x.2⟩

@[simp] theorem map₂_preU {a b : Underlying2 R B} {f g : a ⟶ b}
    (x : F.toPseudo.map f ⟶ F.toPseudo.map g) : F.toPseudo.map₂ (hF.preU x) = x :=
  Subtype.ext (hF.map₂_pre x.1)

omit [TwoSupercategory R B] [TwoSupercategory R C] in
@[simp] theorem pre_map₂ {a b : B} {f g : a ⟶ b} (x : f ⟶ g) : hF.pre (F.map₂ x) = x :=
  (hF.se a b).fullyFaithful.preimage_map x

@[simp] theorem preU_map₂ {a b : Underlying2 R B} {f g : a ⟶ b} (x : f ⟶ g) :
    hF.preU (F.toPseudo.map₂ x) = x :=
  Subtype.ext (hF.pre_map₂ x.1)

theorem map₂U_injective {a b : Underlying2 R B} {f g : a ⟶ b} :
    Function.Injective (F.toPseudo.map₂ : (f ⟶ g) → _) := fun _ _ h =>
  Subtype.ext (hF.map₂_injective (congrArg Subtype.val h))

/-- The quasi-inverse as a pseudofunctor of the underlying bicategories: the lift of `Qc`
along `ℝ`. -/
def pseudoInv : Pseudofunctor (Underlying2 R C) (Underlying2 R B) :=
  PseudofunctorLift.lift F.toPseudo hF.preU hF.map₂_preU hF.preU_map₂
    (fun c => ⟨hF.obj c.obj⟩) hF.mapU (fun η => hF.Qc.map₂ η) (fun c => hF.Qc.mapId c)
    (fun k l => hF.Qc.mapComp k l) (fun k => hF.Qc.map₂_id k)
    (fun η θ => hF.Qc.map₂_comp η θ) (fun k _ _ η => hF.Qc.map₂_whisker_left k η)
    (fun η l => hF.Qc.map₂_whisker_right η l) (fun k l m => hF.Qc.map₂_associator k l m)
    (fun k => hF.Qc.map₂_left_unitor k) (fun k => hF.Qc.map₂_right_unitor k)

theorem map₂_pseudoInv_mapComp_inv {c d f : Underlying2 R C} (k : c ⟶ d) (l : d ⟶ f) :
    F.toPseudo.map₂ (hF.pseudoInv.mapComp k l).inv =
      (F.toPseudo.mapComp (hF.mapU k) (hF.mapU l)).hom ≫ (hF.Qc.mapComp k l).inv :=
  by
    unfold pseudoInv
    apply PseudofunctorLift.map₂_lift_mapComp_inv
    exacts [fun k => hF.Qc.map₂_id k, fun η θ => hF.Qc.map₂_comp η θ,
      fun k _ _ η => hF.Qc.map₂_whisker_left k η, fun η l => hF.Qc.map₂_whisker_right η l,
      fun k l m => hF.Qc.map₂_associator k l m, fun k => hF.Qc.map₂_left_unitor k,
      fun k => hF.Qc.map₂_right_unitor k]

theorem map₂_pseudoInv_mapComp_hom {c d f : Underlying2 R C} (k : c ⟶ d) (l : d ⟶ f) :
    F.toPseudo.map₂ (hF.pseudoInv.mapComp k l).hom =
      (hF.Qc.mapComp k l).hom ≫ (F.toPseudo.mapComp (hF.mapU k) (hF.mapU l)).inv :=
  by
    unfold pseudoInv
    apply PseudofunctorLift.map₂_lift_mapComp_hom
    exacts [fun k => hF.Qc.map₂_id k, fun η θ => hF.Qc.map₂_comp η θ,
      fun k _ _ η => hF.Qc.map₂_whisker_left k η, fun η l => hF.Qc.map₂_whisker_right η l,
      fun k l m => hF.Qc.map₂_associator k l m, fun k => hF.Qc.map₂_left_unitor k,
      fun k => hF.Qc.map₂_right_unitor k]

theorem map₂_pseudoInv_mapId_hom (c : Underlying2 R C) :
    F.toPseudo.map₂ (hF.pseudoInv.mapId c).hom =
      (hF.Qc.mapId c).hom ≫ (F.toPseudo.mapId ⟨hF.obj c.obj⟩).inv :=
  by
    unfold pseudoInv
    apply PseudofunctorLift.map₂_lift_mapId_hom
    exacts [fun k => hF.Qc.map₂_id k, fun η θ => hF.Qc.map₂_comp η θ,
      fun k _ _ η => hF.Qc.map₂_whisker_left k η, fun η l => hF.Qc.map₂_whisker_right η l,
      fun k l m => hF.Qc.map₂_associator k l m, fun k => hF.Qc.map₂_left_unitor k,
      fun k => hF.Qc.map₂_right_unitor k]

end Underlying

/-! ## Naturality of the conjugation data for all 2-morphisms -/

section Super

open BicategoryStruct TwoSupercategory

/-- `e_ν : ℝ(𝕊ν) → ν`. -/
abbrev e (c : C) : F.obj (hF.obj c) ⟶ c := (hF.E ⟨c⟩).hom.obj

/-- `e'_ν : ν → ℝ(𝕊ν)`. -/
abbrev e' (c : C) : c ⟶ F.obj (hF.obj c) := (hF.E ⟨c⟩).inv.obj

/-- The (even) counit `e'_ν e_ν ⇒ 1`. -/
abbrev ε (c : C) : hF.e' c ≫ hF.e c ⟶ 𝟙 c := (hF.E ⟨c⟩).counit.hom.1

omit [TwoSupercategory R B] in
theorem ε_mem (c : C) : hF.ε c ∈ parity (R := R) _ _ 0 := (hF.E ⟨c⟩).counit.hom.2

/-- `(e_ν ≫ k ≫ e'_ν') ≫ e_ν' ⇒ e_ν ≫ k`, contracting by the counit. -/
def nu {c d : C} (k : c ⟶ d) : (hF.e c ≫ k ≫ hF.e' d) ≫ hF.e d ⟶ hF.e c ≫ k :=
  (BicategoryStruct.associator _ _ _).hom ≫ hF.e c ◁
    ((BicategoryStruct.associator _ _ _).hom ≫ k ◁ hF.ε d ≫
      (BicategoryStruct.rightUnitor k).hom)

omit [TwoSupercategory R B] in
theorem nu_eq {c d : C} (k : c ⟶ d) :
    hF.nu k = (ConjPseudofunctor.counitNat hF.E (Underlying2.hom1 (R := R) k)).hom.1 := rfl

omit [TwoSupercategory R B] in
@[reassoc]
theorem nu_naturality {c d : C} {k k' : c ⟶ d} (η : k ⟶ k') :
    (hF.e c ◁ (η ▷ hF.e' d)) ▷ hF.e d ≫ hF.nu k' = hF.nu k ≫ hF.e c ◁ η := by
  rw [nu, nu, associator_naturality_middle_assoc R, ← whiskerLeft_comp' R, Category.assoc,
    ← whiskerLeft_comp' R]
  congr 2
  rw [associator_naturality_left_assoc R,
    whisker_exchange_of_even_right_assoc η (hF.ε_mem d), rightUnitor_naturality R]
  simp only [Category.assoc]

omit [TwoSupercategory R B] in
theorem nu_mem {c d : C} (k : c ⟶ d) : hF.nu k ∈ parity (R := R) _ _ 0 :=
  (ConjPseudofunctor.counitNat hF.E (Underlying2.hom1 (R := R) k)).hom.2

/-- The composition constraint of conjugation,
`(e_ν ≫ k ≫ e'_ν') ≫ (e_ν' ≫ l ≫ e'_ν'') ⇒ e_ν ≫ (k ≫ l) ≫ e'_ν''`. -/
def mu {c d f : C} (k : c ⟶ d) (l : d ⟶ f) :
    (hF.e c ≫ k ≫ hF.e' d) ≫ (hF.e d ≫ l ≫ hF.e' f) ⟶ hF.e c ≫ (k ≫ l) ≫ hF.e' f :=
  (BicategoryStruct.associator _ _ _).inv ≫ hF.nu k ▷ (l ≫ hF.e' f) ≫
    (BicategoryStruct.associator _ _ _).hom ≫ hF.e c ◁ (BicategoryStruct.associator k l _).inv

omit [TwoSupercategory R B] in
theorem mu_eq {c d f : C} (k : c ⟶ d) (l : d ⟶ f) :
    hF.mu k l = (ConjPseudofunctor.comp hF.E (Underlying2.hom1 (R := R) k)
      (Underlying2.hom1 (R := R) l)).hom.1 := rfl

omit [TwoSupercategory R B] in
@[reassoc]
theorem mu_naturality_left {c d f : C} {k k' : c ⟶ d} (η : k ⟶ k') (l : d ⟶ f) :
    (hF.e c ◁ (η ▷ hF.e' d)) ▷ (hF.e d ≫ l ≫ hF.e' f) ≫ hF.mu k' l =
      hF.mu k l ≫ hF.e c ◁ ((η ▷ l) ▷ hF.e' f) := by
  rw [mu, mu, associator_inv_naturality_left_assoc R, ← comp_whiskerRight'_assoc R,
    nu_naturality, comp_whiskerRight'_assoc R, associator_naturality_middle_assoc R,
    ← whiskerLeft_comp' R, associator_inv_naturality_left R, whiskerLeft_comp' R]
  simp only [Category.assoc]

omit [TwoSupercategory R B] in
@[reassoc]
theorem mu_naturality_right {c d f : C} (k : c ⟶ d) {l l' : d ⟶ f} (η : l ⟶ l') :
    (hF.e c ≫ k ≫ hF.e' d) ◁ (hF.e d ◁ (η ▷ hF.e' f)) ≫ hF.mu k l' =
      hF.mu k l ≫ hF.e c ◁ ((k ◁ η) ▷ hF.e' f) := by
  rw [mu, mu, associator_inv_naturality_right_assoc R,
    ← whisker_exchange_of_even_left_assoc (hF.nu_mem k), associator_naturality_right_assoc R,
    ← whiskerLeft_comp' R, associator_inv_naturality_middle R, whiskerLeft_comp' R]
  simp only [Category.assoc]

/-- The inverse counit `1 ⇒ e'_ν e_ν`. -/
abbrev εinv (c : C) : 𝟙 c ⟶ hF.e' c ≫ hF.e c := (hF.E ⟨c⟩).counit.inv.1

omit [TwoSupercategory R B] in
theorem εinv_mem (c : C) : hF.εinv c ∈ parity (R := R) _ _ 0 := (hF.E ⟨c⟩).counit.inv.2

/-- `k ≫ e'_ν' ⇒ e'_ν ≫ (e_ν ≫ k ≫ e'_ν')`, inserting `e'_ν ≫ e_ν` by the inverse counit. -/
def unu {c d : C} (k : c ⟶ d) : k ≫ hF.e' d ⟶ hF.e' c ≫ (hF.e c ≫ k ≫ hF.e' d) :=
  (BicategoryStruct.leftUnitor _).inv ≫ hF.εinv c ▷ (k ≫ hF.e' d) ≫
    (BicategoryStruct.associator _ _ _).hom

omit [TwoSupercategory R B] in
theorem unu_eq {c d : C} (k : c ⟶ d) :
    hF.unu k = (ConjPseudofunctor.unitNat hF.E (Underlying2.hom1 (R := R) k)).hom.1 := rfl

omit [TwoSupercategory R B] in
@[reassoc]
theorem unu_naturality {c d : C} {k k' : c ⟶ d} (η : k ⟶ k') :
    η ▷ hF.e' d ≫ hF.unu k' = hF.unu k ≫ hF.e' c ◁ (hF.e c ◁ (η ▷ hF.e' d)) := by
  rw [unu, unu, leftUnitor_inv_naturality_assoc R,
    ← whisker_exchange_of_even_left_assoc (hF.εinv_mem c), associator_naturality_right R]
  simp only [Category.assoc]

end Super

/-! ## The quasi-inverse 2-superfunctor -/

section Inverse

open BicategoryStruct TwoSupercategory

omit [TwoSupercategory R B] [TwoSupercategory R C] hF in
theorem map₂_whiskerRight_eq {a b c : B} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    F.map₂ (η ▷ h) = (F.mapComp f h).inv ≫ F.map₂ η ▷ F.map h ≫ (F.mapComp g h).hom := by
  rw [F.mapComp_naturality_left, Iso.inv_hom_id_assoc]

omit [TwoSupercategory R B] [TwoSupercategory R C] hF in
theorem map₂_whiskerLeft_eq {a b c : B} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    F.map₂ (f ◁ η) = (F.mapComp f g).inv ≫ F.map f ◁ F.map₂ η ≫ (F.mapComp f h).hom := by
  rw [F.mapComp_naturality_right, Iso.inv_hom_id_assoc]

/-- The 1-morphism `𝕊k := lift (e_ν ≫ k ≫ e'_ν')`. -/
abbrev invMap {c d : C} (k : c ⟶ d) : hF.obj c ⟶ hF.obj d :=
  hF.lift (hF.e c ≫ k ≫ hF.e' d)

/-- `𝕊` on 2-morphisms: the preimage of `ℓ ∘ (e_ν ◁ η ▷ e'_ν') ∘ ℓ⁻¹`. -/
def invMap₂ {c d : C} {k k' : c ⟶ d} (η : k ⟶ k') : hF.invMap k ⟶ hF.invMap k' :=
  hF.pre ((hF.liftIso _).hom ≫ hF.e c ◁ (η ▷ hF.e' d) ≫ (hF.liftIso _).inv)

omit [TwoSupercategory R B] in
theorem map₂_invMap₂ {c d : C} {k k' : c ⟶ d} (η : k ⟶ k') :
    F.map₂ (hF.invMap₂ η) =
      (hF.liftIso _).hom ≫ hF.e c ◁ (η ▷ hF.e' d) ≫ (hF.liftIso _).inv :=
  hF.map₂_pre _

/-- The composition constraint of `𝕊`. -/
def invMapComp {c d f : C} (k : c ⟶ d) (l : d ⟶ f) :
    hF.invMap k ≫ hF.invMap l ≅ hF.invMap (k ≫ l) where
  hom := (hF.pseudoInv.mapComp (Underlying2.hom1 k) (Underlying2.hom1 l)).inv.1
  inv := (hF.pseudoInv.mapComp (Underlying2.hom1 k) (Underlying2.hom1 l)).hom.1
  hom_inv_id := congrArg Subtype.val
    (hF.pseudoInv.mapComp (Underlying2.hom1 k) (Underlying2.hom1 l)).inv_hom_id
  inv_hom_id := congrArg Subtype.val
    (hF.pseudoInv.mapComp (Underlying2.hom1 k) (Underlying2.hom1 l)).hom_inv_id

theorem invMapComp_hom_mem {c d f : C} (k : c ⟶ d) (l : d ⟶ f) :
    (hF.invMapComp k l).hom ∈ parity (R := R) _ _ 0 :=
  (hF.pseudoInv.mapComp (Underlying2.hom1 k) (Underlying2.hom1 l)).inv.2

theorem map₂_invMapComp_hom {c d f : C} (k : c ⟶ d) (l : d ⟶ f) :
    F.map₂ (hF.invMapComp k l).hom =
      (F.mapComp _ _).inv ≫ (hF.liftIso _).hom ▷ F.map (hF.invMap l) ≫
        (hF.e c ≫ k ≫ hF.e' d) ◁ (hF.liftIso _).hom ≫ hF.mu k l ≫ (hF.liftIso _).inv := by
  refine (congrArg Subtype.val (hF.map₂_pseudoInv_mapComp_inv (Underlying2.hom1 k)
    (Underlying2.hom1 l))).trans ?_
  exact congrArg ((F.mapComp _ _).inv ≫ ·) (congrArg Subtype.val
    (PseudofunctorCopy.copy_mapComp_inv hF.Q (fun k => F.toPseudo.map (hF.mapU k)) hF.κ
      (Underlying2.hom1 k) (Underlying2.hom1 l)))

/-- The unit constraint of `𝕊`. -/
def invMapId (c : C) : 𝟙 (hF.obj c) ≅ hF.invMap (𝟙 c) where
  hom := (hF.pseudoInv.mapId ⟨c⟩).inv.1
  inv := (hF.pseudoInv.mapId ⟨c⟩).hom.1
  hom_inv_id := congrArg Subtype.val (hF.pseudoInv.mapId ⟨c⟩).inv_hom_id
  inv_hom_id := congrArg Subtype.val (hF.pseudoInv.mapId ⟨c⟩).hom_inv_id

theorem invMapId_hom_mem (c : C) : (hF.invMapId c).hom ∈ parity (R := R) _ _ 0 :=
  (hF.pseudoInv.mapId ⟨c⟩).inv.2

/-- **The quasi-inverse of a local 2-superequivalence** `ℝ : 𝔄 → 𝔅`: on objects `ν ↦ 𝕊ν`
with a chosen superequivalence `e_ν : ℝ(𝕊ν) → ν`, on 1-morphisms `k ↦ 𝕊k` with
`ℝ(𝕊k) ≅ e_ν ≫ k ≫ e'_ν'`, on 2-morphisms the preimage of `e_ν ◁ η ▷ e'_ν'`, with
coherence maps those of `pseudoInv`. -/
def inverse : TwoSuperfunctor R C B where
  obj := hF.obj
  map k := hF.invMap k
  map₂ η := hF.invMap₂ η
  map₂_id k := hF.map₂_injective (by
    simp [map₂_invMap₂, id_whiskerRight (R := R), whiskerLeft_id (R := R)])
  map₂_comp η θ := hF.map₂_injective (by
    simp [map₂_invMap₂, F.map₂_comp, comp_whiskerRight (R := R), whiskerLeft_comp (R := R)])
  map₂_add η θ := hF.map₂_injective (by
    simp [map₂_invMap₂, add_whiskerRight (R := R), whiskerLeft_add (R := R),
      Preadditive.add_comp, Preadditive.comp_add])
  map₂_smul r η := hF.map₂_injective (by
    simp [map₂_invMap₂, smul_whiskerRight (R := R), whiskerLeft_smul (R := R)])
  map₂_mem {c d k k' p η} hη := hF.pre_mem (by
    simpa using comp_mem (hF.liftIso_hom_mem _)
      (comp_mem (whiskerLeft_mem (hF.e c) (whiskerRight_mem (hF.e' d) hη))
        (inv_mem _ (hF.liftIso_hom_mem _))))
  mapComp k l := hF.invMapComp k l
  mapId c := hF.invMapId c
  mapComp_hom_mem k l := hF.invMapComp_hom_mem k l
  mapId_hom_mem c := hF.invMapId_hom_mem c
  mapComp_naturality_left {c d f k k'} η l := hF.map₂_injective (by
    rw [F.map₂_comp, F.map₂_comp, map₂_whiskerRight_eq, map₂_invMapComp_hom,
      map₂_invMapComp_hom, map₂_invMap₂, map₂_invMap₂]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
      comp_whiskerRight' R, inv_hom_whiskerRight_assoc R]
    rw [whisker_exchange_of_even_right_assoc _ (hF.liftIso_hom_mem _),
      mu_naturality_left_assoc])
  mapComp_naturality_right {c d f} k l l' η := hF.map₂_injective (by
    rw [F.map₂_comp, F.map₂_comp, map₂_whiskerLeft_eq, map₂_invMapComp_hom,
      map₂_invMapComp_hom, map₂_invMap₂, map₂_invMap₂]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
    rw [← whisker_exchange_of_even_left_assoc (hF.liftIso_hom_mem _),
      ← whiskerLeft_comp'_assoc R]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [whiskerLeft_comp'_assoc R, mu_naturality_right_assoc])
  map₂_associator k l m := by
    have h := congrArg (· ≫ hF.pseudoInv.map₂ (Bicategory.associator (Underlying2.hom1 k)
      (Underlying2.hom1 l) (Underlying2.hom1 m)).inv)
      (hF.pseudoInv.mapComp_assoc_right_inv (Underlying2.hom1 k) (Underlying2.hom1 l)
        (Underlying2.hom1 m))
    simp only [Category.assoc, ← PrelaxFunctor.map₂_comp, Iso.hom_inv_id,
      PrelaxFunctor.map₂_id, Category.comp_id] at h
    exact congrArg Subtype.val h
  map₂_leftUnitor {c d} k := by
    have h : Bicategory.whiskerRight (hF.pseudoInv.mapId ⟨c⟩).inv
          (hF.pseudoInv.map (Underlying2.hom1 k)) ≫
        (hF.pseudoInv.mapComp (𝟙 _) (Underlying2.hom1 k)).inv ≫
          hF.pseudoInv.map₂ (Bicategory.leftUnitor (Underlying2.hom1 k)).hom =
        (Bicategory.leftUnitor (hF.pseudoInv.map (Underlying2.hom1 k))).hom := by
      rw [hF.pseudoInv.mapComp_id_left_inv]
      simp only [Category.assoc, ← PrelaxFunctor.map₂_comp, Iso.inv_hom_id,
        PrelaxFunctor.map₂_id, Category.comp_id, Bicategory.inv_hom_whiskerRight_assoc]
    exact congrArg Subtype.val h
  map₂_rightUnitor {c d} k := by
    have h : Bicategory.whiskerLeft (hF.pseudoInv.map (Underlying2.hom1 k))
          (hF.pseudoInv.mapId ⟨d⟩).inv ≫
        (hF.pseudoInv.mapComp (Underlying2.hom1 k) (𝟙 _)).inv ≫
          hF.pseudoInv.map₂ (Bicategory.rightUnitor (Underlying2.hom1 k)).hom =
        (Bicategory.rightUnitor (hF.pseudoInv.map (Underlying2.hom1 k))).hom := by
      rw [hF.pseudoInv.mapComp_id_right_inv]
      simp only [Category.assoc, ← PrelaxFunctor.map₂_comp, Iso.inv_hom_id,
        PrelaxFunctor.map₂_id, Category.comp_id, Bicategory.whiskerLeft_inv_hom_assoc]
    exact congrArg Subtype.val h

end Inverse

/-! ## The superequivalence `ℝ ∘ 𝕊 ≃ 𝕀` -/

section Counit

open Bicategory Oplax

theorem compOplax_map₂ {c d : Underlying2 R C} {k k' : c ⟶ d} (η : k ⟶ k') :
    (hF.inverse.comp F).toOplax.map₂ η = hF.Qc.map₂ η :=
  Subtype.ext (hF.map₂_invMap₂ η.1)

theorem compOplax_mapComp {c d f : Underlying2 R C} (k : c ⟶ d) (l : d ⟶ f) :
    (hF.inverse.comp F).toOplax.mapComp k l = (hF.Qc.mapComp k l).hom := by
  apply Subtype.ext
  change F.map₂ (hF.invMapComp k.obj l.obj).inv ≫ (F.mapComp _ _).inv = _
  rw [show F.map₂ (hF.invMapComp k.obj l.obj).inv =
      (hF.Qc.mapComp k l).hom.1 ≫ (F.mapComp _ _).hom from
    congrArg Subtype.val (hF.map₂_pseudoInv_mapComp_hom k l)]
  exact (Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (F.mapComp _ _).hom_inv_id).trans (Category.comp_id _))

theorem compOplax_mapId (c : Underlying2 R C) :
    (hF.inverse.comp F).toOplax.mapId c = (hF.Qc.mapId c).hom := by
  apply Subtype.ext
  change F.map₂ (hF.invMapId c.obj).inv ≫ (F.mapId _).inv = _
  rw [show F.map₂ (hF.invMapId c.obj).inv = (hF.Qc.mapId c).hom.1 ≫ (F.mapId _).hom from
    congrArg Subtype.val (hF.map₂_pseudoInv_mapId_hom c)]
  exact (Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (F.mapId _).hom_inv_id).trans (Category.comp_id _))

/-- The counit transformation of conjugation, transported to `Qc`. -/
abbrev counitQc : OplaxTrans hF.Qc.toOplax (Pseudofunctor.id (Underlying2 R C)).toOplax :=
  PseudofunctorCopy.transLeft hF.Q (fun k => F.toPseudo.map (hF.mapU k)) hF.κ
    (ConjPseudofunctor.counitTrans hF.E)

/-- The unit transformation of conjugation, transported to `Qc`. -/
abbrev unitQc : OplaxTrans (Pseudofunctor.id (Underlying2 R C)).toOplax hF.Qc.toOplax :=
  PseudofunctorCopy.transRight hF.Q (fun k => F.toPseudo.map (hF.mapU k)) hF.κ
    (ConjPseudofunctor.unitTrans hF.E)

/-- The oplax transformation `ℝ ∘ 𝕊 ⇒ 𝕀` of underlying bicategories, with components `e_ν`. -/
def counitOplax : OplaxTrans (hF.inverse.comp F).toOplax (TwoSuperfunctor.id R C).toOplax where
  app := hF.counitQc.app
  naturality k := hF.counitQc.naturality k
  naturality_naturality η := by
    rw [compOplax_map₂]; exact hF.counitQc.naturality_naturality η
  naturality_id c := by
    rw [compOplax_mapId]; exact hF.counitQc.naturality_id c
  naturality_comp k l := by
    rw [compOplax_mapComp]; exact hF.counitQc.naturality_comp k l

/-- The oplax transformation `𝕀 ⇒ ℝ ∘ 𝕊` of underlying bicategories, with components `e'_ν`. -/
def unitOplax : OplaxTrans (TwoSuperfunctor.id R C).toOplax (hF.inverse.comp F).toOplax where
  app := hF.unitQc.app
  naturality k := hF.unitQc.naturality k
  naturality_naturality η := by
    rw [compOplax_map₂]; exact hF.unitQc.naturality_naturality η
  naturality_id c := by
    rw [compOplax_mapId]; exact hF.unitQc.naturality_id c
  naturality_comp k l := by
    rw [compOplax_mapComp]; exact hF.unitQc.naturality_comp k l

end Counit

section CounitSuper

open BicategoryStruct TwoSupercategory

/-- The 2-natural transformation `ℝ ∘ 𝕊 ⇒ 𝕀`, with components `e_ν`. -/
def counit : TwoNatTrans (hF.inverse.comp F) (TwoSuperfunctor.id R C) :=
  TwoNatTrans.ofOplaxTrans hF.counitOplax (fun {c d f g} ε => by
    change F.map₂ (hF.invMap₂ ε) ▷ hF.e d ≫ ((hF.liftIso _).hom ▷ hF.e d ≫ hF.nu g) =
      ((hF.liftIso _).hom ▷ hF.e d ≫ hF.nu f) ≫ hF.e c ◁ ε
    rw [map₂_invMap₂, comp_whiskerRight' R, comp_whiskerRight' R]
    simp only [Category.assoc, inv_hom_whiskerRight_assoc R]
    rw [nu_naturality])

/-- The 2-natural transformation `𝕀 ⇒ ℝ ∘ 𝕊`, with components `e'_ν`. -/
def unit : TwoNatTrans (TwoSuperfunctor.id R C) (hF.inverse.comp F) :=
  TwoNatTrans.ofOplaxTrans hF.unitOplax (fun {c d f g} ε => by
    change ε ▷ hF.e' d ≫ (hF.unu g ≫ hF.e' c ◁ (hF.liftIso _).inv) =
      (hF.unu f ≫ hF.e' c ◁ (hF.liftIso _).inv) ≫ hF.e' c ◁ F.map₂ (hF.invMap₂ ε)
    rw [map₂_invMap₂, unu_naturality_assoc, Category.assoc, ← whiskerLeft_comp' R,
      ← whiskerLeft_comp' R, Iso.inv_hom_id_assoc])

end CounitSuper

section CounitEquiv

open Bicategory Oplax OplaxTrans

/-- `counit ≫ unit ≅ 𝟙` on the underlying oplax transformations, with components the inverse
units `e_ν ≫ e'_ν ≅ 𝟙`. -/
def counitUnitIso :
    (TwoNatTrans.vcomp hF.counit hF.unit).toOplaxTrans ≅
      (TwoNatTrans.id (hF.inverse.comp F)).toOplaxTrans :=
  let M := PseudofunctorCopy.modLeftRight hF.Q (fun k => F.toPseudo.map (hF.mapU k)) hF.κ
    (ConjPseudofunctor.counitTrans hF.E) (ConjPseudofunctor.unitTrans hF.E)
    (ConjPseudofunctor.counitTransCompUnitTrans hF.E)
  OplaxTrans.isoMk (fun a => PseudofunctorCopy.appIso M a) (fun f => M.hom.as.naturality f)

/-- `unit ≫ counit ≅ 𝟙` on the underlying oplax transformations, with components the counits
`e'_ν ≫ e_ν ≅ 𝟙`. -/
def unitCounitIso :
    (TwoNatTrans.vcomp hF.unit hF.counit).toOplaxTrans ≅
      (TwoNatTrans.id (TwoSuperfunctor.id R C)).toOplaxTrans :=
  let M := PseudofunctorCopy.modRightLeft hF.Q (fun k => F.toPseudo.map (hF.mapU k)) hF.κ
    (ConjPseudofunctor.counitTrans hF.E) (ConjPseudofunctor.unitTrans hF.E)
    (ConjPseudofunctor.unitTransCompCounitTrans hF.E)
  OplaxTrans.isoMk (fun a => PseudofunctorCopy.appIso M a) (fun f => M.hom.as.naturality f)

/-- The counit as a 1-morphism of `𝔥𝔬𝔪(𝔅, 𝔅)`. -/
abbrev counitHom : hF.inverse.comp F ⟶ TwoSuperfunctor.id R C := hF.counit

/-- The counit `ℝ ∘ 𝕊 ⇒ 𝕀` is a superequivalence in `𝔥𝔬𝔪(𝔅, 𝔅)`. -/
theorem counit_isSuperequivalence : TwoSupercategory.IsSuperequivalence R hF.counitHom :=
  ⟨hF.unit, TwoNatTrans.isoOfOplaxModificationIso hF.counitUnitIso,
    TwoNatTrans.isoOfOplaxModificationIso hF.unitCounitIso,
    fun a => (hF.counitUnitIso.hom.as.app ⟨a⟩).2,
    fun a => (hF.unitCounitIso.hom.as.app ⟨a⟩).2⟩

/-- `ℝ ∘ 𝕊` is superequivalent to the identity in `𝔥𝔬𝔪(𝔅, 𝔅)`. -/
theorem superequivalent_inverse_comp :
    TwoSupercategory.Superequivalent R (hF.inverse.comp F) (TwoSuperfunctor.id R C) :=
  ⟨hF.counitHom, hF.counit_isSuperequivalence⟩

end CounitEquiv

/-! ## The superequivalence `𝕊 ∘ ℝ ≃ 𝕀`

Its components are lifts `𝕊(ℝλ) → λ` of `e_{ℝλ}`, obtained by lifting the counit `ℝ𝕊 ⇒ 𝕀`
whiskered by `ℝ` along `ℝ` (`OplaxTransLift.lift`). -/

section UnitB

open Bicategory Oplax
open scoped Oplax.OplaxTrans

omit [TwoSupercategory R B] [TwoSupercategory R C] hF in
theorem natId_aux {𝒞 : Type*} [Bicategory 𝒞] {X Y : 𝒞} {σ : X ⟶ Y} {m m0 m1 : X ⟶ X}
    {m' m1' : Y ⟶ Y} (n : m ≫ σ ⟶ σ ≫ m') (n0 : m0 ≫ σ ⟶ σ ≫ 𝟙 Y) (i : m ⟶ m0)
    (i' : m' ⟶ 𝟙 Y) (j : m0 ⟶ 𝟙 X) (j' : 𝟙 Y ⟶ 𝟙 Y) (k : m ⟶ m1) (l : m1 ⟶ 𝟙 X)
    (k' : m' ⟶ m1') (l' : m1' ⟶ 𝟙 Y)
    (h1 : i ▷ σ ≫ n0 = n ≫ σ ◁ i') (h2 : n0 ≫ σ ◁ j' = j ▷ σ ≫ (λ_ σ).hom ≫ (ρ_ σ).inv)
    (h3 : k ≫ l = i ≫ j) (h4 : k' ≫ l' = i') (hj' : j' = 𝟙 _) :
    n ≫ σ ◁ (k' ≫ l') = (k ≫ l) ▷ σ ≫ (λ_ σ).hom ≫ (ρ_ σ).inv := by
  rw [h4, h3, comp_whiskerRight, Category.assoc, ← h2, hj', whiskerLeft_id, Category.comp_id,
    h1]

omit [TwoSupercategory R B] [TwoSupercategory R C] hF in
theorem natComp_aux {𝒞 : Type*} [Bicategory 𝒞] {A B' C' A' B'' C'' : 𝒞} {sa : A ⟶ A'}
    {sb : B' ⟶ B''} {sc : C' ⟶ C''} {pf : A ⟶ B'} {pg : B' ⟶ C'} {pfg p0 p1 : A ⟶ C'}
    {qf : A' ⟶ B''} {qg : B'' ⟶ C''} {qfg q1 : A' ⟶ C''}
    (nfg : pfg ≫ sc ⟶ sa ≫ qfg) (n0 : p0 ≫ sc ⟶ sa ≫ (qf ≫ qg)) (nf : pf ≫ sb ⟶ sa ≫ qf)
    (ng : pg ≫ sc ⟶ sb ≫ qg) (β : qfg ⟶ qf ≫ qg) (bβ : pfg ⟶ p0) (c : p0 ⟶ pf ≫ pg)
    (c' : qf ≫ qg ⟶ qf ≫ qg) (k : pfg ⟶ p1) (l : p1 ⟶ pf ≫ pg) (k' : qfg ⟶ q1)
    (l' : q1 ⟶ qf ≫ qg)
    (h1 : bβ ▷ sc ≫ n0 = nfg ≫ sa ◁ β)
    (h2 : n0 ≫ sa ◁ c' = c ▷ sc ≫ (α_ _ _ _).hom ≫ pf ◁ ng ≫ (α_ _ _ _).inv ≫ nf ▷ qg ≫
      (α_ _ _ _).hom)
    (h3 : k ≫ l = bβ ≫ c) (h4 : k' ≫ l' = β) (hc' : c' = 𝟙 _) :
    nfg ≫ sa ◁ (k' ≫ l') = (k ≫ l) ▷ sc ≫ (α_ _ _ _).hom ≫ pf ◁ ng ≫ (α_ _ _ _).inv ≫
      nf ▷ qg ≫ (α_ _ _ _).hom := by
  rw [h4, h3, comp_whiskerRight, Category.assoc, ← h2, hc', whiskerLeft_id, Category.comp_id]
  exact h1.symm

theorem comp_inverse_mapId_eq (a : B) :
    F.map₂ ((F.comp hF.inverse).mapId a).inv ≫ (F.mapId _).inv =
      F.map₂ (hF.inverse.map₂ (F.mapId a).inv) ≫ ((hF.inverse.comp F).mapId (F.obj a)).inv := by
  change F.map₂ (hF.inverse.map₂ (F.mapId a).inv ≫ (hF.inverse.mapId (F.obj a)).inv) ≫ _ =
    F.map₂ _ ≫ (F.map₂ (hF.inverse.mapId _).inv ≫ (F.mapId _).inv)
  rw [F.map₂_comp]
  exact Category.assoc _ _ _

theorem comp_inverse_mapComp_eq {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    F.map₂ ((F.comp hF.inverse).mapComp f g).inv ≫ (F.mapComp _ _).inv =
      F.map₂ (hF.inverse.map₂ (F.mapComp f g).inv) ≫
        ((hF.inverse.comp F).mapComp (F.map f) (F.map g)).inv := by
  change F.map₂ (hF.inverse.map₂ (F.mapComp f g).inv ≫
      (hF.inverse.mapComp (F.map f) (F.map g)).inv) ≫ _ =
    F.map₂ _ ≫ (F.map₂ (hF.inverse.mapComp _ _).inv ≫ (F.mapComp _ _).inv)
  rw [F.map₂_comp]
  exact Category.assoc _ _ _

theorem compOplax_mapId_eq (a : Underlying2 R B) :
    F.toPseudo.map₂ ((F.comp hF.inverse).toOplax.mapId a) ≫ (F.toPseudo.mapId _).hom =
      (hF.inverse.comp F).toOplax.map₂ (F.toPseudo.mapId a).hom ≫
        (hF.inverse.comp F).toOplax.mapId (F.toPseudo.obj a) :=
  Subtype.ext (hF.comp_inverse_mapId_eq a.obj)

theorem compOplax_mapComp_eq {a b c : Underlying2 R B} (f : a ⟶ b) (g : b ⟶ c) :
    F.toPseudo.map₂ ((F.comp hF.inverse).toOplax.mapComp f g) ≫
        (F.toPseudo.mapComp _ _).hom =
      (hF.inverse.comp F).toOplax.map₂ (F.toPseudo.mapComp f g).hom ≫
        (hF.inverse.comp F).toOplax.mapComp (F.toPseudo.map f) (F.toPseudo.map g) :=
  Subtype.ext (hF.comp_inverse_mapComp_eq f.obj g.obj)

/-- The counit whiskered by `ℝ`: components. -/
abbrev θapp (a : Underlying2 R B) :
    F.toPseudo.obj ((F.comp hF.inverse).toOplax.obj a) ⟶
      F.toPseudo.obj ((TwoSuperfunctor.id R B).toOplax.obj a) :=
  hF.counitOplax.app (F.toPseudo.obj a)

/-- The counit whiskered by `ℝ`: naturality 2-morphisms. -/
abbrev θnat {a b : Underlying2 R B} (f : a ⟶ b) :
    F.toPseudo.map ((F.comp hF.inverse).toOplax.map f) ≫ hF.θapp b ⟶
      hF.θapp a ≫ F.toPseudo.map ((TwoSuperfunctor.id R B).toOplax.map f) :=
  hF.counitOplax.naturality (F.toPseudo.map f)

theorem θnat_nat {a b : Underlying2 R B} {f g : a ⟶ b} (β : f ⟶ g) :
    F.toPseudo.map₂ ((F.comp hF.inverse).toOplax.map₂ β) ▷ hF.θapp b ≫ hF.θnat g =
      hF.θnat f ≫ hF.θapp a ◁ F.toPseudo.map₂ ((TwoSuperfunctor.id R B).toOplax.map₂ β) :=
  hF.counitOplax.naturality_naturality (F.toPseudo.map₂ β)

theorem θnat_id (a : Underlying2 R B) :
    hF.θnat (𝟙 a) ≫ hF.θapp a ◁ (F.toPseudo.map₂ ((TwoSuperfunctor.id R B).toOplax.mapId a) ≫
        (F.toPseudo.mapId _).hom) =
      (F.toPseudo.map₂ ((F.comp hF.inverse).toOplax.mapId a) ≫ (F.toPseudo.mapId _).hom) ▷
        hF.θapp a ≫ (λ_ _).hom ≫ (ρ_ _).inv :=
  natId_aux _ _ _ _ _ _ _ _ _ _
    (hF.counitOplax.naturality_naturality (F.toPseudo.mapId a).hom)
    (hF.counitOplax.naturality_id (F.toPseudo.obj a)) (hF.compOplax_mapId_eq a)
    (Subtype.ext (by
      change F.map₂ (𝟙 _) ≫ _ = _
      rw [F.map₂_id]
      exact Category.id_comp _))
    rfl

theorem θnat_comp {a b c : Underlying2 R B} (f : a ⟶ b) (g : b ⟶ c) :
    hF.θnat (f ≫ g) ≫ hF.θapp a ◁ (F.toPseudo.map₂ ((TwoSuperfunctor.id R B).toOplax.mapComp f g) ≫
        (F.toPseudo.mapComp _ _).hom) =
      (F.toPseudo.map₂ ((F.comp hF.inverse).toOplax.mapComp f g) ≫
          (F.toPseudo.mapComp _ _).hom) ▷ hF.θapp c ≫ (α_ _ _ _).hom ≫
        F.toPseudo.map ((F.comp hF.inverse).toOplax.map f) ◁ hF.θnat g ≫ (α_ _ _ _).inv ≫
          hF.θnat f ▷ F.toPseudo.map ((TwoSuperfunctor.id R B).toOplax.map g) ≫
            (α_ _ _ _).hom :=
  natComp_aux _ _ _ _ _ _ _ _ _ _ _ _
    (hF.counitOplax.naturality_naturality (F.toPseudo.mapComp f g).hom)
    (hF.counitOplax.naturality_comp (F.toPseudo.map f) (F.toPseudo.map g))
    (hF.compOplax_mapComp_eq f g)
    (Subtype.ext (by
      change F.map₂ (𝟙 _) ≫ _ = _
      rw [F.map₂_id]
      exact Category.id_comp _))
    rfl

omit [TwoSupercategory R B] [TwoSupercategory R C] hF in
theorem natId_aux' {𝒞 : Type*} [Bicategory 𝒞] {X Y : 𝒞} {σ : X ⟶ Y} {m' m1' : X ⟶ X}
    {m m0 m1 : Y ⟶ Y} (n : m' ≫ σ ⟶ σ ≫ m) (n0 : 𝟙 X ≫ σ ⟶ σ ≫ m0) (i' : m' ⟶ 𝟙 X)
    (i : m ⟶ m0) (j : m0 ⟶ 𝟙 Y) (j' : 𝟙 X ⟶ 𝟙 X) (k : m ⟶ m1) (l : m1 ⟶ 𝟙 Y)
    (k' : m' ⟶ m1') (l' : m1' ⟶ 𝟙 X)
    (h1 : i' ▷ σ ≫ n0 = n ≫ σ ◁ i) (h2 : n0 ≫ σ ◁ j = j' ▷ σ ≫ (λ_ σ).hom ≫ (ρ_ σ).inv)
    (h3 : k ≫ l = i ≫ j) (h4 : k' ≫ l' = i') (hj' : j' = 𝟙 _) :
    n ≫ σ ◁ (k ≫ l) = (k' ≫ l') ▷ σ ≫ (λ_ σ).hom ≫ (ρ_ σ).inv := by
  rw [h3, h4, whiskerLeft_comp, ← Category.assoc, ← h1, Category.assoc, h2, hj',
    id_whiskerRight, Category.id_comp]

omit [TwoSupercategory R B] [TwoSupercategory R C] hF in
theorem natComp_aux' {𝒞 : Type*} [Bicategory 𝒞] {A B' C' A' B'' C'' : 𝒞} {sa : A ⟶ A'}
    {sb : B' ⟶ B''} {sc : C' ⟶ C''} {pf : A ⟶ B'} {pg : B' ⟶ C'} {pfg p1 : A ⟶ C'}
    {qf : A' ⟶ B''} {qg : B'' ⟶ C''} {qfg q0 q1 : A' ⟶ C''}
    (nfg : pfg ≫ sc ⟶ sa ≫ qfg) (n0 : (pf ≫ pg) ≫ sc ⟶ sa ≫ q0) (nf : pf ≫ sb ⟶ sa ≫ qf)
    (ng : pg ≫ sc ⟶ sb ≫ qg) (β : pfg ⟶ pf ≫ pg) (bβ : qfg ⟶ q0) (c : q0 ⟶ qf ≫ qg)
    (c' : pf ≫ pg ⟶ pf ≫ pg) (k : qfg ⟶ q1) (l : q1 ⟶ qf ≫ qg) (k' : pfg ⟶ p1)
    (l' : p1 ⟶ pf ≫ pg)
    (h1 : β ▷ sc ≫ n0 = nfg ≫ sa ◁ bβ)
    (h2 : n0 ≫ sa ◁ c = c' ▷ sc ≫ (α_ _ _ _).hom ≫ pf ◁ ng ≫ (α_ _ _ _).inv ≫ nf ▷ qg ≫
      (α_ _ _ _).hom)
    (h3 : k ≫ l = bβ ≫ c) (h4 : k' ≫ l' = β) (hc' : c' = 𝟙 _) :
    nfg ≫ sa ◁ (k ≫ l) = (k' ≫ l') ▷ sc ≫ (α_ _ _ _).hom ≫ pf ◁ ng ≫ (α_ _ _ _).inv ≫
      nf ▷ qg ≫ (α_ _ _ _).hom := by
  rw [h3, h4, whiskerLeft_comp, ← Category.assoc, ← h1, Category.assoc, h2, hc',
    id_whiskerRight, Category.id_comp]

/-- The unit whiskered by `ℝ`: components. -/
abbrev θ'app (a : Underlying2 R B) :
    F.toPseudo.obj ((TwoSuperfunctor.id R B).toOplax.obj a) ⟶
      F.toPseudo.obj ((F.comp hF.inverse).toOplax.obj a) :=
  hF.unitOplax.app (F.toPseudo.obj a)

/-- The unit whiskered by `ℝ`: naturality 2-morphisms. -/
abbrev θ'nat {a b : Underlying2 R B} (f : a ⟶ b) :
    F.toPseudo.map ((TwoSuperfunctor.id R B).toOplax.map f) ≫ hF.θ'app b ⟶
      hF.θ'app a ≫ F.toPseudo.map ((F.comp hF.inverse).toOplax.map f) :=
  hF.unitOplax.naturality (F.toPseudo.map f)

theorem θ'nat_nat {a b : Underlying2 R B} {f g : a ⟶ b} (β : f ⟶ g) :
    F.toPseudo.map₂ ((TwoSuperfunctor.id R B).toOplax.map₂ β) ▷ hF.θ'app b ≫ hF.θ'nat g =
      hF.θ'nat f ≫ hF.θ'app a ◁ F.toPseudo.map₂ ((F.comp hF.inverse).toOplax.map₂ β) :=
  hF.unitOplax.naturality_naturality (F.toPseudo.map₂ β)

theorem θ'nat_id (a : Underlying2 R B) :
    hF.θ'nat (𝟙 a) ≫ hF.θ'app a ◁ (F.toPseudo.map₂ ((F.comp hF.inverse).toOplax.mapId a) ≫
        (F.toPseudo.mapId _).hom) =
      (F.toPseudo.map₂ ((TwoSuperfunctor.id R B).toOplax.mapId a) ≫ (F.toPseudo.mapId _).hom) ▷
        hF.θ'app a ≫ (λ_ _).hom ≫ (ρ_ _).inv :=
  natId_aux' _ _ _ _ _ _ _ _ _ _
    (hF.unitOplax.naturality_naturality (F.toPseudo.mapId a).hom)
    (hF.unitOplax.naturality_id (F.toPseudo.obj a)) (hF.compOplax_mapId_eq a)
    (Subtype.ext (by
      change F.map₂ (𝟙 _) ≫ _ = _
      rw [F.map₂_id]
      exact Category.id_comp _))
    rfl

theorem θ'nat_comp {a b c : Underlying2 R B} (f : a ⟶ b) (g : b ⟶ c) :
    hF.θ'nat (f ≫ g) ≫ hF.θ'app a ◁ (F.toPseudo.map₂ ((F.comp hF.inverse).toOplax.mapComp f g) ≫
        (F.toPseudo.mapComp _ _).hom) =
      (F.toPseudo.map₂ ((TwoSuperfunctor.id R B).toOplax.mapComp f g) ≫
          (F.toPseudo.mapComp _ _).hom) ▷ hF.θ'app c ≫ (α_ _ _ _).hom ≫
        F.toPseudo.map ((TwoSuperfunctor.id R B).toOplax.map f) ◁ hF.θ'nat g ≫ (α_ _ _ _).inv ≫
          hF.θ'nat f ▷ F.toPseudo.map ((F.comp hF.inverse).toOplax.map g) ≫
            (α_ _ _ _).hom :=
  natComp_aux' _ _ _ _ _ _ _ _ _ _ _ _
    (hF.unitOplax.naturality_naturality (F.toPseudo.mapComp f g).hom)
    (hF.unitOplax.naturality_comp (F.toPseudo.map f) (F.toPseudo.map g))
    (hF.compOplax_mapComp_eq f g)
    (Subtype.ext (by
      change F.map₂ (𝟙 _) ≫ _ = _
      rw [F.map₂_id]
      exact Category.id_comp _))
    rfl

/-- `ℝ(lift k) ≅ k` in the underlying bicategory. -/
def liftIsoU {a b : B} (k : F.obj a ⟶ F.obj b) :
    F.toPseudo.map (⟨hF.lift k⟩ : (⟨a⟩ : Underlying2 R B) ⟶ ⟨b⟩) ≅ ⟨k⟩ where
  hom := ⟨(hF.liftIso k).hom, hF.liftIso_hom_mem k⟩
  inv := ⟨(hF.liftIso k).inv, inv_mem _ (hF.liftIso_hom_mem k)⟩
  hom_inv_id := Subtype.ext (hF.liftIso k).hom_inv_id
  inv_hom_id := Subtype.ext (hF.liftIso k).inv_hom_id

/-- The oplax transformation `𝕊 ∘ ℝ ⇒ 𝕀` of underlying bicategories: components lifts of
`e_{ℝλ}`. -/
def θOplax : OplaxTrans (F.comp hF.inverse).toOplax (TwoSuperfunctor.id R B).toOplax :=
  OplaxTransLift.lift F.toPseudo hF.preU hF.map₂_preU hF.preU_map₂ hF.θapp (fun f => hF.θnat f)
    (fun a => ⟨hF.lift (hF.e (F.obj a.obj))⟩) (fun _ => hF.liftIsoU _)
    (fun β => hF.θnat_nat β) hF.θnat_id (fun f g => hF.θnat_comp f g)

/-- The oplax transformation `𝕀 ⇒ 𝕊 ∘ ℝ` of underlying bicategories: components lifts of
`e'_{ℝλ}`. -/
def θ'Oplax : OplaxTrans (TwoSuperfunctor.id R B).toOplax (F.comp hF.inverse).toOplax :=
  OplaxTransLift.lift F.toPseudo hF.preU hF.map₂_preU hF.preU_map₂ hF.θ'app
    (fun f => hF.θ'nat f) (fun a => ⟨hF.lift (hF.e' (F.obj a.obj))⟩) (fun _ => hF.liftIsoU _)
    (fun β => hF.θ'nat_nat β) hF.θ'nat_id (fun f g => hF.θ'nat_comp f g)

/-- `θ ≫ θ' ≅ 𝟙` on underlying oplax transformations. -/
def θθ'Iso : hF.θOplax ≫ hF.θ'Oplax ≅ 𝟙 (F.comp hF.inverse).toOplax :=
  let M := PseudofunctorCopy.modLeftRight hF.Q (fun k => F.toPseudo.map (hF.mapU k)) hF.κ
    (ConjPseudofunctor.counitTrans hF.E) (ConjPseudofunctor.unitTrans hF.E)
    (ConjPseudofunctor.counitTransCompUnitTrans hF.E)
  OplaxTransLift.liftCompIso F.toPseudo hF.preU hF.map₂_preU hF.preU_map₂ hF.θapp
    (fun f => hF.θnat f) (fun a => ⟨hF.lift (hF.e (F.obj a.obj))⟩) (fun _ => hF.liftIsoU _)
    hF.θ'app (fun f => hF.θ'nat f) (fun a => ⟨hF.lift (hF.e' (F.obj a.obj))⟩)
    (fun _ => hF.liftIsoU _) (fun a => PseudofunctorCopy.appIso M (F.toPseudo.obj a))
    (fun β => hF.θnat_nat β) hF.θnat_id (fun f g => hF.θnat_comp f g)
    (fun β => hF.θ'nat_nat β) hF.θ'nat_id (fun f g => hF.θ'nat_comp f g)
    (fun f => M.hom.as.naturality (F.toPseudo.map f))

/-- `θ' ≫ θ ≅ 𝟙` on underlying oplax transformations. -/
def θ'θIso : hF.θ'Oplax ≫ hF.θOplax ≅ 𝟙 (TwoSuperfunctor.id R B).toOplax :=
  let M := PseudofunctorCopy.modRightLeft hF.Q (fun k => F.toPseudo.map (hF.mapU k)) hF.κ
    (ConjPseudofunctor.counitTrans hF.E) (ConjPseudofunctor.unitTrans hF.E)
    (ConjPseudofunctor.unitTransCompCounitTrans hF.E)
  OplaxTransLift.liftCompIso F.toPseudo hF.preU hF.map₂_preU hF.preU_map₂ hF.θ'app
    (fun f => hF.θ'nat f) (fun a => ⟨hF.lift (hF.e' (F.obj a.obj))⟩) (fun _ => hF.liftIsoU _)
    hF.θapp (fun f => hF.θnat f) (fun a => ⟨hF.lift (hF.e (F.obj a.obj))⟩)
    (fun _ => hF.liftIsoU _) (fun a => PseudofunctorCopy.appIso M (F.toPseudo.obj a))
    (fun β => hF.θ'nat_nat β) hF.θ'nat_id (fun f g => hF.θ'nat_comp f g)
    (fun β => hF.θnat_nat β) hF.θnat_id (fun f g => hF.θnat_comp f g)
    (fun f => M.hom.as.naturality (F.toPseudo.map f))

end UnitB

section UnitBSuper

open BicategoryStruct TwoSupercategory
open scoped Oplax.OplaxTrans

theorem map₂_θOplax_nat {a b : B} (f : a ⟶ b) :
    F.map₂ (hF.θOplax.naturality (Underlying2.hom1 f)).1 =
      (F.mapComp _ _).inv ≫ F.map (hF.inverse.map (F.map f)) ◁ (hF.liftIso _).hom ≫
        hF.counit.x (F.map f) ≫ (hF.liftIso _).inv ▷ F.map f ≫ (F.mapComp _ _).hom :=
  hF.map₂_pre _

theorem map₂_θ'Oplax_nat {a b : B} (f : a ⟶ b) :
    F.map₂ (hF.θ'Oplax.naturality (Underlying2.hom1 f)).1 =
      (F.mapComp _ _).inv ≫ F.map f ◁ (hF.liftIso _).hom ≫
        hF.unit.x (F.map f) ≫ (hF.liftIso _).inv ▷ F.map (hF.inverse.map (F.map f)) ≫
          (F.mapComp _ _).hom :=
  hF.map₂_pre _

omit [TwoSupercategory R B] in
theorem nat_lift_aux {a' b' a b : B} {sf sg : a' ⟶ b'} {ta : a' ⟶ a} {tb : b' ⟶ b}
    {f g : a ⟶ b} {ea : F.obj a' ⟶ F.obj a} {eb : F.obj b' ⟶ F.obj b} (sε : sf ⟶ sg)
    (ε : f ⟶ g) (nf : sf ≫ tb ⟶ ta ≫ f) (ng : sg ≫ tb ⟶ ta ≫ g) (ℓa : F.map ta ≅ ea)
    (ℓb : F.map tb ≅ eb) (hℓa : ℓa.inv ∈ parity (R := R) _ _ 0)
    (hℓb : ℓb.hom ∈ parity (R := R) _ _ 0)
    (xf : F.map sf ≫ eb ⟶ ea ≫ F.map f) (xg : F.map sg ≫ eb ⟶ ea ≫ F.map g)
    (hf : F.map₂ nf = (F.mapComp _ _).inv ≫ F.map sf ◁ ℓb.hom ≫ xf ≫ ℓa.inv ▷ F.map f ≫
      (F.mapComp _ _).hom)
    (hg : F.map₂ ng = (F.mapComp _ _).inv ≫ F.map sg ◁ ℓb.hom ≫ xg ≫ ℓa.inv ▷ F.map g ≫
      (F.mapComp _ _).hom)
    (hn : F.map₂ sε ▷ eb ≫ xg = xf ≫ ea ◁ F.map₂ ε) :
    sε ▷ tb ≫ ng = nf ≫ ta ◁ ε := by
  apply hF.map₂_injective
  rw [F.map₂_comp, F.map₂_comp, map₂_whiskerRight_eq, map₂_whiskerLeft_eq, hf, hg]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [whisker_exchange_of_even_right_assoc _ hℓb, reassoc_of% hn,
    whisker_exchange_of_even_left_assoc hℓa]

/-- The 2-natural transformation `𝕊 ∘ ℝ ⇒ 𝕀`, with components lifts of `e_{ℝλ}`. -/
def invCounit : TwoNatTrans (F.comp hF.inverse) (TwoSuperfunctor.id R B) :=
  TwoNatTrans.ofOplaxTrans hF.θOplax (fun {_ _ f g} ε =>
    hF.nat_lift_aux ((F.comp hF.inverse).map₂ ε) ε _ _ (hF.liftIso _) (hF.liftIso _)
      (inv_mem _ (hF.liftIso_hom_mem _)) (hF.liftIso_hom_mem _) _ _
      (hF.map₂_θOplax_nat f) (hF.map₂_θOplax_nat g) (hF.counit.naturality (F.map₂ ε)))

/-- The 2-natural transformation `𝕀 ⇒ 𝕊 ∘ ℝ`, with components lifts of `e'_{ℝλ}`. -/
def invUnit : TwoNatTrans (TwoSuperfunctor.id R B) (F.comp hF.inverse) :=
  TwoNatTrans.ofOplaxTrans hF.θ'Oplax (fun {_ _ f g} ε =>
    hF.nat_lift_aux ε ((F.comp hF.inverse).map₂ ε) _ _ (hF.liftIso _) (hF.liftIso _)
      (inv_mem _ (hF.liftIso_hom_mem _)) (hF.liftIso_hom_mem _) _ _
      (hF.map₂_θ'Oplax_nat f) (hF.map₂_θ'Oplax_nat g) (hF.unit.naturality (F.map₂ ε)))

/-- `𝕊 ∘ ℝ ⇒ 𝕀` as a 1-morphism of `𝔥𝔬𝔪(𝔄, 𝔄)`. -/
abbrev invCounitHom : F.comp hF.inverse ⟶ TwoSuperfunctor.id R B := hF.invCounit

/-- The 2-natural transformation `𝕊 ∘ ℝ ⇒ 𝕀` is a superequivalence in `𝔥𝔬𝔪(𝔄, 𝔄)`. -/
theorem invCounit_isSuperequivalence : IsSuperequivalence R hF.invCounitHom :=
  ⟨hF.invUnit,
    TwoNatTrans.isoOfOplaxModificationIso (θ := TwoNatTrans.vcomp hF.invCounit hF.invUnit)
      (θ' := TwoNatTrans.id _) hF.θθ'Iso,
    TwoNatTrans.isoOfOplaxModificationIso (θ := TwoNatTrans.vcomp hF.invUnit hF.invCounit)
      (θ' := TwoNatTrans.id _) hF.θ'θIso,
    fun a => (hF.θθ'Iso.hom.as.app ⟨a⟩).2,
    fun a => (hF.θ'θIso.hom.as.app ⟨a⟩).2⟩

/-- `𝕊 ∘ ℝ` is superequivalent to the identity in `𝔥𝔬𝔪(𝔄, 𝔄)`. -/
theorem superequivalent_comp_inverse :
    Superequivalent R (F.comp hF.inverse) (TwoSuperfunctor.id R B) :=
  ⟨hF.invCounitHom, hF.invCounit_isSuperequivalence⟩

/-- **Brundan–Ellis, Definition 2.2**, the second formulation implies the first: a 2-superfunctor
which is a superequivalence on morphism supercategories and essentially surjective up to
superequivalence is a 2-superequivalence, with quasi-inverse `hF.inverse`. -/
theorem isTwoSuperequivalence : F.IsTwoSuperequivalence :=
  ⟨hF.inverse, hF.superequivalent_comp_inverse, hF.superequivalent_inverse_comp⟩

end UnitBSuper

end IsLocalTwoSuperequivalence

/-- **Brundan–Ellis, Definition 2.2**: the two formulations of a 2-superequivalence agree. -/
theorem isTwoSuperequivalence_iff_isLocalTwoSuperequivalence (F : TwoSuperfunctor R B C) :
    F.IsTwoSuperequivalence ↔ F.IsLocalTwoSuperequivalence :=
  ⟨IsTwoSuperequivalence.isLocalTwoSuperequivalence,
    IsLocalTwoSuperequivalence.isTwoSuperequivalence⟩

/-- 2-supercategories which are 2-superequivalent in the second formulation of Definition 2.2
are 2-superequivalent in the first. -/
theorem LocalTwoSuperequivalent.twoSuperequivalent (h : LocalTwoSuperequivalent R B C) :
    TwoSuperequivalent R B C := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F, hF.isTwoSuperequivalence⟩

variable (R B C) in
/-- **Brundan–Ellis, Definition 2.2**: the two notions of 2-superequivalent 2-supercategories
agree. -/
theorem twoSuperequivalent_iff_localTwoSuperequivalent :
    TwoSuperequivalent R B C ↔ LocalTwoSuperequivalent R B C :=
  ⟨TwoSuperequivalent.localTwoSuperequivalent, LocalTwoSuperequivalent.twoSuperequivalent⟩

end TwoSuperfunctor

end StringDiagrams

end
