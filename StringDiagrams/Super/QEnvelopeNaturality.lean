import StringDiagrams.Super.QEnvelopeAdjunction
import StringDiagrams.Super.EnvelopeNaturality

/-!
# Naturality of Theorem 6.9

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §6,
Theorem 6.9: "there is a functorial graded superequivalence `ℋom(A, νB) → ℋom(A_{q,π}, B)`".
The graded superequivalence is `QPiEnvelope.extendHomGradedSuperequivalence`
(`StringDiagrams.Super.QEnvelopeAdjunction`); here we prove its naturality in `A` and `B`.

* Pre- and postcomposition with graded superfunctors as functors between the graded
  supercategories `ℋom(A, B)` (`GradedHom.precompose`, `GradedHom.postcompose`).
* **Naturality in `A`, on the nose.** For a graded superfunctor `K : A' → A`,
  `(F ∘ K)~ = F̃ ∘ K_{q,π}` (`QPiEnvelope.extend_comp_left`), also on supernatural
  transformations (`QPiEnvelope.extendSuperNatTrans_whiskerLeft`), i.e. an equality of functors
  `ℋom(A, νB) → ℋom(A'_{q,π}, B)` (`QPiEnvelope.extendHom_precompose`).
* **Naturality in `B`, up to even isomorphism of degree zero.** For a graded superfunctor
  `L : B → B'` between graded `(Q, Π)`-supercategories, `(L ∘ F)~ ≅ L ∘ F̃`
  (`QPiEnvelope.extendCompIso`), with components `βᵃ_L ∘ Πᵃ(γᵐ_L)` on `Q^m Π^a λ`, where
  `γᵐ_L = L((σᵐ)⁻¹) ∘ σᵐ : Q^m(Lμ) ≅ L(Q^m μ)` (`QEnvelope.γPow`) and `βᵃ_L` is as in
  Corollary 3.3(ii) (`Envelope.βPow`); the identity on `J λ` (`QPiEnvelope.extendCompIso_hom_app_J`).
  These isomorphisms are natural in `F` with respect to all supernatural transformations
  (`QPiEnvelope.extendCompIso_naturality`), giving an even natural isomorphism of degree zero
  of functors `ℋom(A, νB) → ℋom(A_{q,π}, B')` (`QPiEnvelope.extendHomPostcomposeIso`).

This is the "functorial" of Theorem 6.9 at the level of the Hom-categories. The coherence of
the isomorphisms `extendHomPostcomposeIso` with composition in `L` (which would be needed to
state a pseudonatural equivalence of Hom-2-functors) is not recorded.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory GradedSupercategory

universe w w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈

variable {R : Type w} [CommRing R]

/-! ## Pre- and postcomposition on `ℋom(A, B)` -/

namespace GradedHom

open GradedSuperfunctor

variable {A : Type w₁} [Category.{w₂} A] [Preadditive A] [Linear R A] [Supercategory R A]
  [GradedSupercategory R A]
  {A' : Type w₃} [Category.{w₄} A'] [Preadditive A'] [Linear R A'] [Supercategory R A']
  [GradedSupercategory R A']
  {B : Type w₅} [Category.{w₆} B] [Preadditive B] [Linear R B] [Supercategory R B]
  [GradedSupercategory R B]
  {B' : Type w₇} [Category.{w₈} B'] [Preadditive B'] [Linear R B'] [Supercategory R B']
  [GradedSupercategory R B']

set_option backward.isDefEq.respectTransparency false in
variable (B) in
/-- Precomposition with a graded superfunctor `K : A' → A`, as a functor
`ℋom(A, B) → ℋom(A', B)`. -/
def precompose (K : GradedSuperfunctor R A' A) : GradedHom R A B ⥤ GradedHom R A' B where
  obj F := ⟨K.comp F.as⟩
  map x := ⟨Superfunctor.whiskerLeft K.toSuperfunctor x.1, whiskerLeft_mem_hom K x.2⟩
  map_id _ := GradedSubcategory.hom_ext (Superfunctor.whiskerLeft_id _ _)
  map_comp x y := GradedSubcategory.hom_ext (Superfunctor.whiskerLeft_comp _ x.1 y.1)

@[simp] theorem precompose_obj (K : GradedSuperfunctor R A' A) (F : GradedHom R A B) :
    (precompose B K).obj F = ⟨K.comp F.as⟩ := rfl

@[simp] theorem precompose_map_val (K : GradedSuperfunctor R A' A) {F G : GradedHom R A B}
    (x : F ⟶ G) : ((precompose B K).map x).1 = Superfunctor.whiskerLeft K.toSuperfunctor x.1 :=
  rfl

set_option backward.isDefEq.respectTransparency false in
variable (A) in
/-- Postcomposition with a graded superfunctor `L : B → B'`, as a functor
`ℋom(A, B) → ℋom(A, B')`. -/
def postcompose (L : GradedSuperfunctor R B B') : GradedHom R A B ⥤ GradedHom R A B' where
  obj F := ⟨F.as.comp L⟩
  map x := ⟨Superfunctor.whiskerRight x.1 L.toSuperfunctor, whiskerRight_mem_hom x.2 L⟩
  map_id _ := GradedSubcategory.hom_ext (Superfunctor.id_whiskerRight _ _)
  map_comp x y := GradedSubcategory.hom_ext (Superfunctor.comp_whiskerRight x.1 y.1 _)

@[simp] theorem postcompose_obj (L : GradedSuperfunctor R B B') (F : GradedHom R A B) :
    (postcompose A L).obj F = ⟨F.as.comp L⟩ := rfl

@[simp] theorem postcompose_map_val (L : GradedSuperfunctor R B B') {F G : GradedHom R A B}
    (x : F ⟶ G) : ((postcompose A L).map x).1 = Superfunctor.whiskerRight x.1 L.toSuperfunctor :=
  rfl

end GradedHom

/-! ## Naturality in `A` -/

namespace QPiEnvelope

open GradedSuperfunctor

variable {A : Type w₁} [Category.{w₂} A] [Preadditive A] [Linear R A] [Supercategory R A]
  [GradedSupercategory R A]
  {A' : Type w₃} [Category.{w₄} A'] [Preadditive A'] [Linear R A'] [Supercategory R A']
  [GradedSupercategory R A']
  {B : Type w₅} [Category.{w₆} B] [Preadditive B] [Linear R B] [Supercategory R B]
  [GradedSupercategory R B] [QPiSupercategory R B]

variable (R) in
/-- `K_{q,π} : A'_{q,π} → A_{q,π}` of a graded superfunctor `K : A' → A`, bundled. -/
abbrev mapGS (K : GradedSuperfunctor R A' A) :
    GradedSuperfunctor R (QPiEnvelope R A') (QPiEnvelope R A) :=
  ⟨⟨map R K.toFunctor⟩⟩

omit [Preadditive A'] [Linear R A'] [Supercategory R A'] [GradedSupercategory R A']
  [Preadditive A] [Linear R A] [Supercategory R A] [GradedSupercategory R A] in
variable (R) in
/-- **Theorem 6.9, naturality in `A`.** `(F ∘ K)~ = F̃ ∘ K_{q,π}`. -/
theorem extend_comp_left (K : A' ⥤ A) (F : A ⥤ B) :
    extend R (K ⋙ F) = map R K ⋙ extend R F := rfl

/-- **Theorem 6.9, naturality in `A`**, for supernatural transformations: `(xK)~ = x̃ K_{q,π}`. -/
theorem extendSuperNatTrans_whiskerLeft (K : GradedSuperfunctor R A' A)
    {F G : GradedSuperfunctor R A B} (x : F.toSuperfunctor ⟶ G.toSuperfunctor) :
    extendSuperNatTrans (F := K.comp F) (G := K.comp G)
        (Superfunctor.whiskerLeft K.toSuperfunctor x) =
      Superfunctor.whiskerLeft (mapGS R K).toSuperfunctor (extendSuperNatTrans x) := rfl

set_option backward.isDefEq.respectTransparency false in
variable (R A B) in
/-- **Theorem 6.9, naturality in `A`.** The graded superequivalences
`ℋom(A, νB) → ℋom(A_{q,π}, B)` commute strictly with precomposition:
`(- ∘ K)~ = -~ ∘ K_{q,π}`. -/
theorem extendHom_precompose (K : GradedSuperfunctor R A' A) :
    extendHom R A B ⋙ GradedHom.precompose B (mapGS R K) =
      GradedHom.precompose B K ⋙ extendHom R A' B :=
  CategoryTheory.Functor.ext (fun _ => rfl) fun _ _ _ => by
    simp only [Functor.comp_map, eqToHom_refl, Category.comp_id, Category.id_comp]
    rfl

end QPiEnvelope

/-! ## Naturality in `B` -/

namespace QEnvelope

open QPiSupercategory

variable {C : Type w₁} [Category.{w₂} C] [Preadditive C] [Linear R C] [Supercategory R C]
  {B : Type w₅} [Category.{w₆} B] [Preadditive B] [Linear R B] [Supercategory R B]
  [GradedSupercategory R B] [QPiSupercategory R B]
  {B' : Type w₇} [Category.{w₈} B'] [Preadditive B'] [Linear R B'] [Supercategory R B']
  [GradedSupercategory R B'] [QPiSupercategory R B']

variable (R) in
/-- `γᵐ_L = L((σᵐ)⁻¹) ∘ σᵐ : Q^m(Lμ) ≅ L(Q^m μ)`, even of degree zero for a graded
superfunctor `L`. -/
def γPow (L : B ⥤ B') (m : ℤ) (Y : B) : qPow R m (L.obj Y) ≅ L.obj (qPow R m Y) :=
  σPow R m (L.obj Y) ≪≫ L.mapIso (σPow R m Y).symm

theorem γPow_hom_mem (L : B ⥤ B') [L.Additive] [L.Linear R] [IsSuperfunctor R L] (m : ℤ)
    (Y : B) : (γPow R L m Y).hom ∈ parity (R := R) _ _ 0 := by
  simpa [γPow] using comp_mem (σPow_hom_mem (R := R) m (L.obj Y))
    (map_mem L (σPow_inv_mem (R := R) m Y))

theorem γPow_hom_mem_degree (L : B ⥤ B') [L.Additive] [L.Linear R] [IsGradedSuperfunctor R L]
    (m : ℤ) (Y : B) : (γPow R L m Y).hom ∈ degree (R := R) _ _ 0 := by
  simpa [γPow] using comp_mem_degree (σPow_hom_mem_degree (R := R) m (L.obj Y))
    (map_mem_degree L (σPow_inv_mem_degree (R := R) m Y))

set_option backward.isDefEq.respectTransparency false in
variable (R) in
/-- For a superfunctor `L : B → B'`, `(L ∘ F)^Q ≅ L ∘ F^Q` by the isomorphisms `γᵐ_L`. -/
def extendCompIso (F : C ⥤ B) (L : B ⥤ B') : extend R (F ⋙ L) ≅ extend R F ⋙ L :=
  NatIso.ofComponents (fun X => γPow R L X.shift (F.obj X.obj)) fun {X Y} f => by
    simp [γPow]

omit [Preadditive C] [Linear R C] [Supercategory R C] in
theorem extendCompIso_hom_app (F : C ⥤ B) (L : B ⥤ B') (X : QEnvelope R C) :
    (extendCompIso R F L).hom.app X = (γPow R L X.shift (F.obj X.obj)).hom := rfl

end QEnvelope

namespace Envelope

variable {B : Type w₅} [Category.{w₆} B] [Preadditive B] [Linear R B] [Supercategory R B]
  [GradedSupercategory R B] [QPiSupercategory R B]
  {B' : Type w₇} [Category.{w₈} B'] [Preadditive B'] [Linear R B'] [Supercategory R B']
  [GradedSupercategory R B'] [QPiSupercategory R B']

theorem βPow_hom_mem_degree (L : B ⥤ B') [L.Additive] [L.Linear R] [IsGradedSuperfunctor R L]
    (a : ZMod 2) (Y : B) : (βPow R L a Y).hom ∈ degree (R := R) _ _ 0 := by
  have e : (βPow R L a Y).hom = (ζPow R a (L.obj Y)).hom ≫ L.map (ζPow R a Y).inv := by
    rw [ζPow_map, Category.assoc, ← L.map_comp, Iso.hom_inv_id, L.map_id, Category.comp_id]
  rw [e]
  have := comp_mem_degree (ζPow_hom_mem_degree (R := R) a (L.obj Y))
    (map_mem_degree L (ζPow_inv_mem_degree (R := R) a Y))
  rwa [add_zero] at this

end Envelope

namespace QPiEnvelope

open GradedSuperfunctor

variable {A : Type w₁} [Category.{w₂} A] [Preadditive A] [Linear R A] [Supercategory R A]
  [GradedSupercategory R A]
  {B : Type w₅} [Category.{w₆} B] [Preadditive B] [Linear R B] [Supercategory R B]
  [GradedSupercategory R B] [QPiSupercategory R B]
  {B' : Type w₇} [Category.{w₈} B'] [Preadditive B'] [Linear R B'] [Supercategory R B']
  [GradedSupercategory R B'] [QPiSupercategory R B']

section Iso

variable (F : A ⥤ B) [F.Additive] [F.Linear R] [IsGradedSuperfunctor R F]
  (L : B ⥤ B') [L.Additive] [L.Linear R] [IsGradedSuperfunctor R L]

variable (R) in
/-- **Theorem 6.9, naturality in `B`.** For a graded superfunctor `L : B → B'` between graded
`(Q, Π)`-supercategories, `(L ∘ F)~ ≅ L ∘ F̃`, with components `βᵃ_L ∘ Πᵃ(γᵐ_L)` on
`Q^m Π^a λ`. -/
def extendCompIso : extend R (F ⋙ L) ≅ extend R F ⋙ L :=
  Envelope.extendIso (QEnvelope.extendCompIso R F L)
      (fun X => QEnvelope.γPow_hom_mem L X.shift (F.obj X.obj)) ≪≫
    Envelope.extendCompIso R (QEnvelope.extend R F) L

theorem extendCompIso_hom_mem (X : QPiEnvelope R A) :
    (extendCompIso R F L).hom.app X ∈ parity (R := R) _ _ 0 := by
  have h1 := (Envelope.isSupernatural_extendNat (isSupernatural_of_natTrans
    (QEnvelope.extendCompIso R F L).hom
    (fun X => QEnvelope.γPow_hom_mem L X.shift (F.obj X.obj)))).mem X
  have h2 := Envelope.extendCompIso_hom_mem (QEnvelope.extend R F) L X
  simpa using! comp_mem h1 h2

theorem extendCompIso_hom_mem_degree (X : QPiEnvelope R A) :
    (extendCompIso R F L).hom.app X ∈ degree (R := R) _ _ 0 := by
  have h1 := Envelope.extendNat_mem_degree (p := 0)
    (x := fun X => (QEnvelope.extendCompIso R F L).hom.app X)
    (fun X => QEnvelope.γPow_hom_mem_degree L X.shift (F.obj X.obj)) X
  have h2 : (Envelope.extendCompIso R (QEnvelope.extend R F) L).hom.app X ∈
      degree (R := R) _ _ 0 :=
    Envelope.βPow_hom_mem_degree L X.par _
  simpa using! comp_mem_degree h1 h2

set_option backward.isDefEq.respectTransparency false in
/-- On `J λ` the isomorphism `(L ∘ F)~ ≅ L ∘ F̃` is the identity. -/
theorem extendCompIso_hom_app_J (X : A) :
    (extendCompIso R F L).hom.app ⟨0, ⟨0, X⟩⟩ = 𝟙 _ := by
  show Envelope.extendNat R (QEnvelope.extend R (F ⋙ L)) (QEnvelope.extend R F ⋙ L) 0
      (fun X => (QEnvelope.extendCompIso R F L).hom.app X)
      ((Envelope.J R (QEnvelope R A)).obj ((QEnvelope.J R A).obj X)) ≫
    (Envelope.extendCompIso R (QEnvelope.extend R F) L).hom.app
      ((Envelope.J R (QEnvelope R A)).obj ((QEnvelope.J R A).obj X)) = 𝟙 (L.obj (F.obj X))
  rw [Envelope.extendNat_zero_par, Envelope.extendCompIso_hom_app_J, Category.comp_id,
    QEnvelope.extendCompIso_hom_app]
  change (QPiSupercategory.σPow R 0 (L.obj (F.obj X))).hom ≫
    L.map (QPiSupercategory.σPow R 0 (F.obj X)).inv = _
  simp

theorem isGradedSupernatural_extendCompIso_hom :
    IsGradedSupernatural R 0 0 fun X => ((extendCompIso R F L).app X).hom :=
  ⟨isSupernatural_of_natTrans (extendCompIso R F L).hom (extendCompIso_hom_mem F L),
    extendCompIso_hom_mem_degree F L⟩

theorem isGradedSupernatural_extendCompIso_inv :
    IsGradedSupernatural R 0 (-0) fun X => ((extendCompIso R F L).app X).inv :=
  ⟨isSupernatural_of_natTrans (extendCompIso R F L).inv
      (fun X => inv_mem ((extendCompIso R F L).app X) (extendCompIso_hom_mem F L X)),
    fun X => inv_mem_degree ((extendCompIso R F L).app X) (extendCompIso_hom_mem_degree F L X)⟩

end Iso

set_option backward.isDefEq.respectTransparency false in
/-- **Theorem 6.9, naturality in `B`**, compatibility with supernatural transformations: for
`x : F ⇒ G` homogeneous of parity `p`, the square
`(Lx)~ ; (L ∘ G)~ ≅ L ∘ G̃` = `(L ∘ F)~ ≅ L ∘ F̃ ; L x̃` commutes. -/
theorem extendCompIso_naturality {F G : A ⥤ B} [F.Additive] [F.Linear R]
    [IsGradedSuperfunctor R F] [G.Additive] [G.Linear R] [IsGradedSuperfunctor R G]
    (L : B ⥤ B') [L.Additive] [L.Linear R] [IsGradedSuperfunctor R L] {p : ZMod 2}
    {x : ∀ X, F.obj X ⟶ G.obj X} (hx : IsSupernatural R p x) (X : QPiEnvelope R A) :
    extendNat R (F ⋙ L) (G ⋙ L) p (fun X => L.map (x X)) X ≫
        (extendCompIso R G L).hom.app X =
      (extendCompIso R F L).hom.app X ≫ L.map (extendNat R F G p x X) := by
  have h1 : IsSupernatural R p (F := extend R (F ⋙ L)) (G := extend R G ⋙ L) fun X =>
      extendNat R (F ⋙ L) (G ⋙ L) p (fun X => L.map (x X)) X ≫
        (extendCompIso R G L).hom.app X := by
    simpa using (isSupernatural_extendNat (hx.whiskerRight L)).comp
      (isSupernatural_of_natTrans (extendCompIso R G L).hom (extendCompIso_hom_mem G L))
  have h2 : IsSupernatural R p (F := extend R (F ⋙ L)) (G := extend R G ⋙ L) fun X =>
      (extendCompIso R F L).hom.app X ≫ L.map (extendNat R F G p x X) := by
    simpa using (isSupernatural_of_natTrans (extendCompIso R F L).hom
      (extendCompIso_hom_mem F L)).comp ((isSupernatural_extendNat hx).whiskerRight L)
  refine congrFun (eq_of_restrict_eq (R := R) h1 h2 fun Y => ?_) X
  simp only [J_obj, extendNat_J]
  rw [extendCompIso_hom_app_J, extendCompIso_hom_app_J, Category.comp_id, Category.id_comp]

variable {A : Type w₁} [Category.{w₂} A] [Preadditive A] [Linear R A] [Supercategory R A]
  [GradedSupercategory R A]

set_option backward.isDefEq.respectTransparency false in
variable (R A) in
/-- **Theorem 6.9, naturality in `B`.** The graded superequivalences
`ℋom(A, νB) → ℋom(A_{q,π}, B)` commute with postcomposition by a graded superfunctor
`L : B → B'` up to an even natural isomorphism of degree zero:
`(L ∘ -)~ ≅ L ∘ -~`, with components `QPiEnvelope.extendCompIso`. -/
def extendHomPostcomposeIso (L : GradedSuperfunctor R B B') :
    GradedHom.postcompose A L ⋙ extendHom R A B' ≅
      extendHom R A B ⋙ GradedHom.postcompose (QPiEnvelope R A) L :=
  NatIso.ofComponents
    (fun F => GradedHom.isoOfHomogeneous
      (F := (extendHom R A B').obj ((GradedHom.postcompose A L).obj F))
      (G := (GradedHom.postcompose (QPiEnvelope R A) L).obj ((extendHom R A B).obj F))
      (x := fun X => (extendCompIso R F.as.toFunctor L.toFunctor).app X)
      (isGradedSupernatural_extendCompIso_hom F.as.toFunctor L.toFunctor)
      (isGradedSupernatural_extendCompIso_inv F.as.toFunctor L.toFunctor))
    fun {F G} x => GradedSubcategory.hom_ext <| Superfunctor.hom_ext fun p X => by
      have key := fun q => extendCompIso_naturality (F := F.as.toFunctor) (G := G.as.toFunctor)
        L.toFunctor (x.1.isSupernatural q) X
      rcases parity_eq_zero_or_one p with rfl | rfl
      · simp [Superfunctor.comp_app, Superfunctor.whiskerRight]
        exact key 0
      · simp [Superfunctor.comp_app, Superfunctor.whiskerRight]
        exact key 1

theorem extendHomPostcomposeIso_hom_app (L : GradedSuperfunctor R B B') (F : GradedHom R A B)
    (X : QPiEnvelope R A) :
    ((extendHomPostcomposeIso R A L).hom.app F).1.app 0 X =
      (extendCompIso R F.as.toFunctor L.toFunctor).hom.app X := rfl

theorem extendHomPostcomposeIso_hom_mem (L : GradedSuperfunctor R B B') (F : GradedHom R A B) :
    (extendHomPostcomposeIso R A L).hom.app F ∈ parity (R := R) _ _ 0 :=
  GradedHom.ofHomogeneous_mem (isGradedSupernatural_extendCompIso_hom F.as.toFunctor L.toFunctor)

theorem extendHomPostcomposeIso_hom_mem_degree (L : GradedSuperfunctor R B B')
    (F : GradedHom R A B) :
    (extendHomPostcomposeIso R A L).hom.app F ∈ degree (R := R) _ _ 0 :=
  GradedHom.ofHomogeneous_mem_degree
    (isGradedSupernatural_extendCompIso_hom F.as.toFunctor L.toFunctor)

end QPiEnvelope

end StringDiagrams

end
