import StringDiagrams.Super.EnvelopeAdjunction

/-!
# Functoriality of the Π-envelope and naturality of Theorem 4.3

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Definition 1.10 (the functor (1) of (1.5), `A ↦ A_π`, on superfunctors) and Theorem 4.3
("a functorial superequivalence `ℋom(A, νB) → ℋom(A_π, B)` ... hence the strict 2-superfunctor
`-_π` is left 2-adjoint to `ν`").

* The Π-envelope `K_π = Envelope.map K : A'_π ⥤ A_π` of a superfunctor `K : A' ⥤ A` is in
  `StringDiagrams.Super.Envelope` (strictly functorial: `Envelope.map_id`, `Envelope.map_comp`,
  and `J ∘ K = K_π ∘ J`: `Envelope.J_comp_map`).
* Naturality of the extension in `A`, on the nose: `(F ∘ K)~ = F̃ ∘ K_π`
  (`Envelope.extend_comp_left`), and for supernatural transformations
  (`Envelope.extendSuperNatTrans_whiskerLeft`); as an equality of the superfunctors
  `ℋom(A, νB) → ℋom(A_π, B)` of Theorem 4.3 composed with precomposition
  (`Envelope.extendHom_precompose`).
* Naturality of the extension in `B`, up to even natural isomorphism: for a superfunctor
  `L : B ⥤ B'` between Π-supercategories, `(L ∘ F)~ ≅ L ∘ F̃` with components `1` on `Π⁰λ` and
  `β_L : Π(Lμ) ≅ L(Πμ)` (Corollary 3.3(ii)) on `Π¹λ` (`Envelope.extendCompIso`,
  `Envelope.extendCompIso_hom_mem`).

Together with `Envelope.extendHomSuperequivalence` (Theorem 4.3) this is the precise content
of "`-_π` is left 2-adjoint to `ν`" formalized here: the superequivalences
`ℋom(A, νB) → ℋom(A_π, B)` are strictly natural in `A` and natural up to even isomorphism in
`B`. The 2-adjunction is not packaged as a biadjunction of 2-supercategories (a notion not
available in Mathlib at this pin), and the compatibility of the isomorphisms
`Envelope.extendCompIso` with supernatural transformations is not recorded.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory

universe w w₁ w₂ w₃ w₄ w₅ w₆ w₇ w₈

namespace Envelope

variable {R : Type w} [CommRing R]
  {A : Type w₁} [Category.{w₂} A] [Preadditive A] [Linear R A] [Supercategory R A]
  {A' : Type w₃} [Category.{w₄} A'] [Preadditive A'] [Linear R A'] [Supercategory R A']

/-! ## Naturality in `A` -/

variable {B : Type w₅} [Category.{w₆} B] [Preadditive B] [Linear R B] [Supercategory R B]
  [PiSupercategory R B]

variable (R) in
/-- **Theorem 4.3, naturality in `A`.** `(F ∘ K)~ = F̃ ∘ K_π`. -/
theorem extend_comp_left (K : A' ⥤ A) [K.Additive] [K.Linear R] [IsSuperfunctor R K]
    (F : A ⥤ B) [F.Additive] [F.Linear R] [IsSuperfunctor R F] :
    extend R (K ⋙ F) = map R K ⋙ extend R F := rfl

/-- **Theorem 4.3, naturality in `A`**, for supernatural transformations: `(xK)~ = x̃ K_π`. -/
theorem extendSuperNatTrans_whiskerLeft (K : Superfunctor R A' A) {F G : Superfunctor R A B}
    (x : F ⟶ G) :
    extendSuperNatTrans (Superfunctor.whiskerLeft K x) =
      Superfunctor.whiskerLeft ⟨map R K.toFunctor⟩ (extendSuperNatTrans x) := rfl

/-- Precomposition with a superfunctor, as a functor between supercategories of superfunctors. -/
@[simps]
def _root_.StringDiagrams.Supercategory.Superfunctor.precompose (K : Superfunctor R A' A) :
    Superfunctor R A B ⥤ Superfunctor R A' B where
  obj F := K.comp F
  map x := Superfunctor.whiskerLeft K x
  map_id F := Superfunctor.whiskerLeft_id K F
  map_comp x y := Superfunctor.whiskerLeft_comp K x y

variable (R A B) in
/-- **Theorem 4.3, naturality in `A`.** The superequivalences `ℋom(A, νB) → ℋom(A_π, B)`
commute strictly with precomposition: `(- ∘ K)~ = -~ ∘ K_π`. -/
theorem extendHom_precompose (K : Superfunctor R A' A) :
    extendHom R A B ⋙ Superfunctor.precompose ⟨map R K.toFunctor⟩ =
      Superfunctor.precompose K ⋙ extendHom R A' B :=
  CategoryTheory.Functor.ext (fun _ => rfl) fun _ _ _ => by
    simp only [Functor.comp_map, eqToHom_refl, Category.comp_id, Category.id_comp]
    rfl

/-! ## Naturality in `B` -/

variable {B' : Type w₇} [Category.{w₈} B'] [Preadditive B'] [Linear R B'] [Supercategory R B']
  [PiSupercategory R B']

variable (R) in
/-- `βᵃ_L : Πᵃ(Lμ) ≅ L(Πᵃμ)`: the identity for `a = 0`, `β_L` (Corollary 3.3(ii)) for `a = 1`. -/
def βPow (L : B ⥤ B') : ∀ (a : ZMod 2) (Y : B), piPow R a (L.obj Y) ≅ L.obj (piPow R a Y)
  | ⟨0, _⟩, Y => Iso.refl _
  | ⟨1, _⟩, Y => PiSupercategory.β R L Y
  | ⟨_ + 2, h⟩, _ => absurd h (by simp)

@[simp] theorem βPow_zero (L : B ⥤ B') (Y : B) : βPow R L 0 Y = Iso.refl _ := rfl

@[simp] theorem βPow_one (L : B ⥤ B') (Y : B) : βPow R L 1 Y = PiSupercategory.β R L Y := rfl

theorem βPow_hom_mem (L : B ⥤ B') [L.Additive] [L.Linear R] [IsSuperfunctor R L] (a : ZMod 2)
    (Y : B) : (βPow R L a Y).hom ∈ parity (R := R) _ _ 0 := by
  rcases parity_eq_zero_or_one a with rfl | rfl
  · exact id_mem _
  · exact PiSupercategory.β_hom_mem L Y

/-- `ζᵃ_{Lμ} = L(ζᵃ_μ) ∘ βᵃ_L`. -/
theorem ζPow_map (L : B ⥤ B') (a : ZMod 2) (Y : B) :
    (ζPow R a (L.obj Y)).hom = (βPow R L a Y).hom ≫ L.map (ζPow R a Y).hom := by
  rcases parity_eq_zero_or_one a with rfl | rfl
  · simp
  · simp [PiSupercategory.β_hom]

/-- `(ζᵃ_{Lμ})⁻¹ ∘ βᵃ_L = L((ζᵃ_μ)⁻¹)`. -/
@[reassoc]
theorem ζPow_inv_map (L : B ⥤ B') (a : ZMod 2) (Y : B) :
    (ζPow R a (L.obj Y)).inv ≫ (βPow R L a Y).hom = L.map (ζPow R a Y).inv := by
  rw [Iso.inv_comp_eq, ζPow_map, Category.assoc, ← L.map_comp, Iso.hom_inv_id, L.map_id,
    Category.comp_id]

variable (R) in
/-- **Theorem 4.3, naturality in `B`.** For a superfunctor `L : B ⥤ B'` between
Π-supercategories, `(L ∘ F)~ ≅ L ∘ F̃` by the even isomorphisms `βᵃ_L`. -/
def extendCompIso (F : A ⥤ B) [F.Additive] [F.Linear R] [IsSuperfunctor R F] (L : B ⥤ B')
    [L.Additive] [L.Linear R] [IsSuperfunctor R L] :
    extend R (F ⋙ L) ≅ extend R F ⋙ L :=
  NatIso.ofComponents (fun X => βPow R L X.par (F.obj X.obj)) fun {X Y} f => by
    simp only [extend_map, Functor.comp_obj, Functor.comp_map, Functor.map_comp, Category.assoc,
      ζPow_inv_map, ζPow_map]

theorem extendCompIso_hom_app (F : A ⥤ B) [F.Additive] [F.Linear R] [IsSuperfunctor R F]
    (L : B ⥤ B') [L.Additive] [L.Linear R] [IsSuperfunctor R L] (X : Envelope R A) :
    (extendCompIso R F L).hom.app X = (βPow R L X.par (F.obj X.obj)).hom := rfl

theorem extendCompIso_hom_mem (F : A ⥤ B) [F.Additive] [F.Linear R] [IsSuperfunctor R F]
    (L : B ⥤ B') [L.Additive] [L.Linear R] [IsSuperfunctor R L] (X : Envelope R A) :
    (extendCompIso R F L).hom.app X ∈ parity (R := R) _ _ 0 :=
  βPow_hom_mem L X.par (F.obj X.obj)

/-- On `Π⁰λ` the isomorphism `(L ∘ F)~ ≅ L ∘ F̃` is the identity. -/
theorem extendCompIso_hom_app_J (F : A ⥤ B) [F.Additive] [F.Linear R] [IsSuperfunctor R F]
    (L : B ⥤ B') [L.Additive] [L.Linear R] [IsSuperfunctor R L] (X : A) :
    (extendCompIso R F L).hom.app ((J R A).obj X) = 𝟙 _ := rfl

end Envelope

end StringDiagrams

end
