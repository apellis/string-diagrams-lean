import StringDiagrams.Super.BicategoryOfHcomp
import StringDiagrams.Super.SKar
import StringDiagrams.Super.QPiTwoCategory

/-!
# The idempotent completion of a bicategory

For a bicategory `B`, the *idempotent completion* `KarBicat B` has the same objects, the hom
categories `Karoubi (a ⟶ b)` (Mathlib's idempotent completion: pairs `(f, e)` of a 1-morphism
and an idempotent 2-endomorphism `e` of it), horizontal composition
`(f, e) ≫ (g, e') = (f ≫ g, e ▷ g ≫ f ◁ e')`, and the coherence isomorphisms of `B` composed
with the idempotents. It is a bicategory (`KarBicat.instBicategory`), preadditive and
`R`-linear when `B` is, and its hom categories have finite biproducts when those of `B` do.

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §6 (the
end of the section), a Π-2-category structure (Definition 5.2) and a `(Q, Π)`-2-category
structure (Definition 6.14) on `B` extend to `KarBicat B` (`KarBicat.instPiTwoCategory`,
`KarBicat.instQPiTwoCategory`), with `π_λ`, `q_λ`, `q_λ⁻¹` the images of those of `B` and
`β`, `γ`, `ξ`, `ii`, `jj` composed with the idempotents. Together with the additive envelope
(`StringDiagrams.Super.MatBicategory`) this gives the additive Karoubi envelope of a 2-category
(`StringDiagrams.Super.KarBicategory`).

## Implementation

A 2-morphism `(f, e) ⟶ (f', e')` of `KarBicat B` is a 2-morphism `η : f ⟶ f'` of `B` with
`η = e ≫ η ≫ e'`. The coherence 2-morphisms are of the form `Karoubi.mkHom c h = c ≫ e'` for a
2-morphism `c : f ⟶ f'` of `B` commuting with the idempotents (`h : e ≫ c = c ≫ e'`); these are
closed under composition and whiskering (`Karoubi.mkHom_comp_mkHom`, `KarBicat.whiskerLeft_mkHom`,
`KarBicat.mkHom_whiskerRight`), which reduces the coherence axioms to those of `B`.

Compositions of 1-morphisms are written in diagrammatic order.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Bicategory Idempotents

universe w v u w₁

/-! ## Morphisms of `Karoubi C` from morphisms commuting with the idempotents -/

namespace Karoubi

variable {C : Type u} [Category.{v} C]

/-- The morphism `(X, p) ⟶ (Y, q)` given by `c ≫ q` for `c : X ⟶ Y` with `p ≫ c = c ≫ q`. -/
def mkHom {P Q : Karoubi C} (c : P.X ⟶ Q.X) (h : P.p ≫ c = c ≫ Q.p) : P ⟶ Q :=
  ⟨c ≫ Q.p, by rw [Category.assoc, Q.idem, ← Category.assoc, h, Category.assoc, Q.idem]⟩

@[simp] theorem mkHom_f {P Q : Karoubi C} (c : P.X ⟶ Q.X) (h : P.p ≫ c = c ≫ Q.p) :
    (mkHom c h).f = c ≫ Q.p := rfl

theorem mkHom_congr {P Q : Karoubi C} {c c' : P.X ⟶ Q.X} (h : P.p ≫ c = c ≫ Q.p)
    (h' : P.p ≫ c' = c' ≫ Q.p) (e : c = c') : mkHom c h = mkHom c' h' := by
  subst e; rfl

theorem mkHom_comp_mkHom {P Q S : Karoubi C} (c : P.X ⟶ Q.X) (h : P.p ≫ c = c ≫ Q.p)
    (c' : Q.X ⟶ S.X) (h' : Q.p ≫ c' = c' ≫ S.p) :
    mkHom c h ≫ mkHom c' h' = mkHom (c ≫ c') (by rw [reassoc_of% h, h', Category.assoc]) :=
  Idempotents.Karoubi.hom_ext _ _ (by
    simp only [Idempotents.Karoubi.comp_f, mkHom_f, Category.assoc]
    rw [reassoc_of% h', S.idem])

theorem mkHom_comp_f {P Q S : Karoubi C} (c : P.X ⟶ Q.X) (h : P.p ≫ c = c ≫ Q.p) (ψ : Q ⟶ S) :
    (mkHom c h ≫ ψ).f = c ≫ ψ.f := by
  rw [Idempotents.Karoubi.comp_f, mkHom_f, Category.assoc, Idempotents.Karoubi.p_comp]

theorem comp_mkHom_f {P Q S : Karoubi C} (ψ : P ⟶ Q) (c : Q.X ⟶ S.X) (h : Q.p ≫ c = c ≫ S.p) :
    (ψ ≫ mkHom c h).f = ψ.f ≫ c ≫ S.p := by
  rw [Idempotents.Karoubi.comp_f, mkHom_f]

theorem id_eq_mkHom (P : Karoubi C) : 𝟙 P = mkHom (𝟙 P.X) (by simp) :=
  Idempotents.Karoubi.hom_ext _ _ (by simp)

theorem comm_inv {P Q : Karoubi C} (e : P.X ≅ Q.X) (h : P.p ≫ e.hom = e.hom ≫ Q.p) :
    Q.p ≫ e.inv = e.inv ≫ P.p := by
  rw [Iso.eq_inv_comp, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The isomorphism `(X, p) ≅ (Y, q)` given by an isomorphism `e : X ≅ Y` with
`p ≫ e = e ≫ q`. -/
@[simps]
def mkIso {P Q : Karoubi C} (e : P.X ≅ Q.X) (h : P.p ≫ e.hom = e.hom ≫ Q.p) : P ≅ Q where
  hom := mkHom e.hom h
  inv := mkHom e.inv (comm_inv e h)
  hom_inv_id := by
    rw [mkHom_comp_mkHom]
    exact (mkHom_congr _ _ (Iso.hom_inv_id e)).trans (id_eq_mkHom P).symm
  inv_hom_id := by
    rw [mkHom_comp_mkHom]
    exact (mkHom_congr _ _ (Iso.inv_hom_id e)).trans (id_eq_mkHom Q).symm

end Karoubi

/-! ## The idempotent completion of a bicategory -/

/-- The idempotent completion of a bicategory: the same objects, with hom categories the
idempotent completions `Karoubi (a ⟶ b)`. -/
@[ext]
structure KarBicat (B : Type u) where
  /-- The object of `B`. -/
  obj : B

namespace KarBicat

open Karoubi

/-! ### The construction

The category structure and the hom categories are local instances during the construction of
the bicategory; afterwards they are only accessed through `Bicategory (KarBicat B)`. -/

section Construction

variable {B : Type u} [Bicategory.{w, v} B]

/-- The category structure: 1-morphisms `(f, e)` with `e` an idempotent 2-endomorphism of `f`,
composed by `(f, e) ≫ (g, e') = (f ≫ g, e ▷ g ≫ f ◁ e')`. -/
@[reducible] def categoryStruct : CategoryStruct (KarBicat B) where
  Hom a b := Karoubi (a.obj ⟶ b.obj)
  id a := ⟨𝟙 a.obj, 𝟙 _, by simp⟩
  comp P Q := ⟨P.X ≫ Q.X, hcomp₂ P.p Q.p, by rw [← hcomp₂_comp, P.idem, Q.idem]⟩

attribute [local instance] categoryStruct

/-- The hom categories `Karoubi (a ⟶ b)`. -/
@[reducible] def homCategory (a b : KarBicat B) : Category (a ⟶ b) :=
  inferInstanceAs (Category (Karoubi (a.obj ⟶ b.obj)))

attribute [local instance] homCategory

variable {a b c d : KarBicat B}

/-- Horizontal composition of 2-morphisms: the horizontal composite in `B`. -/
def hcomp {P P' : a ⟶ b} {Q Q' : b ⟶ c} (η : P ⟶ P') (θ : Q ⟶ Q') : P ≫ Q ⟶ P' ≫ Q' :=
  ⟨hcomp₂ η.f θ.f, by
    show hcomp₂ η.f θ.f = hcomp₂ P.p Q.p ≫ hcomp₂ η.f θ.f ≫ hcomp₂ P'.p Q'.p
    rw [← hcomp₂_comp, ← hcomp₂_comp, ← η.comm, ← θ.comm]⟩

theorem hcomp_f' {P P' : a ⟶ b} {Q Q' : b ⟶ c} (η : P ⟶ P') (θ : Q ⟶ Q') :
    (hcomp η θ).f = hcomp₂ η.f θ.f := rfl

theorem hcomp_id_id (P : a ⟶ b) (Q : b ⟶ c) : hcomp (𝟙 P) (𝟙 Q) = 𝟙 (P ≫ Q) := rfl

theorem hcomp_comp {P₁ P₂ P₃ : a ⟶ b} {Q₁ Q₂ Q₃ : b ⟶ c} (η₁ : P₁ ⟶ P₂) (θ₁ : Q₁ ⟶ Q₂)
    (η₂ : P₂ ⟶ P₃) (θ₂ : Q₂ ⟶ Q₃) :
    hcomp (η₁ ≫ η₂) (θ₁ ≫ θ₂) = hcomp η₁ θ₁ ≫ hcomp η₂ θ₂ :=
  Idempotents.Karoubi.hom_ext _ _ (hcomp₂_comp _ _ _ _)

theorem hcomp_mkHom_id' {P P' : a ⟶ b} (φ : P.X ⟶ P'.X) (h : P.p ≫ φ = φ ≫ P'.p) (Q : b ⟶ c) :
    hcomp (mkHom φ h) (𝟙 Q) = mkHom (φ ▷ Q.X) (by
      show hcomp₂ P.p Q.p ≫ φ ▷ Q.X = φ ▷ Q.X ≫ hcomp₂ P'.p Q.p
      rw [← hcomp₂_id_right φ, ← hcomp₂_comp, ← hcomp₂_comp, h, Category.id_comp,
        Category.comp_id]) :=
  Idempotents.Karoubi.hom_ext _ _ (by
    show hcomp₂ (φ ≫ P'.p) Q.p = φ ▷ Q.X ≫ hcomp₂ P'.p Q.p
    simp only [hcomp₂, comp_whiskerRight, Category.assoc])

theorem hcomp_id_mkHom' (P : a ⟶ b) {Q Q' : b ⟶ c} (φ : Q.X ⟶ Q'.X) (h : Q.p ≫ φ = φ ≫ Q'.p) :
    hcomp (𝟙 P) (mkHom φ h) = mkHom (P.X ◁ φ) (by
      show hcomp₂ P.p Q.p ≫ P.X ◁ φ = P.X ◁ φ ≫ hcomp₂ P.p Q'.p
      rw [← hcomp₂_id_left P.X φ, ← hcomp₂_comp, ← hcomp₂_comp, h, Category.id_comp,
        Category.comp_id]) :=
  Idempotents.Karoubi.hom_ext _ _ (by
    show hcomp₂ P.p (φ ≫ Q'.p) = P.X ◁ φ ≫ hcomp₂ P.p Q'.p
    simp only [hcomp₂, Bicategory.whiskerLeft_comp, Category.assoc]
    rw [whisker_exchange_assoc])

theorem assoc_comm (P : a ⟶ b) (Q : b ⟶ c) (S : c ⟶ d) :
    ((P ≫ Q) ≫ S).p ≫ (α_ P.X Q.X S.X).hom = (α_ P.X Q.X S.X).hom ≫ (P ≫ Q ≫ S).p :=
  hcomp₂_hcomp₂_associator P.p Q.p S.p

theorem assoc_inv_comm (P : a ⟶ b) (Q : b ⟶ c) (S : c ⟶ d) :
    (P ≫ Q ≫ S).p ≫ (α_ P.X Q.X S.X).inv = (α_ P.X Q.X S.X).inv ≫ ((P ≫ Q) ≫ S).p :=
  hcomp₂_hcomp₂_associator_inv P.p Q.p S.p

theorem leftUnitor_comm (P : a ⟶ b) : (𝟙 a ≫ P).p ≫ (λ_ P.X).hom = (λ_ P.X).hom ≫ P.p := by
  show hcomp₂ (𝟙 (𝟙 a.obj)) P.p ≫ (λ_ P.X).hom = (λ_ P.X).hom ≫ P.p
  rw [hcomp₂_id_left, leftUnitor_naturality]

theorem leftUnitor_inv_comm (P : a ⟶ b) :
    P.p ≫ (λ_ P.X).inv = (λ_ P.X).inv ≫ (𝟙 a ≫ P).p := by
  show P.p ≫ (λ_ P.X).inv = (λ_ P.X).inv ≫ hcomp₂ (𝟙 (𝟙 a.obj)) P.p
  rw [hcomp₂_id_left, leftUnitor_inv_naturality]

theorem rightUnitor_comm (P : a ⟶ b) : (P ≫ 𝟙 b).p ≫ (ρ_ P.X).hom = (ρ_ P.X).hom ≫ P.p := by
  show hcomp₂ P.p (𝟙 (𝟙 b.obj)) ≫ (ρ_ P.X).hom = (ρ_ P.X).hom ≫ P.p
  rw [hcomp₂_id_right, rightUnitor_naturality]

theorem rightUnitor_inv_comm (P : a ⟶ b) :
    P.p ≫ (ρ_ P.X).inv = (ρ_ P.X).inv ≫ (P ≫ 𝟙 b).p := by
  show P.p ≫ (ρ_ P.X).inv = (ρ_ P.X).inv ≫ hcomp₂ P.p (𝟙 (𝟙 b.obj))
  rw [hcomp₂_id_right, rightUnitor_inv_naturality]

/-- The associator. -/
def associator (P : a ⟶ b) (Q : b ⟶ c) (S : c ⟶ d) : (P ≫ Q) ≫ S ≅ P ≫ Q ≫ S :=
  mkIso (α_ P.X Q.X S.X) (assoc_comm P Q S)

/-- The left unitor. -/
def leftUnitor (P : a ⟶ b) : 𝟙 a ≫ P ≅ P := mkIso (λ_ P.X) (leftUnitor_comm P)

/-- The right unitor. -/
def rightUnitor (P : a ⟶ b) : P ≫ 𝟙 b ≅ P := mkIso (ρ_ P.X) (rightUnitor_comm P)

theorem associator_hom' (P : a ⟶ b) (Q : b ⟶ c) (S : c ⟶ d) :
    (associator P Q S).hom = mkHom (α_ P.X Q.X S.X).hom (assoc_comm P Q S) := rfl

theorem leftUnitor_hom' (P : a ⟶ b) :
    (leftUnitor P).hom = mkHom (λ_ P.X).hom (leftUnitor_comm P) := rfl

theorem rightUnitor_hom' (P : a ⟶ b) :
    (rightUnitor P).hom = mkHom (ρ_ P.X).hom (rightUnitor_comm P) := rfl

/-- **The idempotent completion of a bicategory is a bicategory.** -/
@[reducible] instance instBicategory : Bicategory (KarBicat B) :=
  Bicategory.ofHcomp hcomp associator leftUnitor rightUnitor hcomp_id_id
    (fun η η' θ θ' => hcomp_comp η θ η' θ')
    (fun η θ ι => Idempotents.Karoubi.hom_ext _ _ (by
      dsimp only
      rw [associator_hom', associator_hom', comp_mkHom_f, mkHom_comp_f, hcomp_f', hcomp_f',
        hcomp_f', hcomp_f', ← Category.assoc, hcomp₂_hcomp₂_associator, Category.assoc]
      exact congrArg _ (Idempotents.Karoubi.comp_p (hcomp η (hcomp θ ι)))))
    (fun η => Idempotents.Karoubi.hom_ext _ _ (by
      dsimp only
      rw [leftUnitor_hom', leftUnitor_hom', comp_mkHom_f, mkHom_comp_f, hcomp_f']
      change hcomp₂ (𝟙 (𝟙 _)) η.f ≫ _ = _
      rw [hcomp₂_id_left, ← Category.assoc, leftUnitor_naturality, Category.assoc,
        Idempotents.Karoubi.comp_p]))
    (fun η => Idempotents.Karoubi.hom_ext _ _ (by
      dsimp only
      rw [rightUnitor_hom', rightUnitor_hom', comp_mkHom_f, mkHom_comp_f, hcomp_f']
      change hcomp₂ η.f (𝟙 (𝟙 _)) ≫ _ = _
      rw [hcomp₂_id_right, ← Category.assoc, rightUnitor_naturality, Category.assoc,
        Idempotents.Karoubi.comp_p]))
    (fun P Q S T => by
      dsimp only
      rw [associator_hom', associator_hom', associator_hom', associator_hom', associator_hom',
        hcomp_mkHom_id', hcomp_id_mkHom', mkHom_comp_mkHom, mkHom_comp_mkHom, mkHom_comp_mkHom]
      refine mkHom_congr _ _ ?_
      exact Bicategory.pentagon _ _ _ _)
    (fun P Q => by
      dsimp only
      rw [associator_hom', leftUnitor_hom', rightUnitor_hom', hcomp_mkHom_id', hcomp_id_mkHom',
        mkHom_comp_mkHom]
      refine mkHom_congr _ _ ?_
      exact Bicategory.triangle _ _)

end Construction

/-! ### The bicategory -/

section Basic

variable {B : Type u} [Bicategory.{w, v} B]

/-- A 1-morphism of `B` with the identity idempotent. -/
abbrev of {a b : B} (f : a ⟶ b) : (⟨a⟩ : KarBicat B) ⟶ ⟨b⟩ := ⟨f, 𝟙 f, by simp⟩

@[simp] theorem of_X {a b : B} (f : a ⟶ b) : (of f).X = f := rfl

@[simp] theorem of_p {a b : B} (f : a ⟶ b) : (of f).p = 𝟙 f := rfl

theorem id_eq (a : KarBicat B) : 𝟙 a = of (𝟙 a.obj) := rfl

@[simp] theorem id_X (a : KarBicat B) : (𝟙 a : a ⟶ a).X = 𝟙 a.obj := rfl

@[simp] theorem id_p (a : KarBicat B) : (𝟙 a : a ⟶ a).p = 𝟙 (𝟙 a.obj) := rfl

@[simp] theorem comp_X {a b c : KarBicat B} (P : a ⟶ b) (Q : b ⟶ c) : (P ≫ Q).X = P.X ≫ Q.X :=
  rfl

@[simp] theorem comp_p {a b c : KarBicat B} (P : a ⟶ b) (Q : b ⟶ c) :
    (P ≫ Q).p = hcomp₂ P.p Q.p := rfl

variable {a b c d : KarBicat B}

@[simp] theorem comp_f {P Q S : a ⟶ b} (η : P ⟶ Q) (θ : Q ⟶ S) : (η ≫ θ).f = η.f ≫ θ.f := rfl

@[simp] theorem id_f (P : a ⟶ b) : (𝟙 P : P ⟶ P).f = P.p := rfl

@[simp] theorem whiskerLeft_f (P : a ⟶ b) {Q Q' : b ⟶ c} (θ : Q ⟶ Q') :
    (P ◁ θ).f = hcomp₂ P.p θ.f := rfl

@[simp] theorem whiskerRight_f {P P' : a ⟶ b} (η : P ⟶ P') (Q : b ⟶ c) :
    (η ▷ Q).f = hcomp₂ η.f Q.p := rfl

/-! The lemmas on `Karoubi.mkHom`, restated for the hom categories of `KarBicat B`. -/

theorem mkHom_comp_mkHom {P Q S : a ⟶ b} (φ : P.X ⟶ Q.X) (h : P.p ≫ φ = φ ≫ Q.p)
    (φ' : Q.X ⟶ S.X) (h' : Q.p ≫ φ' = φ' ≫ S.p) :
    mkHom φ h ≫ mkHom φ' h' = mkHom (φ ≫ φ') (by rw [reassoc_of% h, h', Category.assoc]) :=
  Karoubi.mkHom_comp_mkHom φ h φ' h'

theorem mkHom_comp_f {P Q S : a ⟶ b} (φ : P.X ⟶ Q.X) (h : P.p ≫ φ = φ ≫ Q.p) (ψ : Q ⟶ S) :
    (mkHom φ h ≫ ψ).f = φ ≫ ψ.f :=
  Karoubi.mkHom_comp_f φ h ψ

theorem comp_mkHom_f {P Q S : a ⟶ b} (ψ : P ⟶ Q) (φ : Q.X ⟶ S.X) (h : Q.p ≫ φ = φ ≫ S.p) :
    (ψ ≫ mkHom φ h).f = ψ.f ≫ φ ≫ S.p :=
  Karoubi.comp_mkHom_f ψ φ h

theorem id_eq_mkHom (P : a ⟶ b) : 𝟙 P = mkHom (𝟙 P.X) (by simp) :=
  Karoubi.id_eq_mkHom P

theorem mkHom_congr {P Q : a ⟶ b} {φ φ' : P.X ⟶ Q.X} (h : P.p ≫ φ = φ ≫ Q.p)
    (h' : P.p ≫ φ' = φ' ≫ Q.p) (e : φ = φ') : mkHom φ h = mkHom φ' h' :=
  Karoubi.mkHom_congr h h' e

theorem associator_hom_eq (P : a ⟶ b) (Q : b ⟶ c) (S : c ⟶ d) :
    (α_ P Q S).hom = mkHom (α_ P.X Q.X S.X).hom (assoc_comm P Q S) := rfl

theorem associator_inv_eq (P : a ⟶ b) (Q : b ⟶ c) (S : c ⟶ d) :
    (α_ P Q S).inv = mkHom (α_ P.X Q.X S.X).inv (assoc_inv_comm P Q S) := rfl

theorem leftUnitor_hom_eq (P : a ⟶ b) : (λ_ P).hom = mkHom (λ_ P.X).hom (leftUnitor_comm P) := rfl

theorem leftUnitor_inv_eq (P : a ⟶ b) :
    (λ_ P).inv = mkHom (λ_ P.X).inv (leftUnitor_inv_comm P) := rfl

theorem rightUnitor_hom_eq (P : a ⟶ b) :
    (ρ_ P).hom = mkHom (ρ_ P.X).hom (rightUnitor_comm P) := rfl

theorem rightUnitor_inv_eq (P : a ⟶ b) :
    (ρ_ P).inv = mkHom (ρ_ P.X).inv (rightUnitor_inv_comm P) := rfl

theorem whiskerLeft_mkHom (P : a ⟶ b) {Q Q' : b ⟶ c} (φ : Q.X ⟶ Q'.X) (h : Q.p ≫ φ = φ ≫ Q'.p) :
    P ◁ mkHom φ h = mkHom (P.X ◁ φ) (by
      show hcomp₂ P.p Q.p ≫ P.X ◁ φ = P.X ◁ φ ≫ hcomp₂ P.p Q'.p
      rw [← hcomp₂_id_left P.X φ, ← hcomp₂_comp, ← hcomp₂_comp, h, Category.id_comp,
        Category.comp_id]) :=
  hcomp_id_mkHom' P φ h

theorem mkHom_whiskerRight {P P' : a ⟶ b} (φ : P.X ⟶ P'.X) (h : P.p ≫ φ = φ ≫ P'.p) (Q : b ⟶ c) :
    mkHom φ h ▷ Q = mkHom (φ ▷ Q.X) (by
      show hcomp₂ P.p Q.p ≫ φ ▷ Q.X = φ ▷ Q.X ≫ hcomp₂ P'.p Q.p
      rw [← hcomp₂_id_right φ, ← hcomp₂_comp, ← hcomp₂_comp, h, Category.id_comp,
        Category.comp_id]) :=
  hcomp_mkHom_id' φ h Q

end Basic

/-! ## Preadditive and linear structure -/

section Preadditive

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]

instance (a b : KarBicat B) : Preadditive (a ⟶ b) :=
  inferInstanceAs (Preadditive (Karoubi (a.obj ⟶ b.obj)))

variable {a b : KarBicat B}

@[simp] theorem add_f {P Q : a ⟶ b} (η θ : P ⟶ Q) : (η + θ).f = η.f + θ.f := rfl

@[simp] theorem neg_f {P Q : a ⟶ b} (η : P ⟶ Q) : (-η).f = -η.f := rfl

@[simp] theorem zero_f {P Q : a ⟶ b} : (0 : P ⟶ Q).f = 0 := rfl

variable [PreadditiveBicategory B]

instance instPreadditiveBicategory : PreadditiveBicategory (KarBicat B) where
  whiskerLeft_add P _ _ η θ := Idempotents.Karoubi.hom_ext _ _ (by
    simp [hcomp₂, PreadditiveBicategory.whiskerLeft_add, Preadditive.comp_add])
  add_whiskerRight η θ Q := Idempotents.Karoubi.hom_ext _ _ (by
    simp [hcomp₂, PreadditiveBicategory.add_whiskerRight, Preadditive.add_comp])

instance [∀ a b : B, Limits.HasFiniteBiproducts (a ⟶ b)] (a b : KarBicat B) :
    Limits.HasFiniteBiproducts (a ⟶ b) :=
  inferInstanceAs (Limits.HasFiniteBiproducts (Karoubi (a.obj ⟶ b.obj)))

instance [∀ a b : B, Limits.HasFiniteBiproducts (a ⟶ b)] (a b : KarBicat B) :
    Limits.HasBinaryBiproducts (a ⟶ b) :=
  inferInstanceAs (Limits.HasBinaryBiproducts (Karoubi (a.obj ⟶ b.obj)))

instance (a b : KarBicat B) : IsIdempotentComplete (a ⟶ b) :=
  inferInstanceAs (IsIdempotentComplete (Karoubi (a.obj ⟶ b.obj)))

variable {R : Type w₁} [CommRing R] [∀ a b : B, Linear R (a ⟶ b)] [LinearBicategory R B]

instance (a b : KarBicat B) : Linear R (a ⟶ b) :=
  inferInstanceAs (Linear R (Karoubi (a.obj ⟶ b.obj)))

omit [PreadditiveBicategory B] [LinearBicategory R B] in
@[simp] theorem smul_f {P Q : a ⟶ b} (r : R) (η : P ⟶ Q) : (r • η).f = r • η.f := rfl

instance instLinearBicategory : LinearBicategory R (KarBicat B) where
  whiskerLeft_smul P _ _ r η := Idempotents.Karoubi.hom_ext _ _ (by
    simp [hcomp₂, LinearBicategory.whiskerLeft_smul, Linear.comp_smul])
  smul_whiskerRight r η Q := Idempotents.Karoubi.hom_ext _ _ (by
    simp [hcomp₂, LinearBicategory.smul_whiskerRight, Linear.smul_comp])

end Preadditive

/-! ## Π-2-categories and `(Q, Π)`-2-categories -/

section Pi

variable {B : Type u} [Bicategory.{w, v} B] {a b c d : KarBicat B}

theorem braid_comm {q : b.obj ⟶ b.obj} {q' : a.obj ⟶ a.obj} (P : a ⟶ b)
    (e : ∀ f : a.obj ⟶ b.obj, f ≫ q ≅ q' ≫ f)
    (he : ∀ {f g : a.obj ⟶ b.obj} (η : f ⟶ g), (e f).hom ≫ q' ◁ η = η ▷ q ≫ (e g).hom) :
    (P ≫ of q).p ≫ (e P.X).hom = (e P.X).hom ≫ (of q' ≫ P).p := by
  show hcomp₂ P.p (𝟙 q) ≫ (e P.X).hom = (e P.X).hom ≫ hcomp₂ (𝟙 q') P.p
  rw [hcomp₂_id_right, hcomp₂_id_left, he]

/-- The isomorphism `P ≫ q ≅ q' ≫ P` of the idempotent completion determined by natural
isomorphisms `f ≫ q ≅ q' ≫ f` in `B` (for `q = π`, `q'` etc.). -/
def braidIso {q : b.obj ⟶ b.obj} {q' : a.obj ⟶ a.obj} (P : a ⟶ b)
    (e : ∀ f : a.obj ⟶ b.obj, f ≫ q ≅ q' ≫ f)
    (he : ∀ {f g : a.obj ⟶ b.obj} (η : f ⟶ g), (e f).hom ≫ q' ◁ η = η ▷ q ≫ (e g).hom) :
    P ≫ of q ≅ of q' ≫ P :=
  mkIso (e P.X) (braid_comm P e he)

theorem braidIso_hom {q : b.obj ⟶ b.obj} {q' : a.obj ⟶ a.obj} (P : a ⟶ b)
    (e : ∀ f : a.obj ⟶ b.obj, f ≫ q ≅ q' ≫ f)
    (he : ∀ {f g : a.obj ⟶ b.obj} (η : f ⟶ g), (e f).hom ≫ q' ◁ η = η ▷ q ≫ (e g).hom) :
    (braidIso P e he).hom = mkHom (e P.X).hom (braid_comm P e he) := rfl

theorem braidIso_inv {q : b.obj ⟶ b.obj} {q' : a.obj ⟶ a.obj} (P : a ⟶ b)
    (e : ∀ f : a.obj ⟶ b.obj, f ≫ q ≅ q' ≫ f)
    (he : ∀ {f g : a.obj ⟶ b.obj} (η : f ⟶ g), (e f).hom ≫ q' ◁ η = η ▷ q ≫ (e g).hom) :
    (braidIso P e he).inv =
      mkHom (e P.X).inv (comm_inv (P := P ≫ of q) (Q := of q' ≫ P) (e P.X) (braid_comm P e he)) :=
  rfl

/-- The naturality of `braidIso` with respect to 2-morphisms, from the naturality in `B`. -/
theorem braidIso_naturality {q : b.obj ⟶ b.obj} {q' : a.obj ⟶ a.obj}
    (e : ∀ f : a.obj ⟶ b.obj, f ≫ q ≅ q' ≫ f)
    (he : ∀ {f g : a.obj ⟶ b.obj} (η : f ⟶ g), (e f).hom ≫ q' ◁ η = η ▷ q ≫ (e g).hom)
    {P P' : a ⟶ b} (η : P ⟶ P') :
    (braidIso P e he).hom ≫ of q' ◁ η = η ▷ of q ≫ (braidIso P' e he).hom := by
  apply Idempotents.Karoubi.hom_ext
  rw [braidIso_hom, braidIso_hom, mkHom_comp_f, comp_mkHom_f, whiskerLeft_f, whiskerRight_f,
    comp_p, of_p, of_p]
  simp only [hcomp₂, Bicategory.id_whiskerRight, Category.id_comp, Bicategory.whiskerLeft_id,
    Category.comp_id]
  conv_lhs => rw [← Idempotents.Karoubi.comp_p η]
  rw [Bicategory.whiskerLeft_comp, ← Category.assoc, he, Category.assoc]

theorem unit_comm {q q' : a.obj ⟶ a.obj} (e : q ≫ q' ≅ 𝟙 a.obj) :
    (of q ≫ of q').p ≫ e.hom = e.hom ≫ (𝟙 a : a ⟶ a).p := by
  show hcomp₂ (𝟙 q) (𝟙 q') ≫ e.hom = e.hom ≫ 𝟙 (𝟙 a.obj)
  rw [hcomp₂_id_id, Category.id_comp, Category.comp_id]

/-- The isomorphism `of q ≫ of q' ≅ 𝟙 a` determined by `q ≫ q' ≅ 𝟙`. -/
def unitIso {q q' : a.obj ⟶ a.obj} (e : q ≫ q' ≅ 𝟙 a.obj) : of q ≫ of q' ≅ 𝟙 a :=
  mkIso e (unit_comm e)

theorem unitIso_hom {q q' : a.obj ⟶ a.obj} (e : q ≫ q' ≅ 𝟙 a.obj) :
    (unitIso e).hom = mkHom e.hom (unit_comm e) := rfl

theorem unitIso_inv {q q' : a.obj ⟶ a.obj} (e : q ≫ q' ≅ 𝟙 a.obj) :
    (unitIso e).inv = mkHom e.inv (comm_inv (P := of q ≫ of q') (Q := 𝟙 a) e (unit_comm e)) :=
  rfl

end Pi

section PiInstance

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [PreadditiveBicategory B] {R : Type w₁} [CommRing R] [∀ a b : B, Linear R (a ⟶ b)]
  [LinearBicategory R B] [PiTwoCategory R B] {a b c d : KarBicat B}

local notation "𝛑" => PiTwoCategory.pi (R := R)
local notation "𝛃" => PiTwoCategory.β (R := R)
local notation "𝛏" => PiTwoCategory.ξ (R := R)

/-- The isomorphism `β_P : P ≫ π_b ≅ π_a ≫ P` of the idempotent completion. -/
def βIso (P : a ⟶ b) : P ≫ of (𝛑 b.obj) ≅ of (𝛑 a.obj) ≫ P :=
  braidIso P 𝛃 (fun η => PiTwoCategory.β_naturality η)

theorem βIso_hom (P : a ⟶ b) :
    (βIso P).hom = mkHom (𝛃 P.X).hom (braid_comm P 𝛃 (fun η => PiTwoCategory.β_naturality η)) :=
  rfl

theorem βIso_inv (P : a ⟶ b) :
    (βIso P).inv = mkHom (𝛃 P.X).inv (comm_inv (P := P ≫ of (𝛑 b.obj)) (Q := of (𝛑 a.obj) ≫ P)
      (𝛃 P.X) (braid_comm P 𝛃 (fun η => PiTwoCategory.β_naturality η))) := rfl

theorem βIso_naturality {P P' : a ⟶ b} (η : P ⟶ P') :
    (βIso P).hom ≫ of (𝛑 a.obj) ◁ η = η ▷ of (𝛑 b.obj) ≫ (βIso P').hom :=
  braidIso_naturality 𝛃 (fun η => PiTwoCategory.β_naturality η) η

theorem βIso_comp (P : a ⟶ b) (Q : b ⟶ c) :
    (βIso (P ≫ Q)).hom = (α_ P Q (of (𝛑 c.obj))).hom ≫ P ◁ (βIso Q).hom ≫
      (α_ P (of (𝛑 b.obj)) Q).inv ≫ (βIso P).hom ▷ Q ≫ (α_ (of (𝛑 a.obj)) P Q).hom := by
  simp only [βIso_hom, associator_hom_eq, associator_inv_eq, whiskerLeft_mkHom,
    mkHom_whiskerRight]
  rw [mkHom_comp_mkHom, mkHom_comp_mkHom, mkHom_comp_mkHom, mkHom_comp_mkHom]
  refine mkHom_congr _ _ ?_
  exact PiTwoCategory.β_comp (R := R) P.X Q.X

theorem βIso_id (a : KarBicat B) :
    (βIso (𝟙 a)).hom = (λ_ (of (𝛑 a.obj))).hom ≫ (ρ_ (of (𝛑 a.obj))).inv := by
  simp only [βIso_hom, leftUnitor_hom_eq, rightUnitor_inv_eq]
  rw [mkHom_comp_mkHom]
  refine mkHom_congr _ _ ?_
  exact PiTwoCategory.β_id (R := R) a.obj

theorem βIso_pi (a : KarBicat B) : (βIso (of (𝛑 a.obj))).hom = -𝟙 _ := by
  apply Idempotents.Karoubi.hom_ext
  rw [βIso_hom, mkHom_f, neg_f, id_f]
  simp only [comp_p, comp_X, of_p, of_X, hcomp₂_id_id, Category.comp_id]
  exact PiTwoCategory.β_pi (R := R) a.obj

theorem ξ_comm_aux (P : a ⟶ b) :
    P ◁ (unitIso (𝛏 b.obj)).hom ≫ (ρ_ P).hom ≫ (λ_ P).inv ≫ (unitIso (𝛏 a.obj)).inv ▷ P =
      (α_ P (of (𝛑 b.obj)) (of (𝛑 b.obj))).inv ≫ (βIso P).hom ▷ of (𝛑 b.obj) ≫
        (α_ (of (𝛑 a.obj)) P (of (𝛑 b.obj))).hom ≫ of (𝛑 a.obj) ◁ (βIso P).hom ≫
        (α_ (of (𝛑 a.obj)) (of (𝛑 a.obj)) P).inv := by
  simp only [βIso_hom, unitIso_hom, unitIso_inv, associator_hom_eq, associator_inv_eq,
    leftUnitor_inv_eq, rightUnitor_hom_eq, whiskerLeft_mkHom, mkHom_whiskerRight]
  rw [mkHom_comp_mkHom, mkHom_comp_mkHom, mkHom_comp_mkHom, mkHom_comp_mkHom, mkHom_comp_mkHom,
    mkHom_comp_mkHom, mkHom_comp_mkHom]
  refine mkHom_congr _ _ ?_
  exact PiTwoCategory.ξ_comm (R := R) P.X

/-- **Brundan–Ellis, §6.** The idempotent completion of a Π-2-category is a Π-2-category, with
`π_λ` the image of `π_λ` and `β`, `ξ` composed with the idempotents. -/
instance instPiTwoCategory : PiTwoCategory R (KarBicat B) where
  pi a := of (𝛑 a.obj)
  β P := βIso P
  β_naturality η := βIso_naturality η
  β_comp P Q := βIso_comp P Q
  β_id a := βIso_id a
  β_pi a := βIso_pi a
  ξ a := unitIso (𝛏 a.obj)
  ξ_comm P := ξ_comm_aux P

@[simp] theorem pi_eq (a : KarBicat B) : 𝛑 a = of (𝛑 a.obj) := rfl

theorem β_eq (P : a ⟶ b) : 𝛃 P = βIso P := rfl

theorem β_hom_eq (P : a ⟶ b) :
    (𝛃 P).hom = mkHom (𝛃 P.X).hom (braid_comm P 𝛃 (fun η => PiTwoCategory.β_naturality η)) := rfl

theorem β_inv_eq (P : a ⟶ b) :
    (𝛃 P).inv = mkHom (𝛃 P.X).inv (comm_inv (P := P ≫ of (𝛑 b.obj)) (Q := of (𝛑 a.obj) ≫ P)
      (𝛃 P.X) (braid_comm P 𝛃 (fun η => PiTwoCategory.β_naturality η))) := rfl

theorem ξ_eq (a : KarBicat B) : 𝛏 a = unitIso (𝛏 a.obj) := rfl

theorem ξ_hom_eq (a : KarBicat B) : (𝛏 a).hom = mkHom (𝛏 a.obj).hom (unit_comm (𝛏 a.obj)) := rfl

end PiInstance

section QPiInstance

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [PreadditiveBicategory B] {R : Type w₁} [CommRing R] [∀ a b : B, Linear R (a ⟶ b)]
  [LinearBicategory R B] [QPiTwoCategory R B] {a b c d : KarBicat B}

local notation "𝛑" => PiTwoCategory.pi (R := R)
local notation "𝛃" => PiTwoCategory.β (R := R)
local notation "𝐪" => QPiTwoCategory.q (R := R)
local notation "𝐪⁻¹" => QPiTwoCategory.qinv (R := R)
local notation "𝛄" => QPiTwoCategory.γ (R := R)

/-- The isomorphism `γ_P : P ≫ q_b ≅ q_a ≫ P` of the idempotent completion. -/
def γIso (P : a ⟶ b) : P ≫ of (𝐪 b.obj) ≅ of (𝐪 a.obj) ≫ P :=
  braidIso P 𝛄 (fun η => QPiTwoCategory.γ_naturality η)

theorem γIso_hom (P : a ⟶ b) :
    (γIso P).hom = mkHom (𝛄 P.X).hom (braid_comm P 𝛄 (fun η => QPiTwoCategory.γ_naturality η)) :=
  rfl

theorem γIso_naturality {P P' : a ⟶ b} (η : P ⟶ P') :
    (γIso P).hom ≫ of (𝐪 a.obj) ◁ η = η ▷ of (𝐪 b.obj) ≫ (γIso P').hom :=
  braidIso_naturality 𝛄 (fun η => QPiTwoCategory.γ_naturality η) η

theorem γIso_comp (P : a ⟶ b) (Q : b ⟶ c) :
    (γIso (P ≫ Q)).hom = (α_ P Q (of (𝐪 c.obj))).hom ≫ P ◁ (γIso Q).hom ≫
      (α_ P (of (𝐪 b.obj)) Q).inv ≫ (γIso P).hom ▷ Q ≫ (α_ (of (𝐪 a.obj)) P Q).hom := by
  simp only [γIso_hom, associator_hom_eq, associator_inv_eq, whiskerLeft_mkHom,
    mkHom_whiskerRight]
  rw [mkHom_comp_mkHom, mkHom_comp_mkHom, mkHom_comp_mkHom, mkHom_comp_mkHom]
  refine mkHom_congr _ _ ?_
  exact QPiTwoCategory.γ_comp (R := R) P.X Q.X

theorem γIso_id (a : KarBicat B) :
    (γIso (𝟙 a)).hom = (λ_ (of (𝐪 a.obj))).hom ≫ (ρ_ (of (𝐪 a.obj))).inv := by
  simp only [γIso_hom, leftUnitor_hom_eq, rightUnitor_inv_eq]
  rw [mkHom_comp_mkHom]
  refine mkHom_congr _ _ ?_
  exact QPiTwoCategory.γ_id (R := R) a.obj

theorem γIso_q (a : KarBicat B) : (γIso (of (𝐪 a.obj))).hom = 𝟙 _ := by
  rw [γIso_hom, id_eq_mkHom]
  refine mkHom_congr _ _ ?_
  exact QPiTwoCategory.γ_q (R := R) a.obj

theorem γIso_pi (a : KarBicat B) : (γIso (of (𝛑 a.obj))).hom = (βIso (of (𝐪 a.obj))).inv := by
  rw [γIso_hom, βIso_inv]
  refine mkHom_congr _ _ ?_
  exact QPiTwoCategory.γ_pi (R := R) a.obj

theorem q_ii_aux (a : KarBicat B) :
    (unitIso (QPiTwoCategory.ii (R := R) a.obj)).hom ▷ of (𝐪 a.obj) ≫ (λ_ (of (𝐪 a.obj))).hom =
      (α_ (of (𝐪 a.obj)) (of (𝐪⁻¹ a.obj)) (of (𝐪 a.obj))).hom ≫
        of (𝐪 a.obj) ◁ (unitIso (QPiTwoCategory.jj (R := R) a.obj)).hom ≫
        (ρ_ (of (𝐪 a.obj))).hom := by
  simp only [unitIso_hom, associator_hom_eq, leftUnitor_hom_eq, rightUnitor_hom_eq,
    whiskerLeft_mkHom, mkHom_whiskerRight]
  rw [mkHom_comp_mkHom, mkHom_comp_mkHom, mkHom_comp_mkHom]
  refine mkHom_congr _ _ ?_
  exact QPiTwoCategory.q_ii (R := R) a.obj

theorem ii_qinv_aux (a : KarBicat B) :
    of (𝐪⁻¹ a.obj) ◁ (unitIso (QPiTwoCategory.ii (R := R) a.obj)).hom ≫
        (ρ_ (of (𝐪⁻¹ a.obj))).hom =
      (α_ (of (𝐪⁻¹ a.obj)) (of (𝐪 a.obj)) (of (𝐪⁻¹ a.obj))).inv ≫
        (unitIso (QPiTwoCategory.jj (R := R) a.obj)).hom ▷ of (𝐪⁻¹ a.obj) ≫
        (λ_ (of (𝐪⁻¹ a.obj))).hom := by
  simp only [unitIso_hom, associator_inv_eq, leftUnitor_hom_eq, rightUnitor_hom_eq,
    whiskerLeft_mkHom, mkHom_whiskerRight]
  rw [mkHom_comp_mkHom, mkHom_comp_mkHom, mkHom_comp_mkHom]
  refine mkHom_congr _ _ ?_
  exact QPiTwoCategory.ii_qinv (R := R) a.obj

/-- **Brundan–Ellis, §6.** The idempotent completion of a `(Q, Π)`-2-category is a
`(Q, Π)`-2-category, with `q_λ`, `q_λ⁻¹` the images of those of `B` and `γ`, `ii`, `jj` composed
with the idempotents. -/
instance instQPiTwoCategory : QPiTwoCategory R (KarBicat B) where
  q a := of (𝐪 a.obj)
  qinv a := of (𝐪⁻¹ a.obj)
  γ P := γIso P
  γ_naturality η := γIso_naturality η
  γ_comp P Q := γIso_comp P Q
  γ_id a := γIso_id a
  γ_q a := γIso_q a
  γ_pi a := γIso_pi a
  ii a := unitIso (QPiTwoCategory.ii (R := R) a.obj)
  jj a := unitIso (QPiTwoCategory.jj (R := R) a.obj)
  q_ii a := q_ii_aux a
  ii_qinv a := ii_qinv_aux a

@[simp] theorem q_eq (a : KarBicat B) : 𝐪 a = of (𝐪 a.obj) := rfl

@[simp] theorem qinv_eq (a : KarBicat B) : 𝐪⁻¹ a = of (𝐪⁻¹ a.obj) := rfl

theorem γ_eq (P : a ⟶ b) : 𝛄 P = γIso P := rfl

theorem γ_hom_eq (P : a ⟶ b) :
    (𝛄 P).hom = mkHom (𝛄 P.X).hom (braid_comm P 𝛄 (fun η => QPiTwoCategory.γ_naturality η)) :=
  rfl

theorem ii_eq (a : KarBicat B) :
    QPiTwoCategory.ii (R := R) a = unitIso (QPiTwoCategory.ii (R := R) a.obj) := rfl

theorem jj_eq (a : KarBicat B) :
    QPiTwoCategory.jj (R := R) a = unitIso (QPiTwoCategory.jj (R := R) a.obj) := rfl

end QPiInstance


end KarBicat

end StringDiagrams

end
