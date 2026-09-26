import StringDiagrams.Super.TwoHom
import StringDiagrams.Super.UnderlyingBicategory
import StringDiagrams.Super.Strictification
import Mathlib.Tactic.CategoryTheory.Coherence

/-!
# Strictification of 2-supercategories

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, Section 2
(after Definition 2.2): "The Coherence Theorem for 2-supercategories implies that any
2-supercategory is 2-superequivalent to a strict 2-supercategory. The proof can be obtained by
mimicking the argument in the purely even case".

## The construction

This is the hom-wise version of the strictification of monoidal supercategories
(`StringDiagrams.Super.Strictification`), a Yoneda-type construction. For a 2-supercategory
`𝔄` (1-morphisms composed in diagrammatic order, `f ≫ g` is the paper's `gf`), the strict
2-supercategory `TwoStrictification R 𝔄` has:

* the objects of `𝔄`;
* as 1-morphisms `a → b` the *right `𝔄`-module families* (`TwoStrictification.Hom1`):
  superfunctors `F_c : ℋom(c, a) → ℋom(c, b)` for all objects `c`, with even natural
  isomorphisms `γ_{h,u} : h ≫ F_c(u) ≅ F_d(h ≫ u)` for `h : d → c` (compatibility with
  precomposition) satisfying an associativity axiom (`Hom1.γ_assoc`); composition is
  composition of the families, which is strictly associative and unital;
* as 2-morphisms `F ⇒ G` the families of supernatural transformations `θ_c : F_c ⇒ G_c` (of
  either parity) such that each homogeneous component satisfies
  `γ^F_{h,u} ≫ θ_d(h ≫ u) = (h ◁ θ_c(u)) ≫ γ^G_{h,u}`.

*Sign conventions.* As in the monoidal case, the compatibility condition only whiskers
`θ` by a 1-morphism, so it carries no Koszul sign for either parity; the super interchange law
enters through the supernaturality of the families `u ◁ η : u ≫ f ⇒ u ≫ f'` attached to a
2-morphism `η : f ⇒ f'` of `𝔄`.

## Main results

* `TwoStrictification.instTwoSupercategory`, `TwoStrictification.instStrict`: a strict
  2-supercategory (Definition 2.1).
* `TwoStrictification.yoneda : TwoSuperfunctor R 𝔄 (TwoStrictification R 𝔄)`: the identity on
  objects, `f ↦ (- ≫ f)` with `γ = a⁻¹`, `η ↦ (- ◁ η)`; a (non-strict) 2-superfunctor
  (Definition 2.2(ii)).
* `TwoStrictification.yoneda_isLocalTwoSuperequivalence`: `yoneda` is a superequivalence on
  each morphism supercategory (fully faithful: `θ = - ◁ (l_{f'} ∘ θ_a(1_a) ∘ l_f⁻¹)`; evenly
  dense: `F ≅ - ≫ F_a(1_a)` via `F(r) ∘ γ_{-,1}`) and bijective on objects.
* **Coherence theorem** (`TwoSupercategory.exists_strict_localTwoSuperequivalent`): every
  2-supercategory is 2-superequivalent to a strict 2-supercategory, in the second formulation
  of 2-superequivalence of Definition 2.2 (`TwoSuperfunctor.IsLocalTwoSuperequivalence`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory BicategoryStruct TwoSupercategory

universe w w₁ v₁ u₁

variable (R : Type w) [CommRing R] (B : Type u₁) [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]

/-- The strictification of a 2-supercategory `𝔄`: it has the objects of `𝔄`. See the module
documentation. -/
@[ext]
structure TwoStrictification (R : Type w) (B : Type u₁) where
  /-- The underlying object of `𝔄`. -/
  as : B

namespace TwoStrictification

variable {R B}

/-- A 1-morphism `a → b` of the strictification: a right `𝔄`-module family of superfunctors
`F_c : ℋom(c, a) → ℋom(c, b)`, with even natural isomorphisms
`γ_{h,u} : h ≫ F_c(u) ≅ F_d(h ≫ u)` compatible with the associator. -/
structure Hom1 (a b : TwoStrictification R B) where
  /-- The superfunctors `F_c : ℋom(c, a) → ℋom(c, b)`. -/
  F : ∀ c : B, (c ⟶ a.as) ⥤ (c ⟶ b.as)
  [additive : ∀ c, (F c).Additive]
  [linear : ∀ c, (F c).Linear R]
  [isSuperfunctor : ∀ c, IsSuperfunctor R (F c)]
  /-- The module structure `γ_{h,u} : h ≫ F_c(u) ≅ F_d(h ≫ u)`. -/
  γ : ∀ {c d : B} (h : d ⟶ c) (u : c ⟶ a.as), h ≫ (F c).obj u ≅ (F d).obj (h ≫ u)
  γ_mem : ∀ {c d : B} (h : d ⟶ c) (u : c ⟶ a.as), (γ h u).hom ∈ parity (R := R) _ _ 0
  γ_naturality_left : ∀ {c d : B} {h h' : d ⟶ c} (η : h ⟶ h') (u : c ⟶ a.as),
    η ▷ (F c).obj u ≫ (γ h' u).hom = (γ h u).hom ≫ (F d).map (η ▷ u)
  γ_naturality_right : ∀ {c d : B} (h : d ⟶ c) {u u' : c ⟶ a.as} (θ : u ⟶ u'),
    h ◁ (F c).map θ ≫ (γ h u').hom = (γ h u).hom ≫ (F d).map (h ◁ θ)
  γ_assoc : ∀ {c d e : B} (k : e ⟶ d) (h : d ⟶ c) (u : c ⟶ a.as),
    (associator k h ((F c).obj u)).hom ≫ k ◁ (γ h u).hom ≫ (γ k (h ≫ u)).hom =
      (γ (k ≫ h) u).hom ≫ (F e).map (associator k h u).hom

namespace Hom1

attribute [instance] additive linear isSuperfunctor
attribute [reassoc] γ_naturality_left γ_naturality_right γ_assoc

variable {a b : TwoStrictification R B}

/-- The component `F_c`, as a bundled superfunctor. -/
abbrev sf (F : Hom1 a b) (c : B) : Superfunctor R (c ⟶ a.as) (c ⟶ b.as) := ⟨F.F c⟩

omit [TwoSupercategory R B] in
theorem ext_of_heq {F G : Hom1 a b} (h : F.F = G.F)
    (hγ : ∀ {c d : B} (k : d ⟶ c) (u : c ⟶ a.as), HEq (F.γ k u).hom (G.γ k u).hom) : F = G := by
  obtain ⟨F, γ, _, _, _, _⟩ := F
  obtain ⟨G, γ', _, _, _, _⟩ := G
  obtain rfl : F = G := h
  have : @γ = @γ' := by
    funext c d k u
    exact Iso.ext (eq_of_heq (hγ k u))
  subst this
  rfl

/-! ### 2-morphisms -/

/-- The families of supernatural transformations compatible with the module structures. -/
def homSubmodule (F G : Hom1 a b) : Submodule R (∀ c : B, F.sf c ⟶ G.sf c) where
  carrier := {θ | ∀ (p : ZMod 2) {c d : B} (h : d ⟶ c) (u : c ⟶ a.as),
    (F.γ h u).hom ≫ (θ d).app p (h ≫ u) = h ◁ (θ c).app p u ≫ (G.γ h u).hom}
  add_mem' {θ θ'} hθ hθ' p c d h u := by
    simp only [Pi.add_apply, Superfunctor.add_app, Preadditive.comp_add, hθ p h u, hθ' p h u,
      TwoSupercategory.whiskerLeft_add (R := R), Preadditive.add_comp]
  zero_mem' p c d h u := by
    simp [TwoSupercategory.whiskerLeft_zero R]
  smul_mem' r θ hθ p c d h u := by
    simp only [Pi.smul_apply, Superfunctor.smul_app, Linear.comp_smul, hθ p h u,
      TwoSupercategory.whiskerLeft_smul (R := R), Linear.smul_comp]

theorem id_mem_homSubmodule (F : Hom1 a b) : (fun c => 𝟙 (F.sf c)) ∈ homSubmodule F F := by
  intro p c d h u
  rcases parity_eq_zero_or_one p with rfl | rfl
  · simp [TwoSupercategory.whiskerLeft_id (R := R)]
  · simp [TwoSupercategory.whiskerLeft_zero R]

theorem comp_mem_homSubmodule {F G H : Hom1 a b} {θ : ∀ c, F.sf c ⟶ G.sf c}
    {θ' : ∀ c, G.sf c ⟶ H.sf c} (hθ : θ ∈ homSubmodule F G) (hθ' : θ' ∈ homSubmodule G H) :
    (fun c => θ c ≫ θ' c) ∈ homSubmodule F H := by
  intro r c d h u
  simp only [Superfunctor.comp_app, Preadditive.comp_add, Preadditive.add_comp,
    TwoSupercategory.whiskerLeft_add (R := R), TwoSupercategory.whiskerLeft_comp (R := R),
    Category.assoc]
  rw [reassoc_of% (hθ 0 h u), reassoc_of% (hθ 1 h u), hθ' r h u, hθ' (r + 1) h u]

theorem proj_mem_homSubmodule {F G : Hom1 a b} (p : ZMod 2) {θ : ∀ c, F.sf c ⟶ G.sf c}
    (hθ : θ ∈ homSubmodule F G) : (fun c => proj R p (θ c)) ∈ homSubmodule F G := by
  intro q c d h u
  simp only [Superfunctor.proj_app]
  split_ifs with hq
  · subst hq; exact hθ q h u
  · simp [TwoSupercategory.whiskerLeft_zero R]

instance (a b : TwoStrictification R B) : Category (Hom1 a b) where
  Hom F G := homSubmodule F G
  id F := ⟨fun c => 𝟙 (F.sf c), id_mem_homSubmodule F⟩
  comp θ θ' := ⟨fun c => θ.1 c ≫ θ'.1 c, comp_mem_homSubmodule θ.2 θ'.2⟩
  id_comp θ := Subtype.ext (funext fun c => Category.id_comp (θ.1 c))
  comp_id θ := Subtype.ext (funext fun c => Category.comp_id (θ.1 c))
  assoc θ θ' θ'' := Subtype.ext (funext fun c => Category.assoc (θ.1 c) (θ'.1 c) (θ''.1 c))

theorem hom2_ext {F G : Hom1 a b} {θ θ' : F ⟶ G} (h : ∀ c, θ.1 c = θ'.1 c) : θ = θ' :=
  Subtype.ext (funext h)

@[simp] theorem id2_val (F : Hom1 a b) (c : B) : (𝟙 F : F ⟶ F).1 c = 𝟙 (F.sf c) := rfl

@[simp] theorem comp2_val {F G H : Hom1 a b} (θ : F ⟶ G) (θ' : G ⟶ H) (c : B) :
    (θ ≫ θ').1 c = θ.1 c ≫ θ'.1 c := rfl

theorem hom2_compat {F G : Hom1 a b} (θ : F ⟶ G) (p : ZMod 2) {c d : B} (h : d ⟶ c)
    (u : c ⟶ a.as) :
    (F.γ h u).hom ≫ (θ.1 d).app p (h ≫ u) = h ◁ (θ.1 c).app p u ≫ (G.γ h u).hom :=
  θ.2 p h u

instance (a b : TwoStrictification R B) : Preadditive (Hom1 a b) where
  homGroup F G := inferInstanceAs (AddCommGroup (homSubmodule F G))
  add_comp _ _ _ θ θ' η := hom2_ext fun c =>
    show (θ.1 c + θ'.1 c) ≫ η.1 c = θ.1 c ≫ η.1 c + θ'.1 c ≫ η.1 c from
      Preadditive.add_comp _ _ _ _ _ _
  comp_add _ _ _ θ η η' := hom2_ext fun c =>
    show θ.1 c ≫ (η.1 c + η'.1 c) = θ.1 c ≫ η.1 c + θ.1 c ≫ η'.1 c from
      Preadditive.comp_add _ _ _ _ _ _

instance (a b : TwoStrictification R B) : Linear R (Hom1 a b) where
  homModule F G := inferInstanceAs (Module R (homSubmodule F G))
  smul_comp _ _ _ r θ η := hom2_ext fun c =>
    show (r • θ.1 c) ≫ η.1 c = r • (θ.1 c ≫ η.1 c) from Linear.smul_comp _ _ _ _ _ _
  comp_smul _ _ _ θ r η := hom2_ext fun c =>
    show θ.1 c ≫ (r • η.1 c) = r • (θ.1 c ≫ η.1 c) from Linear.comp_smul _ _ _ _ _ _

@[simp] theorem add2_val {F G : Hom1 a b} (θ θ' : F ⟶ G) (c : B) :
    (θ + θ').1 c = θ.1 c + θ'.1 c := rfl

@[simp] theorem zero2_val {F G : Hom1 a b} (c : B) : (0 : F ⟶ G).1 c = 0 := rfl

@[simp] theorem smul2_val {F G : Hom1 a b} (r : R) (θ : F ⟶ G) (c : B) :
    (r • θ).1 c = r • θ.1 c := rfl

@[simp] theorem zsmul2_val {F G : Hom1 a b} (n : ℤ) (θ : F ⟶ G) (c : B) :
    (n • θ).1 c = n • θ.1 c := rfl

/-- The 2-morphisms of parity `p`: all components have parity `p`. -/
def parityHom (F G : Hom1 a b) (p : ZMod 2) : Submodule R (F ⟶ G) where
  carrier := {θ | ∀ c, θ.1 c ∈ parity (R := R) (F.sf c) (G.sf c) p}
  add_mem' hθ hθ' c := Submodule.add_mem _ (hθ c) (hθ' c)
  zero_mem' _ := Submodule.zero_mem _
  smul_mem' r _ hθ c := Submodule.smul_mem _ r (hθ c)

instance (a b : TwoStrictification R B) : Supercategory R (Hom1 a b) where
  parity := parityHom
  isInternal F G := by
    rw [DirectSum.isInternal_submodule_iff_isCompl _ (i := 0) (j := 1) (by decide)
      (by ext p; rcases parity_eq_zero_or_one p with rfl | rfl <;> simp)]
    constructor
    · rw [Submodule.disjoint_def]
      intro θ h0 h1
      refine hom2_ext fun c => ?_
      have h0' := (Superfunctor.mem_parity_iff (p := 0)).1 (h0 c)
      have h1' := (Superfunctor.mem_parity_iff (p := 1)).1 (h1 c)
      exact Superfunctor.hom_ext_parity (fun X => by simpa using congrFun h1' X)
        (fun X => by simpa using congrFun h0' X)
    · rw [codisjoint_iff, eq_top_iff]
      intro θ _
      have e : θ = ⟨fun c => proj R 0 (θ.1 c), proj_mem_homSubmodule 0 θ.2⟩ +
          ⟨fun c => proj R 1 (θ.1 c), proj_mem_homSubmodule 1 θ.2⟩ :=
        hom2_ext fun c => (proj_add_proj (R := R) (θ.1 c)).symm
      rw [e]
      exact Submodule.add_mem_sup (fun c => proj_mem (R := R) 0 (θ.1 c))
        (fun c => proj_mem (R := R) 1 (θ.1 c))
  id_mem F c := id_mem (R := R) (F.sf c)
  comp_mem hθ hθ' c := comp_mem (R := R) (hθ c) (hθ' c)

theorem mem_parity_iff {F G : Hom1 a b} {p : ZMod 2} {θ : F ⟶ G} :
    θ ∈ parity (R := R) F G p ↔ ∀ c, θ.1 c ∈ parity (R := R) (F.sf c) (G.sf c) p := Iff.rfl

end Hom1

/-! ## The strict 2-supercategory structure -/

/-- The identity 1-morphism: the identity superfunctors, with `γ = 1`. -/
@[simps]
def id1 (a : TwoStrictification R B) : Hom1 a a where
  F c := 𝟭 _
  γ h u := Iso.refl _
  γ_mem h u := id_mem _
  γ_naturality_left η u := by simp
  γ_naturality_right h {_ _} θ := by simp
  γ_assoc k h u := by simp [TwoSupercategory.whiskerLeft_id (R := R)]

/-- Composition of 1-morphisms: `(F ≫ G)_c = G_c ∘ F_c`, with
`γ^{F ≫ G}_{h,u} = G(γ^F_{h,u}) ∘ γ^G_{h,F u}`. -/
@[simps]
def comp1 {a b c : TwoStrictification R B} (F : Hom1 a b) (G : Hom1 b c) : Hom1 a c where
  F e := F.F e ⋙ G.F e
  γ h u := G.γ h ((F.F _).obj u) ≪≫ (G.F _).mapIso (F.γ h u)
  γ_mem h u := by simpa using comp_mem (G.γ_mem h _) (map_mem (G.F _) (F.γ_mem h u))
  γ_naturality_left η u := by
    simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.comp_map, Functor.comp_obj,
      Category.assoc]
    rw [G.γ_naturality_left_assoc, ← Functor.map_comp, ← Functor.map_comp,
      F.γ_naturality_left]
  γ_naturality_right {_ _} h {_ _} θ := by
    simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.comp_map, Functor.comp_obj,
      Category.assoc]
    rw [G.γ_naturality_right_assoc, ← Functor.map_comp, ← Functor.map_comp,
      F.γ_naturality_right]
  γ_assoc k h u := by
    simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.comp_map, Functor.comp_obj,
      Category.assoc, TwoSupercategory.whiskerLeft_comp (R := R)]
    rw [G.γ_naturality_right_assoc, G.γ_assoc_assoc, ← Functor.map_comp, ← Functor.map_comp,
      F.γ_assoc, Functor.map_comp]

/-- `F ◁ η := η_{F -}`. -/
def whiskerLeft2 {a b c : TwoStrictification R B} (F : Hom1 a b) {G H : Hom1 b c}
    (η : G ⟶ H) : comp1 F G ⟶ comp1 F H :=
  ⟨fun e => Superfunctor.whiskerLeft (F.sf e) (η.1 e), fun p d e h u => by
    simp only [comp1_γ, Iso.trans_hom, Functor.mapIso_hom, Superfunctor.whiskerLeft_app,
      Superfunctor.obj, Category.assoc]
    have hn := (η.1 e).naturality p (F.γ h u).hom (F.γ_mem h u)
    rw [koszulSign_zero_right, one_smul] at hn
    erw [hn]
    rw [← Category.assoc, Hom1.hom2_compat, Category.assoc]⟩

/-- `η ▷ H := H(η_-)`. -/
def whiskerRight2 {a b c : TwoStrictification R B} {F G : Hom1 a b} (η : F ⟶ G)
    (H : Hom1 b c) : comp1 F H ⟶ comp1 G H :=
  ⟨fun e => Superfunctor.whiskerRight (η.1 e) (H.sf e), fun p d e h u => by
    simp only [comp1_γ, Iso.trans_hom, Functor.mapIso_hom, Superfunctor.whiskerRight_app,
      Superfunctor.map, Category.assoc]
    rw [← Functor.map_comp, Hom1.hom2_compat, Functor.map_comp, ← H.γ_naturality_right_assoc]⟩

theorem comp1_assoc {a b c d : TwoStrictification R B} (F : Hom1 a b) (G : Hom1 b c)
    (H : Hom1 c d) : comp1 (comp1 F G) H = comp1 F (comp1 G H) :=
  Hom1.ext_of_heq rfl fun k u => heq_of_eq (by simp [Functor.map_comp])

theorem id1_comp {a b : TwoStrictification R B} (F : Hom1 a b) : comp1 (id1 a) F = F :=
  Hom1.ext_of_heq rfl fun k u => heq_of_eq (by simp)

theorem comp1_id {a b : TwoStrictification R B} (F : Hom1 a b) : comp1 F (id1 b) = F :=
  Hom1.ext_of_heq rfl fun k u => heq_of_eq (by simp)

instance instBicategoryStruct :
    BicategoryStruct.{max u₁ v₁ w₁, max u₁ v₁ w₁} (TwoStrictification R B) where
  Hom := Hom1
  id := id1
  comp := comp1
  homCategory _ _ := inferInstance
  whiskerLeft := whiskerLeft2
  whiskerRight := whiskerRight2
  associator F G H := eqToIso (comp1_assoc F G H)
  leftUnitor F := eqToIso (id1_comp F)
  rightUnitor F := eqToIso (comp1_id F)

instance (a b : TwoStrictification R B) : Preadditive (a ⟶ b) :=
  inferInstanceAs (Preadditive (Hom1 a b))

instance (a b : TwoStrictification R B) : Linear R (a ⟶ b) :=
  inferInstanceAs (Linear R (Hom1 a b))

instance (a b : TwoStrictification R B) : Supercategory R (a ⟶ b) :=
  inferInstanceAs (Supercategory R (Hom1 a b))

section Val

variable {a b c : TwoStrictification R B}

@[simp] theorem comp2_val' {F G H : a ⟶ b} (θ : F ⟶ G) (θ' : G ⟶ H) (e : B) :
    (θ ≫ θ').1 e = θ.1 e ≫ θ'.1 e := rfl

@[simp] theorem id2_val' (F : a ⟶ b) (e : B) : (𝟙 F : F ⟶ F).1 e = 𝟙 (Hom1.sf F e) := rfl

@[simp] theorem comp_F (F : a ⟶ b) (G : b ⟶ c) (e : B) :
    Hom1.F (F ≫ G) e = Hom1.F F e ⋙ Hom1.F G e := rfl

@[simp] theorem id_F (e : B) : Hom1.F (𝟙 a) e = 𝟭 _ := rfl

@[simp] theorem comp_γ_hom (F : a ⟶ b) (G : b ⟶ c) {d e : B} (h : e ⟶ d) (u : d ⟶ a.as) :
    (Hom1.γ (F ≫ G) h u).hom =
      (Hom1.γ G h ((Hom1.F F d).obj u)).hom ≫ (Hom1.F G e).map (Hom1.γ F h u).hom := rfl

@[simp] theorem id_γ_hom {d e : B} (h : e ⟶ d) (u : d ⟶ a.as) :
    (Hom1.γ (𝟙 a) h u).hom = 𝟙 _ := rfl

@[simp] theorem whiskerLeft_val (F : a ⟶ b) {G H : b ⟶ c} (η : G ⟶ H) (e : B) :
    (F ◁ η).1 e = Superfunctor.whiskerLeft (Hom1.sf F e) (η.1 e) := rfl

@[simp] theorem whiskerRight_val {F G : a ⟶ b} (η : F ⟶ G) (H : b ⟶ c) (e : B) :
    (η ▷ H).1 e = Superfunctor.whiskerRight (η.1 e) (Hom1.sf H e) := rfl

theorem eqToHom_val {F G : Hom1 a b} (h : F = G) (e : B) :
    (eqToHom h).1 e = eqToHom (congrArg (fun F => Hom1.sf F e) h) := by
  subst h; rfl

@[simp] theorem associator_hom_val {d : TwoStrictification R B} (F : a ⟶ b) (G : b ⟶ c)
    (H : c ⟶ d) (e : B) : (BicategoryStruct.associator F G H).hom.1 e = 𝟙 _ := by
  change (eqToHom (comp1_assoc F G H)).1 e = _
  rw [eqToHom_val]; rfl

@[simp] theorem associator_inv_val {d : TwoStrictification R B} (F : a ⟶ b) (G : b ⟶ c)
    (H : c ⟶ d) (e : B) : (BicategoryStruct.associator F G H).inv.1 e = 𝟙 _ := by
  change (eqToHom (comp1_assoc F G H).symm).1 e = _
  rw [eqToHom_val]; rfl

@[simp] theorem leftUnitor_hom_val (F : a ⟶ b) (e : B) :
    (BicategoryStruct.leftUnitor F).hom.1 e = 𝟙 _ := by
  change (eqToHom (id1_comp F)).1 e = _
  rw [eqToHom_val]; rfl

@[simp] theorem leftUnitor_inv_val (F : a ⟶ b) (e : B) :
    (BicategoryStruct.leftUnitor F).inv.1 e = 𝟙 _ := by
  change (eqToHom (id1_comp F).symm).1 e = _
  rw [eqToHom_val]; rfl

@[simp] theorem rightUnitor_hom_val (F : a ⟶ b) (e : B) :
    (BicategoryStruct.rightUnitor F).hom.1 e = 𝟙 _ := by
  change (eqToHom (comp1_id F)).1 e = _
  rw [eqToHom_val]; rfl

@[simp] theorem rightUnitor_inv_val (F : a ⟶ b) (e : B) :
    (BicategoryStruct.rightUnitor F).inv.1 e = 𝟙 _ := by
  change (eqToHom (comp1_id F).symm).1 e = _
  rw [eqToHom_val]; rfl

end Val

/-- Componentwise extensionality for 2-morphisms. -/
theorem hom2_ext' {a b : TwoStrictification R B} {F G : a ⟶ b} {θ θ' : F ⟶ G}
    (h : ∀ (e : B) (p : ZMod 2) (u : e ⟶ a.as), (θ.1 e).app p u = (θ'.1 e).app p u) :
    θ = θ' :=
  Hom1.hom2_ext fun e => Superfunctor.hom_ext fun p u => h e p u

/-- **Brundan–Ellis, after Definition 2.2.** The strictification is a 2-supercategory. -/
instance instTwoSupercategory : TwoSupercategory R (TwoStrictification R B) where
  whiskerLeft_id F G := Hom1.hom2_ext fun e => Superfunctor.whiskerLeft_id _ _
  whiskerLeft_comp F _ _ _ η θ := Hom1.hom2_ext fun e => Superfunctor.whiskerLeft_comp _ _ _
  id_whiskerLeft η := hom2_ext' fun e p u => by
    rcases parity_eq_zero_or_one p with rfl | rfl <;>
      simp [Superfunctor.comp_app, SuperNatTrans.zmod2_one_add_one, Superfunctor.obj,
        Superfunctor.map]
  comp_whiskerLeft F G _ _ η := hom2_ext' fun e p u => by
    rcases parity_eq_zero_or_one p with rfl | rfl <;>
      simp [Superfunctor.comp_app, SuperNatTrans.zmod2_one_add_one, Superfunctor.obj,
        Superfunctor.map]
  id_whiskerRight F G := Hom1.hom2_ext fun e => Superfunctor.id_whiskerRight _ _
  comp_whiskerRight η θ H := Hom1.hom2_ext fun e => Superfunctor.comp_whiskerRight _ _ _
  whiskerRight_id η := hom2_ext' fun e p u => by
    rcases parity_eq_zero_or_one p with rfl | rfl <;>
      simp [Superfunctor.comp_app, SuperNatTrans.zmod2_one_add_one, Superfunctor.obj,
        Superfunctor.map]
  whiskerRight_comp η G H := hom2_ext' fun e p u => by
    rcases parity_eq_zero_or_one p with rfl | rfl <;>
      simp [Superfunctor.comp_app, SuperNatTrans.zmod2_one_add_one, Superfunctor.obj,
        Superfunctor.map]
  whisker_assoc F _ _ η H := hom2_ext' fun e p u => by
    rcases parity_eq_zero_or_one p with rfl | rfl <;>
      simp [Superfunctor.comp_app, SuperNatTrans.zmod2_one_add_one, Superfunctor.obj,
        Superfunctor.map]
  pentagon F G H I := hom2_ext' fun e p u => by
    rcases parity_eq_zero_or_one p with rfl | rfl <;>
      simp [Superfunctor.comp_app, SuperNatTrans.zmod2_one_add_one, Superfunctor.obj,
        Superfunctor.map]
  triangle F G := hom2_ext' fun e p u => by
    rcases parity_eq_zero_or_one p with rfl | rfl <;>
      simp [Superfunctor.comp_app, SuperNatTrans.zmod2_one_add_one, Superfunctor.obj,
        Superfunctor.map]
  whiskerLeft_add F _ _ η θ := Hom1.hom2_ext fun e => Superfunctor.whiskerLeft_add _ _ _
  add_whiskerRight η θ H := Hom1.hom2_ext fun e => Superfunctor.add_whiskerRight _ _ _
  whiskerLeft_smul F _ _ r η := Hom1.hom2_ext fun e => Superfunctor.whiskerLeft_smul _ _ _
  smul_whiskerRight r η H := Hom1.hom2_ext fun e => Superfunctor.smul_whiskerRight _ _ _
  whiskerLeft_mem F _ _ _ _ hη e := Superfunctor.whiskerLeft_mem _ (hη e)
  whiskerRight_mem H hη e := Superfunctor.whiskerRight_mem (hη e) _
  super_interchange hη hθ := Hom1.hom2_ext fun e =>
    Superfunctor.whisker_exchange (hη e) (hθ e)
  associator_hom_mem F G H e := by rw [associator_hom_val]; exact id_mem _
  leftUnitor_hom_mem F e := by rw [leftUnitor_hom_val]; exact id_mem _
  rightUnitor_hom_mem F e := by rw [rightUnitor_hom_val]; exact id_mem _

/-- **Brundan–Ellis, after Definition 2.2.** The strictification is a strict
2-supercategory (Definition 2.1). -/
instance instStrict : BicategoryStruct.Strict (TwoStrictification R B) where
  id_comp := id1_comp
  comp_id := comp1_id
  assoc := comp1_assoc
  leftUnitor_eqToIso _ := rfl
  rightUnitor_eqToIso _ := rfl
  associator_eqToIso _ _ _ := rfl

end TwoStrictification

end StringDiagrams

end
