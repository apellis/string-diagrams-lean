import StringDiagrams.Super.MonoidalEquivalence
import StringDiagrams.Super.EndMonoidal
import Mathlib.Tactic.CategoryTheory.Coherence

/-!
# Strictification of monoidal supercategories

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, the
paragraph after Definition 1.4: "There is a version of Mac Lane's Coherence Theorem for
monoidal supercategories. It implies that any monoidal supercategory `A` is monoidally
superequivalent to a strict monoidal supercategory `B`".

## The construction

We follow the standard strictification by module endofunctors (as in the purely even case,
e.g. Joyal–Street). An object of `Strictification R A` is a *right `A`-module superfunctor*
`A → A`: a superfunctor `F : A → A` with an even supernatural isomorphism
`γ_{X,Y} : F(X) ⊗ Y ≅ F(X ⊗ Y)` (`Strictification.γ`) such that
`γ_{X, Y ⊗ Z} ∘ a_{FX,Y,Z} = F(a_{X,Y,Z}) ∘ γ_{X ⊗ Y, Z} ∘ (γ_{X,Y} ⊗ 1_Z)`
(`Strictification.γ_assoc`). The compatibility with the right unitor
`F(r_X) ∘ γ_{X,1} = r_{FX}` follows (`Strictification.γ_unit`). A morphism `x : F ⇒ G` is a
supernatural transformation (of either parity, Definition 1.1(iii)) such that each homogeneous
component satisfies `x_{X ⊗ Y} ∘ γ^F_{X,Y} = γ^G_{X,Y} ∘ (x_X ⊗ 1_Y)`.

*Sign conventions.* The action is on the right and the transformation `x_X ⊗ 1_Y` involves only
the identity of `Y`, so no Koszul sign appears in the compatibility condition, for either
parity of `x`. The sign of the super interchange law enters only through the supernaturality of
`x` in `X`: for the left multiplication superfunctors `X ⊗ -`, the family `f ⊗ 1_- : X ⊗ - ⇒
X' ⊗ -` attached to a homogeneous `f : X → X'` is a supernatural transformation of parity `|f|`
precisely because `(f ⊗ 1)(1 ⊗ g) = (-1)^{|f||g|}(1 ⊗ g)(f ⊗ 1)` (`Strictification.ι`).

`Strictification R A` is a strict monoidal supercategory (`Strictification.instIsStrict`)
under composition: `F ⊗ G := F ∘ G` with `γ^{F ⊗ G}_{X,Y} = F(γ^G_{X,Y}) ∘ γ^F_{GX,Y}`, and
`x ⊗ y := x_{K-} ∘ F(y_-)` as in `End(A)` (Example 1.5(ii), `SuperEnd`). It is a (non-full)
supercategory of `End(A)` whose objects carry the extra data `γ`.

## Main results

* `Strictification.ι : A ⥤ Strictification R A`, `X ↦ (X ⊗ -, a_{X,-,-})`, is a monoidal
  superfunctor (`Strictification.ιMonoidal`, with coherence maps `a⁻¹` and `l⁻¹`), fully
  faithful (`Strictification.ιFullyFaithful`: a morphism `θ : X ⊗ - ⇒ X' ⊗ -` is `f ⊗ 1_-`
  for the unique `f = r_{X'} ∘ θ_1 ∘ r_X⁻¹`) and evenly dense
  (`Strictification.ι_evenlyDense`: `F ≅ F(1) ⊗ -` via `F(l) ∘ γ_{1,-}`), hence a
  superequivalence (`Strictification.ιSuperequivalence`).
* `Strictification.ev : Strictification R A ⥤ A`, `F ↦ F(1)`, is a monoidal superfunctor
  (`Strictification.evMonoidal`), and `ι`, `ev` form a monoidal superequivalence
  (`Strictification.monoidalSuperequivalence`).
* **Coherence theorem** (`MonoidalSupercategory.exists_strict_monoidalSuperequivalence`): every
  monoidal supercategory is monoidally superequivalent to a strict one.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory MonoidalCategory Supercategory

universe w v u

variable (R : Type w) [CommRing R] (A : Type u) [Category.{v} A] [Preadditive A] [Linear R A]
  [Supercategory R A] [MonoidalCategoryStruct A] [MonoidalSupercategory R A]

/-! ## Auxiliary lemmas -/

namespace Supercategory

variable {R} {C : Type*} [Category C] [Preadditive C] [Linear R C] [Supercategory R C]

/-- The parity components of a composite: `(f ≫ g)_r = f₀ ≫ g_r + f₁ ≫ g_{r+1}`. -/
theorem proj_comp (r : ZMod 2) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    proj R r (f ≫ g) = proj R 0 f ≫ proj R r g + proj R 1 f ≫ proj R (r + 1) g := by
  conv_lhs => rw [← proj_add_proj (R := R) f]
  rw [Preadditive.add_comp, map_add]
  have h0 := proj_comp_of_mem_left (R := R) r (proj_mem 0 f) g
  have h1 := proj_comp_of_mem_left (R := R) (r + 1) (proj_mem 1 f) g
  rw [zero_add] at h0
  have e : (1 : ZMod 2) + (r + 1) = r := by
    rcases parity_eq_zero_or_one r with rfl | rfl <;> rfl
  rw [e] at h1
  rw [h0, h1]

theorem zmod2_one_ne_zero : (1 : ZMod 2) ≠ 0 := by decide

end Supercategory

namespace MonoidalSupercategory

variable {R} {A}

include R in
theorem associator_inv_naturality_left {X X' : A} (f : X ⟶ X') (Y Z : A) :
    f ▷ (Y ⊗ Z) ≫ (α_ X' Y Z).inv = (α_ X Y Z).inv ≫ (f ▷ Y) ▷ Z := by
  rw [Iso.comp_inv_eq, Category.assoc, associator_naturality_left R, Iso.inv_hom_id_assoc]

include R in
theorem associator_inv_naturality_middle (X : A) {Y Y' : A} (g : Y ⟶ Y') (Z : A) :
    X ◁ (g ▷ Z) ≫ (α_ X Y' Z).inv = (α_ X Y Z).inv ≫ (X ◁ g) ▷ Z := by
  rw [Iso.comp_inv_eq, Category.assoc, associator_naturality_middle R, Iso.inv_hom_id_assoc]

include R in
theorem leftUnitor_inv_naturality {X Y : A} (f : X ⟶ Y) :
    f ≫ (λ_ Y).inv = (λ_ X).inv ≫ 𝟙_ A ◁ f := by
  rw [Iso.eq_inv_comp, ← Category.assoc, ← leftUnitor_naturality (R := R), Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-! Some equations between composites of coherence maps, obtained from Mathlib's coherence
theorem for the underlying monoidal category (`Underlying.instMonoidalCategory`). -/

section Coherence

variable (R)

/-- The simp set translating equations in `Underlying R A` into equations in `A`. -/
local macro "underlying_val" h:ident : tactic =>
  `(tactic| (simp only [Underlying.comp_val, Underlying.id_val, Underlying.whiskerLeft_val,
    Underlying.whiskerRight_val, Underlying.tensorHom_val, Underlying.associator_hom_val,
    Underlying.associator_inv_val, Underlying.leftUnitor_hom_val, Underlying.leftUnitor_inv_val,
    Underlying.rightUnitor_hom_val, Underlying.rightUnitor_inv_val, Underlying.tensorObj_obj,
    Underlying.tensorUnit_obj] at $h:ident; exact $h:ident))

include R in
theorem coherence_pentagon_inv (X Y Z W : A) :
    (α_ X (Y ⊗ Z) W).hom ≫ X ◁ (α_ Y Z W).hom ≫ (α_ X Y (Z ⊗ W)).inv =
      (α_ X Y Z).inv ▷ W ≫ (α_ (X ⊗ Y) Z W).hom := by
  have hU : ∀ X Y Z W : Underlying R A,
    (α_ X (Y ⊗ Z) W).hom ≫ X ◁ (α_ Y Z W).hom ≫ (α_ X Y (Z ⊗ W)).inv =
      (α_ X Y Z).inv ▷ W ≫ (α_ (X ⊗ Y) Z W).hom := by
    intros; coherence
  have h := congrArg Subtype.val (hU ⟨X⟩ ⟨Y⟩ ⟨Z⟩ ⟨W⟩)
  underlying_val h

include R in
theorem coherence_pentagon_inv' (X Y Z W : A) :
    (α_ X Y (Z ⊗ W)).inv ≫ (α_ (X ⊗ Y) Z W).inv ≫ (α_ X Y Z).hom ▷ W =
      X ◁ (α_ Y Z W).inv ≫ (α_ X (Y ⊗ Z) W).inv := by
  have hU : ∀ X Y Z W : Underlying R A,
    (α_ X Y (Z ⊗ W)).inv ≫ (α_ (X ⊗ Y) Z W).inv ≫ (α_ X Y Z).hom ▷ W =
      X ◁ (α_ Y Z W).inv ≫ (α_ X (Y ⊗ Z) W).inv := by
    intros; coherence
  have h := congrArg Subtype.val (hU ⟨X⟩ ⟨Y⟩ ⟨Z⟩ ⟨W⟩)
  underlying_val h

include R in
theorem coherence_leftUnitor_inv_tensor (Z W : A) :
    (λ_ (Z ⊗ W)).inv = (λ_ Z).inv ▷ W ≫ (α_ (𝟙_ A) Z W).hom := by
  have hU : ∀ Z W : Underlying R A,
    (λ_ (Z ⊗ W)).inv = (λ_ Z).inv ▷ W ≫ (α_ (𝟙_ _) Z W).hom := by
    intros; coherence
  have h := congrArg Subtype.val (hU ⟨Z⟩ ⟨W⟩)
  underlying_val h

include R in
theorem coherence_left_unitality (X Y : A) :
    (λ_ (X ⊗ Y)).inv ≫ (α_ (𝟙_ A) X Y).inv ≫ (λ_ X).hom ▷ Y = 𝟙 _ := by
  have hU : ∀ X Y : Underlying R A,
    (λ_ (X ⊗ Y)).inv ≫ (α_ (𝟙_ _) X Y).inv ≫ (λ_ X).hom ▷ Y = 𝟙 _ := by
    intros; coherence
  have h := congrArg Subtype.val (hU ⟨X⟩ ⟨Y⟩)
  underlying_val h

include R in
theorem coherence_right_unitality (X Y : A) :
    X ◁ (λ_ Y).inv ≫ (α_ X (𝟙_ A) Y).inv ≫ (ρ_ X).hom ▷ Y = 𝟙 _ := by
  have hU : ∀ X Y : Underlying R A,
    X ◁ (λ_ Y).inv ≫ (α_ X (𝟙_ _) Y).inv ≫ (ρ_ X).hom ▷ Y = 𝟙 _ := by
    intros; coherence
  have h := congrArg Subtype.val (hU ⟨X⟩ ⟨Y⟩)
  underlying_val h

include R in
theorem coherence_rightUnitor_inv_tensor (X Y : A) :
    (ρ_ (X ⊗ Y)).inv = ((ρ_ X).inv ⊗ (ρ_ Y).inv) ≫ (α_ X (𝟙_ A) (Y ⊗ 𝟙_ A)).hom ≫
      X ◁ (λ_ (Y ⊗ 𝟙_ A)).hom ≫ (α_ X Y (𝟙_ A)).inv := by
  have hU : ∀ X Y : Underlying R A,
    (ρ_ (X ⊗ Y)).inv = ((ρ_ X).inv ⊗ (ρ_ Y).inv) ≫ (α_ X (𝟙_ _) (Y ⊗ 𝟙_ _)).hom ≫
      X ◁ (λ_ (Y ⊗ 𝟙_ _)).hom ≫ (α_ X Y (𝟙_ _)).inv := by
    intros; coherence
  have h := congrArg Subtype.val (hU ⟨X⟩ ⟨Y⟩)
  underlying_val h

include R in
theorem coherence_leftUnitor_inv_unit : (λ_ (𝟙_ A)).inv = (ρ_ (𝟙_ A)).inv := by
  have h := congrArg Subtype.val
    (show (λ_ (𝟙_ (Underlying R A))).inv = (ρ_ (𝟙_ (Underlying R A))).inv by coherence)
  underlying_val h

end Coherence

end MonoidalSupercategory

/-- The strictification of a monoidal supercategory `A`: its objects are the right `A`-module
superfunctors `A → A`, i.e. superfunctors `F` with an even natural isomorphism
`γ_{X,Y} : F(X) ⊗ Y ≅ F(X ⊗ Y)` compatible with the associator. See the module
documentation. -/
structure Strictification where
  /-- The underlying functor `F : A → A`. -/
  toFunctor : A ⥤ A
  [additive : toFunctor.Additive]
  [linear : toFunctor.Linear R]
  [isSuperfunctor : IsSuperfunctor R toFunctor]
  /-- The module structure `γ_{X,Y} : F(X) ⊗ Y ≅ F(X ⊗ Y)`. -/
  γ : ∀ X Y : A, toFunctor.obj X ⊗ Y ≅ toFunctor.obj (X ⊗ Y)
  γ_mem : ∀ X Y : A, (γ X Y).hom ∈ parity (R := R) _ _ 0
  γ_naturality_left : ∀ {X X' : A} (f : X ⟶ X') (Y : A),
    toFunctor.map f ▷ Y ≫ (γ X' Y).hom = (γ X Y).hom ≫ toFunctor.map (f ▷ Y)
  γ_naturality_right : ∀ (X : A) {Y Y' : A} (g : Y ⟶ Y'),
    toFunctor.obj X ◁ g ≫ (γ X Y').hom = (γ X Y).hom ≫ toFunctor.map (X ◁ g)
  γ_assoc : ∀ X Y Z : A,
    (α_ (toFunctor.obj X) Y Z).hom ≫ (γ X (Y ⊗ Z)).hom =
      (γ X Y).hom ▷ Z ≫ (γ (X ⊗ Y) Z).hom ≫ toFunctor.map (α_ X Y Z).hom

namespace Strictification

open Supercategory.Superfunctor

variable {R A}

attribute [instance] additive linear isSuperfunctor
attribute [reassoc] γ_naturality_left γ_naturality_right γ_assoc

/-- The underlying superfunctor, an object of `End(A)`. -/
abbrev toSuperfunctor (M : Strictification R A) : Superfunctor R A A := ⟨M.toFunctor⟩

omit [MonoidalSupercategory R A] in
theorem ext_of_heq {M N : Strictification R A} (h : M.toFunctor = N.toFunctor)
    (hγ : ∀ X Y, HEq (M.γ X Y).hom (N.γ X Y).hom) : M = N := by
  obtain ⟨F, γ, _, _, _, _⟩ := M
  obtain ⟨G, γ', _, _, _, _⟩ := N
  obtain rfl : F = G := h
  obtain rfl : γ = γ' := funext fun X => funext fun Y => Iso.ext (eq_of_heq (hγ X Y))
  rfl

/-- The compatibility with the right unitor, `F(r_X) ∘ γ_{X,1} = r_{FX}`, is a consequence of
the associativity axiom. -/
theorem γ_unit (M : Strictification R A) (X : A) :
    (M.γ X (𝟙_ A)).hom ≫ M.toFunctor.map (ρ_ X).hom = (ρ_ (M.toFunctor.obj X)).hom := by
  -- `r_{FX} ⊗ 1_Z` and `(F(r_X) ∘ γ_{X,1}) ⊗ 1_Z` agree after composing with `γ_{X,Z}`.
  have key : ∀ Z : A, ((M.γ X (𝟙_ A)).hom ≫ M.toFunctor.map (ρ_ X).hom) ▷ Z ≫ (M.γ X Z).hom =
      (ρ_ (M.toFunctor.obj X)).hom ▷ Z ≫ (M.γ X Z).hom := by
    intro Z
    rw [MonoidalSupercategory.comp_whiskerRight (R := R), Category.assoc,
      M.γ_naturality_left, ← MonoidalSupercategory.triangle (R := R) (M.toFunctor.obj X) Z,
      Category.assoc, M.γ_naturality_right, M.γ_assoc_assoc, ← Functor.map_comp,
      MonoidalSupercategory.triangle (R := R) X Z]
  have h := key (𝟙_ A)
  rw [cancel_mono] at h
  rw [← cancel_mono (ρ_ (M.toFunctor.obj X)).inv, ← cancel_epi (ρ_ (M.toFunctor.obj X ⊗ 𝟙_ A)).hom]
  have e := MonoidalSupercategory.rightUnitor_naturality (R := R)
    ((M.γ X (𝟙_ A)).hom ≫ M.toFunctor.map (ρ_ X).hom)
  have e' := MonoidalSupercategory.rightUnitor_naturality (R := R) (ρ_ (M.toFunctor.obj X)).hom
  rw [h] at e
  rw [← Category.assoc, ← e, ← Category.assoc, ← e']

/-! ## Morphisms -/

/-- The supernatural transformations `F ⇒ G` compatible with the module structures. -/
def homSubmodule (M N : Strictification R A) :
    Submodule R (M.toSuperfunctor ⟶ N.toSuperfunctor) where
  carrier := {x | ∀ (p : ZMod 2) (X Y : A),
    (M.γ X Y).hom ≫ x.app p (X ⊗ Y) = x.app p X ▷ Y ≫ (N.γ X Y).hom}
  add_mem' {x y} hx hy p X Y := by
    simp only [add_app, Preadditive.comp_add, hx p X Y, hy p X Y,
      MonoidalSupercategory.add_whiskerRight (R := R), Preadditive.add_comp]
  zero_mem' p X Y := by
    simp [MonoidalSupercategory.zero_whiskerRight R]
  smul_mem' r x hx p X Y := by
    simp only [smul_app, Linear.comp_smul, hx p X Y,
      MonoidalSupercategory.smul_whiskerRight (R := R), Linear.smul_comp]

theorem mem_homSubmodule {M N : Strictification R A} {x : M.toSuperfunctor ⟶ N.toSuperfunctor} :
    x ∈ homSubmodule M N ↔ ∀ (p : ZMod 2) (X Y : A),
      (M.γ X Y).hom ≫ x.app p (X ⊗ Y) = x.app p X ▷ Y ≫ (N.γ X Y).hom := Iff.rfl

theorem id_mem_homSubmodule (M : Strictification R A) :
    𝟙 M.toSuperfunctor ∈ homSubmodule M M := by
  intro p X Y
  rcases parity_eq_zero_or_one p with rfl | rfl
  · simp [MonoidalSupercategory.id_whiskerRight (R := R)]
  · simp [MonoidalSupercategory.zero_whiskerRight R]

theorem comp_mem_homSubmodule {M N P : Strictification R A}
    {x : M.toSuperfunctor ⟶ N.toSuperfunctor} {y : N.toSuperfunctor ⟶ P.toSuperfunctor}
    (hx : x ∈ homSubmodule M N) (hy : y ∈ homSubmodule N P) : x ≫ y ∈ homSubmodule M P := by
  intro r X Y
  simp only [comp_app, Preadditive.comp_add, Preadditive.add_comp,
    MonoidalSupercategory.add_whiskerRight (R := R),
    MonoidalSupercategory.comp_whiskerRight (R := R), Category.assoc]
  rw [reassoc_of% (hx 0 X Y), reassoc_of% (hx 1 X Y), hy r X Y, hy (r + 1) X Y]

theorem proj_mem_homSubmodule {M N : Strictification R A} (p : ZMod 2)
    {x : M.toSuperfunctor ⟶ N.toSuperfunctor} (hx : x ∈ homSubmodule M N) :
    proj R p x ∈ homSubmodule M N := by
  intro q X Y
  simp only [proj_app]
  split_ifs with h
  · subst h; exact hx q X Y
  · simp [MonoidalSupercategory.zero_whiskerRight R]

instance : Category (Strictification R A) where
  Hom M N := homSubmodule M N
  id M := ⟨𝟙 M.toSuperfunctor, id_mem_homSubmodule M⟩
  comp x y := ⟨x.1 ≫ y.1, comp_mem_homSubmodule x.2 y.2⟩
  id_comp x := Subtype.ext (Category.id_comp x.1)
  comp_id x := Subtype.ext (Category.comp_id x.1)
  assoc x y z := Subtype.ext (Category.assoc x.1 y.1 z.1)

@[ext] theorem hom_ext {M N : Strictification R A} {x y : M ⟶ N} (h : x.1 = y.1) : x = y :=
  Subtype.ext h

@[simp] theorem id_val (M : Strictification R A) : (𝟙 M : M ⟶ M).1 = 𝟙 M.toSuperfunctor := rfl

@[simp] theorem comp_val {M N P : Strictification R A} (x : M ⟶ N) (y : N ⟶ P) :
    (x ≫ y).1 = x.1 ≫ y.1 := rfl

/-- A morphism satisfies the compatibility with the module structures. -/
theorem hom_compat {M N : Strictification R A} (x : M ⟶ N) (p : ZMod 2) (X Y : A) :
    (M.γ X Y).hom ≫ x.1.app p (X ⊗ Y) = x.1.app p X ▷ Y ≫ (N.γ X Y).hom := x.2 p X Y

instance : Preadditive (Strictification R A) where
  homGroup M N := inferInstanceAs (AddCommGroup (homSubmodule M N))
  add_comp _ _ _ x x' y := Subtype.ext (Preadditive.add_comp _ _ _ x.1 x'.1 y.1)
  comp_add _ _ _ x y y' := Subtype.ext (Preadditive.comp_add _ _ _ x.1 y.1 y'.1)

instance : Linear R (Strictification R A) where
  homModule M N := inferInstanceAs (Module R (homSubmodule M N))
  smul_comp _ _ _ r x y := Subtype.ext (Linear.smul_comp _ _ _ r x.1 y.1)
  comp_smul _ _ _ x r y := Subtype.ext (Linear.comp_smul _ _ _ x.1 r y.1)

@[simp] theorem add_val {M N : Strictification R A} (x y : M ⟶ N) : (x + y).1 = x.1 + y.1 := rfl

@[simp] theorem zero_val {M N : Strictification R A} : (0 : M ⟶ N).1 = 0 := rfl

@[simp] theorem smul_val {M N : Strictification R A} (r : R) (x : M ⟶ N) :
    (r • x).1 = r • x.1 := rfl

@[simp] theorem zsmul_val {M N : Strictification R A} (n : ℤ) (x : M ⟶ N) :
    (n • x).1 = n • x.1 := rfl

/-! ## The supercategory structure -/

/-- The morphisms of parity `p`: those whose underlying supernatural transformation has
parity `p`. -/
def parityHom (M N : Strictification R A) (p : ZMod 2) : Submodule R (M ⟶ N) :=
  (parity (R := R) M.toSuperfunctor N.toSuperfunctor p).comap (homSubmodule M N).subtype

theorem mem_parityHom {M N : Strictification R A} {p : ZMod 2} {x : M ⟶ N} :
    x ∈ parityHom M N p ↔ x.1 ∈ parity (R := R) M.toSuperfunctor N.toSuperfunctor p := Iff.rfl

instance : Supercategory R (Strictification R A) where
  parity := parityHom
  isInternal M N := by
    rw [DirectSum.isInternal_submodule_iff_isCompl _ (i := 0) (j := 1) (by decide)
      (by ext p; rcases parity_eq_zero_or_one p with rfl | rfl <;> simp)]
    constructor
    · rw [Submodule.disjoint_def]
      intro x h0 h1
      have h0' := (Superfunctor.mem_parity_iff (p := 0)).1 (mem_parityHom.1 h0)
      have h1' := (Superfunctor.mem_parity_iff (p := 1)).1 (mem_parityHom.1 h1)
      exact Subtype.ext (hom_ext_parity (fun X => by simpa using congrFun h1' X)
        (fun X => by simpa using congrFun h0' X))
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      have e : x = ⟨proj R 0 x.1, proj_mem_homSubmodule 0 x.2⟩ +
          ⟨proj R 1 x.1, proj_mem_homSubmodule 1 x.2⟩ :=
        Subtype.ext (proj_add_proj (R := R) x.1).symm
      rw [e]
      exact Submodule.add_mem_sup (proj_mem (R := R) 0 x.1) (proj_mem (R := R) 1 x.1)
  id_mem M := id_mem (R := R) M.toSuperfunctor
  comp_mem {M N P p q x y} hx hy :=
    mem_parityHom.2 (comp_mem (R := R) (mem_parityHom.1 hx) (mem_parityHom.1 hy))

theorem mem_parity_iff {M N : Strictification R A} {p : ZMod 2} {x : M ⟶ N} :
    x ∈ parity (R := R) M N p ↔ x.1 ∈ parity (R := R) M.toSuperfunctor N.toSuperfunctor p :=
  Iff.rfl

/-! ## The strict monoidal structure -/

/-- The tensor product `F ⊗ G := F ∘ G` (in Lean `G ⋙ F`), with module structure
`γ^{F ⊗ G}_{X,Y} = F(γ^G_{X,Y}) ∘ γ^F_{GX,Y}`. -/
@[simps]
def tensorObj (M N : Strictification R A) : Strictification R A where
  toFunctor := N.toFunctor ⋙ M.toFunctor
  γ X Y := M.γ (N.toFunctor.obj X) Y ≪≫ M.toFunctor.mapIso (N.γ X Y)
  γ_mem X Y := by
    simpa using comp_mem (M.γ_mem (N.toFunctor.obj X) Y) (map_mem M.toFunctor (N.γ_mem X Y))
  γ_naturality_left f Y := by
    simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.comp_map, Functor.comp_obj,
      Category.assoc]
    rw [M.γ_naturality_left_assoc, ← Functor.map_comp, ← Functor.map_comp,
      N.γ_naturality_left]
  γ_naturality_right X {_ _} g := by
    simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.comp_map, Functor.comp_obj,
      Category.assoc]
    rw [M.γ_naturality_right_assoc, ← Functor.map_comp, ← Functor.map_comp,
      N.γ_naturality_right]
  γ_assoc X Y Z := by
    simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.comp_map, Functor.comp_obj,
      Category.assoc, MonoidalSupercategory.comp_whiskerRight (R := R)]
    rw [M.γ_assoc_assoc, ← Functor.map_comp, N.γ_assoc, Functor.map_comp, Functor.map_comp,
      M.γ_naturality_left_assoc]

/-- The unit object: the identity superfunctor with `γ = 1`. -/
@[simps]
def tensorUnit : Strictification R A where
  toFunctor := 𝟭 A
  γ X Y := Iso.refl _
  γ_mem X Y := id_mem _
  γ_naturality_left f Y := by simp
  γ_naturality_right X {_ _} g := by simp
  γ_assoc X Y Z := by simp [MonoidalSupercategory.id_whiskerRight (R := R)]

/-- `F ◁ y := F(y_-)`. -/
def whiskerLeft (M : Strictification R A) {N N' : Strictification R A} (y : N ⟶ N') :
    tensorObj M N ⟶ tensorObj M N' :=
  ⟨Superfunctor.whiskerRight y.1 M.toSuperfunctor, fun p X Y => by
    simp only [tensorObj_γ, Iso.trans_hom, Functor.mapIso_hom,
      Superfunctor.whiskerRight_app, Superfunctor.map,
      Category.assoc]
    rw [← Functor.map_comp, hom_compat, Functor.map_comp, ← M.γ_naturality_left_assoc]⟩

/-- `x ▷ G := x_{G-}`. -/
def whiskerRight {M M' : Strictification R A} (x : M ⟶ M') (N : Strictification R A) :
    tensorObj M N ⟶ tensorObj M' N :=
  ⟨Superfunctor.whiskerLeft N.toSuperfunctor x.1, fun p X Y => by
    simp only [tensorObj_γ, Iso.trans_hom, Functor.mapIso_hom,
      Superfunctor.whiskerLeft_app, Superfunctor.obj,
      Category.assoc]
    have h := x.1.naturality p (N.γ X Y).hom (N.γ_mem X Y)
    rw [koszulSign_zero_right, one_smul] at h
    erw [h]
    rw [← Category.assoc, hom_compat, Category.assoc]⟩

theorem tensorObj_assoc (M N P : Strictification R A) :
    tensorObj (tensorObj M N) P = tensorObj M (tensorObj N P) :=
  ext_of_heq rfl fun X Y => heq_of_eq (by simp [Functor.map_comp])

theorem unit_tensorObj (M : Strictification R A) : tensorObj tensorUnit M = M :=
  ext_of_heq rfl fun X Y => heq_of_eq (by simp)

theorem tensorObj_unit (M : Strictification R A) : tensorObj M tensorUnit = M :=
  ext_of_heq rfl fun X Y => heq_of_eq (by simp)

instance instMonoidalCategoryStruct : MonoidalCategoryStruct (Strictification R A) where
  tensorObj := tensorObj
  whiskerLeft := whiskerLeft
  whiskerRight := whiskerRight
  tensorUnit := tensorUnit
  associator M N P := eqToIso (tensorObj_assoc M N P)
  leftUnitor M := eqToIso (unit_tensorObj M)
  rightUnitor M := eqToIso (tensorObj_unit M)

theorem tensorObj_toSuperfunctor (M N : Strictification R A) :
    (M ⊗ N).toSuperfunctor = N.toSuperfunctor.comp M.toSuperfunctor := rfl

@[simp] theorem tensorObj_toFunctor' (M N : Strictification R A) :
    (M ⊗ N).toFunctor = N.toFunctor ⋙ M.toFunctor := rfl

@[simp] theorem tensorObj_γ_hom (M N : Strictification R A) (X Y : A) :
    ((M ⊗ N).γ X Y).hom = (M.γ (N.toFunctor.obj X) Y).hom ≫ M.toFunctor.map (N.γ X Y).hom :=
  rfl

theorem tensorUnit_toSuperfunctor :
    (𝟙_ (Strictification R A)).toSuperfunctor = Superfunctor.id R A := rfl

@[simp] theorem tensorUnit_toFunctor' : (𝟙_ (Strictification R A)).toFunctor = 𝟭 A := rfl

@[simp] theorem tensorUnit_γ_hom (X Y : A) : ((𝟙_ (Strictification R A)).γ X Y).hom = 𝟙 _ :=
  rfl

@[simp] theorem whiskerLeft_val (M : Strictification R A) {N N' : Strictification R A}
    (y : N ⟶ N') : (M ◁ y).1 = Superfunctor.whiskerRight y.1 M.toSuperfunctor := rfl

@[simp] theorem whiskerRight_val {M M' : Strictification R A} (x : M ⟶ M')
    (N : Strictification R A) : (x ▷ N).1 = Superfunctor.whiskerLeft N.toSuperfunctor x.1 := rfl

theorem tensorHom_val {M M' N N' : Strictification R A} (f : M ⟶ M') (g : N ⟶ N') :
    (f ⊗ g).1 = Superfunctor.whiskerLeft N.toSuperfunctor f.1 ≫
      Superfunctor.whiskerRight g.1 M'.toSuperfunctor := rfl

theorem eqToHom_val {M N : Strictification R A} (h : M = N) :
    (eqToHom h).1 = eqToHom (congrArg Strictification.toSuperfunctor h) := by
  subst h; rfl

@[simp] theorem associator_hom_val (M N P : Strictification R A) :
    (α_ M N P).hom.1 = 𝟙 _ := by
  change (eqToHom (tensorObj_assoc M N P)).1 = _
  rw [eqToHom_val]; rfl

@[simp] theorem associator_inv_val (M N P : Strictification R A) :
    (α_ M N P).inv.1 = 𝟙 _ := by
  change (eqToHom (tensorObj_assoc M N P).symm).1 = _
  rw [eqToHom_val]; rfl

@[simp] theorem leftUnitor_hom_val (M : Strictification R A) : (λ_ M).hom.1 = 𝟙 _ := by
  change (eqToHom (unit_tensorObj M)).1 = _
  rw [eqToHom_val]; rfl

@[simp] theorem leftUnitor_inv_val (M : Strictification R A) : (λ_ M).inv.1 = 𝟙 _ := by
  change (eqToHom (unit_tensorObj M).symm).1 = _
  rw [eqToHom_val]; rfl

@[simp] theorem rightUnitor_hom_val (M : Strictification R A) : (ρ_ M).hom.1 = 𝟙 _ := by
  change (eqToHom (tensorObj_unit M)).1 = _
  rw [eqToHom_val]; rfl

@[simp] theorem rightUnitor_inv_val (M : Strictification R A) : (ρ_ M).inv.1 = 𝟙 _ := by
  change (eqToHom (tensorObj_unit M).symm).1 = _
  rw [eqToHom_val]; rfl

/-- **Brundan–Ellis, after Definition 1.4.** The strictification is a monoidal
supercategory. -/
instance instMonoidalSupercategory : MonoidalSupercategory R (Strictification R A) where
  tensorHom_def _ _ := rfl
  whiskerLeft_id M N := hom_ext (Superfunctor.id_whiskerRight _ _)
  id_whiskerRight M N := hom_ext (Superfunctor.whiskerLeft_id _ _)
  whiskerLeft_comp M _ _ _ f g := hom_ext (Superfunctor.comp_whiskerRight f.1 g.1 _)
  comp_whiskerRight f g P := hom_ext (Superfunctor.whiskerLeft_comp _ f.1 g.1)
  whiskerLeft_add M _ _ f g := hom_ext (Superfunctor.add_whiskerRight f.1 g.1 _)
  add_whiskerRight f g P := hom_ext (Superfunctor.whiskerLeft_add _ f.1 g.1)
  whiskerLeft_smul M _ _ r f := hom_ext (Superfunctor.smul_whiskerRight r f.1 _)
  smul_whiskerRight r f P := hom_ext (Superfunctor.whiskerLeft_smul _ r f.1)
  whiskerLeft_mem M _ _ _ _ hf := Superfunctor.whiskerRight_mem hf _
  whiskerRight_mem P hf := Superfunctor.whiskerLeft_mem _ hf
  super_interchange {M M' N N' p q f g} hf hg := hom_ext (by
    change Superfunctor.whiskerLeft _ f.1 ≫ Superfunctor.whiskerRight g.1 _ =
      koszulSign p q • (Superfunctor.whiskerRight g.1 _ ≫ Superfunctor.whiskerLeft _ f.1)
    rw [Superfunctor.whisker_exchange (mem_parity_iff.1 hg) (mem_parity_iff.1 hf),
      koszulSign_comm, koszulSign_smul_smul])
  associator_naturality f₁ f₂ f₃ := hom_ext (by
    simp only [comp_val, associator_hom_val, Category.comp_id, Category.id_comp, tensorHom_val]
    ext p X
    simp only [Superfunctor.comp_app, Superfunctor.whiskerLeft_app,
      Superfunctor.whiskerRight_app, Superfunctor.map, Superfunctor.obj, Functor.map_add,
      Functor.map_comp, Preadditive.add_comp, Preadditive.comp_add, Category.assoc,
      tensorObj_toFunctor', Functor.comp_map, Functor.comp_obj, zero_add,
      SuperNatTrans.zmod2_one_add_one, add_assoc, add_zero]
    abel)
  leftUnitor_naturality f := hom_ext (by
    simp only [comp_val, leftUnitor_hom_val, Category.comp_id, Category.id_comp,
      whiskerLeft_val]
    exact SuperEnd.whiskerRight_id' f.1)
  rightUnitor_naturality f := hom_ext (by
    simp only [comp_val, rightUnitor_hom_val, Category.comp_id, Category.id_comp,
      whiskerRight_val]
    exact SuperEnd.whiskerLeft_id' f.1)
  pentagon W X Y Z := hom_ext (by
    simp only [comp_val, whiskerLeft_val, whiskerRight_val, associator_hom_val,
      Superfunctor.whiskerLeft_id, Superfunctor.id_whiskerRight]
    erw [Category.id_comp]
    rfl)
  triangle X Y := hom_ext (by
    simp only [comp_val, whiskerLeft_val, whiskerRight_val, associator_hom_val,
      leftUnitor_hom_val, rightUnitor_hom_val, Superfunctor.whiskerLeft_id,
      Superfunctor.id_whiskerRight]
    erw [Category.id_comp]
    rfl)
  associator_hom_mem M N P := by
    rw [mem_parity_iff, associator_hom_val]; exact id_mem _
  leftUnitor_hom_mem M := by rw [mem_parity_iff, leftUnitor_hom_val]; exact id_mem _
  rightUnitor_hom_mem M := by rw [mem_parity_iff, rightUnitor_hom_val]; exact id_mem _

/-- **Brundan–Ellis, after Definition 1.4.** The strictification is a strict monoidal
supercategory. -/
instance instIsStrict : MonoidalSupercategory.IsStrict (Strictification R A) where
  tensor_assoc := tensorObj_assoc
  unit_tensor := unit_tensorObj
  tensor_unit := tensorObj_unit
  associator_eq _ _ _ := rfl
  leftUnitor_eq _ := rfl
  rightUnitor_eq _ := rfl

/-! ## Even morphisms and isomorphisms -/

/-- A morphism of `Strictification R A` given by an even natural family compatible with the
module structures. -/
def homMk {M N : Strictification R A} (x : ∀ X, M.toFunctor.obj X ⟶ N.toFunctor.obj X)
    (mem : ∀ X, x X ∈ parity (R := R) _ _ 0)
    (nat : ∀ {X Y : A} (f : X ⟶ Y), M.toFunctor.map f ≫ x Y = x X ≫ N.toFunctor.map f)
    (compat : ∀ X Y, (M.γ X Y).hom ≫ x (X ⊗ Y) = x X ▷ Y ≫ (N.γ X Y).hom) : M ⟶ N :=
  ⟨SuperNatTrans.ofNatTrans (F := M.toFunctor) (G := N.toFunctor) ⟨x, fun _ _ f => nat f⟩ mem,
    fun p X Y => by
      rcases parity_eq_zero_or_one p with rfl | rfl
      · simpa [SuperNatTrans.ofNatTrans] using compat X Y
      · simp [SuperNatTrans.ofNatTrans, MonoidalSupercategory.zero_whiskerRight R]⟩

section homMk

variable {M N : Strictification R A} (x : ∀ X, M.toFunctor.obj X ⟶ N.toFunctor.obj X)
  (mem : ∀ X, x X ∈ parity (R := R) _ _ 0)
  (nat : ∀ {X Y : A} (f : X ⟶ Y), M.toFunctor.map f ≫ x Y = x X ≫ N.toFunctor.map f)
  (compat : ∀ X Y, (M.γ X Y).hom ≫ x (X ⊗ Y) = x X ▷ Y ≫ (N.γ X Y).hom)

@[simp] theorem homMk_val_app (p : ZMod 2) (X : A) :
    (homMk x mem nat compat).1.app p X = if p = 0 then x X else 0 := rfl

theorem homMk_mem : homMk x mem nat compat ∈ parity (R := R) M N 0 := by
  rw [mem_parity_iff, Superfunctor.mem_parity_iff]
  funext X
  simp [zmod2_one_ne_zero]

end homMk

/-- An isomorphism of `Strictification R A` given by an even natural family of isomorphisms
compatible with the module structures. -/
def isoMk {M N : Strictification R A} (e : ∀ X, M.toFunctor.obj X ≅ N.toFunctor.obj X)
    (mem : ∀ X, (e X).hom ∈ parity (R := R) _ _ 0)
    (nat : ∀ {X Y : A} (f : X ⟶ Y), M.toFunctor.map f ≫ (e Y).hom = (e X).hom ≫ N.toFunctor.map f)
    (compat : ∀ X Y, (M.γ X Y).hom ≫ (e (X ⊗ Y)).hom = (e X).hom ▷ Y ≫ (N.γ X Y).hom) :
    M ≅ N where
  hom := homMk (fun X => (e X).hom) mem nat compat
  inv := homMk (fun X => (e X).inv) (fun X => inv_mem _ (mem X))
    (fun {X Y} f => by
      dsimp only
      rw [← cancel_mono (e Y).hom, Category.assoc, Iso.inv_hom_id, Category.comp_id,
        Category.assoc, nat, Iso.inv_hom_id_assoc])
    (fun X Y => by
      have h1 : (e X).inv ▷ Y ≫ (e X).hom ▷ Y = 𝟙 _ := by
        rw [← MonoidalSupercategory.comp_whiskerRight (R := R), Iso.inv_hom_id,
          MonoidalSupercategory.id_whiskerRight (R := R)]
      calc (N.γ X Y).hom ≫ (e (X ⊗ Y)).inv
          = ((e X).inv ▷ Y ≫ (e X).hom ▷ Y) ≫ (N.γ X Y).hom ≫ (e (X ⊗ Y)).inv := by
            rw [h1, Category.id_comp]
        _ = (e X).inv ▷ Y ≫ (M.γ X Y).hom := by
            rw [Category.assoc, ← reassoc_of% (compat X Y), Iso.hom_inv_id, Category.comp_id])
  hom_inv_id := hom_ext (Superfunctor.hom_ext_parity (fun X => by simp)
    (fun X => by simp [zmod2_one_ne_zero]))
  inv_hom_id := hom_ext (Superfunctor.hom_ext_parity (fun X => by simp)
    (fun X => by simp [zmod2_one_ne_zero]))

section isoMk

variable {M N : Strictification R A} (e : ∀ X, M.toFunctor.obj X ≅ N.toFunctor.obj X)
  (mem : ∀ X, (e X).hom ∈ parity (R := R) _ _ 0)
  (nat : ∀ {X Y : A} (f : X ⟶ Y), M.toFunctor.map f ≫ (e Y).hom = (e X).hom ≫ N.toFunctor.map f)
  (compat : ∀ X Y, (M.γ X Y).hom ≫ (e (X ⊗ Y)).hom = (e X).hom ▷ Y ≫ (N.γ X Y).hom)

@[simp] theorem isoMk_hom_val_app (p : ZMod 2) (X : A) :
    (isoMk e mem nat compat).hom.1.app p X = if p = 0 then (e X).hom else 0 := rfl

@[simp] theorem isoMk_inv_val_app (p : ZMod 2) (X : A) :
    (isoMk e mem nat compat).inv.1.app p X = if p = 0 then (e X).inv else 0 := rfl

theorem isoMk_hom_mem : (isoMk e mem nat compat).hom ∈ parity (R := R) M N 0 :=
  homMk_mem (fun X => (e X).hom) mem nat compat

end isoMk

/-! ## The superfunctor `ι : A → Strictification R A` -/

variable (R) in
/-- The superfunctor `X ⊗ - : A → A`. -/
@[simps]
def leftMul (X : A) : A ⥤ A where
  obj Y := X ⊗ Y
  map g := X ◁ g
  map_id Y := MonoidalSupercategory.whiskerLeft_id (R := R) X Y
  map_comp f g := MonoidalSupercategory.whiskerLeft_comp (R := R) X f g

instance (X : A) : (leftMul R X).Additive where
  map_add := MonoidalSupercategory.whiskerLeft_add (R := R) _ _ _

instance (X : A) : (leftMul R X).Linear R where
  map_smul f r := MonoidalSupercategory.whiskerLeft_smul _ r f

instance (X : A) : IsSuperfunctor R (leftMul R X) where
  map_mem hf := MonoidalSupercategory.whiskerLeft_mem _ hf

variable (R) in
/-- The superfunctor `- ⊗ Y : A → A`. -/
@[simps]
def rightMul (Y : A) : A ⥤ A where
  obj X := X ⊗ Y
  map f := f ▷ Y
  map_id X := MonoidalSupercategory.id_whiskerRight (R := R) X Y
  map_comp f g := MonoidalSupercategory.comp_whiskerRight (R := R) f g Y

instance (Y : A) : (rightMul R Y).Additive where
  map_add := MonoidalSupercategory.add_whiskerRight (R := R) _ _ _

instance (Y : A) : (rightMul R Y).Linear R where
  map_smul f r := MonoidalSupercategory.smul_whiskerRight r f _

instance (Y : A) : IsSuperfunctor R (rightMul R Y) where
  map_mem hf := MonoidalSupercategory.whiskerRight_mem _ hf

theorem proj_whiskerLeft (p : ZMod 2) (X : A) {Y Y' : A} (g : Y ⟶ Y') :
    proj R p (X ◁ g) = X ◁ proj R p g :=
  (map_proj (leftMul R X) p g).symm

theorem proj_whiskerRight (p : ZMod 2) {X X' : A} (f : X ⟶ X') (Y : A) :
    proj R p (f ▷ Y) = proj R p f ▷ Y :=
  (map_proj (rightMul R Y) p f).symm

/-- The right `A`-module superfunctor `X ⊗ -`, with module structure `γ = a_{X,-,-}`. -/
@[simps]
def ιObj (X : A) : Strictification R A where
  toFunctor := leftMul R X
  γ Y Z := α_ X Y Z
  γ_mem Y Z := MonoidalSupercategory.associator_hom_mem (R := R) X Y Z
  γ_naturality_left g Z := MonoidalSupercategory.associator_naturality_middle R X g Z
  γ_naturality_right Y {_ _} h := MonoidalSupercategory.associator_naturality_right R X Y h
  γ_assoc Y Z W := (MonoidalSupercategory.pentagon (R := R) X Y Z W).symm

/-- For `f : X ⟶ X'`, the supernatural transformation `f ⊗ 1 : X ⊗ - ⇒ X' ⊗ -`, whose
component of parity `p` is `f_p ⊗ 1`. It is supernatural by the super interchange law. -/
def leftMulHom {X X' : A} (f : X ⟶ X') :
    SuperNatTrans R (leftMul R X) (leftMul R X') where
  app p Y := proj R p f ▷ Y
  app_mem p Y := MonoidalSupercategory.whiskerRight_mem Y (proj_mem p f)
  naturality p {Y Y'} {q} g hg := by
    change X ◁ g ≫ proj R p f ▷ Y' = koszulSign p q • (proj R p f ▷ Y ≫ X' ◁ g)
    rw [MonoidalSupercategory.super_interchange (proj_mem p f) hg, koszulSign_smul_smul]

variable (R A) in
/-- **Brundan–Ellis, after Definition 1.4.** The superfunctor
`ι : A → Strictification R A`, `X ↦ (X ⊗ -, a_{X,-,-})`, `f ↦ f ⊗ 1_-`. -/
def ι : A ⥤ Strictification R A where
  obj := ιObj
  map f := ⟨leftMulHom f, fun p Y Z =>
    (MonoidalSupercategory.associator_naturality_left R (proj R p f) Y Z).symm⟩
  map_id X := hom_ext (Superfunctor.hom_ext fun p Y => by
    change proj R p (𝟙 X) ▷ Y = (SuperNatTrans.id (leftMul R X)).app p Y
    rw [proj_id]
    rcases parity_eq_zero_or_one p with rfl | rfl
    · simp [MonoidalSupercategory.id_whiskerRight (R := R)]
    · simp [zmod2_one_ne_zero, MonoidalSupercategory.zero_whiskerRight R])
  map_comp f g := hom_ext (Superfunctor.hom_ext fun r Y => by
    change proj R r (f ≫ g) ▷ Y =
      proj R 0 f ▷ Y ≫ proj R r g ▷ Y + proj R 1 f ▷ Y ≫ proj R (r + 1) g ▷ Y
    rw [proj_comp, MonoidalSupercategory.add_whiskerRight (R := R),
      MonoidalSupercategory.comp_whiskerRight (R := R),
      MonoidalSupercategory.comp_whiskerRight (R := R)])

@[simp] theorem ι_obj (X : A) : (ι R A).obj X = ιObj X := rfl

@[simp] theorem ι_map_val_app {X X' : A} (f : X ⟶ X') (p : ZMod 2) (Y : A) :
    ((ι R A).map f).1.app p Y = proj R p f ▷ Y := rfl

instance : (ι R A).Additive where
  map_add {X X' f g} := hom_ext (Superfunctor.hom_ext fun p Y => by
    change proj R p (f + g) ▷ Y = proj R p f ▷ Y + proj R p g ▷ Y
    rw [map_add, MonoidalSupercategory.add_whiskerRight (R := R)])

instance : (ι R A).Linear R where
  map_smul {X X'} f r := hom_ext (Superfunctor.hom_ext fun p Y => by
    change proj R p (r • f) ▷ Y = r • (proj R p f ▷ Y)
    rw [map_smul, MonoidalSupercategory.smul_whiskerRight (R := R)])

instance : IsSuperfunctor R (ι R A) where
  map_mem {X X' p f} hf := by
    rw [mem_parity_iff, Superfunctor.mem_parity_iff]
    funext Y
    change proj R (p + 1) f ▷ Y = 0
    rw [proj_of_mem_ne hf (zmod2_add_one_ne p).symm, MonoidalSupercategory.zero_whiskerRight R]

/-! ## `ι` is fully faithful and evenly dense -/

section FullyFaithful

variable {X X' : A} (θ : (ι R A).obj X ⟶ (ι R A).obj X')

theorem ι_hom_compat (p : ZMod 2) (Y Z : A) :
    (α_ X Y Z).hom ≫ θ.1.app p (Y ⊗ Z) = θ.1.app p Y ▷ Z ≫ (α_ X' Y Z).hom :=
  θ.2 p Y Z

/-- A morphism `θ : X ⊗ - ⇒ X' ⊗ -` of right module superfunctors is `f ⊗ 1_-` for
`f = r_{X'} ∘ θ_1 ∘ r_X⁻¹` (componentwise in the parity). -/
theorem ι_app_eq (p : ZMod 2) (Y : A) :
    θ.1.app p Y = ((ρ_ X).inv ≫ θ.1.app p (𝟙_ A) ≫ (ρ_ X').hom) ▷ Y := by
  have hn : X ◁ (λ_ Y).hom ≫ θ.1.app p Y = θ.1.app p (𝟙_ A ⊗ Y) ≫ X' ◁ (λ_ Y).hom := by
    have := θ.1.naturality p (λ_ Y).hom (MonoidalSupercategory.leftUnitor_hom_mem (R := R) Y)
    rwa [koszulSign_zero_right, one_smul] at this
  have key : (ρ_ X).hom ▷ Y ≫ θ.1.app p Y = θ.1.app p (𝟙_ A) ▷ Y ≫ (ρ_ X').hom ▷ Y := by
    rw [← MonoidalSupercategory.triangle (R := R) X Y, Category.assoc, hn,
      ← Category.assoc, ι_hom_compat, Category.assoc,
      MonoidalSupercategory.triangle (R := R) X' Y]
  rw [MonoidalSupercategory.comp_whiskerRight (R := R),
    MonoidalSupercategory.comp_whiskerRight (R := R), ← key, ← Category.assoc,
    ← MonoidalSupercategory.comp_whiskerRight (R := R), Iso.inv_hom_id,
    MonoidalSupercategory.id_whiskerRight (R := R), Category.id_comp]

/-- The preimage of `θ : X ⊗ - ⇒ X' ⊗ -` under `ι`: `r_{X'} ∘ θ_1 ∘ r_X⁻¹`. -/
def ιPreimage : X ⟶ X' :=
  (ρ_ X).inv ≫ (θ.1.app 0 (𝟙_ A) + θ.1.app 1 (𝟙_ A)) ≫ (ρ_ X').hom

theorem proj_ιPreimage (p : ZMod 2) :
    proj R p (ιPreimage θ) = (ρ_ X).inv ≫ θ.1.app p (𝟙_ A) ≫ (ρ_ X').hom := by
  have hmem : ∀ q, (ρ_ X).inv ≫ θ.1.app q (𝟙_ A) ≫ (ρ_ X').hom ∈ parity (R := R) X X' q := by
    intro q
    have := comp_mem (inv_mem _ (MonoidalSupercategory.rightUnitor_hom_mem (R := R) X))
      (comp_mem (θ.1.app_mem q (𝟙_ A)) (MonoidalSupercategory.rightUnitor_hom_mem (R := R) X'))
    simpa using this
  have e : ιPreimage θ = (ρ_ X).inv ≫ θ.1.app 0 (𝟙_ A) ≫ (ρ_ X').hom +
      (ρ_ X).inv ≫ θ.1.app 1 (𝟙_ A) ≫ (ρ_ X').hom := by
    simp [ιPreimage, Preadditive.add_comp, Preadditive.comp_add]
  rcases parity_eq_zero_or_one p with rfl | rfl
  · exact proj_eq_of_add e (hmem 0) (hmem 1)
  · rw [add_comm] at e
    exact proj_eq_of_add e (hmem 1) (hmem 0)

end FullyFaithful

/-- **Brundan–Ellis, after Definition 1.4.** `ι` is fully faithful. -/
def ιFullyFaithful : (ι R A).FullyFaithful where
  preimage := ιPreimage
  map_preimage θ := hom_ext (Superfunctor.hom_ext fun p Y => by
    rw [ι_map_val_app, proj_ιPreimage, ← ι_app_eq])
  preimage_map {X X'} f := by
    change (ρ_ X).inv ≫ (proj R 0 f ▷ 𝟙_ A + proj R 1 f ▷ 𝟙_ A) ≫ (ρ_ X').hom = f
    rw [← MonoidalSupercategory.add_whiskerRight (R := R), proj_add_proj,
      MonoidalSupercategory.rightUnitor_naturality (R := R), Iso.inv_hom_id_assoc]

instance : (ι R A).Full := ιFullyFaithful.full

instance : (ι R A).Faithful := ιFullyFaithful.faithful

/-- The even isomorphism `F(1) ⊗ - ≅ F`, with components `F(l_X) ∘ γ_{1,X}`. -/
def ιObjIso (M : Strictification R A) : (ι R A).obj (M.toFunctor.obj (𝟙_ A)) ≅ M :=
  isoMk (fun Y => M.γ (𝟙_ A) Y ≪≫ M.toFunctor.mapIso (λ_ Y))
    (fun Y => by
      simpa using comp_mem (M.γ_mem (𝟙_ A) Y)
        (map_mem M.toFunctor (MonoidalSupercategory.leftUnitor_hom_mem (R := R) Y)))
    (fun {Y Y'} g => by
      change M.toFunctor.obj (𝟙_ A) ◁ g ≫ (M.γ (𝟙_ A) Y').hom ≫ M.toFunctor.map (λ_ Y').hom =
        ((M.γ (𝟙_ A) Y).hom ≫ M.toFunctor.map (λ_ Y).hom) ≫ M.toFunctor.map g
      rw [M.γ_naturality_right_assoc, Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
        MonoidalSupercategory.leftUnitor_naturality (R := R)])
    (fun Y Z => by
      change (α_ (M.toFunctor.obj (𝟙_ A)) Y Z).hom ≫ (M.γ (𝟙_ A) (Y ⊗ Z)).hom ≫
          M.toFunctor.map (λ_ (Y ⊗ Z)).hom =
        ((M.γ (𝟙_ A) Y).hom ≫ M.toFunctor.map (λ_ Y).hom) ▷ Z ≫ (M.γ Y Z).hom
      rw [M.γ_assoc_assoc, MonoidalSupercategory.comp_whiskerRight (R := R), Category.assoc,
        M.γ_naturality_left, ← Functor.map_comp, MonoidalSupercategory.leftUnitor_tensor R,
        Iso.hom_inv_id_assoc])

theorem ιObjIso_hom_val_app (M : Strictification R A) (p : ZMod 2) (Y : A) :
    (ιObjIso M).hom.1.app p Y =
      if p = 0 then (M.γ (𝟙_ A) Y).hom ≫ M.toFunctor.map (λ_ Y).hom else 0 := rfl

theorem ιObjIso_hom_mem (M : Strictification R A) :
    (ιObjIso M).hom ∈ parity (R := R) _ _ 0 := by
  rw [mem_parity_iff, Superfunctor.mem_parity_iff]
  funext Y
  rw [ιObjIso_hom_val_app]
  simp [zmod2_one_ne_zero]

/-- **Brundan–Ellis, after Definition 1.4.** `ι` is evenly dense: every right module
superfunctor `F` is evenly isomorphic to `F(1) ⊗ -`. -/
theorem ι_evenlyDense : EvenlyDense R (ι R A) :=
  fun M => ⟨M.toFunctor.obj (𝟙_ A), ιObjIso M, ιObjIso_hom_mem M⟩

/-- **Brundan–Ellis, after Definition 1.4.** `ι : A → Strictification R A` is a
superequivalence (Definition 1.1(iv)). -/
def ιSuperequivalence : Superequivalence R (ι R A) :=
  Superequivalence.ofFullyFaithful (ι R A) ι_evenlyDense

/-! ## `ι` is monoidal -/

section Components

variable {M N P : Strictification R A}

theorem comp_isoMk_hom_val_app (x : M ⟶ N) (e : ∀ X, N.toFunctor.obj X ≅ P.toFunctor.obj X)
    (mem : ∀ X, (e X).hom ∈ parity (R := R) _ _ 0)
    (nat : ∀ {X Y : A} (f : X ⟶ Y), N.toFunctor.map f ≫ (e Y).hom = (e X).hom ≫ P.toFunctor.map f)
    (compat : ∀ X Y, (N.γ X Y).hom ≫ (e (X ⊗ Y)).hom = (e X).hom ▷ Y ≫ (P.γ X Y).hom)
    (r : ZMod 2) (X : A) :
    (x ≫ (isoMk e mem nat compat).hom).1.app r X = x.1.app r X ≫ (e X).hom := by
  rw [comp_val, comp_app]
  rcases parity_eq_zero_or_one r with rfl | rfl <;>
    simp [zmod2_one_ne_zero, SuperNatTrans.zmod2_one_add_one]

theorem isoMk_hom_comp_val_app (e : ∀ X, M.toFunctor.obj X ≅ N.toFunctor.obj X)
    (mem : ∀ X, (e X).hom ∈ parity (R := R) _ _ 0)
    (nat : ∀ {X Y : A} (f : X ⟶ Y), M.toFunctor.map f ≫ (e Y).hom = (e X).hom ≫ N.toFunctor.map f)
    (compat : ∀ X Y, (M.γ X Y).hom ≫ (e (X ⊗ Y)).hom = (e X).hom ▷ Y ≫ (N.γ X Y).hom)
    (x : N ⟶ P) (r : ZMod 2) (X : A) :
    ((isoMk e mem nat compat).hom ≫ x).1.app r X = (e X).hom ≫ x.1.app r X := by
  rw [comp_val, comp_app]
  rcases parity_eq_zero_or_one r with rfl | rfl <;>
    simp [zmod2_one_ne_zero, SuperNatTrans.zmod2_one_add_one]

end Components

/-- The coherence isomorphism `(X ⊗ -) ∘ (Y ⊗ -) ≅ (X ⊗ Y) ⊗ -` of `ι`, with components
`a⁻¹_{X,Y,-}`. -/
def ιμIso (X Y : A) : (ι R A).obj X ⊗ (ι R A).obj Y ≅ (ι R A).obj (X ⊗ Y) :=
  isoMk (fun Z => (α_ X Y Z).symm)
    (fun Z => inv_mem _ (MonoidalSupercategory.associator_hom_mem (R := R) X Y Z))
    (fun {_ _} g => MonoidalSupercategory.associator_inv_naturality_right R X Y g)
    (fun Z W => by
      change ((α_ X (Y ⊗ Z) W).hom ≫ X ◁ (α_ Y Z W).hom) ≫ (α_ X Y (Z ⊗ W)).inv =
        (α_ X Y Z).inv ▷ W ≫ (α_ (X ⊗ Y) Z W).hom
      rw [Category.assoc, MonoidalSupercategory.coherence_pentagon_inv R])

/-- The coherence isomorphism `1 ≅ 1 ⊗ -` of `ι`, with components `l⁻¹`. -/
def ιεIso : 𝟙_ (Strictification R A) ≅ (ι R A).obj (𝟙_ A) :=
  isoMk (fun Z => (λ_ Z).symm)
    (fun Z => inv_mem _ (MonoidalSupercategory.leftUnitor_hom_mem (R := R) Z))
    (fun {_ _} g => MonoidalSupercategory.leftUnitor_inv_naturality (R := R) g)
    (fun Z W => by
      change 𝟙 ((Z : A) ⊗ W) ≫ (λ_ ((Z : A) ⊗ W)).inv = (λ_ Z).inv ▷ W ≫ (α_ (𝟙_ A) Z W).hom
      rw [Category.id_comp, MonoidalSupercategory.coherence_leftUnitor_inv_tensor R])

omit [MonoidalCategoryStruct A] [MonoidalSupercategory R A] in
theorem proj_of_even {X Y : A} {f : X ⟶ Y} (hf : f ∈ parity (R := R) X Y 0) (p : ZMod 2) :
    proj R p f = if p = 0 then f else 0 := by
  split_ifs with h
  · subst h; exact proj_of_mem hf
  · exact proj_of_mem_ne hf (Ne.symm h)

/-- **Brundan–Ellis, after Definition 1.4.** `ι : A → Strictification R A` is a monoidal
superfunctor, with coherence maps `c_{X,Y} = a⁻¹_{X,Y,-}` and `i = l⁻¹`. -/
def ιMonoidal : MonoidalSuperfunctor R (ι R A) where
  μIso := ιμIso
  εIso := ιεIso
  μ_mem X Y := isoMk_hom_mem _ _ _ _
  ε_mem := isoMk_hom_mem _ _ _ _
  μ_natural_left {X X'} f Y := hom_ext (Superfunctor.hom_ext fun r Z => by
    rw [ιμIso, ιμIso, comp_isoMk_hom_val_app, isoMk_hom_comp_val_app]
    change proj R r f ▷ (Y ⊗ Z) ≫ (α_ X' Y Z).inv = (α_ X Y Z).inv ≫ proj R r (f ▷ Y) ▷ Z
    rw [proj_whiskerRight, MonoidalSupercategory.associator_inv_naturality_left (R := R)])
  μ_natural_right {Y Y'} X g := hom_ext (Superfunctor.hom_ext fun r Z => by
    rw [ιμIso, ιμIso, comp_isoMk_hom_val_app, isoMk_hom_comp_val_app]
    change X ◁ (proj R r g ▷ Z) ≫ (α_ X Y' Z).inv = (α_ X Y Z).inv ≫ proj R r (X ◁ g) ▷ Z
    rw [proj_whiskerLeft, MonoidalSupercategory.associator_inv_naturality_middle (R := R)])
  associativity X Y Z := hom_ext (Superfunctor.hom_ext fun r W => by
    have ha := proj_of_even (MonoidalSupercategory.associator_hom_mem (R := R) X Y Z)
    rcases parity_eq_zero_or_one r with rfl | rfl
    · simp [ιμIso, ha, zmod2_one_ne_zero, MonoidalSupercategory.zero_whiskerRight R,
        MonoidalSupercategory.whiskerLeft_zero R]
      exact MonoidalSupercategory.coherence_pentagon_inv' R X Y Z W
    · simp [ιμIso, ha, zmod2_one_ne_zero, MonoidalSupercategory.zero_whiskerRight R,
        MonoidalSupercategory.whiskerLeft_zero R])
  left_unitality X := hom_ext (Superfunctor.hom_ext fun r Y => by
    have hl := proj_of_even (MonoidalSupercategory.leftUnitor_hom_mem (R := R) X)
    rcases parity_eq_zero_or_one r with rfl | rfl
    · simp [ιμIso, ιεIso, hl, zmod2_one_ne_zero, MonoidalSupercategory.zero_whiskerRight R]
      exact (MonoidalSupercategory.coherence_left_unitality R X Y).symm
    · simp [ιμIso, ιεIso, hl, zmod2_one_ne_zero, MonoidalSupercategory.zero_whiskerRight R])
  right_unitality X := hom_ext (Superfunctor.hom_ext fun r Y => by
    have hr := proj_of_even (MonoidalSupercategory.rightUnitor_hom_mem (R := R) X)
    rcases parity_eq_zero_or_one r with rfl | rfl
    · simp [ιμIso, ιεIso, hr, zmod2_one_ne_zero, MonoidalSupercategory.zero_whiskerRight R]
      exact (MonoidalSupercategory.coherence_right_unitality R X Y).symm
    · simp [ιμIso, ιεIso, hr, zmod2_one_ne_zero, MonoidalSupercategory.zero_whiskerRight R,
        MonoidalSupercategory.whiskerLeft_zero R])

/-! ## Evaluation at the unit object -/

variable (R A) in
/-- **Brundan–Ellis, after Definition 1.4.** Evaluation at the unit object,
`ev : Strictification R A → A`, `F ↦ F(1)`, `x ↦ x_1`. -/
def ev : Strictification R A ⥤ A where
  obj M := M.toFunctor.obj (𝟙_ A)
  map x := x.1.app 0 (𝟙_ A) + x.1.app 1 (𝟙_ A)
  map_id M := by simp
  map_comp x y := by
    simp only [comp_val, comp_app_zero, comp_app_one, Preadditive.add_comp,
      Preadditive.comp_add]
    abel

@[simp] theorem ev_obj (M : Strictification R A) : (ev R A).obj M = M.toFunctor.obj (𝟙_ A) :=
  rfl

theorem ev_map {M N : Strictification R A} (x : M ⟶ N) :
    (ev R A).map x = x.1.app 0 (𝟙_ A) + x.1.app 1 (𝟙_ A) := rfl

instance : (ev R A).Additive where
  map_add {M N x y} := by simp only [ev_map, add_val, add_app]; abel

instance : (ev R A).Linear R where
  map_smul {M N} x r := by simp only [ev_map, smul_val, smul_app, smul_add]

instance : IsSuperfunctor R (ev R A) where
  map_mem {M N p x} hx := by
    rw [mem_parity_iff, Superfunctor.mem_parity_iff] at hx
    have h := congrFun hx (𝟙_ A)
    rw [ev_map]
    rcases parity_eq_zero_or_one p with rfl | rfl
    · simp only [zero_add, Pi.zero_apply] at h
      rw [h, add_zero]; exact x.1.app_mem 0 _
    · simp only [SuperNatTrans.zmod2_one_add_one, Pi.zero_apply] at h
      rw [h, zero_add]; exact x.1.app_mem 1 _

/-- The compatibility of a morphism `x : F ⇒ G` of `Strictification R A` with the
isomorphisms `F(1) ⊗ - ≅ F`: `x_- ∘ F(l) ∘ γ_{1,-} = G(l) ∘ γ_{1,-} ∘ (x_1 ⊗ 1)`. -/
theorem ev_compat {M N : Strictification R A} (x : M ⟶ N) (p : ZMod 2) (Y : A) :
    x.1.app p (𝟙_ A) ▷ Y ≫ (N.γ (𝟙_ A) Y).hom ≫ N.toFunctor.map (λ_ Y).hom =
      (M.γ (𝟙_ A) Y).hom ≫ M.toFunctor.map (λ_ Y).hom ≫ x.1.app p Y := by
  have hn := x.1.naturality p (λ_ Y).hom (MonoidalSupercategory.leftUnitor_hom_mem (R := R) Y)
  rw [koszulSign_zero_right, one_smul] at hn
  rw [← reassoc_of% (hom_compat x p (𝟙_ A) Y), hn]

/-- The coherence isomorphism `F(1) ⊗ G(1) ≅ F(G(1))` of `ev`, `F(l) ∘ γ_{1,G(1)}`. -/
def evμIso (M N : Strictification R A) : (ev R A).obj M ⊗ (ev R A).obj N ≅ (ev R A).obj (M ⊗ N) :=
  M.γ (𝟙_ A) (N.toFunctor.obj (𝟙_ A)) ≪≫ M.toFunctor.mapIso (λ_ (N.toFunctor.obj (𝟙_ A)))

theorem evμIso_hom (M N : Strictification R A) :
    (evμIso M N).hom = (M.γ (𝟙_ A) (N.toFunctor.obj (𝟙_ A))).hom ≫
      M.toFunctor.map (λ_ (N.toFunctor.obj (𝟙_ A))).hom := rfl

@[simp] theorem ev_map_associator_hom (M N P : Strictification R A) :
    (ev R A).map (α_ M N P).hom = 𝟙 _ := by
  rw [ev_map, associator_hom_val, Superfunctor.id_app_zero, Superfunctor.id_app_one, add_zero]
  rfl

@[simp] theorem ev_map_leftUnitor_hom (M : Strictification R A) :
    (ev R A).map (λ_ M).hom = 𝟙 _ := by
  rw [ev_map, leftUnitor_hom_val, Superfunctor.id_app_zero, Superfunctor.id_app_one, add_zero]
  rfl

@[simp] theorem ev_map_rightUnitor_hom (M : Strictification R A) :
    (ev R A).map (ρ_ M).hom = 𝟙 _ := by
  rw [ev_map, rightUnitor_hom_val, Superfunctor.id_app_zero, Superfunctor.id_app_one, add_zero]
  rfl

/-- **Brundan–Ellis, after Definition 1.4.** `ev : Strictification R A → A` is a monoidal
superfunctor, with coherence maps `c_{F,G} = F(l_{G(1)}) ∘ γ_{1,G(1)}` and `i = 1`. -/
def evMonoidal : MonoidalSuperfunctor R (ev R A) where
  μIso := evμIso
  εIso := Iso.refl _
  μ_mem M N := by
    simpa [evμIso] using comp_mem (M.γ_mem (𝟙_ A) (N.toFunctor.obj (𝟙_ A)))
      (map_mem M.toFunctor (MonoidalSupercategory.leftUnitor_hom_mem (R := R) _))
  ε_mem := id_mem _
  μ_natural_left {M M'} x N := by
    rw [evμIso_hom, evμIso_hom, ev_map, ev_map]
    simp only [whiskerRight_val, Superfunctor.whiskerLeft_app, Superfunctor.obj, ev_obj,
      MonoidalSupercategory.add_whiskerRight (R := R), Preadditive.add_comp,
      Preadditive.comp_add, Category.assoc, ev_compat]
  μ_natural_right {N N'} M y := by
    rw [evμIso_hom, evμIso_hom, ev_map, ev_map, M.γ_naturality_right_assoc, ← Functor.map_comp,
      ← Functor.map_comp, MonoidalSupercategory.leftUnitor_naturality (R := R),
      Functor.map_comp]
    simp only [whiskerLeft_val, Superfunctor.whiskerRight_app, Superfunctor.map,
      Functor.map_add]
    rfl
  associativity M N P := by
    rw [evμIso_hom, evμIso_hom, evμIso_hom, evμIso_hom, ev_map_associator_hom, Category.comp_id]
    simp only [tensorObj_γ_hom, tensorObj_toFunctor', Functor.comp_map, Functor.comp_obj,
      MonoidalSupercategory.comp_whiskerRight (R := R),
      MonoidalSupercategory.whiskerLeft_comp (R := R), Category.assoc, ev_obj]
    rw [M.γ_naturality_left_assoc, M.γ_naturality_right_assoc, M.γ_naturality_right_assoc,
      M.γ_assoc_assoc]
    simp only [← Functor.map_comp]
    have key : (λ_ (N.toFunctor.obj (𝟙_ A))).hom ▷ P.toFunctor.obj (𝟙_ A) ≫
        (N.γ (𝟙_ A) (P.toFunctor.obj (𝟙_ A))).hom ≫
          N.toFunctor.map (λ_ (P.toFunctor.obj (𝟙_ A))).hom =
        (α_ (𝟙_ A) (N.toFunctor.obj (𝟙_ A)) (P.toFunctor.obj (𝟙_ A))).hom ≫
          𝟙_ A ◁ (N.γ (𝟙_ A) (P.toFunctor.obj (𝟙_ A))).hom ≫
            𝟙_ A ◁ N.toFunctor.map (λ_ (P.toFunctor.obj (𝟙_ A))).hom ≫
              (λ_ (N.toFunctor.obj (P.toFunctor.obj (𝟙_ A)))).hom := by
      rw [MonoidalSupercategory.leftUnitor_naturality (R := R),
        reassoc_of% (MonoidalSupercategory.leftUnitor_naturality (R := R)
          (N.γ (𝟙_ A) (P.toFunctor.obj (𝟙_ A))).hom),
        MonoidalSupercategory.leftUnitor_tensor R, Iso.hom_inv_id_assoc]
    rw [key]
  left_unitality M := by
    rw [evμIso_hom, ev_map_leftUnitor_hom]
    simp [MonoidalSupercategory.id_whiskerRight (R := R)]
  right_unitality M := by
    rw [evμIso_hom, ev_map_rightUnitor_hom]
    simp only [Iso.refl_hom, MonoidalSupercategory.whiskerLeft_id (R := R), Category.id_comp,
      Category.comp_id, tensorUnit_toFunctor', Functor.id_obj]
    rw [MonoidalSupercategory.unitors_equal R, γ_unit]
    rfl

end Strictification

end StringDiagrams

end
