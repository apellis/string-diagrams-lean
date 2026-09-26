import StringDiagrams.Super.Supernatural

/-!
# The supercategory of superfunctors

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Example 1.2(iv) and the construction of the strict 2-supercategory `𝔖ℭ𝔞𝔱` after
Definition 2.1.

For supercategories `A` and `B`, the superfunctors `A → B` and the supernatural transformations
between them form a supercategory `ℋom(A, B)` (Example 1.2(iv)). We bundle a superfunctor as
`Supercategory.Superfunctor R A B` (an `R`-linear functor preserving parities), and make it a
category whose morphisms are the supernatural transformations `Supercategory.SuperNatTrans`
(given by their homogeneous components), composed vertically. The morphisms of parity `p` are
the supernatural transformations whose component of parity `p + 1` vanishes; every
supernatural transformation is uniquely `x = x₀ + x₁` (Definition 1.1(iii)).

Horizontal composition of supernatural transformations `x : F ⇒ H` and `y : G ⇒ K` (for
`F, H : A → B` and `G, K : B → C`) is `(yx)_λ := y_{Hλ} ∘ G x_λ`
(`Superfunctor.hcomp`); in the diagrammatic order used here it is
`whiskerRight x G ≫ whiskerLeft H y`. The super interchange law of Section 2 holds
(`Superfunctor.whisker_exchange`, `Superfunctor.hcomp_comp_hcomp`); as the paper remarks, this
works because of the signs in the definition of a supernatural transformation.

## Main definitions

* `Supercategory.Superfunctor R C D`, `Superfunctor.id`, `Superfunctor.comp`.
* Instances `Category`, `Preadditive`, `Linear R` and `Supercategory R` on
  `Superfunctor R C D` (Example 1.2(iv)).
* `Superfunctor.whiskerLeft`, `Superfunctor.whiskerRight`, `Superfunctor.hcomp`.

## Main statements

* `Superfunctor.mem_parity_iff`: the morphisms of parity `p` are the supernatural
  transformations that are homogeneous of parity `p` in the sense of Definition 1.1(iii).
* `Superfunctor.whisker_exchange`: `yH ∘ Gx = (-1)^{|x||y|} Kx ∘ yF`.
* `Superfunctor.hcomp_comp_hcomp`: `(vu) ∘ (yx) = (-1)^{|u||y|} (v ∘ y)(u ∘ x)`.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory

universe w u₁ v₁ u₂ v₂ u₃ v₃

namespace Supercategory

variable {R : Type w} [CommRing R]

/-! ## Components of supernatural transformations -/

namespace SuperNatTrans

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear R C] [Supercategory R C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear R D] [Supercategory R D]
  {F G H : C ⥤ D}

theorem zmod2_one_add_one : (1 : ZMod 2) + 1 = 0 := rfl

/-- Supernatural transformations are equal if their even and odd components are. -/
theorem ext_parity {x y : SuperNatTrans R F G} (h0 : ∀ X, x.app 0 X = y.app 0 X)
    (h1 : ∀ X, x.app 1 X = y.app 1 X) : x = y := by
  ext p X
  rcases parity_eq_zero_or_one p with rfl | rfl
  · exact h0 X
  · exact h1 X

@[simp] theorem vcomp_app_zero (x : SuperNatTrans R F G) (y : SuperNatTrans R G H) (X : C) :
    (x.vcomp y).app 0 X = x.app 0 X ≫ y.app 0 X + x.app 1 X ≫ y.app 1 X := by
  simp [vcomp]

@[simp] theorem vcomp_app_one (x : SuperNatTrans R F G) (y : SuperNatTrans R G H) (X : C) :
    (x.vcomp y).app 1 X = x.app 0 X ≫ y.app 1 X + x.app 1 X ≫ y.app 0 X := by
  simp only [vcomp, zmod2_one_add_one]

end SuperNatTrans

/-! ## Bundled superfunctors -/

variable (R) in
/-- A superfunctor (Brundan–Ellis, Definition 1.1(ii)), bundled: an `R`-linear functor
preserving the parity of homogeneous morphisms. These are the objects of the supercategory
`ℋom(C, D)` of Example 1.2(iv). -/
@[ext]
structure Superfunctor (C : Type u₁) [Category.{v₁} C] [Preadditive C] [Linear R C]
    [Supercategory R C] (D : Type u₂) [Category.{v₂} D] [Preadditive D] [Linear R D]
    [Supercategory R D] where
  /-- The underlying functor. -/
  toFunctor : C ⥤ D
  [additive : toFunctor.Additive]
  [linear : toFunctor.Linear R]
  [isSuperfunctor : IsSuperfunctor R toFunctor]

namespace Superfunctor

attribute [instance] additive linear isSuperfunctor

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear R C] [Supercategory R C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear R D] [Supercategory R D]
  {E : Type u₃} [Category.{v₃} E] [Preadditive E] [Linear R E] [Supercategory R E]

/-- The object part of a superfunctor. -/
abbrev obj (F : Superfunctor R C D) (X : C) : D := F.toFunctor.obj X

/-- The morphism part of a superfunctor. -/
abbrev map (F : Superfunctor R C D) {X Y : C} (f : X ⟶ Y) : F.obj X ⟶ F.obj Y :=
  F.toFunctor.map f

theorem map_mem (F : Superfunctor R C D) {X Y : C} {p : ZMod 2} {f : X ⟶ Y}
    (hf : f ∈ parity (R := R) X Y p) : F.map f ∈ parity (R := R) (F.obj X) (F.obj Y) p :=
  IsSuperfunctor.map_mem hf

variable (R C) in
/-- The identity superfunctor. -/
@[simps]
def id : Superfunctor R C C := ⟨𝟭 C⟩

/-- The composite of superfunctors `F ⋙ G` (the paper's `G F`). -/
@[simps]
def comp (F : Superfunctor R C D) (G : Superfunctor R D E) : Superfunctor R C E :=
  ⟨F.toFunctor ⋙ G.toFunctor⟩

theorem id_comp (F : Superfunctor R C D) : (id R C).comp F = F := rfl

theorem comp_id (F : Superfunctor R C D) : F.comp (id R D) = F := rfl

theorem comp_assoc {C' : Type*} [Category C'] [Preadditive C'] [Linear R C'] [Supercategory R C']
    (F : Superfunctor R C D) (G : Superfunctor R D E) (H : Superfunctor R E C') :
    (F.comp G).comp H = F.comp (G.comp H) := rfl

/-! ## The category of superfunctors -/

instance : Category (Superfunctor R C D) where
  Hom F G := SuperNatTrans R F.toFunctor G.toFunctor
  id F := SuperNatTrans.id F.toFunctor
  comp x y := x.vcomp y
  id_comp x := SuperNatTrans.ext_parity (fun X => by simp) (fun X => by simp)
  comp_id x := SuperNatTrans.ext_parity (fun X => by simp) (fun X => by simp)
  assoc x y z := SuperNatTrans.ext_parity
    (fun X => by simp only [SuperNatTrans.vcomp_app_zero, SuperNatTrans.vcomp_app_one,
      Preadditive.add_comp, Preadditive.comp_add, Category.assoc]; abel)
    (fun X => by simp only [SuperNatTrans.vcomp_app_zero, SuperNatTrans.vcomp_app_one,
      Preadditive.add_comp, Preadditive.comp_add, Category.assoc]; abel)

variable {F G H K : Superfunctor R C D}

/-- A morphism of superfunctors, viewed as a supernatural transformation. -/
abbrev toSuperNatTrans (x : F ⟶ G) : SuperNatTrans R F.toFunctor G.toFunctor := x

/-- A supernatural transformation, viewed as a morphism of superfunctors. -/
abbrev homMk (x : SuperNatTrans R F.toFunctor G.toFunctor) : F ⟶ G := x

@[ext]
theorem hom_ext {x y : F ⟶ G} (h : ∀ p X, x.app p X = y.app p X) : x = y :=
  SuperNatTrans.ext (funext fun p => funext fun X => h p X)

theorem hom_ext_parity {x y : F ⟶ G} (h0 : ∀ X, x.app 0 X = y.app 0 X)
    (h1 : ∀ X, x.app 1 X = y.app 1 X) : x = y :=
  SuperNatTrans.ext_parity h0 h1

@[simp] theorem id_app_zero (F : Superfunctor R C D) (X : C) :
    (𝟙 F : F ⟶ F).app 0 X = 𝟙 (F.obj X) := rfl

@[simp] theorem id_app_one (F : Superfunctor R C D) (X : C) :
    (𝟙 F : F ⟶ F).app 1 X = 0 := rfl

@[simp] theorem comp_app_zero (x : F ⟶ G) (y : G ⟶ H) (X : C) :
    (x ≫ y).app 0 X = x.app 0 X ≫ y.app 0 X + x.app 1 X ≫ y.app 1 X :=
  SuperNatTrans.vcomp_app_zero x y X

@[simp] theorem comp_app_one (x : F ⟶ G) (y : G ⟶ H) (X : C) :
    (x ≫ y).app 1 X = x.app 0 X ≫ y.app 1 X + x.app 1 X ≫ y.app 0 X :=
  SuperNatTrans.vcomp_app_one x y X

theorem comp_app (x : F ⟶ G) (y : G ⟶ H) (r : ZMod 2) (X : C) :
    (x ≫ y).app r X = x.app 0 X ≫ y.app r X + x.app 1 X ≫ y.app (r + 1) X := rfl

theorem comp_total (x : F ⟶ G) (y : G ⟶ H) (X : C) :
    SuperNatTrans.total (x ≫ y) X = x.total X ≫ y.total X :=
  SuperNatTrans.vcomp_total x y X

/-! ## Linear structure -/

section Linear

instance : Zero (F ⟶ G) where
  zero :=
    { app := fun _ _ => 0
      app_mem := fun _ _ => Submodule.zero_mem _
      naturality := fun _ _ _ _ _ _ => by simp }

instance : Add (F ⟶ G) where
  add x y :=
    { app := fun p X => x.app p X + y.app p X
      app_mem := fun p X => Submodule.add_mem _ (x.app_mem p X) (y.app_mem p X)
      naturality := fun p X Y q f hf => by
        rw [Preadditive.comp_add, x.naturality p f hf, y.naturality p f hf, Preadditive.add_comp,
          smul_add] }

instance : Neg (F ⟶ G) where
  neg x :=
    { app := fun p X => -x.app p X
      app_mem := fun p X => Submodule.neg_mem _ (x.app_mem p X)
      naturality := fun p X Y q f hf => by
        rw [Preadditive.comp_neg, x.naturality p f hf, Preadditive.neg_comp, smul_neg] }

instance : Sub (F ⟶ G) where
  sub x y :=
    { app := fun p X => x.app p X - y.app p X
      app_mem := fun p X => Submodule.sub_mem _ (x.app_mem p X) (y.app_mem p X)
      naturality := fun p X Y q f hf => by
        rw [Preadditive.comp_sub, x.naturality p f hf, y.naturality p f hf, Preadditive.sub_comp,
          smul_sub] }

instance : SMul R (F ⟶ G) where
  smul r x :=
    { app := fun p X => r • x.app p X
      app_mem := fun p X => Submodule.smul_mem _ r (x.app_mem p X)
      naturality := fun p X Y q f hf => by
        rw [Linear.comp_smul, x.naturality p f hf, Linear.smul_comp, smul_comm] }

instance : SMul ℕ (F ⟶ G) where
  smul n x :=
    { app := fun p X => n • x.app p X
      app_mem := fun p X => Submodule.smul_of_tower_mem _ n (x.app_mem p X)
      naturality := fun p X Y q f hf => by
        rw [Preadditive.comp_nsmul, x.naturality p f hf, Preadditive.nsmul_comp, smul_comm] }

instance : SMul ℤ (F ⟶ G) where
  smul n x :=
    { app := fun p X => n • x.app p X
      app_mem := fun p X => Submodule.smul_of_tower_mem _ n (x.app_mem p X)
      naturality := fun p X Y q f hf => by
        rw [Preadditive.comp_zsmul, x.naturality p f hf, Preadditive.zsmul_comp, smul_comm] }

@[simp] theorem zero_app (p : ZMod 2) (X : C) : (0 : F ⟶ G).app p X = 0 := rfl

@[simp] theorem add_app (x y : F ⟶ G) (p : ZMod 2) (X : C) :
    (x + y).app p X = x.app p X + y.app p X := rfl

@[simp] theorem neg_app (x : F ⟶ G) (p : ZMod 2) (X : C) : (-x).app p X = -x.app p X := rfl

@[simp] theorem sub_app (x y : F ⟶ G) (p : ZMod 2) (X : C) :
    (x - y).app p X = x.app p X - y.app p X := rfl

@[simp] theorem smul_app (r : R) (x : F ⟶ G) (p : ZMod 2) (X : C) :
    (r • x).app p X = r • x.app p X := rfl

@[simp] theorem nsmul_app (n : ℕ) (x : F ⟶ G) (p : ZMod 2) (X : C) :
    (n • x).app p X = n • x.app p X := rfl

@[simp] theorem zsmul_app (n : ℤ) (x : F ⟶ G) (p : ZMod 2) (X : C) :
    (n • x).app p X = n • x.app p X := rfl

theorem app_injective :
    Function.Injective (fun (x : F ⟶ G) (p : ZMod 2) (X : C) => x.app p X) :=
  fun _ _ h => SuperNatTrans.ext h

instance : AddCommGroup (F ⟶ G) :=
  app_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

instance : Module R (F ⟶ G) :=
  app_injective.module R
    { toFun := fun (x : F ⟶ G) (p : ZMod 2) (X : C) => x.app p X
      map_zero' := rfl
      map_add' := fun _ _ => rfl } (fun _ _ => rfl)

instance : Preadditive (Superfunctor R C D) where
  homGroup _ _ := inferInstance
  add_comp _ _ _ x x' y := hom_ext fun p X => by
    simp only [comp_app, add_app, Preadditive.add_comp]; abel
  comp_add _ _ _ x y y' := hom_ext fun p X => by
    simp only [comp_app, add_app, Preadditive.comp_add]; abel

instance : Linear R (Superfunctor R C D) where
  homModule _ _ := inferInstance
  smul_comp _ _ _ r x y := hom_ext fun p X => by
    simp only [comp_app, smul_app, Linear.smul_comp, smul_add]
  comp_smul _ _ _ x r y := hom_ext fun p X => by
    simp only [comp_app, smul_app, Linear.comp_smul, smul_add]

end Linear

/-! ## The supercategory structure (Example 1.2(iv)) -/

section Super

variable (F G) in
/-- The supernatural transformations of parity `p`: those whose component of parity `p + 1`
vanishes. -/
def parityHom (p : ZMod 2) : Submodule R (F ⟶ G) where
  carrier := {x | x.app (p + 1) = 0}
  zero_mem' := rfl
  add_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq] at *
    funext X; simp [congrFun hx X, congrFun hy X]
  smul_mem' r x hx := by
    simp only [Set.mem_setOf_eq] at *
    funext X; simp [congrFun hx X]

theorem mem_parityHom {p : ZMod 2} {x : F ⟶ G} : x ∈ parityHom F G p ↔ x.app (p + 1) = 0 :=
  Iff.rfl

/-- The homogeneous component of parity `p` of a supernatural transformation. -/
def component (p : ZMod 2) (x : F ⟶ G) : F ⟶ G :=
  (x.isSupernatural p).toSuperNatTrans

theorem component_app (p : ZMod 2) (x : F ⟶ G) (q : ZMod 2) (X : C) :
    (component p x).app q X = if q = p then x.app p X else 0 := rfl

theorem component_mem (p : ZMod 2) (x : F ⟶ G) : component p x ∈ parityHom F G p := by
  rw [mem_parityHom]; funext X
  simp [component_app, zmod2_add_one_ne p]

theorem component_add_component (x : F ⟶ G) : component 0 x + component 1 x = x :=
  hom_ext_parity (fun X => by simp [component_app]) (fun X => by simp [component_app])

instance : Supercategory R (Superfunctor R C D) where
  parity := parityHom
  isInternal F G := by
    rw [DirectSum.isInternal_submodule_iff_isCompl _ (i := 0) (j := 1) (by decide)
      (by ext p; rcases parity_eq_zero_or_one p with rfl | rfl <;> simp)]
    constructor
    · rw [Submodule.disjoint_def]
      intro x h0 h1
      rw [mem_parityHom] at h0 h1
      exact hom_ext_parity (fun X => by simpa using congrFun h1 X)
        (fun X => by simpa using congrFun h0 X)
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      rw [← component_add_component x]
      exact Submodule.add_mem_sup (component_mem 0 x) (component_mem 1 x)
  id_mem F := by rw [mem_parityHom]; rfl
  comp_mem {F G H p q x y} hx hy := by
    rw [mem_parityHom] at hx hy ⊢
    funext X
    have hx' := congrFun hx X
    have hy' := congrFun hy X
    simp only at hx' hy'
    rw [comp_app]
    rcases parity_eq_zero_or_one p with rfl | rfl <;>
      rcases parity_eq_zero_or_one q with rfl | rfl <;>
      simp_all [SuperNatTrans.zmod2_one_add_one]

theorem mem_parity_iff {p : ZMod 2} {x : F ⟶ G} :
    x ∈ parity (R := R) F G p ↔ x.app (p + 1) = 0 := Iff.rfl

/-- The morphisms of parity `p` of `ℋom(C, D)` are the supernatural transformations that are
homogeneous of parity `p` (Definition 1.1(iii)). -/
theorem mem_parity_iff_isHomogeneous {p : ZMod 2} {x : F ⟶ G} :
    x ∈ parity (R := R) F G p ↔ SuperNatTrans.IsHomogeneous (toSuperNatTrans x) p := by
  rw [mem_parity_iff]
  constructor
  · intro h q hq
    rcases parity_eq_zero_or_one p with rfl | rfl <;>
      rcases parity_eq_zero_or_one q with rfl | rfl
    · exact absurd rfl hq
    · exact h
    · exact h
    · exact absurd rfl hq
  · intro h; exact h _ (zmod2_add_one_ne p)

theorem app_eq_zero_of_mem {p q : ZMod 2} {x : F ⟶ G} (hx : x ∈ parity (R := R) F G p)
    (hq : q ≠ p) (X : C) : x.app q X = 0 :=
  congrFun (mem_parity_iff_isHomogeneous.1 hx q hq) X

theorem proj_app (p : ZMod 2) (x : F ⟶ G) (q : ZMod 2) (X : C) :
    (proj R p x).app q X = if q = p then x.app p X else 0 := by
  have h : proj R p x = component p x :=
    proj_eq_of_add (h := component (p + 1) x)
      (by
        rcases parity_eq_zero_or_one p with rfl | rfl
        · exact (component_add_component x).symm
        · rw [SuperNatTrans.zmod2_one_add_one, add_comm]; exact (component_add_component x).symm)
      (component_mem p x)
      (component_mem (p + 1) x)
  rw [h, component_app]

/-- A homogeneous supernatural transformation of parity `p` (in the sense of
`IsSupernatural`) as a morphism of parity `p` in `ℋom(C, D)`. -/
theorem IsSupernatural.toSuperNatTrans_mem {p : ZMod 2}
    {x : ∀ X, F.obj X ⟶ G.obj X} (hx : IsSupernatural R p (F := F.toFunctor) (G := G.toFunctor) x) :
    (homMk hx.toSuperNatTrans : F ⟶ G) ∈ parity (R := R) F G p :=
  mem_parity_iff_isHomogeneous.2 hx.toSuperNatTrans_isHomogeneous

end Super

/-! ## Horizontal composition -/

section Horizontal

variable {G' K' : Superfunctor R D E}

/-- Whiskering on the inside: for `F : C → D` and `y : G ⇒ K` between superfunctors
`D → E`, the supernatural transformation `yF : GF ⇒ KF` with `(yF)_λ = y_{Fλ}`. In
diagrammatic order it is a morphism `F.comp G ⟶ F.comp K`. -/
@[simps]
def whiskerLeft (F : Superfunctor R C D) (y : G' ⟶ K') : F.comp G' ⟶ F.comp K' where
  app p X := y.app p (F.obj X)
  app_mem p X := y.app_mem p (F.obj X)
  naturality p _ _ _ f hf := y.naturality p (F.map f) (F.map_mem hf)

/-- Whiskering on the outside: for `x : F ⇒ H` between superfunctors `C → D` and
`G : D → E`, the supernatural transformation `Gx : GF ⇒ GH` with `(Gx)_λ = G(x_λ)`. -/
@[simps]
def whiskerRight (x : F ⟶ H) (G : Superfunctor R D E) : F.comp G ⟶ H.comp G where
  app p X := G.map (x.app p X)
  app_mem p X := G.map_mem (x.app_mem p X)
  naturality p X Y q f hf := by
    simp only [comp_toFunctor, Functor.comp_map]
    rw [← G.toFunctor.map_comp, x.naturality p f hf, Functor.map_zsmul, G.toFunctor.map_comp]

/-- Horizontal composition (Brundan–Ellis, Section 2): for `x : F ⇒ H` and `y : G ⇒ K`,
`(yx)_λ := y_{Hλ} ∘ G x_λ`. -/
def hcomp (x : F ⟶ H) (y : G' ⟶ K') : F.comp G' ⟶ H.comp K' :=
  whiskerRight x G' ≫ whiskerLeft H y

/-- The component formula `(yx)_λ = y_{Hλ} ∘ G x_λ`, for the total morphisms
`x_λ = x_{λ,0} + x_{λ,1}`. -/
theorem hcomp_total (x : F ⟶ H) (y : G' ⟶ K') (X : C) :
    SuperNatTrans.total (hcomp x y) X = G'.map (x.total X) ≫ y.total (H.obj X) := by
  rw [hcomp, comp_total]
  simp [SuperNatTrans.total, Preadditive.add_comp, Preadditive.comp_add]

@[simp] theorem whiskerLeft_id (F : Superfunctor R C D) (G : Superfunctor R D E) :
    whiskerLeft F (𝟙 G) = 𝟙 (F.comp G) :=
  hom_ext_parity (fun _ => rfl) (fun _ => rfl)

@[simp] theorem whiskerLeft_comp (F : Superfunctor R C D) {G K L : Superfunctor R D E}
    (y : G ⟶ K) (z : K ⟶ L) : whiskerLeft F (y ≫ z) = whiskerLeft F y ≫ whiskerLeft F z :=
  hom_ext_parity (fun _ => by simp) (fun _ => by simp)

@[simp] theorem id_whiskerRight (F : Superfunctor R C D) (G : Superfunctor R D E) :
    whiskerRight (𝟙 F) G = 𝟙 (F.comp G) :=
  hom_ext_parity (fun _ => G.toFunctor.map_id _) (fun _ => G.toFunctor.map_zero _ _)

@[simp] theorem comp_whiskerRight (x : F ⟶ H) (z : H ⟶ K) (G : Superfunctor R D E) :
    whiskerRight (x ≫ z) G = whiskerRight x G ≫ whiskerRight z G :=
  hom_ext_parity (fun _ => by simp) (fun _ => by simp)

theorem whiskerLeft_add (F : Superfunctor R C D) (y z : G' ⟶ K') :
    whiskerLeft F (y + z) = whiskerLeft F y + whiskerLeft F z := rfl

theorem add_whiskerRight (x z : F ⟶ H) (G : Superfunctor R D E) :
    whiskerRight (x + z) G = whiskerRight x G + whiskerRight z G :=
  hom_ext fun _ _ => by simp

theorem whiskerLeft_smul (F : Superfunctor R C D) (r : R) (y : G' ⟶ K') :
    whiskerLeft F (r • y) = r • whiskerLeft F y := rfl

theorem smul_whiskerRight (r : R) (x : F ⟶ H) (G : Superfunctor R D E) :
    whiskerRight (r • x) G = r • whiskerRight x G :=
  hom_ext fun _ _ => by simp

theorem whiskerLeft_mem (F : Superfunctor R C D) {p : ZMod 2} {y : G' ⟶ K'}
    (hy : y ∈ parity (R := R) G' K' p) :
    whiskerLeft F y ∈ parity (R := R) (F.comp G') (F.comp K') p := by
  rw [mem_parity_iff] at hy ⊢
  funext X; exact congrFun hy (F.obj X)

theorem whiskerRight_mem {p : ZMod 2} {x : F ⟶ H} (hx : x ∈ parity (R := R) F H p)
    (G : Superfunctor R D E) : whiskerRight x G ∈ parity (R := R) (F.comp G) (H.comp G) p := by
  rw [mem_parity_iff] at hx ⊢
  funext X; simp [congrFun hx X]

/-- **The super interchange law** for supernatural transformations (Brundan–Ellis,
Section 2): `yH ∘ Gx = (-1)^{|x||y|} Kx ∘ yF` for homogeneous `x : F ⇒ H` and
`y : G ⇒ K`. -/
theorem whisker_exchange {p q : ZMod 2} {x : F ⟶ H} {y : G' ⟶ K'}
    (hx : x ∈ parity (R := R) F H p) (hy : y ∈ parity (R := R) G' K' q) :
    whiskerRight x G' ≫ whiskerLeft H y = koszulSign p q • (whiskerLeft F y ≫ whiskerRight x K') := by
  have key : ∀ (a b : ZMod 2) (X : C),
      G'.map (x.app a X) ≫ y.app b (H.obj X) =
        koszulSign a b • (y.app b (F.obj X) ≫ K'.map (x.app a X)) := fun a b X => by
    rw [y.naturality b (x.app a X) (x.app_mem a X), koszulSign_comm]
  have hx0 : ∀ a, a ≠ p → ∀ X, x.app a X = 0 := fun a ha X => app_eq_zero_of_mem hx ha X
  have hy0 : ∀ b, b ≠ q → ∀ X, y.app b X = 0 := fun b hb X => app_eq_zero_of_mem hy hb X
  apply hom_ext
  intro r X
  simp only [comp_app, whiskerRight_app, whiskerLeft_app, zsmul_app, key, ← smul_add]
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    rcases parity_eq_zero_or_one q with rfl | rfl <;>
    rcases parity_eq_zero_or_one r with rfl | rfl <;>
    simp [hx0, hy0, SuperNatTrans.zmod2_one_add_one]

/-- The two expressions for horizontal composition: `yx = yH ∘ Gx = (-1)^{|x||y|} Kx ∘ yF`. -/
theorem hcomp_eq {p q : ZMod 2} {x : F ⟶ H} {y : G' ⟶ K'}
    (hx : x ∈ parity (R := R) F H p) (hy : y ∈ parity (R := R) G' K' q) :
    hcomp x y = koszulSign p q • (whiskerLeft F y ≫ whiskerRight x K') :=
  whisker_exchange hx hy

/-- **The super interchange law** (Brundan–Ellis, Section 2):
`(vu) ∘ (yx) = (-1)^{|u||y|} (v ∘ y)(u ∘ x)`. -/
theorem hcomp_comp_hcomp {L : Superfunctor R C D} {L' : Superfunctor R D E} {pu py : ZMod 2}
    (x : F ⟶ H) (u : H ⟶ L) (y : G' ⟶ K') (v : K' ⟶ L')
    (hu : u ∈ parity (R := R) H L pu) (hy : y ∈ parity (R := R) G' K' py) :
    hcomp x y ≫ hcomp u v = koszulSign pu py • hcomp (x ≫ u) (y ≫ v) := by
  simp only [hcomp, Category.assoc, comp_whiskerRight, whiskerLeft_comp]
  rw [← Category.assoc (whiskerLeft H y), ← koszulSign_smul_smul pu py
    (whiskerLeft H y ≫ whiskerRight u K'), ← whisker_exchange hu hy, Linear.smul_comp,
    Linear.comp_smul]
  simp only [Category.assoc]

end Horizontal

end Superfunctor

end Supercategory

end StringDiagrams

end
