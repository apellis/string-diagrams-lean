import StringDiagrams.Super.Parity

/-!
# The super-opposite of a supercategory

Following J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Definition 3.4: for a supercategory `𝒜`, the supercategory `𝒜^{sop}` has the same objects,
morphisms `Hom_{𝒜^{sop}}(λ, μ) := Hom_𝒜(μ, λ)`, and the composition law
`f^{sop} ∘ g^{sop} := (-1)^{|f||g|} (g ∘ f)^{sop}` on homogeneous morphisms.

Here `SOp R C` is a structure wrapping the objects of a linear supercategory `C`, a morphism
`X ⟶ Y` in `SOp R C` is a morphism `Y.unop ⟶ X.unop` in `C`, and the composite of `f` and `g`
(diagrammatic order) is `g₀ ≫ f + g₁ ≫ twist 1 f` (`SOp.comp_def`), which is
`(-1)^{|f||g|} (g ≫ f)` for homogeneous `f`, `g` (`SOp.comp_of_mem`). Parities are those of `C`.

## Main definitions

* `SOp R C` with its `Category`, `Preadditive`, `Linear R` and `Supercategory R` instances.
* `SOp.comp_of_mem`: the composition law on homogeneous morphisms.
* `SOp.mapFunctor`: a linear functor preserving parities induces a functor of super-opposites.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory

universe w w₁ w₂ w₃ w₄

/-- The super-opposite of a linear supercategory `C` (Brundan–Ellis, SKM, Definition 3.4). -/
@[ext]
structure SOp (R : Type w) (C : Type w₁) where
  /-- The underlying object of `C`. -/
  unop : C

namespace SOp

variable {R : Type w} [CommRing R] {C : Type w₁} [Category.{w₂} C] [Preadditive C] [Linear R C]
  [Supercategory R C]

/-- The composition law of the super-opposite, on morphisms of `C`: `g₀ ≫ f + g₁ ≫ twist 1 f`. -/
def compC {X Y Z : C} (f : Y ⟶ X) (g : Z ⟶ Y) : Z ⟶ X :=
  proj R 0 g ≫ f + proj R 1 g ≫ twist R 1 f

theorem compC_of_mem {X Y Z : C} {p q : ZMod 2} {f : Y ⟶ X} {g : Z ⟶ Y}
    (hf : f ∈ parity (R := R) Y X p) (hg : g ∈ parity (R := R) Z Y q) :
    compC (R := R) f g = sign R (p * q) • (g ≫ f) := by
  unfold compC
  rcases parity_eq_zero_or_one q with rfl | rfl
  · rw [proj_of_mem hg, proj_of_mem_ne hg (by decide), Limits.zero_comp, add_zero, mul_zero,
      sign_zero, one_smul]
  · rw [proj_of_mem hg, proj_of_mem_ne hg (by decide), Limits.zero_comp, zero_add,
      twist_one_of_mem hf, Linear.comp_smul, mul_one]

theorem compC_add {X Y Z : C} (f : Y ⟶ X) (g g' : Z ⟶ Y) :
    compC (R := R) f (g + g') = compC (R := R) f g + compC (R := R) f g' := by
  unfold compC
  rw [map_add, map_add, Preadditive.add_comp, Preadditive.add_comp]
  abel

theorem add_compC {X Y Z : C} (f f' : Y ⟶ X) (g : Z ⟶ Y) :
    compC (R := R) (f + f') g = compC (R := R) f g + compC (R := R) f' g := by
  unfold compC
  rw [map_add, Preadditive.comp_add, Preadditive.comp_add]
  abel

theorem compC_smul {X Y Z : C} (f : Y ⟶ X) (r : R) (g : Z ⟶ Y) :
    compC (R := R) f (r • g) = r • compC (R := R) f g := by
  unfold compC
  rw [map_smul, map_smul, Linear.smul_comp, Linear.smul_comp, smul_add]

theorem smul_compC {X Y Z : C} (r : R) (f : Y ⟶ X) (g : Z ⟶ Y) :
    compC (R := R) (r • f) g = r • compC (R := R) f g := by
  unfold compC
  rw [map_smul, Linear.comp_smul, Linear.comp_smul, smul_add]

theorem compC_zero {X Y Z : C} (f : Y ⟶ X) : compC (R := R) f (0 : Z ⟶ Y) = 0 := by
  rw [← zero_smul R (0 : Z ⟶ Y), compC_smul, zero_smul]

theorem zero_compC {X Y Z : C} (g : Z ⟶ Y) : compC (R := R) (0 : Y ⟶ X) g = 0 := by
  rw [← zero_smul R (0 : Y ⟶ X), smul_compC, zero_smul]

theorem compC_assoc {W X Y Z : C} (f : X ⟶ W) (g : Y ⟶ X) (h : Z ⟶ Y) :
    compC (R := R) (compC (R := R) f g) h = compC (R := R) f (compC (R := R) g h) := by
  refine induction_on (R := R) f (by simp only [zero_compC]) (fun p f hf => ?_)
    (fun f f' hf hf' => by rw [add_compC, add_compC, add_compC, hf, hf'])
  refine induction_on (R := R) g (by simp only [zero_compC, compC_zero])
    (fun q g hg => ?_) (fun g g' hg hg' => by rw [compC_add, add_compC, add_compC, compC_add, hg, hg'])
  refine induction_on (R := R) h (by simp only [compC_zero])
    (fun r h hh => ?_) (fun h h' hh hh' => by rw [compC_add, compC_add, compC_add, hh, hh'])
  have m₁ : compC (R := R) f g ∈ parity (R := R) Y W (q + p) := by
    rw [compC_of_mem hf hg]; exact Submodule.smul_mem _ _ (comp_mem hg hf)
  have m₂ : compC (R := R) g h ∈ parity (R := R) Z X (r + q) := by
    rw [compC_of_mem hg hh]; exact Submodule.smul_mem _ _ (comp_mem hh hg)
  rw [compC_of_mem m₁ hh, compC_of_mem hf m₂, compC_of_mem hf hg, compC_of_mem hg hh,
    Linear.comp_smul, Linear.smul_comp, smul_smul, smul_smul, Category.assoc, ← sign_add,
    ← sign_add]
  congr 2
  ring

/-- Morphisms of the super-opposite: morphisms of `C` in the opposite direction. -/
@[ext]
structure Hom (X Y : SOp R C) where
  /-- The underlying morphism of `C`. -/
  unsop : Y.unop ⟶ X.unop

instance category : Category (SOp R C) where
  Hom := Hom
  id X := ⟨𝟙 X.unop⟩
  comp f g := ⟨compC (R := R) f.unsop g.unsop⟩
  id_comp f := by
    ext
    change proj R 0 f.unsop ≫ 𝟙 _ + proj R 1 f.unsop ≫ twist R 1 (𝟙 _) = f.unsop
    rw [twist_id, Category.comp_id, Category.comp_id, proj_add_proj]
  comp_id f := by
    ext
    change proj R 0 (𝟙 _) ≫ f.unsop + proj R 1 (𝟙 _) ≫ twist R 1 f.unsop = f.unsop
    rw [proj_id, proj_id]
    simp
  assoc f g h := Hom.ext (compC_assoc f.unsop g.unsop h.unsop)

/-- A morphism of `C`, viewed as a morphism of `SOp R C` in the opposite direction. -/
def sop {X Y : C} (f : X ⟶ Y) : (⟨Y⟩ : SOp R C) ⟶ ⟨X⟩ := ⟨f⟩

/-- A morphism of `SOp R C`, viewed as a morphism of `C`. -/
def unsop {X Y : SOp R C} (f : X ⟶ Y) : Y.unop ⟶ X.unop := Hom.unsop f

@[simp] theorem unsop_sop {X Y : C} (f : X ⟶ Y) : unsop (sop (R := R) f) = f := rfl

@[simp] theorem sop_unsop {X Y : C} (f : (⟨Y⟩ : SOp R C) ⟶ ⟨X⟩) : sop (unsop f) = f := rfl

@[ext]
theorem hom_ext {X Y : SOp R C} {f g : X ⟶ Y} (h : unsop f = unsop g) : f = g := Hom.ext h

theorem unsop_comp {X Y Z : SOp R C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    unsop (f ≫ g) = compC (R := R) (unsop f) (unsop g) := rfl

@[simp] theorem unsop_id (X : SOp R C) : unsop (𝟙 X) = 𝟙 X.unop := rfl

/-- **The composition law of `𝒜^{sop}`**: `f^{sop} ∘ g^{sop} = (-1)^{|f||g|} (g ∘ f)^{sop}`. -/
theorem comp_of_mem {X Y Z : SOp R C} {p q : ZMod 2} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : unsop f ∈ parity (R := R) Y.unop X.unop p)
    (hg : unsop g ∈ parity (R := R) Z.unop Y.unop q) :
    unsop (f ≫ g) = sign R (p * q) • (unsop g ≫ unsop f) :=
  compC_of_mem hf hg

/-- A morphism of `C`, as a morphism of `SOp R C` between the same objects. -/
def mk' {X Y : SOp R C} (f : Y.unop ⟶ X.unop) : X ⟶ Y := ⟨f⟩

@[simp] theorem unsop_mk' {X Y : SOp R C} (f : Y.unop ⟶ X.unop) : unsop (mk' (X := X) (Y := Y) f) = f :=
  rfl

theorem unsop_injective {X Y : SOp R C} : Function.Injective (unsop (X := X) (Y := Y)) :=
  fun _ _ h => hom_ext h

instance (X Y : SOp R C) : Zero (X ⟶ Y) := ⟨⟨0⟩⟩
instance (X Y : SOp R C) : Add (X ⟶ Y) := ⟨fun f g => ⟨unsop f + unsop g⟩⟩
instance (X Y : SOp R C) : Neg (X ⟶ Y) := ⟨fun f => ⟨-unsop f⟩⟩
instance (X Y : SOp R C) : Sub (X ⟶ Y) := ⟨fun f g => ⟨unsop f - unsop g⟩⟩
instance (X Y : SOp R C) : SMul ℕ (X ⟶ Y) := ⟨fun n f => ⟨n • unsop f⟩⟩
instance (X Y : SOp R C) : SMul ℤ (X ⟶ Y) := ⟨fun n f => ⟨n • unsop f⟩⟩
instance (X Y : SOp R C) : SMul R (X ⟶ Y) := ⟨fun r f => ⟨r • unsop f⟩⟩

@[simp] theorem unsop_add {X Y : SOp R C} (f g : X ⟶ Y) : unsop (f + g) = unsop f + unsop g := rfl
@[simp] theorem unsop_smul {X Y : SOp R C} (r : R) (f : X ⟶ Y) : unsop (r • f) = r • unsop f := rfl
@[simp] theorem unsop_zero {X Y : SOp R C} : unsop (0 : X ⟶ Y) = 0 := rfl
@[simp] theorem unsop_neg {X Y : SOp R C} (f : X ⟶ Y) : unsop (-f) = -unsop f := rfl
@[simp] theorem unsop_sub {X Y : SOp R C} (f g : X ⟶ Y) : unsop (f - g) = unsop f - unsop g := rfl

instance homAddCommGroup (X Y : SOp R C) : AddCommGroup (X ⟶ Y) :=
  Function.Injective.addCommGroup unsop unsop_injective rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/-- `unsop` as an additive map. -/
def unsopAddHom (X Y : SOp R C) : (X ⟶ Y) →+ (Y.unop ⟶ X.unop) where
  toFun := unsop
  map_zero' := rfl
  map_add' _ _ := rfl

instance homModule (X Y : SOp R C) : Module R (X ⟶ Y) :=
  Function.Injective.module R (unsopAddHom X Y) unsop_injective (fun _ _ => rfl)

/-- `unsop` as a linear map. -/
def unsopₗ (X Y : SOp R C) : (X ⟶ Y) →ₗ[R] (Y.unop ⟶ X.unop) where
  toFun := unsop
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance preadditive : Preadditive (SOp R C) where
  homGroup := homAddCommGroup
  add_comp _ _ _ f f' g := hom_ext (add_compC (R := R) (unsop f) (unsop f') (unsop g))
  comp_add _ _ _ f g g' := hom_ext (compC_add (R := R) (unsop f) (unsop g) (unsop g'))

instance linear : Linear R (SOp R C) where
  homModule := homModule
  smul_comp _ _ _ r f g := hom_ext (smul_compC (R := R) r (unsop f) (unsop g))
  comp_smul _ _ _ f r g := hom_ext (compC_smul (R := R) (unsop f) r (unsop g))

theorem unsop_eqToHom {X Y : SOp R C} (h : X = Y) :
    unsop (eqToHom h) = eqToHom (congrArg SOp.unop h).symm := by
  subst h; rfl

/-- The super-opposite is a supercategory, with the parities of `C`. -/
instance supercategory : Supercategory R (SOp R C) where
  parity X Y p := (parity (R := R) Y.unop X.unop p).comap (unsopₗ X Y)
  isInternal X Y := by
    rw [DirectSum.isInternal_submodule_iff_isCompl _ (i := 0) (j := 1) (by decide)
      (by ext p; rcases parity_eq_zero_or_one p with rfl | rfl <;> simp)]
    constructor
    · rw [Submodule.disjoint_def]
      intro f h0 h1
      have := proj_of_mem (R := R) (Submodule.mem_comap.1 h0)
      rw [proj_of_mem_ne (Submodule.mem_comap.1 h1) (by decide)] at this
      exact hom_ext this.symm
    · rw [codisjoint_iff, eq_top_iff]
      intro f _
      have e : f = mk' (proj R 0 (unsop f)) + mk' (proj R 1 (unsop f)) :=
        hom_ext (proj_add_proj (R := R) (unsop f)).symm
      rw [e]
      exact Submodule.add_mem_sup (Submodule.mem_comap.2 (proj_mem 0 _))
        (Submodule.mem_comap.2 (proj_mem 1 _))
  id_mem X := Submodule.mem_comap.2 (id_mem X.unop)
  comp_mem {_ _ _ p q f g} hf hg := by
    have hf' : unsop f ∈ parity (R := R) _ _ p := Submodule.mem_comap.1 hf
    have hg' : unsop g ∈ parity (R := R) _ _ q := Submodule.mem_comap.1 hg
    refine Submodule.mem_comap.2 ?_
    change compC (R := R) (unsop f) (unsop g) ∈ _
    rw [compC_of_mem hf' hg', add_comm]
    exact Submodule.smul_mem _ _ (comp_mem hg' hf')

theorem mem_parity_iff {X Y : SOp R C} {p : ZMod 2} {f : X ⟶ Y} :
    f ∈ parity (R := R) X Y p ↔ unsop f ∈ parity (R := R) Y.unop X.unop p := Iff.rfl

/-! ## The super-opposite of the super-opposite -/

/-- `(𝒜^{sop})^{sop} = 𝒜`: the identity on objects and morphisms is a functor
`SOp R (SOp R C) ⥤ C`, since the two signs cancel. -/
def unsopUnsop : SOp R (SOp R C) ⥤ C where
  obj X := X.unop.unop
  map f := unsop (unsop f)
  map_id _ := rfl
  map_comp {X Y Z} f g := by
    refine induction_on (R := R) f (P := fun f => unsop (unsop (f ≫ g)) =
        unsop (unsop f) ≫ unsop (unsop g)) ?_ (fun p f hf => ?_) (fun f f' hf hf' => ?_)
    · simp only [Limits.zero_comp, unsop_zero]
    · refine induction_on (R := R) g (P := fun g => unsop (unsop (f ≫ g)) =
          unsop (unsop f) ≫ unsop (unsop g)) ?_ (fun q g hg => ?_) (fun g g' hg hg' => ?_)
      · simp only [Limits.comp_zero, unsop_zero]
      · have hf' : unsop f ∈ parity (R := R) Y.unop X.unop p := hf
        have hg' : unsop g ∈ parity (R := R) Z.unop Y.unop q := hg
        rw [comp_of_mem hf' hg', unsop_smul, comp_of_mem (X := Z.unop) (Y := Y.unop) (Z := X.unop)
          (f := unsop g) (g := unsop f) hg hf, smul_smul, mul_comm q p, sign_mul_self, one_smul]
      · rw [Preadditive.comp_add, unsop_add, unsop_add, hg, hg', unsop_add, unsop_add,
          Preadditive.comp_add]
    · rw [Preadditive.add_comp, unsop_add, unsop_add, hf, hf', unsop_add, unsop_add,
        Preadditive.add_comp]

@[simp] theorem unsopUnsop_map {X Y : SOp R (SOp R C)} (f : X ⟶ Y) :
    unsopUnsop.map f = unsop (unsop f) := rfl

/-! ## Functoriality -/

variable {D : Type w₃} [Category.{w₄} D] [Preadditive D] [Linear R D] [Supercategory R D]

/-- A linear functor commutes with the parity projections if it preserves parities. -/
theorem proj_map (F : C ⥤ D) [F.Additive] [F.Linear R]
    (hF : ∀ {X Y : C} {p : ZMod 2} {f : X ⟶ Y}, f ∈ parity (R := R) X Y p →
      F.map f ∈ parity (R := R) (F.obj X) (F.obj Y) p)
    (p : ZMod 2) {X Y : C} (f : X ⟶ Y) : proj R p (F.map f) = F.map (proj R p f) := by
  conv_lhs => rw [← proj_add_proj (R := R) f, F.map_add]
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [map_add, proj_of_mem (hF (proj_mem 0 f)), proj_of_mem_ne (hF (proj_mem 1 f)) (by decide),
      add_zero]
  · rw [map_add, proj_of_mem (hF (proj_mem 1 f)), proj_of_mem_ne (hF (proj_mem 0 f)) (by decide),
      zero_add]

/-- A linear functor preserving parities induces a functor of super-opposites. -/
@[simps]
def mapFunctor (F : C ⥤ D) [F.Additive] [F.Linear R]
    (hF : ∀ {X Y : C} {p : ZMod 2} {f : X ⟶ Y}, f ∈ parity (R := R) X Y p →
      F.map f ∈ parity (R := R) (F.obj X) (F.obj Y) p) : SOp R C ⥤ SOp R D where
  obj X := ⟨F.obj X.unop⟩
  map f := sop (F.map (unsop f))
  map_id X := hom_ext (F.map_id X.unop)
  map_comp {X Y Z} f g := by
    ext
    change F.map (proj R 0 (unsop g) ≫ unsop f + proj R 1 (unsop g) ≫ twist R 1 (unsop f)) =
      proj R 0 (F.map (unsop g)) ≫ F.map (unsop f) +
        proj R 1 (F.map (unsop g)) ≫ twist R 1 (F.map (unsop f))
    rw [F.map_add, F.map_comp, F.map_comp, proj_map F hF, proj_map F hF, twist_apply, twist_apply,
      F.map_add, F.map_smul, proj_map F hF, proj_map F hF]

end SOp

end StringDiagrams

end
