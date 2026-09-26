import StringDiagrams.Super.Parity
import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Parity-preserving functors and supernatural transformations

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Definition 1.1(ii)–(iv), in the unpacked form of `StringDiagrams.Supercategory`:

* a superfunctor is an `R`-linear functor `F` (`[F.Additive] [F.Linear R]`) preserving parities
  (`Supercategory.PreservesParity R F`);
* a supernatural transformation of parity `p` between superfunctors is a family of morphisms of
  parity `p` satisfying `x_μ ∘ F f = (-1)^{p|f|} G f ∘ x_λ` for homogeneous `f`
  (`Supercategory.IsSupernatural R p x`); a general supernatural transformation is a family
  whose parity components are supernatural (`Supercategory.IsSupernaturalTrans`);
* a superfunctor is evenly dense if every object of the target is evenly isomorphic to an
  object in its image, and a superequivalence if it has a quasi-inverse superfunctor with even
  unit and counit isomorphisms (`Supercategory.Superequivalence`).

These are the unbundled forms of Definition 1.1(ii)–(iv) used by the files on Π-structures.
An even supernatural transformation is the same thing as a natural transformation with even
components (`Supercategory.IsSupernatural.naturality_zero`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory

universe w w₁ w₂ w₃ w₄ w₅ w₆

namespace Supercategory

variable {R : Type w} [CommRing R]
  {C : Type w₁} [Category.{w₂} C] [Preadditive C] [Linear R C] [Supercategory R C]
  {D : Type w₃} [Category.{w₄} D] [Preadditive D] [Linear R D] [Supercategory R D]
  {E : Type w₅} [Category.{w₆} E] [Preadditive E] [Linear R E] [Supercategory R E]

variable (R) in
/-- A functor between supercategories preserves parities (Brundan–Ellis, Definition 1.1(ii),
together with `R`-linearity). -/
class PreservesParity (F : C ⥤ D) : Prop where
  map_mem : ∀ {X Y : C} {p : ZMod 2} {f : X ⟶ Y}, f ∈ parity (R := R) X Y p →
    F.map f ∈ parity (R := R) (F.obj X) (F.obj Y) p

theorem map_mem (F : C ⥤ D) [PreservesParity R F] {X Y : C} {p : ZMod 2} {f : X ⟶ Y}
    (hf : f ∈ parity (R := R) X Y p) : F.map f ∈ parity (R := R) (F.obj X) (F.obj Y) p :=
  PreservesParity.map_mem hf

instance PreservesParity.id : PreservesParity R (𝟭 C) where
  map_mem hf := hf

instance PreservesParity.comp (F : C ⥤ D) (G : D ⥤ E) [PreservesParity R F]
    [PreservesParity R G] : PreservesParity R (F ⋙ G) where
  map_mem hf := Supercategory.map_mem (R := R) G (Supercategory.map_mem (R := R) F hf)

section Superfunctor

theorem map_proj (F : C ⥤ D) [F.Additive] [PreservesParity R F] (p : ZMod 2) {X Y : C}
    (f : X ⟶ Y) :
    F.map (proj R p f) = proj R p (F.map f) := by
  refine induction_on (R := R) f (by simp) (fun q g hg => ?_) (fun g h hg hh => ?_)
  · by_cases h : q = p
    · subst h; rw [proj_of_mem hg, proj_of_mem (map_mem F hg)]
    · rw [proj_of_mem_ne hg h, proj_of_mem_ne (map_mem F hg) h, F.map_zero]
  · rw [map_add, F.map_add, hg, hh, F.map_add, map_add]

theorem map_twist (F : C ⥤ D) [F.Additive] [F.Linear R] [PreservesParity R F] (p : ZMod 2)
    {X Y : C} (f : X ⟶ Y) :
    F.map (twist R p f) = twist R p (F.map f) := by
  rw [twist_apply, twist_apply, F.map_add, F.map_smul, map_proj, map_proj]

end Superfunctor

/-! ## Supernatural transformations -/

variable (R) in
/-- A supernatural transformation of parity `p` (Brundan–Ellis, Definition 1.1(iii)): a family
of morphisms `x X : F X ⟶ G X` of parity `p` with `x_μ ∘ F f = (-1)^{p|f|} G f ∘ x_λ` for all
homogeneous `f`. -/
structure IsSupernatural (p : ZMod 2) {F G : C ⥤ D} (x : ∀ X, F.obj X ⟶ G.obj X) : Prop where
  mem : ∀ X, x X ∈ parity (R := R) (F.obj X) (G.obj X) p
  naturality : ∀ {X Y : C} {q : ZMod 2} {f : X ⟶ Y}, f ∈ parity (R := R) X Y q →
    F.map f ≫ x Y = sign R (p * q) • (x X ≫ G.map f)

variable (R) in
/-- A (not necessarily homogeneous) supernatural transformation: both parity components are
supernatural (Brundan–Ellis, Definition 1.1(iii)). -/
def IsSupernaturalTrans {F G : C ⥤ D} (x : ∀ X, F.obj X ⟶ G.obj X) : Prop :=
  ∀ p, IsSupernatural R p fun X => proj R p (x X)

section

variable {F G H : C ⥤ D}

/-- The supernaturality condition for arbitrary (inhomogeneous) morphisms. -/
theorem IsSupernatural.naturality_twist [F.Additive] [G.Additive] [G.Linear R] {p : ZMod 2} {x : ∀ X, F.obj X ⟶ G.obj X}
    (hx : IsSupernatural R p x) {X Y : C} (f : X ⟶ Y) :
    F.map f ≫ x Y = x X ≫ G.map (twist R p f) := by
  refine induction_on (R := R) f (by simp) (fun q g hg => ?_) (fun g h hg hh => ?_)
  · rw [hx.naturality hg, twist_of_mem p hg, G.map_smul, Linear.comp_smul]
  · rw [F.map_add, Preadditive.add_comp, hg, hh, map_add, G.map_add, Preadditive.comp_add]

theorem IsSupernatural.of_twist [G.Linear R] {p : ZMod 2} {x : ∀ X, F.obj X ⟶ G.obj X}
    (mem : ∀ X, x X ∈ parity (R := R) (F.obj X) (G.obj X) p)
    (nat : ∀ {X Y : C} (f : X ⟶ Y), F.map f ≫ x Y = x X ≫ G.map (twist R p f)) :
    IsSupernatural R p x where
  mem := mem
  naturality hf := by rw [nat, twist_of_mem p hf, G.map_smul, Linear.comp_smul]

/-- Even supernatural transformations are natural. -/
theorem IsSupernatural.naturality_zero [F.Additive] [G.Additive] [G.Linear R] {x : ∀ X, F.obj X ⟶ G.obj X}
    (hx : IsSupernatural R 0 x) {X Y : C} (f : X ⟶ Y) : F.map f ≫ x Y = x X ≫ G.map f := by
  rw [hx.naturality_twist, twist_zero]

/-- The natural transformation underlying an even supernatural transformation. -/
@[simps]
def IsSupernatural.toNatTrans [F.Additive] [G.Additive] [G.Linear R] {x : ∀ X, F.obj X ⟶ G.obj X} (hx : IsSupernatural R 0 x) :
    F ⟶ G where
  app := x
  naturality _ _ f := hx.naturality_zero f

/-- A natural transformation with even components is an even supernatural transformation. -/
theorem isSupernatural_of_natTrans [G.Linear R] (x : F ⟶ G)
    (mem : ∀ X, x.app X ∈ parity (R := R) (F.obj X) (G.obj X) 0) :
    IsSupernatural R 0 x.app :=
  IsSupernatural.of_twist mem fun f => by rw [twist_zero, x.naturality]

theorem isSupernatural_id [F.Linear R] : IsSupernatural R 0 fun X => 𝟙 (F.obj X) :=
  IsSupernatural.of_twist (fun X => id_mem _) fun f => by simp

/-- Vertical composition of supernatural transformations adds parities. -/
theorem IsSupernatural.comp [F.Additive] [G.Additive] [G.Linear R] [H.Additive] [H.Linear R]
    {p q : ZMod 2} {x : ∀ X, F.obj X ⟶ G.obj X}
    {y : ∀ X, G.obj X ⟶ H.obj X} (hx : IsSupernatural R p x) (hy : IsSupernatural R q y) :
    IsSupernatural R (p + q) fun X => x X ≫ y X :=
  IsSupernatural.of_twist (fun X => comp_mem (hx.mem X) (hy.mem X)) fun f => by
    rw [← Category.assoc, hx.naturality_twist, Category.assoc, hy.naturality_twist,
      add_comm p q, twist_add, Category.assoc]

/-- Whiskering a supernatural transformation by a superfunctor on the outside. -/
theorem IsSupernatural.whiskerRight [F.Additive] [G.Additive] [G.Linear R] {p : ZMod 2}
    {x : ∀ X, F.obj X ⟶ G.obj X} (hx : IsSupernatural R p x) (K : D ⥤ E) [K.Additive]
    [K.Linear R] [PreservesParity R K] :
    IsSupernatural R p (F := F ⋙ K) (G := G ⋙ K) fun X => K.map (x X) where
  mem X := Supercategory.map_mem K (hx.mem X)
  naturality hf := by
    simp only [Functor.comp_map]
    rw [← K.map_comp, hx.naturality hf, K.map_smul, K.map_comp]

/-- Whiskering a supernatural transformation by a superfunctor on the inside. -/
theorem IsSupernatural.whiskerLeft {B : Type*} [Category B] [Preadditive B] [Linear R B]
    [Supercategory R B] {p : ZMod 2} {x : ∀ X, F.obj X ⟶ G.obj X} (hx : IsSupernatural R p x)
    (K : B ⥤ C) [PreservesParity R K] :
    IsSupernatural R p (F := K ⋙ F) (G := K ⋙ G) fun X => x (K.obj X) where
  mem X := hx.mem (K.obj X)
  naturality hf := hx.naturality (Supercategory.map_mem K hf)

end

/-! ## Faithful superfunctors reflect parity -/

theorem mem_of_map_mem (F : C ⥤ D) [F.Additive] [PreservesParity R F] [F.Faithful]
    {X Y : C} {p : ZMod 2} {f : X ⟶ Y} (hf : F.map f ∈ parity (R := R) (F.obj X) (F.obj Y) p) :
    f ∈ parity (R := R) X Y p := by
  have h0 : proj R (p + 1) f = 0 := F.map_injective (by
    rw [map_proj, F.map_zero, proj_of_mem_ne hf (Ne.symm (zmod2_add_one_ne p))])
  have h := proj_add_proj (R := R) f
  rcases zmod2_cases p with rfl | rfl
  · rw [show (0 : ZMod 2) + 1 = 1 from rfl] at h0
    rw [h0, add_zero] at h; exact h ▸ proj_mem _ _
  · rw [show (1 : ZMod 2) + 1 = 0 from rfl] at h0
    rw [h0, zero_add] at h; exact h ▸ proj_mem _ _

/-! ## Superequivalences -/

variable (R) in
/-- A superfunctor is evenly dense if every object of the target is isomorphic to an object in
its image via an even isomorphism (Brundan–Ellis, Definition 1.1(iv)). -/
def EvenlyDense (F : C ⥤ D) : Prop :=
  ∀ Y : D, ∃ (X : C) (e : F.obj X ≅ Y), e.hom ∈ parity (R := R) (F.obj X) Y 0

variable (R) in
/-- A superequivalence (Brundan–Ellis, Definition 1.1(iv)): a superfunctor `F` together with a
superfunctor `inverse` and even supernatural isomorphisms `𝟭 ≅ F ⋙ inverse`,
`inverse ⋙ F ≅ 𝟭`. -/
structure Superequivalence (F : C ⥤ D) where
  /-- The quasi-inverse superfunctor. -/
  inverse : D ⥤ C
  [inverse_additive : inverse.Additive]
  [inverse_linear : inverse.Linear R]
  [inverse_preservesParity : PreservesParity R inverse]
  /-- The unit isomorphism. -/
  unitIso : 𝟭 C ≅ F ⋙ inverse
  /-- The counit isomorphism. -/
  counitIso : inverse ⋙ F ≅ 𝟭 D
  unitIso_mem : ∀ X, unitIso.hom.app X ∈ parity (R := R) X (inverse.obj (F.obj X)) 0
  counitIso_mem : ∀ Y, counitIso.hom.app Y ∈ parity (R := R) (F.obj (inverse.obj Y)) Y 0

attribute [instance] Superequivalence.inverse_additive Superequivalence.inverse_linear
  Superequivalence.inverse_preservesParity

/-- A superequivalence is evenly dense. -/
theorem Superequivalence.evenlyDense {F : C ⥤ D} (e : Superequivalence R F) :
    EvenlyDense R F := fun Y => ⟨e.inverse.obj Y, e.counitIso.app Y, e.counitIso_mem Y⟩

section OfFullyFaithful

variable (F : C ⥤ D) [F.Additive] [F.Linear R] [PreservesParity R F] [F.Full] [F.Faithful]
  (hF : EvenlyDense R F)

/-- The object chosen by even density. -/
def EvenlyDense.obj (Y : D) : C := (hF Y).choose

/-- The even isomorphism chosen by even density. -/
def EvenlyDense.iso (Y : D) : F.obj (hF.obj F Y) ≅ Y := (hF Y).choose_spec.choose

omit [Preadditive C] [Linear R C] [Supercategory R C] [F.Additive] [F.Linear R]
  [PreservesParity R F] [F.Full] [F.Faithful] in
theorem EvenlyDense.iso_mem (Y : D) :
    (hF.iso F Y).hom ∈ parity (R := R) (F.obj (hF.obj F Y)) Y 0 :=
  (hF Y).choose_spec.choose_spec

/-- The quasi-inverse of a full, faithful, evenly dense superfunctor. -/
@[simps]
def EvenlyDense.inverse : D ⥤ C where
  obj := hF.obj F
  map {Y Y'} g := F.preimage ((hF.iso F Y).hom ≫ g ≫ (hF.iso F Y').inv)
  map_id Y := F.map_injective (by simp)
  map_comp f g := F.map_injective (by simp)

instance EvenlyDense.inverse_additive : (hF.inverse F).Additive where
  map_add := F.map_injective (by simp)

instance EvenlyDense.inverse_linear : (hF.inverse F).Linear R where
  map_smul _ _ := F.map_injective (by simp [F.map_smul])

instance EvenlyDense.inverse_preservesParity : PreservesParity R (hF.inverse F) where
  map_mem {Y Y' p g} hg := by
    apply mem_of_map_mem F
    rw [EvenlyDense.inverse_map, F.map_preimage]
    have := comp_mem (comp_mem (hF.iso_mem F Y) hg) (inv_mem _ (hF.iso_mem F Y'))
    simpa using this

/-- **Brundan–Ellis, Definition 1.1(iv).** A full, faithful and evenly dense superfunctor is
a superequivalence. -/
def Superequivalence.ofFullyFaithful : Superequivalence R F where
  inverse := hF.inverse F
  unitIso := NatIso.ofComponents (fun X => F.preimageIso (hF.iso F (F.obj X)).symm)
    (fun f => F.map_injective (by simp))
  counitIso := NatIso.ofComponents (fun Y => hF.iso F Y) (fun g => by simp)
  unitIso_mem X := by
    apply mem_of_map_mem F
    simpa using inv_mem _ (hF.iso_mem F (F.obj X))
  counitIso_mem Y := hF.iso_mem F Y

end OfFullyFaithful

end Supercategory

end StringDiagrams

end
