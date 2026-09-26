import StringDiagrams.Super.QPi
import StringDiagrams.Super.Envelope

/-!
# The (Q, Π)-envelope of a graded supercategory

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §6,
Definition 6.8, the universal property "similar to Lemma 4.2", the characterization of
`(Q, Π)`-complete graded supercategories ("cf. Lemma 4.1") and Theorem 6.9.

The `(Q, Π)`-envelope `A_{q,π}` of a graded supercategory `A` has objects `Q^m Π^a λ` and
`Hom(Q^m Π^a λ, Q^n Π^b μ) := Q^{n-m} Π^{a+b} Hom_A(λ, μ)`, composition being induced by that
of `A` without signs. We build it in two steps:

* the *`Q`-envelope* `QEnvelope R A`, with objects `Q^m λ` and
  `Hom(Q^m λ, Q^n μ) := Q^{n-m} Hom_A(λ, μ)` (parities unchanged, degrees shifted by `n - m`),
  a graded supercategory;
* the Π-envelope `Envelope R (QEnvelope R A)` of Definition 1.10, which is a graded
  supercategory for the unchanged degrees (instance `Envelope.instGraded`).

Thus `QPiEnvelope R A := Envelope R (QEnvelope R A)`: the object `⟨a, ⟨m, λ⟩⟩` is the paper's
`Q^m Π^a λ`, and the morphism `f^{n,b}_{m,a}` coming from a homogeneous `f : λ → μ` is
`Envelope.ofHom (QEnvelope.ofHom f)`, of parity `|f| + a + b` and degree `deg f + n - m`
(`QPiEnvelope.ofHom_mem`, `QPiEnvelope.ofHom_mem_degree`). `Π` and `ζ` are those of the
Π-envelope (Definition 1.10), `Q(Q^m Π^a λ) = Q^{m+1} Π^a λ` and `σ`, `σ̄` are induced by the
identity morphisms of `A` (instance `QPiEnvelope.instQPi`).

## Main definitions and statements

* `QEnvelope R C`, `QPiEnvelope R C` (**Definition 6.8**); `QPiEnvelope.J : A → A_{q,π}`,
  `λ ↦ Q⁰ Π⁰ λ`, a full and faithful graded superfunctor.
* `QPiEnvelope.QPiComplete`, `QPiEnvelope.J_gradedEvenlyDense_iff`,
  `QPiEnvelope.gradedSuperequivalenceJ`, `QPiEnvelope.qpiComplete_of_gradedSuperequivalence`:
  `J` is a graded superequivalence if and only if `A` is `(Q, Π)`-complete, i.e. every object
  is the target of even isomorphisms of degrees `±1` and of an odd isomorphism of degree `0`.
* Universal property (the analogue of Lemma 4.2): `QPiEnvelope.extend F` for a graded
  superfunctor `F : A → B` into a graded `(Q, Π)`-supercategory, with `J ⋙ F̃ = F`
  (`J_comp_extend`); `QPiEnvelope.extendNat` extends supernatural transformations
  homogeneous of parity `p` and degree `n`, uniquely (`eq_of_restrict_eq`, `eq_extendNat`).
* **Theorem 6.9**: restriction along `J` is a bijection between supernatural transformations
  `F̃ ⇒ G̃` and `F ⇒ G` homogeneous of parity `p` and degree `n` (`restrict_bijective`),
  extension respects identities and composition (`extendNat_id`, `extendNat_comp`), and every
  graded superfunctor `H : A_{q,π} → B` is isomorphic to `(J ⋙ H)~` by even isomorphisms of
  degree zero (`extendRestrictIso`, `extendRestrictIso_hom_mem`,
  `extendRestrictIso_hom_mem_degree`).
* `QPiEnvelope.map F : A_{q,π} → B_{q,π}` (the strict graded 2-superfunctor `-_{q,π}` on
  1-morphisms), with `J ⋙ F_{q,π} = F ⋙ J`, `map_id`, `map_comp`, commuting with `Π` and `Q`
  on objects.

## Scope

As for Theorem 4.3 (`StringDiagrams.Super.Envelope`), Theorem 6.9 is stated through its
content on objects, on homogeneous supernatural transformations of each parity and degree,
and on composition; the graded Hom-supercategories and the 2-adjunction `-_{q,π} ⊣ ν` are not
packaged.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory GradedSupercategory

universe w w₁ w₂ w₃ w₄

/-! ## The `Q`-envelope -/

/-- The objects `Q^m λ` of the `Q`-envelope of `C`. -/
@[ext]
structure QEnvelope (R : Type w) (C : Type w₁) where
  /-- The degree shift `m`. -/
  shift : ℤ
  /-- The underlying object `λ`. -/
  obj : C

namespace QEnvelope

variable {R : Type w} {C : Type w₁} [Category.{w₂} C]

instance : Category (QEnvelope R C) where
  Hom X Y := X.obj ⟶ Y.obj
  id X := 𝟙 X.obj
  comp {X Y Z} (f : X.obj ⟶ Y.obj) (g : Y.obj ⟶ Z.obj) := f ≫ g
  id_comp {X Y} (f : X.obj ⟶ Y.obj) := Category.id_comp f
  comp_id {X Y} (f : X.obj ⟶ Y.obj) := Category.comp_id f
  assoc {W X _ _} (f : W.obj ⟶ X.obj) g h := Category.assoc f g h

/-- The morphism of `C` underlying a morphism of the `Q`-envelope. -/
def toHom {X Y : QEnvelope R C} (f : X ⟶ Y) : X.obj ⟶ Y.obj := f

/-- The morphism `f_m^n : Q^m λ ⟶ Q^n μ` given by `f : λ ⟶ μ`. -/
def ofHom {X Y : QEnvelope R C} (f : X.obj ⟶ Y.obj) : X ⟶ Y := f

@[simp] theorem toHom_ofHom {X Y : QEnvelope R C} (f : X.obj ⟶ Y.obj) : toHom (ofHom f) = f :=
  rfl

@[simp] theorem ofHom_toHom {X Y : QEnvelope R C} (f : X ⟶ Y) : ofHom (toHom f) = f := rfl

@[ext] theorem hom_ext {X Y : QEnvelope R C} {f g : X ⟶ Y} (h : toHom f = toHom g) : f = g := h

@[simp] theorem toHom_id (X : QEnvelope R C) : toHom (𝟙 X) = 𝟙 X.obj := rfl

@[simp] theorem toHom_comp {X Y Z : QEnvelope R C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    toHom (f ≫ g) = toHom f ≫ toHom g := rfl

/-- An isomorphism of underlying objects gives an isomorphism of the `Q`-envelope. -/
@[simps]
def isoOfIso {X Y : QEnvelope R C} (e : X.obj ≅ Y.obj) : X ≅ Y where
  hom := ofHom e.hom
  inv := ofHom e.inv
  hom_inv_id := e.hom_inv_id
  inv_hom_id := e.inv_hom_id

/-- An isomorphism of the `Q`-envelope gives an isomorphism of underlying objects. -/
@[simps]
def isoToIso {X Y : QEnvelope R C} (e : X ≅ Y) : X.obj ≅ Y.obj where
  hom := toHom e.hom
  inv := toHom e.inv
  hom_inv_id := e.hom_inv_id
  inv_hom_id := e.inv_hom_id

variable [Preadditive C]

instance : Preadditive (QEnvelope R C) where
  homGroup X Y := inferInstanceAs (AddCommGroup (X.obj ⟶ Y.obj))
  add_comp _ _ _ f f' g := Preadditive.add_comp (C := C) _ _ _ f f' g
  comp_add _ _ _ f g g' := Preadditive.comp_add (C := C) _ _ _ f g g'

@[simp] theorem toHom_add {X Y : QEnvelope R C} (f g : X ⟶ Y) :
    toHom (f + g) = toHom f + toHom g := rfl

@[simp] theorem toHom_zero {X Y : QEnvelope R C} : toHom (0 : X ⟶ Y) = 0 := rfl

variable [CommRing R] [Linear R C]

instance : Linear R (QEnvelope R C) where
  homModule X Y := inferInstanceAs (Module R (X.obj ⟶ Y.obj))
  smul_comp _ _ _ r f g := Linear.smul_comp (C := C) _ _ _ r f g
  comp_smul _ _ _ f r g := Linear.comp_smul (C := C) _ _ _ f r g

@[simp] theorem toHom_smul {X Y : QEnvelope R C} (r : R) (f : X ⟶ Y) :
    toHom (r • f) = r • toHom f := rfl

variable [Supercategory R C]

/-- The `Q`-envelope is a supercategory with the parities of `C`. -/
instance : Supercategory R (QEnvelope R C) where
  parity X Y p := parity (R := R) X.obj Y.obj p
  isInternal X Y := isInternal (R := R) X.obj Y.obj
  id_mem X := id_mem X.obj
  comp_mem hf hg := comp_mem (R := R) (C := C) hf hg

theorem mem_parity_iff {X Y : QEnvelope R C} {f : X ⟶ Y} {p : ZMod 2} :
    f ∈ parity (R := R) X Y p ↔ toHom f ∈ parity (R := R) X.obj Y.obj p := Iff.rfl

theorem toHom_proj (p : ZMod 2) {X Y : QEnvelope R C} (f : X ⟶ Y) :
    toHom (proj R p f) = proj R p (toHom f) := by
  let g : X ⟶ Y := ofHom (proj R p (toHom f))
  let h : X ⟶ Y := ofHom (proj R (p + 1) (toHom f))
  have e : f = g + h := (proj_add_proj_add_one (R := R) p (toHom f)).symm
  rw [proj_eq_of_add e (proj_mem (R := R) (C := C) p (toHom f))
    (proj_mem (R := R) (C := C) (p + 1) (toHom f))]
  rfl

variable [GradedSupercategory R C]

theorem isInternal_shift (X Y : C) (s : ℤ) :
    DirectSum.IsInternal fun n => degree (R := R) X Y (n + s) := by
  have h := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).1
    (isInternal_degree (R := R) X Y)
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  exact ⟨h.1.comp (add_left_injective s), by
    rw [← h.2]; exact (Equiv.addRight s).iSup_comp (g := fun n => degree (R := R) X Y n)⟩

/-- The `Q`-envelope is a graded supercategory: `f_m^n : Q^m λ → Q^n μ` has degree
`deg f + n - m`. -/
instance instGraded : GradedSupercategory R (QEnvelope R C) where
  degree X Y k := degree (R := R) X.obj Y.obj (k + (X.shift - Y.shift))
  isInternal_degree X Y := isInternal_shift (R := R) X.obj Y.obj (X.shift - Y.shift)
  proj_mem_degree p hf := by
    show toHom (proj R p _) ∈ _
    rw [toHom_proj]; exact proj_mem_degree p hf
  id_mem_degree X := by
    show 𝟙 X.obj ∈ degree (R := R) X.obj X.obj (0 + (X.shift - X.shift))
    simpa using id_mem_degree (R := R) X.obj
  comp_mem_degree {X Y Z m n f g} hf hg := by
    have := comp_mem_degree hf hg
    rwa [show m + (X.shift - Y.shift) + (n + (Y.shift - Z.shift)) =
      m + n + (X.shift - Z.shift) by ring] at this

theorem mem_degree_iff {X Y : QEnvelope R C} {f : X ⟶ Y} {k : ℤ} :
    f ∈ degree (R := R) X Y k ↔ toHom f ∈ degree (R := R) X.obj Y.obj (k + (X.shift - Y.shift)) :=
  Iff.rfl

theorem ofHom_mem_degree {X Y : QEnvelope R C} {f : X.obj ⟶ Y.obj} {d : ℤ}
    (hf : f ∈ degree (R := R) X.obj Y.obj d) :
    ofHom f ∈ degree (R := R) X Y (d + Y.shift - X.shift) := by
  rw [mem_degree_iff, toHom_ofHom]
  convert hf using 2; ring

variable (R C) in
/-- The inclusion `λ ↦ Q⁰ λ`. -/
@[simps]
def J : C ⥤ QEnvelope R C where
  obj X := ⟨0, X⟩
  map f := ofHom f

instance : (J R C).Additive where
instance : (J R C).Linear R where
instance : IsGradedSuperfunctor R (J R C) where
  map_mem hf := hf
  map_mem_degree {X Y n f} hf := by
    rw [mem_degree_iff]; simpa using hf
instance : (J R C).Full where
  map_surjective f := ⟨toHom f, rfl⟩
instance : (J R C).Faithful where
  map_injective h := h

/-- The even isomorphism `(1_λ)_0^m : Q⁰ λ ≅ Q^m λ`, of degree `m`. -/
def shiftIso (X : QEnvelope R C) : (J R C).obj X.obj ≅ X := isoOfIso (Iso.refl X.obj)

omit [GradedSupercategory R C] in
theorem shiftIso_hom_mem (X : QEnvelope R C) :
    (shiftIso X).hom ∈ parity (R := R) ((J R C).obj X.obj) X 0 := id_mem (R := R) X.obj

theorem shiftIso_hom_mem_degree (X : QEnvelope R C) :
    (shiftIso X).hom ∈ degree (R := R) ((J R C).obj X.obj) X X.shift := by
  rw [mem_degree_iff]
  show 𝟙 X.obj ∈ _
  simpa using id_mem_degree (R := R) X.obj

/-! ### The universal property of the `Q`-envelope -/

section Universal

variable {B : Type w₃} [Category.{w₄} B] [Preadditive B] [Linear R B] [Supercategory R B]
  [GradedSupercategory R B] [QPiSupercategory R B]

open QPiSupercategory

variable (R) (F : C ⥤ B)

/-- The extension `F^Q : Q^m λ ↦ Q^m (F λ)`, `f_m^n ↦ (σ^n)⁻¹ ∘ F f ∘ σ^m`. -/
@[simps]
def extend : QEnvelope R C ⥤ B where
  obj X := qPow R X.shift (F.obj X.obj)
  map {X Y} f := (σPow R X.shift (F.obj X.obj)).hom ≫ F.map (toHom f) ≫
    (σPow R Y.shift (F.obj Y.obj)).inv
  map_id X := by simp
  map_comp f g := by simp

variable [F.Additive] [F.Linear R] [IsGradedSuperfunctor R F]

instance : (extend R F).Additive where
  map_add := by simp [Preadditive.add_comp, Preadditive.comp_add]

instance : (extend R F).Linear R where
  map_smul _ _ := by simp

instance : IsGradedSuperfunctor R (extend R F) where
  map_mem {X Y p f} hf := by
    have := comp_mem (comp_mem (σPow_hom_mem (R := R) X.shift (F.obj X.obj)) (map_mem F hf))
      (σPow_inv_mem (R := R) Y.shift (F.obj Y.obj))
    simpa using this
  map_mem_degree {X Y n f} hf := by
    have := comp_mem_degree (comp_mem_degree (σPow_hom_mem_degree (R := R) X.shift (F.obj X.obj))
      (map_mem_degree F hf)) (σPow_inv_mem_degree (R := R) Y.shift (F.obj Y.obj))
    rw [show -X.shift + (n + (X.shift - Y.shift)) + Y.shift = n by ring] at this
    simpa using this

omit [Preadditive C] [Linear R C] [Supercategory R C] [GradedSupercategory R C] [F.Additive]
  [F.Linear R] [IsGradedSuperfunctor R F] in
theorem J_comp_extend : J R C ⋙ extend R F = F :=
  CategoryTheory.Functor.ext (fun _ => rfl) (fun X Y f => by simp)

variable {R F}

variable {G : C ⥤ B}

variable (R F G) in
/-- The extension `x^Q_{Q^m λ} = (σ^m)⁻¹ ∘ x_λ ∘ σ^m`. -/
def extendNat (x : ∀ X, F.obj X ⟶ G.obj X) (X : QEnvelope R C) :
    (extend R F).obj X ⟶ (extend R G).obj X :=
  (σPow R X.shift (F.obj X.obj)).hom ≫ x X.obj ≫ (σPow R X.shift (G.obj X.obj)).inv

omit [GradedSupercategory R C] in
omit [F.Additive] [F.Linear R] [IsGradedSuperfunctor R F] in
theorem isGradedSupernatural_extendNat [G.Linear R] {p : ZMod 2} {n : ℤ}
    {x : ∀ X, F.obj X ⟶ G.obj X} (hx : IsGradedSupernatural R p n x) :
    IsGradedSupernatural R p n (F := extend R F) (G := extend R G) (extendNat R F G x) where
  mem X := by
    have := comp_mem (comp_mem (σPow_hom_mem (R := R) X.shift (F.obj X.obj)) (hx.mem X.obj))
      (σPow_inv_mem (R := R) X.shift (G.obj X.obj))
    simpa [extendNat] using this
  naturality {X Y q f} hf := by
    simp only [extend_obj, extend_map, extendNat, Category.assoc, Iso.inv_hom_id_assoc,
      Linear.comp_smul, Linear.smul_comp]
    rw [reassoc_of% (hx.naturality (f := toHom f) hf), Linear.smul_comp, Linear.comp_smul]
    simp only [Category.assoc]
  mem_degree X := by
    have := comp_mem_degree (comp_mem_degree
      (σPow_hom_mem_degree (R := R) X.shift (F.obj X.obj)) (hx.mem_degree X.obj))
      (σPow_inv_mem_degree (R := R) X.shift (G.obj X.obj))
    rw [show -X.shift + n + X.shift = n by ring] at this
    simpa [extendNat] using this

omit [Preadditive C] [Linear R C] [Supercategory R C] [GradedSupercategory R C] [F.Additive]
  [F.Linear R] [IsGradedSuperfunctor R F] in
@[simp] theorem extendNat_J (x : ∀ X, F.obj X ⟶ G.obj X) (X : C) :
    extendNat R F G x ((J R C).obj X) = x X := by
  simp [extendNat]

omit [F.Additive] [F.Linear R] [IsGradedSuperfunctor R F] [QPiSupercategory R B]
  [GradedSupercategory R B] [GradedSupercategory R C] in
/-- Supernatural transformations of the same parity out of the `Q`-envelope agree if they agree
on the objects `Q⁰ λ`. -/
theorem eq_of_restrict_eq {H K : QEnvelope R C ⥤ B} [K.Linear R] {p : ZMod 2}
    {y y' : ∀ X, H.obj X ⟶ K.obj X} (hy : IsSupernatural R p y) (hy' : IsSupernatural R p y')
    (h : ∀ X : C, y ((J R C).obj X) = y' ((J R C).obj X)) : y = y' := by
  funext X
  have hu : (isoOfIso (Iso.refl X.obj) : (J R C).obj X.obj ≅ X).hom ∈
      parity (R := R) ((J R C).obj X.obj) X 0 := id_mem (R := R) X.obj
  have e1 := hy.naturality hu
  have e2 := hy'.naturality hu
  rw [h X.obj, ← e2] at e1
  exact (cancel_epi (H.mapIso (isoOfIso (Iso.refl X.obj) : (J R C).obj X.obj ≅ X)).hom).1 e1

omit [QPiSupercategory R B] in
/-- Restriction of a supernatural transformation along `J`. -/
theorem isGradedSupernatural_restrict {H K : QEnvelope R C ⥤ B} {p : ZMod 2} {n : ℤ}
    {y : ∀ X, H.obj X ⟶ K.obj X} (hy : IsGradedSupernatural R p n y) :
    IsGradedSupernatural R p n (F := J R C ⋙ H) (G := J R C ⋙ K)
      fun X => y ((J R C).obj X) :=
  hy.whiskerLeft (J R C)

/-- The even isomorphisms `σ^m ≫ H((1_λ)_0^m) : Q^m(H Q⁰ λ) ≅ H(Q^m λ)`, of degree `0`. -/
def extendRestrictIso (H : QEnvelope R C ⥤ B) [H.Additive] [H.Linear R]
    [IsGradedSuperfunctor R H] : extend R (J R C ⋙ H) ≅ H :=
  NatIso.ofComponents (fun X => σPow R X.shift (H.obj ((J R C).obj X.obj)) ≪≫
      H.mapIso (shiftIso X))
    (fun {X Y} f => by
      simp only [extend_obj, Functor.comp_obj, extend_map, Functor.comp_map, Iso.trans_hom,
        Functor.mapIso_hom, Category.assoc, Iso.inv_hom_id_assoc]
      rw [← H.map_comp, ← H.map_comp]
      congr 2
      exact hom_ext (by simp [shiftIso]))

theorem extendRestrictIso_hom_mem (H : QEnvelope R C ⥤ B) [H.Additive] [H.Linear R]
    [IsGradedSuperfunctor R H] (X : QEnvelope R C) :
    (extendRestrictIso H).hom.app X ∈ parity (R := R) _ (H.obj X) 0 := by
  simpa [extendRestrictIso] using comp_mem (σPow_hom_mem (R := R) X.shift _)
    (map_mem H (shiftIso_hom_mem (R := R) X))

theorem extendRestrictIso_hom_mem_degree (H : QEnvelope R C ⥤ B) [H.Additive] [H.Linear R]
    [IsGradedSuperfunctor R H] (X : QEnvelope R C) :
    (extendRestrictIso H).hom.app X ∈ degree (R := R) _ (H.obj X) 0 := by
  simpa [extendRestrictIso] using comp_mem_degree (σPow_hom_mem_degree (R := R) X.shift _)
    (map_mem_degree H (shiftIso_hom_mem_degree (R := R) X))

end Universal

/-! ### Functoriality -/

section Map

variable {D : Type w₃} [Category.{w₄} D] [Preadditive D] [Linear R D] [Supercategory R D]
  [GradedSupercategory R D]

variable (R) in
/-- The extension `F_q : Q^m λ ↦ Q^m (F λ)`, `f_m^n ↦ (F f)_m^n`. -/
@[simps]
def map (F : C ⥤ D) : QEnvelope R C ⥤ QEnvelope R D where
  obj X := ⟨X.shift, F.obj X.obj⟩
  map f := ofHom (F.map (toHom f))
  map_id X := F.map_id X.obj
  map_comp f g := F.map_comp (toHom f) (toHom g)

instance (F : C ⥤ D) [F.Additive] : (map R F).Additive where
  map_add := F.map_add

instance (F : C ⥤ D) [F.Additive] [F.Linear R] : (map R F).Linear R where
  map_smul f r := Functor.Linear.map_smul (F := F) (toHom f) r

instance (F : C ⥤ D) [F.Additive] [F.Linear R] [IsGradedSuperfunctor R F] :
    IsGradedSuperfunctor R (map R F) where
  map_mem hf := map_mem (R := R) F hf
  map_mem_degree hf := map_mem_degree (R := R) F hf

end Map

end QEnvelope

/-! ## The Π-envelope of a graded supercategory is graded -/

namespace Envelope

variable {R : Type w} [CommRing R] {D : Type w₁} [Category.{w₂} D] [Preadditive D] [Linear R D]
  [Supercategory R D] [GradedSupercategory R D]

/-- The Π-envelope of a graded supercategory is a graded supercategory, with the degrees of
`D`: `f_a^b` has degree `deg f`. -/
instance instGraded : GradedSupercategory R (Envelope R D) where
  degree X Y n := degree (R := R) X.obj Y.obj n
  isInternal_degree X Y := isInternal_degree (R := R) X.obj Y.obj
  proj_mem_degree p hf := by
    show toHom (proj R p _) ∈ _
    rw [toHom_proj]; exact proj_mem_degree _ hf
  id_mem_degree X := id_mem_degree (R := R) X.obj
  comp_mem_degree hf hg := comp_mem_degree (R := R) (C := D) hf hg

theorem mem_degree_iff {X Y : Envelope R D} {f : X ⟶ Y} {n : ℤ} :
    f ∈ degree (R := R) X Y n ↔ toHom f ∈ degree (R := R) X.obj Y.obj n := Iff.rfl

instance : IsGradedSuperfunctor R (J R D) where
  map_mem_degree hf := hf

theorem ζIso_mem_degree (X : Envelope R D) :
    (ζIso X).hom ∈ degree (R := R) (⟨X.par + 1, X.obj⟩ : Envelope R D) X 0 :=
  id_mem_degree (R := R) X.obj

theorem shiftIso_hom_mem_degree (X : Envelope R D) :
    (shiftIso X).hom ∈ degree (R := R) ((J R D).obj X.obj) X 0 :=
  id_mem_degree (R := R) X.obj

instance (F : D ⥤ D) [F.Additive] [F.Linear R] [IsGradedSuperfunctor R F] :
    IsGradedSuperfunctor R (map R F) where
  map_mem_degree hf := map_mem_degree (R := R) F hf

section Universal

variable {B : Type w₃} [Category.{w₄} B] [Preadditive B] [Linear R B] [Supercategory R B]
  [GradedSupercategory R B] [QPiSupercategory R B]

theorem ζPow_hom_mem_degree (a : ZMod 2) (X : B) :
    (ζPow R a X).hom ∈ degree (R := R) (piPow R a X) X 0 := by
  rcases parity_eq_zero_or_one a with rfl | rfl
  · exact id_mem_degree X
  · exact QPiSupercategory.ζ_hom_mem_degree X

theorem ζPow_inv_mem_degree (a : ZMod 2) (X : B) :
    (ζPow R a X).inv ∈ degree (R := R) X (piPow R a X) 0 := by
  simpa using inv_mem_degree _ (ζPow_hom_mem_degree (R := R) a X)

instance (F : D ⥤ B) [F.Additive] [F.Linear R] [IsGradedSuperfunctor R F] :
    IsGradedSuperfunctor R (extend R F) where
  map_mem_degree {X Y n f} hf := by
    have := comp_mem_degree (comp_mem_degree (ζPow_hom_mem_degree X.par (F.obj X.obj))
      (map_mem_degree F hf)) (ζPow_inv_mem_degree Y.par (F.obj Y.obj))
    simpa using this

omit [Preadditive D] [Linear R D] [Supercategory R D] [GradedSupercategory R D] in
theorem extendNat_mem_degree {F G : D ⥤ B} {p : ZMod 2} {n : ℤ} {x : ∀ X, F.obj X ⟶ G.obj X}
    (hx : ∀ X, x X ∈ degree (R := R) (F.obj X) (G.obj X) n) (X : Envelope R D) :
    extendNat R F G p x X ∈ degree (R := R) ((extend R F).obj X) ((extend R G).obj X) n := by
  have := comp_mem_degree (comp_mem_degree (ζPow_hom_mem_degree X.par (F.obj X.obj)) (hx X.obj))
    (ζPow_inv_mem_degree X.par (G.obj X.obj))
  simp only [zero_add, add_zero] at this
  exact Submodule.smul_mem _ _ (by simpa [Category.assoc] using this)

/-- The extension of an even isomorphism `G ≅ G'` to an even isomorphism `G̃ ≅ G̃'`. -/
def extendIso {G G' : D ⥤ B} [G.Additive] [G.Linear R] [IsSuperfunctor R G] [G'.Additive]
    [G'.Linear R] [IsSuperfunctor R G'] (α : G ≅ G')
    (hα : ∀ X, α.hom.app X ∈ parity (R := R) (G.obj X) (G'.obj X) 0) :
    extend R G ≅ extend R G' where
  hom := (isSupernatural_extendNat (isSupernatural_of_natTrans α.hom hα)).toNatTrans
  inv := (isSupernatural_extendNat (isSupernatural_of_natTrans α.inv
    fun X => inv_mem (α.app X) (hα X))).toNatTrans
  hom_inv_id := by
    ext X
    have := congrFun (extendNat_comp (isSupernatural_of_natTrans α.hom hα)
      (isSupernatural_of_natTrans α.inv fun X => inv_mem (α.app X) (hα X))) X
    simp only [Iso.hom_inv_id_app, zero_add] at this
    simp only [NatTrans.comp_app, IsSupernatural.toNatTrans_app, NatTrans.id_app]
    rw [← this, extendNat_id]
  inv_hom_id := by
    ext X
    have := congrFun (extendNat_comp
      (isSupernatural_of_natTrans α.inv fun X => inv_mem (α.app X) (hα X))
      (isSupernatural_of_natTrans α.hom hα)) X
    simp only [Iso.inv_hom_id_app, zero_add] at this
    simp only [NatTrans.comp_app, IsSupernatural.toNatTrans_app, NatTrans.id_app]
    rw [← this, extendNat_id]

omit [GradedSupercategory R D] in
theorem extendIso_hom_app {G G' : D ⥤ B} [G.Additive] [G.Linear R] [IsSuperfunctor R G]
    [G'.Additive] [G'.Linear R] [IsSuperfunctor R G'] (α : G ≅ G')
    (hα : ∀ X, α.hom.app X ∈ parity (R := R) (G.obj X) (G'.obj X) 0) (X : Envelope R D) :
    (extendIso α hα).hom.app X = extendNat R G G' 0 (fun X => α.hom.app X) X := rfl

end Universal

end Envelope

/-! ## The `(Q, Π)`-envelope -/

/-- **Definition 6.8.** The `(Q, Π)`-envelope `A_{q,π}` of a graded supercategory `A`: the
Π-envelope of the `Q`-envelope. Its object `⟨a, ⟨m, λ⟩⟩` is the paper's `Q^m Π^a λ`. -/
abbrev QPiEnvelope (R : Type w) (C : Type w₁) := Envelope R (QEnvelope R C)

namespace QPiEnvelope

variable {R : Type w} [CommRing R] {C : Type w₁} [Category.{w₂} C] [Preadditive C] [Linear R C]
  [Supercategory R C] [GradedSupercategory R C]

/-- The object `Q^m Π^a λ`. -/
abbrev mk (m : ℤ) (a : ZMod 2) (X : C) : QPiEnvelope R C := ⟨a, ⟨m, X⟩⟩

/-- The morphism `f^{n,b}_{m,a} : Q^m Π^a λ ⟶ Q^n Π^b μ` coming from `f : λ ⟶ μ`. -/
def ofHom {X Y : QPiEnvelope R C} (f : X.obj.obj ⟶ Y.obj.obj) : X ⟶ Y :=
  Envelope.ofHom (QEnvelope.ofHom f)

/-- The morphism of `A` underlying a morphism of `A_{q,π}`. -/
def toHom {X Y : QPiEnvelope R C} (f : X ⟶ Y) : X.obj.obj ⟶ Y.obj.obj :=
  QEnvelope.toHom (Envelope.toHom f)

omit [CommRing R] [Preadditive C] [Linear R C] [Supercategory R C] [GradedSupercategory R C] in
@[simp] theorem toHom_ofHom {X Y : QPiEnvelope R C} (f : X.obj.obj ⟶ Y.obj.obj) :
    toHom (ofHom f) = f := rfl

omit [CommRing R] [Preadditive C] [Linear R C] [Supercategory R C] [GradedSupercategory R C] in
@[simp] theorem toHom_comp {X Y Z : QPiEnvelope R C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    toHom (f ≫ g) = toHom f ≫ toHom g := rfl

omit [CommRing R] [Preadditive C] [Linear R C] [Supercategory R C] [GradedSupercategory R C] in
/-- **Definition 6.8.** Composition: `g^{n,c}_{m,b} ∘ f^{m,b}_{l,a} = (g ∘ f)^{n,c}_{l,a}`. -/
theorem ofHom_comp {X Y Z : QPiEnvelope R C} (f : X.obj.obj ⟶ Y.obj.obj)
    (g : Y.obj.obj ⟶ Z.obj.obj) : ofHom f ≫ ofHom g = ofHom (X := X) (Y := Z) (f ≫ g) := rfl

omit [GradedSupercategory R C] in
/-- **Definition 6.8.** `f^{n,b}_{m,a}` has parity `|f| + a + b`. -/
theorem ofHom_mem {X Y : QPiEnvelope R C} {f : X.obj.obj ⟶ Y.obj.obj} {q : ZMod 2}
    (hf : f ∈ parity (R := R) X.obj.obj Y.obj.obj q) :
    ofHom f ∈ parity (R := R) X Y (q + X.par + Y.par) := by
  rw [add_assoc]; exact Envelope.ofHom_mem (R := R) (X := X) (Y := Y) hf

/-- **Definition 6.8.** `f^{n,b}_{m,a}` has degree `deg f + n - m`. -/
theorem ofHom_mem_degree {X Y : QPiEnvelope R C} {f : X.obj.obj ⟶ Y.obj.obj} {d : ℤ}
    (hf : f ∈ degree (R := R) X.obj.obj Y.obj.obj d) :
    ofHom f ∈ degree (R := R) X Y (d + Y.obj.shift - X.obj.shift) :=
  QEnvelope.ofHom_mem_degree (R := R) (X := X.obj) (Y := Y.obj) hf

/-- The even isomorphism `σ = (1_λ)^{m,a}_{m+1,a} : Q^{m+1} Π^a λ ≅ Q^m Π^a λ`. -/
def σIso (X : QPiEnvelope R C) : (⟨X.par, ⟨X.obj.shift + 1, X.obj.obj⟩⟩ : QPiEnvelope R C) ≅ X :=
  Envelope.isoOfIso (QEnvelope.isoOfIso (Iso.refl X.obj.obj))

/-- The even isomorphism `σ̄ = (1_λ)^{m,a}_{m-1,a} : Q^{m-1} Π^a λ ≅ Q^m Π^a λ`. -/
def σbarIso (X : QPiEnvelope R C) :
    (⟨X.par, ⟨X.obj.shift - 1, X.obj.obj⟩⟩ : QPiEnvelope R C) ≅ X :=
  Envelope.isoOfIso (QEnvelope.isoOfIso (Iso.refl X.obj.obj))

omit [GradedSupercategory R C] in
theorem idIso_mem {X Y : QPiEnvelope R C} (hXY : X.par = Y.par) (hobj : X.obj.obj = Y.obj.obj)
    (e : X.obj.obj ≅ Y.obj.obj) (he : e = eqToIso hobj) :
    (Envelope.isoOfIso (QEnvelope.isoOfIso e) : X ≅ Y).hom ∈ parity (R := R) X Y 0 := by
  obtain ⟨a, ⟨m, x⟩⟩ := X
  obtain ⟨b, ⟨n, y⟩⟩ := Y
  simp only at hXY hobj
  subst hXY hobj he
  rw [Envelope.mem_parity_iff]
  show 𝟙 x ∈ parity (R := R) x x (0 + (a + a))
  rw [zmod2_add_self, add_zero]; exact id_mem x

/-- **Definition 6.8.** The `(Q, Π)`-envelope is a graded `(Q, Π)`-supercategory: `Π` and `ζ`
as in Definition 1.10, `Q(Q^m Π^a λ) = Q^{m+1} Π^a λ`, `Q⁻¹(Q^m Π^a λ) = Q^{m-1} Π^a λ`, with
`σ` and `σ̄` induced by the identity morphisms of `A`. -/
instance instQPi : QPiSupercategory R (QPiEnvelope R C) :=
  QPiSupercategory.ofIso (fun X => Envelope.ζIso_mem_degree X)
    (fun X => ⟨X.par, ⟨X.obj.shift + 1, X.obj.obj⟩⟩) σIso
    (fun X => idIso_mem rfl rfl _ rfl)
    (fun X => by
      show 𝟙 X.obj.obj ∈ degree (R := R) X.obj.obj X.obj.obj (-1 + (X.obj.shift + 1 - X.obj.shift))
      simpa using id_mem_degree (R := R) X.obj.obj)
    (fun X => ⟨X.par, ⟨X.obj.shift - 1, X.obj.obj⟩⟩) σbarIso
    (fun X => idIso_mem rfl rfl _ rfl)
    (fun X => by
      show 𝟙 X.obj.obj ∈ degree (R := R) X.obj.obj X.obj.obj (1 + (X.obj.shift - 1 - X.obj.shift))
      simpa using id_mem_degree (R := R) X.obj.obj)

@[simp] theorem Q_obj (X : QPiEnvelope R C) :
    (QPiSupercategory.Q (R := R)).obj X = ⟨X.par, ⟨X.obj.shift + 1, X.obj.obj⟩⟩ := rfl

@[simp] theorem Qinv_obj (X : QPiEnvelope R C) :
    (QPiSupercategory.Qinv (R := R)).obj X = ⟨X.par, ⟨X.obj.shift - 1, X.obj.obj⟩⟩ := rfl

omit [GradedSupercategory R C] in
@[simp] theorem pi_obj (X : QPiEnvelope R C) :
    (PiSupercategory.pi (R := R)).obj X = ⟨X.par + 1, X.obj⟩ := rfl

@[simp] theorem toHom_σ_hom (X : QPiEnvelope R C) :
    toHom (QPiSupercategory.σ (R := R) X).hom = 𝟙 X.obj.obj := rfl

@[simp] theorem toHom_σbar_hom (X : QPiEnvelope R C) :
    toHom (QPiSupercategory.σbar (R := R) X).hom = 𝟙 X.obj.obj := rfl

omit [GradedSupercategory R C] in
@[simp] theorem toHom_ζ_hom (X : QPiEnvelope R C) :
    toHom (PiSupercategory.ζ (R := R) X).hom = 𝟙 X.obj.obj := rfl

/-! ### The canonical graded superfunctor `J` -/

variable (R C) in
/-- The canonical graded superfunctor `J : A → A_{q,π}`, `λ ↦ Q⁰ Π⁰ λ`, `f ↦ f^{0,0}_{0,0}`. -/
abbrev J : C ⥤ QPiEnvelope R C := QEnvelope.J R C ⋙ Envelope.J R (QEnvelope R C)

omit [CommRing R] [Preadditive C] [Linear R C] [Supercategory R C] [GradedSupercategory R C] in
@[simp] theorem J_obj (X : C) : (J R C).obj X = ⟨0, ⟨0, X⟩⟩ := rfl

omit [CommRing R] [Preadditive C] [Linear R C] [Supercategory R C] [GradedSupercategory R C] in
@[simp] theorem toHom_J_map {X Y : C} (f : X ⟶ Y) : toHom ((J R C).map f) = f := rfl

instance : (J R C).Full := Functor.Full.comp _ _

instance : (J R C).Faithful := Functor.Faithful.comp _ _

/-! ### `(Q, Π)`-completeness -/

variable (R C) in
/-- A graded supercategory is `(Q, Π)`-complete if every object is the target of even
isomorphisms of degrees `1` and `-1` and of an odd isomorphism of degree `0` (Brundan–Ellis,
§6, after Definition 6.8). -/
def QPiComplete : Prop :=
  ∀ X : C, (∃ (Y : C) (e : Y ≅ X), e.hom ∈ parity (R := R) Y X 0 ∧ e.hom ∈ degree (R := R) Y X 1) ∧
    (∃ (Y : C) (e : Y ≅ X), e.hom ∈ parity (R := R) Y X 0 ∧ e.hom ∈ degree (R := R) Y X (-1)) ∧
    (∃ (Y : C) (e : Y ≅ X), e.hom ∈ parity (R := R) Y X 1 ∧ e.hom ∈ degree (R := R) Y X 0)

/-- In a `(Q, Π)`-complete graded supercategory, every object is the target of an isomorphism
of every parity and degree. -/
theorem QPiComplete.exists_iso (h : QPiComplete R C) (m : ℤ) :
    ∀ (a : ZMod 2) (X : C), ∃ (Y : C) (e : Y ≅ X),
      e.hom ∈ parity (R := R) Y X a ∧ e.hom ∈ degree (R := R) Y X m := by
  induction m using Int.induction_on with
  | hz =>
    intro a X
    rcases parity_eq_zero_or_one a with rfl | rfl
    · exact ⟨X, Iso.refl X, id_mem X, id_mem_degree X⟩
    · exact (h X).2.2
  | hp k ih =>
    intro a X
    obtain ⟨Y, e, he, he'⟩ := ih a X
    obtain ⟨Z, e₂, he₂, he₂'⟩ := (h Y).1
    refine ⟨Z, e₂ ≪≫ e, ?_, ?_⟩
    · simpa using comp_mem he₂ he
    · simpa [add_comm] using comp_mem_degree he₂' he'
  | hn k ih =>
    intro a X
    obtain ⟨Y, e, he, he'⟩ := ih a X
    obtain ⟨Z, e₂, he₂, he₂'⟩ := (h Y).2.1
    refine ⟨Z, e₂ ≪≫ e, ?_, ?_⟩
    · simpa using comp_mem he₂ he
    · have := comp_mem_degree he₂' he'
      rwa [show -1 + (-(k : ℤ)) = -(k : ℤ) - 1 by ring] at this

/-- `J` is gradedly evenly dense if and only if `A` is `(Q, Π)`-complete. -/
theorem J_gradedEvenlyDense_iff : GradedEvenlyDense R (J R C) ↔ QPiComplete R C := by
  constructor
  · intro h X
    have key : ∀ (m : ℤ) (a : ZMod 2), ∃ (Y : C) (e : Y ≅ X),
        e.hom ∈ parity (R := R) Y X a ∧ e.hom ∈ degree (R := R) Y X (-m) := by
      intro m a
      obtain ⟨Y, e, he, he'⟩ := h (QPiEnvelope.mk m a X)
      refine ⟨Y, QEnvelope.isoToIso (Envelope.isoToIso e), ?_, ?_⟩
      · rw [Envelope.mem_parity_iff] at he
        simpa using he
      · rw [Envelope.mem_degree_iff, QEnvelope.mem_degree_iff] at he'
        simpa using he'
    refine ⟨?_, ?_, ?_⟩
    · simpa using key (-1) 0
    · simpa using key 1 0
    · simpa using key 0 1
  · intro h X
    obtain ⟨a, ⟨m, X⟩⟩ := X
    obtain ⟨Y, e, he, he'⟩ := h.exists_iso (-m) a X
    refine ⟨Y, Envelope.isoOfIso (QEnvelope.isoOfIso e), ?_, ?_⟩
    · rw [Envelope.mem_parity_iff]
      show e.hom ∈ parity (R := R) Y X (0 + (0 + a))
      simpa using he
    · rw [Envelope.mem_degree_iff, QEnvelope.mem_degree_iff]
      show e.hom ∈ degree (R := R) Y X (0 + (0 - m))
      simpa using he'

/-- If `A` is `(Q, Π)`-complete, `J : A → A_{q,π}` is a graded superequivalence. -/
def gradedSuperequivalenceJ (h : QPiComplete R C) : GradedSuperequivalence R (J R C) :=
  GradedSuperequivalence.ofFullyFaithful (J R C) (J_gradedEvenlyDense_iff.2 h)

/-- If `J : A → A_{q,π}` is a graded superequivalence, `A` is `(Q, Π)`-complete. -/
theorem qpiComplete_of_gradedSuperequivalence (e : GradedSuperequivalence R (J R C)) :
    QPiComplete R C :=
  J_gradedEvenlyDense_iff.1 e.gradedEvenlyDense

/-! ### The universal property and Theorem 6.9 -/

section Universal

variable {B : Type w₃} [Category.{w₄} B] [Preadditive B] [Linear R B] [Supercategory R B]
  [GradedSupercategory R B] [QPiSupercategory R B]

variable (R) (F : C ⥤ B) [F.Additive] [F.Linear R] [IsGradedSuperfunctor R F]

/-- The extension `F̃ : A_{q,π} ⥤ B` of a graded superfunctor (the analogue of Lemma 4.2(i)):
`F̃(Q^m Π^a λ) = Πᵃ Q^m (F λ)`, and `F̃(f^{n,b}_{m,a})` is `F f` conjugated by the isomorphisms
`σ^m ζ^a`. -/
abbrev extend : QPiEnvelope R C ⥤ B := Envelope.extend R (QEnvelope.extend R F)

instance : IsGradedSuperfunctor R (extend R F) := inferInstance

omit [Preadditive C] [Linear R C] [Supercategory R C] [GradedSupercategory R C] [F.Additive]
  [Functor.Linear R F] [IsGradedSuperfunctor R F] in
theorem J_comp_extend : J R C ⋙ extend R F = F := by
  rw [Functor.assoc, Envelope.J_comp_extend, QEnvelope.J_comp_extend]

variable {R F}

variable {G : C ⥤ B} [G.Additive] [G.Linear R] [IsGradedSuperfunctor R G]

variable (R F G) in
/-- The extension of a supernatural transformation homogeneous of parity `p`. -/
def extendNat (p : ZMod 2) (x : ∀ X, F.obj X ⟶ G.obj X) :
    ∀ X : QPiEnvelope R C, (extend R F).obj X ⟶ (extend R G).obj X :=
  Envelope.extendNat R (QEnvelope.extend R F) (QEnvelope.extend R G) p
    (QEnvelope.extendNat R F G x)

omit [F.Additive] [Functor.Linear R F] [IsGradedSuperfunctor R F] [G.Additive]
  [IsGradedSuperfunctor R G] in
omit [GradedSupercategory R C] in
/-- The extension of a supernatural transformation homogeneous of parity `p` and degree `n` is
homogeneous of parity `p` and degree `n`. -/
theorem isGradedSupernatural_extendNat {p : ZMod 2} {n : ℤ} {x : ∀ X, F.obj X ⟶ G.obj X}
    (hx : IsGradedSupernatural R p n x) :
    IsGradedSupernatural R p n (F := extend R F) (G := extend R G) (extendNat R F G p x) :=
  ⟨Envelope.isSupernatural_extendNat
      (QEnvelope.isGradedSupernatural_extendNat hx).toIsSupernatural,
    Envelope.extendNat_mem_degree (QEnvelope.isGradedSupernatural_extendNat hx).mem_degree⟩

omit [F.Additive] [F.Linear R] [IsGradedSuperfunctor R F] [G.Additive] [G.Linear R]
  [IsGradedSuperfunctor R G] in
omit [Preadditive C] [Linear R C] [Supercategory R C] [GradedSupercategory R C] in
@[simp] theorem extendNat_J (p : ZMod 2) (x : ∀ X, F.obj X ⟶ G.obj X) (X : C) :
    extendNat R F G p x ⟨0, ⟨0, X⟩⟩ = x X := by
  simp [extendNat, Envelope.extendNat, QEnvelope.extendNat]

omit [GradedSupercategory R C] in
omit [GradedSupercategory R B] [QPiSupercategory R B] in
/-- **Uniqueness** (the analogue of Lemma 4.2(ii)): supernatural transformations of the same
parity between superfunctors out of `A_{q,π}` agree if they agree on the objects `J λ`. -/
theorem eq_of_restrict_eq [PiSupercategory R B] {H K : QPiEnvelope R C ⥤ B} [H.Additive]
    [H.Linear R] [IsSuperfunctor R H] [K.Additive] [K.Linear R] [IsSuperfunctor R K]
    {p : ZMod 2} {y y' : ∀ X, H.obj X ⟶ K.obj X} (hy : IsSupernatural R p y)
    (hy' : IsSupernatural R p y') (h : ∀ X : C, y ((J R C).obj X) = y' ((J R C).obj X)) :
    y = y' :=
  Envelope.eq_of_restrict_eq hy hy' fun X =>
    congrFun (QEnvelope.eq_of_restrict_eq (H := Envelope.J R _ ⋙ H) (K := Envelope.J R _ ⋙ K)
      (hy.whiskerLeft (Envelope.J R _)) (hy'.whiskerLeft (Envelope.J R _)) h) X

theorem eq_extendNat {p : ZMod 2} {n : ℤ} {x : ∀ X, F.obj X ⟶ G.obj X}
    (hx : IsGradedSupernatural R p n x) {y : ∀ X, (extend R F).obj X ⟶ (extend R G).obj X}
    (hy : IsSupernatural R p (F := extend R F) (G := extend R G) y)
    (h : ∀ X : C, y ((J R C).obj X) = x X) : y = extendNat R F G p x :=
  eq_of_restrict_eq hy (isGradedSupernatural_extendNat hx).toIsSupernatural fun X => by
    rw [h]; exact (extendNat_J p x X).symm

/-- **Theorem 6.9**, full faithfulness: restriction along `J` is a bijection from supernatural
transformations `F̃ ⇒ G̃` homogeneous of parity `p` and degree `n` to those `F ⇒ G`. -/
theorem restrict_bijective (p : ZMod 2) (n : ℤ) :
    Function.Bijective (fun y : {y : ∀ X, (extend R F).obj X ⟶ (extend R G).obj X //
        IsGradedSupernatural R p n (F := extend R F) (G := extend R G) y} =>
      (⟨fun X => y.1 ((J R C).obj X), y.2.whiskerLeft (J R C)⟩ :
        {x : ∀ X, (J R C ⋙ extend R F).obj X ⟶ (J R C ⋙ extend R G).obj X //
          IsGradedSupernatural R p n (F := J R C ⋙ extend R F) (G := J R C ⋙ extend R G) x})) := by
  constructor
  · intro y y' hyy
    exact Subtype.ext (eq_of_restrict_eq y.2.toIsSupernatural y'.2.toIsSupernatural
      fun X => congrFun (congrArg Subtype.val hyy) X)
  · intro x
    have hx : IsGradedSupernatural R p n (F := F) (G := G) x.1 := by
      have h1 := J_comp_extend (R := R) F
      have h2 := J_comp_extend (R := R) G
      exact ⟨⟨fun X => x.2.mem X, fun hf => by
          have := x.2.naturality (map_mem (J R C) hf)
          simpa using this⟩, fun X => x.2.mem_degree X⟩
    exact ⟨⟨extendNat R F G p x.1, isGradedSupernatural_extendNat hx⟩,
      Subtype.ext (funext fun X => extendNat_J p x.1 X)⟩

variable (R F) in
/-- **Theorem 6.9**, functoriality: `1̃ = 1`. -/
theorem extendNat_id :
    extendNat R F F 0 (fun X => 𝟙 (F.obj X)) = fun X => 𝟙 ((extend R F).obj X) :=
  eq_of_restrict_eq (isGradedSupernatural_extendNat isGradedSupernatural_id).toIsSupernatural
    isSupernatural_id fun X => extendNat_J 0 _ X

omit [IsGradedSuperfunctor R G] in
/-- **Theorem 6.9**, functoriality: `(x ≫ y)~ = x̃ ≫ ỹ`. -/
theorem extendNat_comp {H : C ⥤ B} [H.Additive] [H.Linear R] [IsGradedSuperfunctor R H]
    {p q : ZMod 2} {m n : ℤ} {x : ∀ X, F.obj X ⟶ G.obj X} {y : ∀ X, G.obj X ⟶ H.obj X}
    (hx : IsGradedSupernatural R p m x) (hy : IsGradedSupernatural R q n y) :
    extendNat R F H (p + q) (fun X => x X ≫ y X) =
      fun X => extendNat R F G p x X ≫ extendNat R G H q y X :=
  eq_of_restrict_eq (isGradedSupernatural_extendNat (hx.comp hy)).toIsSupernatural
    ((isGradedSupernatural_extendNat hx).toIsSupernatural.comp
      (isGradedSupernatural_extendNat hy).toIsSupernatural) fun X =>
    (extendNat_J (p + q) _ X).trans
      (congrArg₂ (· ≫ ·) (extendNat_J p x X).symm (extendNat_J q y X).symm)

/-- **Theorem 6.9**, even density: every graded superfunctor `H : A_{q,π} ⥤ B` is isomorphic to
the extension of its restriction `J ⋙ H`. -/
def extendRestrictIso (H : QPiEnvelope R C ⥤ B) [H.Additive] [H.Linear R]
    [IsGradedSuperfunctor R H] : extend R (J R C ⋙ H) ≅ H :=
  (Envelope.extendIso (G := QEnvelope.extend R (QEnvelope.J R C ⋙ Envelope.J R _ ⋙ H))
    (G' := Envelope.J R _ ⋙ H) (QEnvelope.extendRestrictIso (R := R) (Envelope.J R _ ⋙ H))
    (QEnvelope.extendRestrictIso_hom_mem (R := R) (Envelope.J R _ ⋙ H)) :
      extend R (J R C ⋙ H) ≅ Envelope.extend R (Envelope.J R _ ⋙ H)) ≪≫
    Envelope.extendRestrictIso H

theorem extendRestrictIso_hom_mem (H : QPiEnvelope R C ⥤ B) [H.Additive] [H.Linear R]
    [IsGradedSuperfunctor R H] (X : QPiEnvelope R C) :
    (extendRestrictIso H).hom.app X ∈ parity (R := R) _ (H.obj X) 0 := by
  have h1 := (Envelope.isSupernatural_extendNat (isSupernatural_of_natTrans
    (QEnvelope.extendRestrictIso (Envelope.J R _ ⋙ H)).hom
    (QEnvelope.extendRestrictIso_hom_mem _))).mem X
  have h2 := Envelope.extendRestrictIso_hom_mem H X
  simpa using comp_mem h1 h2

theorem extendRestrictIso_hom_mem_degree (H : QPiEnvelope R C ⥤ B) [H.Additive] [H.Linear R]
    [IsGradedSuperfunctor R H] (X : QPiEnvelope R C) :
    (extendRestrictIso H).hom.app X ∈ degree (R := R) _ (H.obj X) 0 := by
  have h1 := Envelope.extendNat_mem_degree (p := 0)
    (x := fun X => (QEnvelope.extendRestrictIso (Envelope.J R _ ⋙ H)).hom.app X)
    (QEnvelope.extendRestrictIso_hom_mem_degree _) X
  have h2 : (Envelope.extendRestrictIso H).hom.app X ∈ degree (R := R) _ (H.obj X) 0 := by
    have := comp_mem_degree (Envelope.ζPow_hom_mem_degree (R := R) X.par
      (H.obj ((Envelope.J R _).obj X.obj))) (map_mem_degree H
      (Envelope.shiftIso_hom_mem_degree (R := R) X))
    simpa [Envelope.extendRestrictIso] using this
  simpa using comp_mem_degree h1 h2

end Universal

/-! ### Functoriality: the 2-superfunctor `-_{q,π}` on 1-morphisms -/

section Map

variable {D : Type w₃} [Category.{w₄} D] [Preadditive D] [Linear R D] [Supercategory R D]
  [GradedSupercategory R D]

variable (R) in
/-- `F_{q,π} : A_{q,π} ⥤ B_{q,π}`, `Q^m Π^a λ ↦ Q^m Π^a (F λ)`, `f^{n,b}_{m,a} ↦ (F f)^{n,b}_{m,a}`. -/
abbrev map (F : C ⥤ D) : QPiEnvelope R C ⥤ QPiEnvelope R D :=
  Envelope.map R (QEnvelope.map R F)

instance (F : C ⥤ D) [F.Additive] [F.Linear R] [IsGradedSuperfunctor R F] :
    IsGradedSuperfunctor R (map R F) where
  map_mem_degree hf := map_mem_degree (R := R) F hf

omit [CommRing R] [Preadditive C] [Linear R C] [Supercategory R C] [GradedSupercategory R C]
  [Preadditive D] [Linear R D] [Supercategory R D] [GradedSupercategory R D] in
theorem J_comp_map (F : C ⥤ D) : J R C ⋙ map R F = F ⋙ J R D := rfl

omit [CommRing R] [Preadditive C] [Linear R C] [Supercategory R C] [GradedSupercategory R C] in
theorem map_id : map R (𝟭 C) = 𝟭 (QPiEnvelope R C) := rfl

omit [Preadditive C] [Linear R C] [Supercategory R C] [GradedSupercategory R C] [Preadditive D]
  [Linear R D] [Supercategory R D] [GradedSupercategory R D] in
theorem map_comp {E : Type*} [Category E] [Preadditive E] [Linear R E] [Supercategory R E]
    [GradedSupercategory R E] (F : C ⥤ D) (G : D ⥤ E) :
    map R (F ⋙ G) = map R F ⋙ map R G := rfl

omit [GradedSupercategory R C] [GradedSupercategory R D] in
/-- `F_{q,π}` commutes with `Π` on objects. -/
theorem map_pi_obj (F : C ⥤ D) (X : QPiEnvelope R C) :
    (map R F).obj ((PiSupercategory.pi (R := R)).obj X) =
      (PiSupercategory.pi (R := R)).obj ((map R F).obj X) := rfl

/-- `F_{q,π}` commutes with `Q` on objects. -/
theorem map_Q_obj (F : C ⥤ D) (X : QPiEnvelope R C) :
    (map R F).obj ((QPiSupercategory.Q (R := R)).obj X) =
      (QPiSupercategory.Q (R := R)).obj ((map R F).obj X) := rfl

end Map

end QPiEnvelope

end StringDiagrams

end
