import StringDiagrams.Super.Pi

/-!
# The Π-envelope of a supercategory

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Definition 1.10, Lemmas 4.1–4.2 and Theorem 4.3 (the first half of Theorem 1.9).

The Π-envelope `A_π` of a supercategory `A` (`StringDiagrams.Envelope C`) has objects `Πᵃ λ`
for `λ ∈ A`, `a ∈ ℤ/2`, and morphisms `Hom(Πᵃ λ, Πᵇ μ) := Π^{a+b} Hom_A(λ, μ)`: the morphism
`f_a^b : Πᵃ λ → Πᵇ μ` coming from a homogeneous `f : λ → μ` has parity `|f| + a + b`, and
composition is induced by that of `A` (without signs). It is a Π-supercategory with
`Π(Πᵃ λ) = Π^{a+1} λ` and `ζ_{Πᵃ λ} = (1_λ)_{a+1}^a`.

## Main definitions and statements

* `Envelope C`, with its `Preadditive`, `Linear`, `Supercategory` and `PiSupercategory`
  instances (Definition 1.10).
* `Envelope.J`: the canonical superfunctor `J : A → A_π`, `λ ↦ Π⁰ λ`, `f ↦ f₀⁰`; it is full
  and faithful.
* `Envelope.J_evenlyDense_iff`, `Envelope.superequivalenceJ`,
  `Envelope.piComplete_of_superequivalence` (**Lemma 4.1**): `J` is a superequivalence if and
  only if `A` is Π-complete (every object is the target of an odd isomorphism).
* `Envelope.extend` (**Lemma 4.2(i)**): a superfunctor `F : A → B` into a Π-supercategory
  extends to a superfunctor `F̃ : A_π → B` with `J ⋙ F̃ = F` (`Envelope.J_comp_extend`).
* `Envelope.extendNat` (**Lemma 4.2(ii)**): a supernatural transformation `x : F ⇒ G` of
  parity `p` extends to a supernatural transformation `x̃ : F̃ ⇒ G̃` of parity `p` with
  `x̃ J = x`, given by (4.2); it is unique (`Envelope.eq_of_restrict_eq`,
  `Envelope.eq_extendNat`).
* **Theorem 4.3**: restriction along `J` is a bijection from parity-`p` supernatural
  transformations `F̃ ⇒ G̃` to parity-`p` supernatural transformations `F ⇒ G`
  (`Envelope.restrict_bijective`), the extension `x ↦ x̃` is compatible with identities,
  vertical composition and linear combinations (`extendNat_id`, `extendNat_comp`,
  `extendNat_add`, `extendNat_smul`), and every superfunctor `H : A_π → B` is isomorphic to
  `(J ⋙ H)~` via an even supernatural isomorphism (`Envelope.extendRestrictIso`, even density).
* `Envelope.map`: the extension `F_π : A_π → B_π` of a superfunctor (Definition 1.10).

## Scope

The statement of Theorem 4.3 is about the supercategories `Hom(A, νB)` and `Hom(A_π, B)` of
superfunctors and supernatural transformations. These Hom-supercategories are not constructed
here; instead their content is stated directly: on objects (`extend`, `J_comp_extend`,
`extendRestrictIso`), on morphisms of each parity (`restrict_bijective`), and for the
compositional structure (`extendNat_comp`, `extendNat_id`, linearity). The 2-adjunction
formulation (`-π` left 2-adjoint to the forgetful 2-superfunctor `ν`) is not packaged.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory

universe w w₁ w₂ w₃ w₄

/-- The objects `Πᵃ λ` of the Π-envelope of `C` (Brundan–Ellis, Definition 1.10). -/
@[ext]
structure Envelope (C : Type w₁) where
  /-- The parity shift `a`. -/
  par : ZMod 2
  /-- The underlying object `λ`. -/
  obj : C

namespace Envelope

variable {R : Type w} [CommRing R] {C : Type w₁} [Category.{w₂} C]

instance : Category (Envelope C) where
  Hom X Y := X.obj ⟶ Y.obj
  id X := 𝟙 X.obj
  comp {X Y Z} (f : X.obj ⟶ Y.obj) (g : Y.obj ⟶ Z.obj) := f ≫ g
  id_comp {X Y} (f : X.obj ⟶ Y.obj) := Category.id_comp f
  comp_id {X Y} (f : X.obj ⟶ Y.obj) := Category.comp_id f
  assoc {W X _ _} (f : W.obj ⟶ X.obj) g h := Category.assoc f g h

/-- The morphism of `C` underlying a morphism of the envelope. -/
def toHom {X Y : Envelope C} (f : X ⟶ Y) : X.obj ⟶ Y.obj := f

/-- The morphism `f_a^b : Πᵃ λ ⟶ Πᵇ μ` of the envelope given by `f : λ ⟶ μ`. -/
def ofHom {X Y : Envelope C} (f : X.obj ⟶ Y.obj) : X ⟶ Y := f

@[simp] theorem toHom_ofHom {X Y : Envelope C} (f : X.obj ⟶ Y.obj) : toHom (ofHom f) = f := rfl

@[simp] theorem ofHom_toHom {X Y : Envelope C} (f : X ⟶ Y) : ofHom (toHom f) = f := rfl

@[ext] theorem hom_ext {X Y : Envelope C} {f g : X ⟶ Y} (h : toHom f = toHom g) : f = g := h

@[simp] theorem toHom_id (X : Envelope C) : toHom (𝟙 X) = 𝟙 X.obj := rfl

@[simp] theorem toHom_comp {X Y Z : Envelope C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    toHom (f ≫ g) = toHom f ≫ toHom g := rfl

/-- An isomorphism of the envelope gives an isomorphism of underlying objects. -/
@[simps]
def isoToIso {X Y : Envelope C} (e : X ≅ Y) : X.obj ≅ Y.obj where
  hom := toHom e.hom
  inv := toHom e.inv
  hom_inv_id := e.hom_inv_id
  inv_hom_id := e.inv_hom_id

/-- An isomorphism of underlying objects gives an isomorphism of the envelope. -/
@[simps]
def isoOfIso {X Y : Envelope C} (e : X.obj ≅ Y.obj) : X ≅ Y where
  hom := ofHom e.hom
  inv := ofHom e.inv
  hom_inv_id := e.hom_inv_id
  inv_hom_id := e.inv_hom_id

section Linear

variable [Preadditive C]

instance : Preadditive (Envelope C) where
  homGroup X Y := inferInstanceAs (AddCommGroup (X.obj ⟶ Y.obj))
  add_comp _ _ _ f f' g := Preadditive.add_comp (C := C) _ _ _ f f' g
  comp_add _ _ _ f g g' := Preadditive.comp_add (C := C) _ _ _ f g g'

@[simp] theorem toHom_add {X Y : Envelope C} (f g : X ⟶ Y) : toHom (f + g) = toHom f + toHom g :=
  rfl

@[simp] theorem toHom_zero {X Y : Envelope C} : toHom (0 : X ⟶ Y) = 0 := rfl

@[simp] theorem toHom_neg {X Y : Envelope C} (f : X ⟶ Y) : toHom (-f) = -toHom f := rfl

variable [Linear R C]

instance : Linear R (Envelope C) where
  homModule X Y := inferInstanceAs (Module R (X.obj ⟶ Y.obj))
  smul_comp _ _ _ r f g := Linear.smul_comp (C := C) _ _ _ r f g
  comp_smul _ _ _ f r g := Linear.comp_smul (C := C) _ _ _ f r g

@[simp] theorem toHom_smul {X Y : Envelope C} (r : R) (f : X ⟶ Y) : toHom (r • f) = r • toHom f :=
  rfl

/-! ## The supercategory structure -/

variable [Supercategory R C]

theorem isInternal_shift (X Y : C) (s : ZMod 2) :
    DirectSum.IsInternal fun p => parity (R := R) X Y (p + s) := by
  have h := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).1
    (isInternal (R := R) X Y)
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  exact ⟨h.1.comp (add_left_injective s), by
    rw [← h.2]; exact (Equiv.addRight s).iSup_comp (g := fun p => parity (R := R) X Y p)⟩

/-- The Π-envelope is a supercategory: `f_a^b` has parity `|f| + a + b`. -/
instance : Supercategory R (Envelope C) where
  parity X Y p := parity (R := R) X.obj Y.obj (p + (X.par + Y.par))
  isInternal X Y := isInternal_shift (R := R) X.obj Y.obj (X.par + Y.par)
  id_mem X := by
    show 𝟙 X.obj ∈ parity (R := R) X.obj X.obj (0 + (X.par + X.par))
    rw [zmod2_add_self, add_zero]
    exact id_mem X.obj
  comp_mem {X Y Z p q f g} hf hg := by
    have := comp_mem hf hg
    rw [show p + (X.par + Y.par) + (q + (Y.par + Z.par)) = p + q + (X.par + Z.par) + (Y.par + Y.par)
      by ring, zmod2_add_self, add_zero] at this
    exact this

theorem mem_parity_iff {X Y : Envelope C} {f : X ⟶ Y} {p : ZMod 2} :
    f ∈ parity (R := R) X Y p ↔ toHom f ∈ parity (R := R) X.obj Y.obj (p + (X.par + Y.par)) :=
  Iff.rfl

theorem ofHom_mem {X Y : Envelope C} {f : X.obj ⟶ Y.obj} {q : ZMod 2}
    (hf : f ∈ parity (R := R) X.obj Y.obj q) :
    ofHom f ∈ parity (R := R) X Y (q + (X.par + Y.par)) := by
  rw [mem_parity_iff, toHom_ofHom, add_assoc, zmod2_add_self, add_zero]
  exact hf

/-- The parity components in the envelope are shifted components in `C`. -/
theorem toHom_proj (p : ZMod 2) {X Y : Envelope C} (f : X ⟶ Y) :
    toHom (proj R p f) = proj R (p + (X.par + Y.par)) (toHom f) := by
  set s := X.par + Y.par
  let g : X ⟶ Y := ofHom (proj R (p + s) (toHom f))
  let h : X ⟶ Y := ofHom (proj R (p + s + 1) (toHom f))
  have e : f = g + h := (proj_add_proj_add_one (R := R) (p + s) (toHom f)).symm
  have hg : g ∈ parity (R := R) X Y p := proj_mem (R := R) (p + s) (toHom f)
  have hh : h ∈ parity (R := R) X Y (p + 1) := by
    show proj R (p + s + 1) (toHom f) ∈ parity (R := R) X.obj Y.obj (p + 1 + s)
    rw [add_right_comm]; exact proj_mem _ _
  rw [proj_eq_of_add e hg hh]
  rfl

/-- The twist in the envelope: `f_a^b ↦ (-1)^{p(a+b)} (f')_a^b` where `f'` is the twist in
`C`. -/
theorem toHom_twist (p : ZMod 2) {X Y : Envelope C} (f : X ⟶ Y) :
    toHom (twist R p f) = sign R (p * (X.par + Y.par)) • twist R p (toHom f) := by
  rw [twist_apply, twist_apply, toHom_add, toHom_smul, toHom_proj, toHom_proj]
  rcases zmod2_cases (X.par + Y.par) with h | h <;> rw [h]
  · simp
  · rw [show (0 : ZMod 2) + 1 = 1 from rfl, show (1 : ZMod 2) + 1 = 0 from rfl, mul_one,
      smul_add, sign_smul_sign_smul, add_comm]

/-! ## The Π-supercategory structure -/

/-- The odd isomorphism `ζ_{Πᵃ λ} = (1_λ)_{a+1}^a : Π^{a+1} λ ≅ Πᵃ λ`. -/
def ζIso (X : Envelope C) : (⟨X.par + 1, X.obj⟩ : Envelope C) ≅ X :=
  isoOfIso (Iso.refl X.obj)

theorem ζIso_mem (X : Envelope C) :
    (ζIso X).hom ∈ parity (R := R) (⟨X.par + 1, X.obj⟩ : Envelope C) X 1 := by
  rw [mem_parity_iff]
  show 𝟙 X.obj ∈ parity (R := R) X.obj X.obj (1 + (X.par + 1 + X.par))
  rw [show (1 : ZMod 2) + (X.par + 1 + X.par) = (1 + 1) + (X.par + X.par) by ring,
    zmod2_add_self, zmod2_add_self, add_zero]
  exact id_mem X.obj

/-- The Π-envelope is a Π-supercategory: `Π(Πᵃ λ) = Π^{a+1} λ`, `ζ = (1_λ)_{a+1}^a`
(Brundan–Ellis, Definition 1.10). -/
instance : PiSupercategory R (Envelope C) :=
  PiSupercategory.ofIso (fun X => ⟨X.par + 1, X.obj⟩) ζIso ζIso_mem

@[simp] theorem pi_obj (X : Envelope C) :
    (PiSupercategory.pi (R := R)).obj X = ⟨X.par + 1, X.obj⟩ := rfl

theorem ζ_eq (X : Envelope C) : PiSupercategory.ζ (R := R) X = ζIso X := rfl

@[simp] theorem toHom_ζ_hom (X : Envelope C) :
    toHom (PiSupercategory.ζ (R := R) X).hom = 𝟙 X.obj := rfl

@[simp] theorem toHom_ζ_inv (X : Envelope C) :
    toHom (PiSupercategory.ζ (R := R) X).inv = 𝟙 X.obj := rfl

/-- The action of `Π` on morphisms of the envelope: `Π(f_a^b) = (-1)^{a+b} (f₀ - f₁)_{a+1}^{b+1}`. -/
theorem toHom_pi_map {X Y : Envelope C} (f : X ⟶ Y) :
    toHom ((PiSupercategory.pi (R := R)).map f) =
      sign R (X.par + Y.par) • twist R 1 (toHom f) := by
  show toHom (ζIso X).hom ≫ toHom (twist R 1 f) ≫ toHom (ζIso Y).inv = _
  rw [toHom_twist, one_mul]
  simp [ζIso]

/-! ## The canonical superfunctor `J` -/

variable (C) in
/-- The canonical superfunctor `J : A ⥤ A_π`, `λ ↦ Π⁰ λ`, `f ↦ f₀⁰`. -/
@[simps]
def J : C ⥤ Envelope C where
  obj X := ⟨0, X⟩
  map f := ofHom f
  map_id _ := rfl
  map_comp _ _ := rfl

instance : (J C).Additive where
  map_add := rfl

instance : (J C).Linear R where
  map_smul _ _ := rfl

instance : PreservesParity R (J C) where
  map_mem {X Y p f} hf := by
    rw [mem_parity_iff]
    simpa using hf

instance : (J C).Full where
  map_surjective f := ⟨toHom f, rfl⟩

instance : (J C).Faithful where
  map_injective h := h

/-- The morphism `(1_λ)_0^a : Π⁰ λ ⟶ Πᵃ λ`, of parity `a`. -/
def shiftIso (X : Envelope C) : (J C).obj X.obj ≅ X := isoOfIso (Iso.refl X.obj)

theorem shiftIso_hom_mem (X : Envelope C) :
    (shiftIso X).hom ∈ parity (R := R) ((J C).obj X.obj) X X.par := by
  rw [mem_parity_iff]
  show 𝟙 X.obj ∈ parity (R := R) X.obj X.obj (X.par + (0 + X.par))
  rw [zero_add, zmod2_add_self]; exact id_mem X.obj

theorem shiftIso_inv_mem (X : Envelope C) :
    (shiftIso X).inv ∈ parity (R := R) X ((J C).obj X.obj) X.par :=
  inv_mem _ (shiftIso_hom_mem X)

/-! ## Lemma 4.1 -/

variable (R C) in
/-- A supercategory is Π-complete if every object is the target of an odd isomorphism
(Brundan–Ellis, Lemma 4.1). -/
def PiComplete : Prop := ∀ X : C, ∃ (Y : C) (e : Y ≅ X), e.hom ∈ parity (R := R) Y X 1

/-- A Π-supercategory is Π-complete. -/
theorem piComplete_of_piSupercategory [PiSupercategory R C] : PiComplete R C :=
  fun X => ⟨_, PiSupercategory.ζ (R := R) X, PiSupercategory.ζ_hom_mem X⟩

/-- A Π-complete supercategory admits a Π-supercategory structure (by choosing, for each
object, an odd isomorphism onto it). -/
def PiComplete.piSupercategory (h : PiComplete R C) : PiSupercategory R C :=
  PiSupercategory.ofIso (fun X => (h X).choose) (fun X => (h X).choose_spec.choose)
    (fun X => (h X).choose_spec.choose_spec)

/-- **Lemma 4.1**, even density: `J` is evenly dense if and only if `A` is Π-complete. -/
theorem J_evenlyDense_iff : EvenlyDense R (J C) ↔ PiComplete R C := by
  constructor
  · intro h X
    obtain ⟨Y, e, he⟩ := h ⟨1, X⟩
    refine ⟨Y, isoToIso e, ?_⟩
    rw [mem_parity_iff] at he
    simpa using he
  · intro h X
    obtain ⟨a, X⟩ := X
    rcases zmod2_cases a with rfl | rfl
    · exact ⟨X, Iso.refl _, id_mem _⟩
    · obtain ⟨Y, e, he⟩ := h X
      refine ⟨Y, isoOfIso e, ?_⟩
      rw [mem_parity_iff]
      simpa using he

/-- **Lemma 4.1** ("if"): if `A` is Π-complete then `J : A → A_π` is a superequivalence. -/
def superequivalenceJ (h : PiComplete R C) : Superequivalence R (J C) :=
  Superequivalence.ofFullyFaithful (J C) (J_evenlyDense_iff.2 h)

/-- **Lemma 4.1** ("only if"): if `J : A → A_π` is a superequivalence then `A` is
Π-complete. -/
theorem piComplete_of_superequivalence (e : Superequivalence R (J C)) : PiComplete R C :=
  J_evenlyDense_iff.1 e.evenlyDense

/-! ## Lemma 4.2: the universal property -/

section Universal

variable {B : Type w₃} [Category.{w₄} B] [Preadditive B] [Linear R B] [Supercategory R B]
  [PiSupercategory R B]

variable (R) in
/-- `Πᵃ X` in a Π-supercategory: `X` if `a = 0`, `Π X` if `a = 1`. -/
def piPow : ZMod 2 → B → B
  | ⟨0, _⟩, X => X
  | ⟨1, _⟩, X => (PiSupercategory.pi (R := R)).obj X
  | ⟨_ + 2, h⟩, _ => absurd h (by simp)

variable (R) in
/-- The isomorphism `ζᵃ_X : Πᵃ X ≅ X`: the identity if `a = 0`, `ζ_X` if `a = 1`. -/
def ζPow : ∀ (a : ZMod 2) (X : B), piPow R a X ≅ X
  | ⟨0, _⟩, X => Iso.refl X
  | ⟨1, _⟩, X => PiSupercategory.ζ (R := R) X
  | ⟨_ + 2, h⟩, _ => absurd h (by simp)

@[simp] theorem piPow_zero (X : B) : piPow R 0 X = X := rfl

@[simp] theorem piPow_one (X : B) : piPow R 1 X = (PiSupercategory.pi (R := R)).obj X := rfl

@[simp] theorem ζPow_zero (X : B) : ζPow R 0 X = Iso.refl X := rfl

@[simp] theorem ζPow_one (X : B) : ζPow R 1 X = PiSupercategory.ζ (R := R) X := rfl

theorem ζPow_hom_mem (a : ZMod 2) (X : B) :
    (ζPow R a X).hom ∈ parity (R := R) (piPow R a X) X a := by
  rcases zmod2_cases a with rfl | rfl
  · exact id_mem X
  · exact PiSupercategory.ζ_hom_mem X

theorem ζPow_inv_mem (a : ZMod 2) (X : B) :
    (ζPow R a X).inv ∈ parity (R := R) X (piPow R a X) a :=
  inv_mem _ (ζPow_hom_mem a X)

variable (R) (F : C ⥤ B) [F.Additive] [F.Linear R] [PreservesParity R F]

/-- **Lemma 4.2(i).** The extension `F̃ : A_π ⥤ B` of a superfunctor `F : A ⥤ B` to the
Π-envelope: `F̃(Πᵃ λ) = Πᵃ(F λ)`, `F̃(f_a^b) = (ζᵇ_{F μ})⁻¹ ∘ F f ∘ ζᵃ_{F λ}`. -/
@[simps]
def extend : Envelope C ⥤ B where
  obj X := piPow R X.par (F.obj X.obj)
  map {X Y} f := (ζPow R X.par (F.obj X.obj)).hom ≫ F.map (toHom f) ≫
    (ζPow R Y.par (F.obj Y.obj)).inv
  map_id X := by simp
  map_comp f g := by simp

instance : (extend R F).Additive where
  map_add := by simp [Preadditive.add_comp, Preadditive.comp_add]

instance : (extend R F).Linear R where
  map_smul _ _ := by simp

instance : PreservesParity R (extend R F) where
  map_mem {X Y p f} hf := by
    have := comp_mem (comp_mem (ζPow_hom_mem X.par (F.obj X.obj)) (map_mem F hf))
      (ζPow_inv_mem Y.par (F.obj Y.obj))
    rw [show X.par + (p + (X.par + Y.par)) + Y.par = p + (X.par + X.par) + (Y.par + Y.par) by
      ring, zmod2_add_self, zmod2_add_self, add_zero, add_zero] at this
    simpa using this

omit [Preadditive C] [Linear R C] [Supercategory R C] [F.Additive] [F.Linear R]
  [PreservesParity R F] in
/-- **Lemma 4.2(i).** `F = F̃ J`. -/
theorem J_comp_extend : J C ⋙ extend R F = F :=
  CategoryTheory.Functor.ext (fun _ => rfl) (fun X Y f => by simp)

variable {R F}

variable {G : C ⥤ B} [G.Additive] [G.Linear R] [PreservesParity R G]

variable (R F G) in
/-- **Lemma 4.2(ii)**, formula (4.2): the extension
`x̃_{Πᵃ λ} = (-1)^{a|x|} (ζᵃ_{G λ})⁻¹ ∘ x_λ ∘ ζᵃ_{F λ}` of a family `x` of parity `p`. -/
def extendNat (p : ZMod 2) (x : ∀ X, F.obj X ⟶ G.obj X) (X : Envelope C) :
    (extend R F).obj X ⟶ (extend R G).obj X :=
  sign R (X.par * p) • ((ζPow R X.par (F.obj X.obj)).hom ≫ x X.obj ≫
    (ζPow R X.par (G.obj X.obj)).inv)

omit [F.Additive] [F.Linear R] [PreservesParity R F] [G.Additive] [G.Linear R]
  [PreservesParity R G] in
/-- **Lemma 4.2(ii).** `x̃` is a supernatural transformation of the same parity. -/
theorem isSupernatural_extendNat {p : ZMod 2} {x : ∀ X, F.obj X ⟶ G.obj X}
    (hx : IsSupernatural R p x) :
    IsSupernatural R p (F := extend R F) (G := extend R G) (extendNat R F G p x) where
  mem X := by
    have := comp_mem (comp_mem (ζPow_hom_mem X.par (F.obj X.obj)) (hx.mem X.obj))
      (ζPow_inv_mem X.par (G.obj X.obj))
    rw [show X.par + p + X.par = p by
      rw [add_right_comm, zmod2_add_self, zero_add], Category.assoc] at this
    exact Submodule.smul_mem _ _ this
  naturality {X Y q f} hf := by
    rw [mem_parity_iff] at hf
    simp only [extend_obj, extend_map, extendNat, Linear.comp_smul, Linear.smul_comp,
      Category.assoc, Iso.inv_hom_id_assoc, smul_smul]
    rw [reassoc_of% (hx.naturality hf), Linear.smul_comp, Linear.comp_smul, smul_smul,
      ← sign_add, ← sign_add]
    rw [show Y.par * p + p * (q + (X.par + Y.par)) = p * q + X.par * p + (Y.par * p + Y.par * p)
      by ring, zmod2_add_self, add_zero]
    simp only [Category.assoc]

omit [Preadditive C] [Linear R C] [Supercategory R C] [F.Additive] [F.Linear R]
  [PreservesParity R F] [G.Additive] [G.Linear R] [PreservesParity R G] in
/-- **Lemma 4.2(ii).** `x̃ J = x`. -/
@[simp] theorem extendNat_zero_par (p : ZMod 2) (x : ∀ X, F.obj X ⟶ G.obj X) (X : C) :
    extendNat R F G p x ((J C).obj X) = x X := by
  simp [extendNat]

omit [PiSupercategory R B] in
/-- **Uniqueness in Lemma 4.2(ii).** Supernatural transformations of the same parity between
superfunctors out of the Π-envelope agree if they agree on the objects `Π⁰ λ`. -/
theorem eq_of_restrict_eq {H K : Envelope C ⥤ B} [H.Additive] [H.Linear R] [PreservesParity R H]
    [K.Additive] [K.Linear R] [PreservesParity R K] {p : ZMod 2}
    {y y' : ∀ X, H.obj X ⟶ K.obj X} (hy : IsSupernatural R p y) (hy' : IsSupernatural R p y')
    (h : ∀ X : C, y ((J C).obj X) = y' ((J C).obj X)) : y = y' := by
  funext X
  obtain ⟨a, X⟩ := X
  rcases zmod2_cases a with rfl | rfl
  · exact h X
  · have hu := ζIso_mem (R := R) (⟨0, X⟩ : Envelope C)
    have e1 := hy.naturality hu
    have e2 := hy'.naturality hu
    have h0 : y ⟨0, X⟩ = y' ⟨0, X⟩ := h X
    change H.map _ ≫ y ⟨0, X⟩ = sign R (p * 1) • (y ⟨1, X⟩ ≫ K.map _) at e1
    change H.map _ ≫ y' ⟨0, X⟩ = sign R (p * 1) • (y' ⟨1, X⟩ ≫ K.map _) at e2
    rw [h0, e2] at e1
    have e3 := congrArg (fun t => sign R (p * 1) • t) e1
    simp only [sign_smul_sign_smul] at e3
    exact ((cancel_mono _).1 e3).symm

/-- **Lemma 4.2(ii).** `x̃` is the unique supernatural transformation `F̃ ⇒ G̃` of parity `p`
restricting to `x`. -/
theorem eq_extendNat {p : ZMod 2} {x : ∀ X, F.obj X ⟶ G.obj X} (hx : IsSupernatural R p x)
    {y : ∀ X, (extend R F).obj X ⟶ (extend R G).obj X}
    (hy : IsSupernatural R p (F := extend R F) (G := extend R G) y)
    (h : ∀ X : C, y ((J C).obj X) = x X) : y = extendNat R F G p x :=
  eq_of_restrict_eq hy (isSupernatural_extendNat hx) fun X => by rw [h, extendNat_zero_par]

/-- **Theorem 4.3**, full faithfulness: restriction along `J` is a bijection from parity-`p`
supernatural transformations `F̃ ⇒ G̃` to parity-`p` supernatural transformations `F ⇒ G`. -/
theorem restrict_bijective (p : ZMod 2) :
    Function.Bijective (fun y : {y : ∀ X, (extend R F).obj X ⟶ (extend R G).obj X //
        IsSupernatural R p (F := extend R F) (G := extend R G) y} =>
      (⟨fun X => y.1 ((J C).obj X), ⟨fun X => y.2.mem ((J C).obj X), fun {X Y q f} hf => by
        simpa using y.2.naturality (map_mem (J C) hf)⟩⟩ :
        {x : ∀ X, F.obj X ⟶ G.obj X // IsSupernatural R p x})) := by
  constructor
  · intro y y' hyy
    exact Subtype.ext (eq_of_restrict_eq y.2 y'.2 fun X => congrFun (congrArg Subtype.val hyy) X)
  · intro x
    exact ⟨⟨extendNat R F G p x.1, isSupernatural_extendNat x.2⟩,
      Subtype.ext (funext fun X => extendNat_zero_par p x.1 X)⟩

variable (R F) in
/-- **Theorem 4.3**, functoriality: `1̃ = 1`. -/
theorem extendNat_id :
    extendNat R F F 0 (fun X => 𝟙 (F.obj X)) = fun X => 𝟙 ((extend R F).obj X) :=
  (eq_of_restrict_eq (isSupernatural_extendNat isSupernatural_id) isSupernatural_id
    fun X => by simp).trans rfl

omit [PreservesParity R G] in
/-- **Theorem 4.3**, functoriality: `(x ≫ y)~ = x̃ ≫ ỹ`. -/
theorem extendNat_comp {H : C ⥤ B} [H.Additive] [H.Linear R] [PreservesParity R H]
    {p q : ZMod 2} {x : ∀ X, F.obj X ⟶ G.obj X} {y : ∀ X, G.obj X ⟶ H.obj X}
    (hx : IsSupernatural R p x) (hy : IsSupernatural R q y) :
    extendNat R F H (p + q) (fun X => x X ≫ y X) =
      fun X => extendNat R F G p x X ≫ extendNat R G H q y X :=
  (eq_of_restrict_eq (isSupernatural_extendNat (hx.comp hy))
    ((isSupernatural_extendNat hx).comp (isSupernatural_extendNat hy))
    fun X => by simp).trans rfl

omit [Preadditive C] [Linear R C] [Supercategory R C] [F.Additive] [F.Linear R]
  [PreservesParity R F] [G.Additive] [G.Linear R] [PreservesParity R G] in
theorem extendNat_add {p : ZMod 2} (x y : ∀ X, F.obj X ⟶ G.obj X) :
    extendNat R F G p (x + y) = extendNat R F G p x + extendNat R F G p y := by
  funext X; simp [extendNat, Preadditive.add_comp, Preadditive.comp_add, smul_add]

omit [Preadditive C] [Linear R C] [Supercategory R C] [F.Additive] [F.Linear R]
  [PreservesParity R F] [G.Additive] [G.Linear R] [PreservesParity R G] in
theorem extendNat_smul {p : ZMod 2} (r : R) (x : ∀ X, F.obj X ⟶ G.obj X) :
    extendNat R F G p (r • x) = r • extendNat R F G p x := by
  funext X; simp [extendNat, smul_comm r]

/-- **Theorem 4.3**, even density: every superfunctor `H : A_π ⥤ B` is isomorphic to the
extension of its restriction `J ⋙ H`, via the even isomorphisms
`ζᵃ ≫ H((1_λ)_0^a) : Πᵃ(H Π⁰ λ) ≅ H(Πᵃ λ)`. -/
def extendRestrictIso (H : Envelope C ⥤ B) [H.Additive] [H.Linear R] [PreservesParity R H] :
    extend R (J C ⋙ H) ≅ H :=
  NatIso.ofComponents (fun X => ζPow R X.par (H.obj ((J C).obj X.obj)) ≪≫ H.mapIso (shiftIso X))
    (fun {X Y} f => by
      simp only [extend_obj, Functor.comp_obj, extend_map, Functor.comp_map, Iso.trans_hom,
        Functor.mapIso_hom, Category.assoc, Iso.inv_hom_id_assoc]
      rw [← H.map_comp, ← H.map_comp]
      congr 2
      exact hom_ext (by simp [shiftIso]))

theorem extendRestrictIso_hom_mem (H : Envelope C ⥤ B) [H.Additive] [H.Linear R]
    [PreservesParity R H] (X : Envelope C) :
    (extendRestrictIso H).hom.app X ∈
      parity (R := R) ((extend R (J C ⋙ H)).obj X) (H.obj X) 0 := by
  have := comp_mem (ζPow_hom_mem X.par (H.obj ((J C).obj X.obj)))
    (map_mem H (shiftIso_hom_mem (R := R) X))
  rw [zmod2_add_self] at this
  exact this

end Universal

/-! ## Functoriality of the envelope -/

section Map

variable {D : Type w₃} [Category.{w₄} D] [Preadditive D] [Linear R D] [Supercategory R D]

/-- The extension `F_π : A_π ⥤ B_π` of a functor, `Πᵃ λ ↦ Πᵃ(F λ)`, `f_a^b ↦ (F f)_a^b`
(Brundan–Ellis, Definition 1.10). -/
@[simps]
def map (F : C ⥤ D) : Envelope C ⥤ Envelope D where
  obj X := ⟨X.par, F.obj X.obj⟩
  map f := ofHom (F.map (toHom f))
  map_id X := F.map_id X.obj
  map_comp f g := F.map_comp (toHom f) (toHom g)

instance (F : C ⥤ D) [F.Additive] : (map F).Additive where
  map_add := F.map_add

instance (F : C ⥤ D) [F.Additive] [F.Linear R] : (map F).Linear R where
  map_smul f r := Functor.Linear.map_smul (F := F) (toHom f) r

instance (F : C ⥤ D) [PreservesParity R F] : PreservesParity R (map F) where
  map_mem hf := map_mem (R := R) F hf

omit [Preadditive C] [Preadditive D] in
theorem J_comp_map (F : C ⥤ D) : J C ⋙ map F = F ⋙ J D := rfl

omit [Preadditive C] in
theorem map_id : map (𝟭 C) = 𝟭 (Envelope C) := rfl

omit [Preadditive C] [Preadditive D] in
theorem map_comp {E : Type*} [Category E] (F : C ⥤ D) (G : D ⥤ E) :
    map (F ⋙ G) = map F ⋙ map G := rfl

/-- `F_π` commutes with `Π` on the nose. -/
theorem map_pi_obj (F : C ⥤ D) (X : Envelope C) :
    (map F).obj ((PiSupercategory.pi (R := R)).obj X) =
      (PiSupercategory.pi (R := R)).obj ((map F).obj X) := rfl

end Map

end Linear

end Envelope

end StringDiagrams

end
