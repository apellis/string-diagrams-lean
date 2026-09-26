import StringDiagrams.Super.Supernatural

/-!
# Π-supercategories

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Definition 1.7, Lemma 3.2 and Corollary 3.3.

A Π-supercategory `(A, Π, ζ)` is a supercategory `A` with a superfunctor `Π : A → A` and an odd
supernatural isomorphism `ζ : Π ⇒ 𝟭` (`StringDiagrams.PiSupercategory`).

## Main definitions and statements

* `PiSupercategory.ofIso`: the remark after Definition 1.7 — it suffices to give objects `Π X`
  and odd isomorphisms `ζ_X : Π X ≅ X`; the action of `Π` on morphisms is then forced
  (`PiSupercategory.pi_map_eq`: `Π f = ζ_X⁻¹ ∘ f' ∘ ζ_Y` in the notation below, where
  `f' = f₀ - f₁`).
* `PiSupercategory.ξ`: the even isomorphism `ξ := ζζ : Π² ≅ 𝟭`, with the two formulas of
  (1.4) (`ξ_hom`, `ξ_hom_eq_neg`), its naturality, and `ξ Π = Π ξ` (`ξ_pi`,
  Corollary 3.3(i)); also `Π ζ = -ζ Π` (`pi_map_ζ`, Lemma 3.2(iii)).
* `PiSupercategory.β F`: for a superfunctor `F` between Π-supercategories, the even
  isomorphism `β_F := -ζ_B F ζ_A⁻¹ : Π F ≅ F Π` (Corollary 3.3(ii)); its components are
  `ζ_{F X} ≫ F(ζ_X⁻¹)` (the minus sign is absorbed by the super interchange law, see the
  docstring of `β`). We prove that `β_F` is natural and even (Corollary 3.3(ii)), satisfies
  `ξ F ξ⁻¹ = β_F Π ∘ Π β_F` (`β_comm`, Corollary 3.3(ii)), is compatible with supernatural
  transformations of either parity (`β_naturality_supernatural`, Corollary 3.3(iii)), and
  satisfies `β_{GF} = G β_F ∘ β_G F`, `β_𝟭 = 1`, `β_Π = -1` (Corollary 3.3(iv)).

Compositions are written in diagrammatic order `f ≫ g` (`= g ∘ f`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory

universe w w₁ w₂ w₃ w₄ w₅ w₆

variable (R : Type w) [CommRing R]

/-- A Π-supercategory (Brundan–Ellis, Definition 1.7): a supercategory with a superfunctor
`pi : C ⥤ C` and an odd supernatural isomorphism `ζ : Π ⇒ 𝟭`. -/
class PiSupercategory (C : Type w₁) [Category.{w₂} C] [Preadditive C] [Linear R C]
    [Supercategory R C] where
  /-- The parity-switching superfunctor `Π`. -/
  pi : C ⥤ C
  [pi_additive : pi.Additive]
  [pi_linear : pi.Linear R]
  [pi_isSuperfunctor : IsSuperfunctor R pi]
  /-- The odd isomorphisms `ζ_X : Π X ≅ X`. -/
  ζ : ∀ X : C, pi.obj X ≅ X
  ζ_isSupernatural : IsSupernatural R 1 (F := pi) (G := 𝟭 C) fun X => (ζ X).hom

attribute [instance] PiSupercategory.pi_additive PiSupercategory.pi_linear
  PiSupercategory.pi_isSuperfunctor

namespace PiSupercategory

variable {R} {C : Type w₁} [Category.{w₂} C] [Preadditive C] [Linear R C] [Supercategory R C]

/-! ## Construction from odd isomorphisms -/

section OfIso

variable (obj : C → C) (e : ∀ X, obj X ≅ X)

/-- The parity-switching functor determined by odd isomorphisms `e X : obj X ≅ X`:
`f ↦ e_X ≫ (f₀ - f₁) ≫ e_Y⁻¹`. -/
@[simps]
def ofIsoFunctor : C ⥤ C where
  obj := obj
  map {X Y} f := (e X).hom ≫ twist R 1 f ≫ (e Y).inv
  map_id X := by simp
  map_comp f g := by simp [twist_comp]

instance : (ofIsoFunctor (R := R) obj e).Additive where
  map_add := by simp [Preadditive.add_comp, Preadditive.comp_add]

instance : (ofIsoFunctor (R := R) obj e).Linear R where
  map_smul _ _ := by simp

theorem ofIsoFunctor_preservesParity (he : ∀ X, (e X).hom ∈ parity (R := R) (obj X) X 1) :
    IsSuperfunctor R (ofIsoFunctor (R := R) obj e) where
  map_mem {X Y p f} hf := by
    have := comp_mem (comp_mem (he X) (twist_mem 1 hf)) (inv_mem _ (he Y))
    rw [show (1 : ZMod 2) + p + 1 = p by rcases parity_eq_zero_or_one p with rfl | rfl <;> rfl,
      Category.assoc] at this
    exact this

/-- **Brundan–Ellis, remark after Definition 1.7.** A Π-supercategory structure is determined
by objects `obj X` and odd isomorphisms `e X : obj X ≅ X`. -/
def ofIso (he : ∀ X, (e X).hom ∈ parity (R := R) (obj X) X 1) : PiSupercategory R C where
  pi := ofIsoFunctor (R := R) obj e
  pi_isSuperfunctor := ofIsoFunctor_preservesParity obj e he
  ζ := e
  ζ_isSupernatural := IsSupernatural.of_twist he fun f => by simp

end OfIso

variable [PiSupercategory R C]

/-! ## Basic properties -/

theorem ζ_hom_mem (X : C) :
    (ζ (R := R) X).hom ∈ parity (R := R) ((pi (R := R)).obj X) X 1 :=
  (ζ_isSupernatural (R := R)).mem X

theorem ζ_inv_mem (X : C) :
    (ζ (R := R) X).inv ∈ parity (R := R) X ((pi (R := R)).obj X) 1 :=
  inv_mem _ (ζ_hom_mem X)

/-- Supernaturality of `ζ`: `ζ_Y ∘ Π f = (f₀ - f₁) ∘ ζ_X`. -/
@[reassoc]
theorem ζ_naturality {X Y : C} (f : X ⟶ Y) :
    (pi (R := R)).map f ≫ (ζ (R := R) Y).hom = (ζ (R := R) X).hom ≫ twist R 1 f :=
  (ζ_isSupernatural (R := R)).naturality_twist f

/-- Supernaturality of `ζ` on homogeneous morphisms: `ζ_Y ∘ Π f = (-1)^{|f|} f ∘ ζ_X`. -/
theorem ζ_naturality_of_mem {X Y : C} {q : ZMod 2} {f : X ⟶ Y}
    (hf : f ∈ parity (R := R) X Y q) :
    (pi (R := R)).map f ≫ (ζ (R := R) Y).hom = sign R q • ((ζ (R := R) X).hom ≫ f) := by
  rw [ζ_naturality, twist_one_of_mem hf, Linear.comp_smul]

/-- The action of `Π` on morphisms is determined by `ζ`. -/
theorem pi_map_eq {X Y : C} (f : X ⟶ Y) :
    (pi (R := R)).map f = (ζ (R := R) X).hom ≫ twist R 1 f ≫ (ζ (R := R) Y).inv := by
  rw [← ζ_naturality_assoc, Iso.hom_inv_id, Category.comp_id]

/-- **Lemma 3.2(iii) / Corollary 3.3(i).** `Π ζ = -ζ Π`. -/
theorem pi_map_ζ (X : C) :
    (pi (R := R)).map (ζ (R := R) X).hom = -(ζ (R := R) ((pi (R := R)).obj X)).hom := by
  have h := ζ_naturality_of_mem (R := R) (ζ_hom_mem (R := R) X)
  rw [sign_one, neg_smul, one_smul, ← Preadditive.neg_comp] at h
  exact (cancel_mono _).1 h

/-! ## The even isomorphism `ξ = ζζ` -/

/-- The even isomorphism `ξ_X := ζ_X ∘ Π ζ_X : Π² X ≅ X` (Brundan–Ellis, (1.4)). -/
def ξ (X : C) : (pi (R := R)).obj ((pi (R := R)).obj X) ≅ X :=
  (pi (R := R)).mapIso (ζ (R := R) X) ≪≫ ζ (R := R) X

/-- The first formula of (1.4): `ξ_X = ζ_X ∘ Π ζ_X`. -/
theorem ξ_hom (X : C) :
    (ξ (R := R) X).hom = (pi (R := R)).map (ζ (R := R) X).hom ≫ (ζ (R := R) X).hom := rfl

/-- The second formula of (1.4): `ξ_X = -ζ_X ∘ ζ_{Π X}`. -/
theorem ξ_hom_eq_neg (X : C) :
    (ξ (R := R) X).hom = -((ζ (R := R) ((pi (R := R)).obj X)).hom ≫ (ζ (R := R) X).hom) := by
  rw [ξ_hom, pi_map_ζ, Preadditive.neg_comp]

theorem ξ_inv_eq_neg (X : C) :
    (ξ (R := R) X).inv = -((ζ (R := R) X).inv ≫ (ζ (R := R) ((pi (R := R)).obj X)).inv) := by
  rw [← cancel_mono (ξ (R := R) X).hom, Iso.inv_hom_id, ξ_hom_eq_neg]
  simp

theorem ξ_hom_mem (X : C) :
    (ξ (R := R) X).hom ∈ parity (R := R) ((pi (R := R)).obj ((pi (R := R)).obj X)) X 0 := by
  have := comp_mem (map_mem (R := R) (pi (R := R)) (ζ_hom_mem (R := R) X))
    (ζ_hom_mem (R := R) X)
  exact this

/-- `ξ` is natural (it is an even supernatural isomorphism). -/
theorem ξ_naturality {X Y : C} (f : X ⟶ Y) :
    (pi (R := R)).map ((pi (R := R)).map f) ≫ (ξ (R := R) Y).hom = (ξ (R := R) X).hom ≫ f := by
  rw [ξ_hom, ξ_hom, ← Functor.map_comp_assoc, ζ_naturality (R := R) f, Functor.map_comp,
    Category.assoc, ζ_naturality (R := R) (twist R 1 f), twist_twist, Category.assoc]

/-- **Corollary 3.3(i).** `ξ Π = Π ξ`. -/
theorem ξ_pi (X : C) :
    (ξ (R := R) ((pi (R := R)).obj X)).hom = (pi (R := R)).map (ξ (R := R) X).hom := by
  have h : (ζ (R := R) ((pi (R := R)).obj X)).hom = -(pi (R := R)).map (ζ (R := R) X).hom := by
    rw [pi_map_ζ, neg_neg]
  rw [ξ_hom, ξ_hom, h, Functor.map_neg, Preadditive.neg_comp, Preadditive.comp_neg, neg_neg,
    Functor.map_comp]

/-- The natural isomorphism `ξ : Π² ≅ 𝟭`. -/
def ξIso : pi (R := R) ⋙ pi (R := R) ≅ 𝟭 C :=
  NatIso.ofComponents (fun X => ξ (R := R) X) fun f => ξ_naturality f

@[simp] theorem ξIso_hom_app (X : C) : (ξIso (R := R) (C := C)).hom.app X = (ξ (R := R) X).hom :=
  rfl

@[simp] theorem ξIso_inv_app (X : C) : (ξIso (R := R) (C := C)).inv.app X = (ξ (R := R) X).inv :=
  rfl

/-! ## The isomorphisms `β_F` -/

variable {D : Type w₃} [Category.{w₄} D] [Preadditive D] [Linear R D] [Supercategory R D]
  [PiSupercategory R D] {E : Type w₅} [Category.{w₆} E] [Preadditive E] [Linear R E]
  [Supercategory R E] [PiSupercategory R E]

variable (R) in
/-- **Corollary 3.3(ii).** For a superfunctor `F`, the isomorphism
`β_F := -ζ_B F ζ_A⁻¹ : Π_B F ≅ F Π_A`.

With the horizontal composition of Example 1.5(ii), the component of `ζ_B F ζ_A⁻¹` at `X` is
`ζ_{F Π X} ∘ Π(F(ζ_X⁻¹))`, which equals `-F(ζ_X⁻¹) ∘ ζ_{F X}` by the supernaturality of the
odd transformation `ζ_B` applied to the odd morphism `F(ζ_X⁻¹)`. Hence the components of `β_F`
are `F(ζ_X⁻¹) ∘ ζ_{F X}`, i.e. `ζ_{F X} ≫ F(ζ_X⁻¹)`; see `β_hom_eq_neg` for the literal
formula. -/
def β (F : C ⥤ D) (X : C) : (pi (R := R)).obj (F.obj X) ≅ F.obj ((pi (R := R)).obj X) :=
  ζ (R := R) (F.obj X) ≪≫ F.mapIso (ζ (R := R) X).symm

theorem β_hom (F : C ⥤ D) (X : C) :
    (β R F X).hom = (ζ (R := R) (F.obj X)).hom ≫ F.map (ζ (R := R) X).inv := rfl

theorem β_inv (F : C ⥤ D) (X : C) :
    (β R F X).inv = F.map (ζ (R := R) X).hom ≫ (ζ (R := R) (F.obj X)).inv := rfl

variable (F : C ⥤ D)

/-- The literal formula of Corollary 3.3(ii): `β_F = -(ζ_B F ζ_A⁻¹)`, whose component at `X` is
`-(Π(F(ζ_X⁻¹)) ≫ ζ_{F Π X})`. -/
theorem β_hom_eq_neg [F.Additive] [F.Linear R] [IsSuperfunctor R F] (X : C) :
    (β R F X).hom = -((pi (R := R)).map (F.map (ζ (R := R) X).inv) ≫
      (ζ (R := R) (F.obj ((pi (R := R)).obj X))).hom) := by
  rw [ζ_naturality_of_mem (map_mem F (ζ_inv_mem (R := R) X)), sign_one, neg_smul, one_smul,
    neg_neg, β_hom]

theorem β_hom_mem [F.Additive] [F.Linear R] [IsSuperfunctor R F] (X : C) :
    (β R F X).hom ∈ parity (R := R) ((pi (R := R)).obj (F.obj X)) (F.obj ((pi (R := R)).obj X)) 0 :=
  comp_mem (ζ_hom_mem (F.obj X)) (map_mem F (ζ_inv_mem (R := R) X))

/-- **Corollary 3.3(ii).** `β_F` is natural. -/
theorem β_naturality [F.Additive] [F.Linear R] [IsSuperfunctor R F] {X Y : C} (f : X ⟶ Y) :
    (pi (R := R)).map (F.map f) ≫ (β R F Y).hom = (β R F X).hom ≫ F.map ((pi (R := R)).map f) := by
  rw [β_hom, β_hom, ζ_naturality_assoc, Category.assoc, pi_map_eq, ← F.map_comp,
    Iso.inv_hom_id_assoc, F.map_comp, map_twist]

/-- The natural isomorphism `β_F : F ⋙ Π ≅ Π ⋙ F`. -/
def βIso [F.Additive] [F.Linear R] [IsSuperfunctor R F] : F ⋙ pi (R := R) ≅ pi (R := R) ⋙ F :=
  NatIso.ofComponents (fun X => β R F X) fun f => β_naturality F f

@[simp] theorem βIso_hom_app [F.Additive] [F.Linear R] [IsSuperfunctor R F] (X : C) :
    (βIso (R := R) F).hom.app X = (β R F X).hom := rfl

/-- **Corollary 3.3(ii).** `ξ_B F ξ_A⁻¹ = β_F Π_A ∘ Π_B β_F`. -/
theorem β_comm [F.Additive] [F.Linear R] [IsSuperfunctor R F] (X : C) :
    (ξ (R := R) (F.obj X)).hom ≫ F.map (ξ (R := R) X).inv =
      (pi (R := R)).map (β R F X).hom ≫ (β R F ((pi (R := R)).obj X)).hom := by
  have h := ζ_naturality_of_mem (R := R) (map_mem F (ζ_inv_mem (R := R) X))
  rw [sign_one, neg_smul, one_smul] at h
  rw [β_hom, β_hom, Functor.map_comp, Category.assoc, reassoc_of% h, ξ_hom, ξ_inv_eq_neg,
    F.map_neg, F.map_comp]
  simp

/-- **Corollary 3.3(iii).** For a supernatural transformation `x : F ⇒ G` of any parity,
`β_G ∘ Π_B x = x Π_A ∘ β_F`. -/
theorem β_naturality_supernatural [F.Additive] (G : C ⥤ D) [G.Additive] [G.Linear R]
    {p : ZMod 2} {x : ∀ X, F.obj X ⟶ G.obj X} (hx : IsSupernatural R p x) (X : C) :
    (pi (R := R)).map (x X) ≫ (β R G X).hom = (β R F X).hom ≫ x ((pi (R := R)).obj X) := by
  rw [β_hom, β_hom, ζ_naturality_assoc, Category.assoc, hx.naturality (ζ_inv_mem (R := R) X),
    twist_one_of_mem (hx.mem X), Linear.comp_smul, Linear.smul_comp, Linear.comp_smul,
    mul_one]

/-- **Corollary 3.3(iv).** `β_{GF} = G β_F ∘ β_G F`. -/
theorem β_comp (G : D ⥤ E) (X : C) :
    (β R (F ⋙ G) X).hom = (β R G (F.obj X)).hom ≫ G.map (β R F X).hom := by
  simp [β_hom]

/-- **Corollary 3.3(iv).** `β_𝟭 = 1`. -/
theorem β_id (X : C) : (β R (𝟭 C) X).hom = 𝟙 _ := by
  simp [β_hom]

/-- **Corollary 3.3(iv).** `β_Π = -1`. -/
theorem β_pi (X : C) : (β R (pi (R := R)) X).hom = -𝟙 _ := by
  have h : (ζ (R := R) ((pi (R := R)).obj X)).hom = -(pi (R := R)).map (ζ (R := R) X).hom := by
    rw [pi_map_ζ, neg_neg]
  rw [β_hom, h, Preadditive.neg_comp, ← Functor.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id]

end PiSupercategory

end StringDiagrams

end
