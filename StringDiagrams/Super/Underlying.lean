import StringDiagrams.Super.Pi
import StringDiagrams.Super.PiCategory

/-!
# The underlying category of a supercategory, and the functor `E₁ : Π-SCat → Π-Cat`

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Definition 1.1(v), the functor (2) of (1.5), and (5.1).

* `Underlying R C`: the underlying category of a supercategory: the same objects, only the even
  morphisms (Definition 1.1(v)).
* `Underlying.map F`: the restriction of a superfunctor.
* For a Π-supercategory `(A, Π, ζ)`, the underlying category is a Π-category `(A, Π, ξ)` with
  `ξ := ζζ` (instance `Underlying.instPiCategory`; Corollary 3.3(i)).
* `Underlying.piFunctor F`: for a superfunctor between Π-supercategories, the Π-functor
  `(F, β_F)` (Corollary 3.3(ii)); `Underlying.isPiNatural`: even supernatural transformations
  give Π-natural transformations (Corollary 3.3(iii)). Together these are the functor
  `E₁ : Π-SCat → Π-Cat` of (5.1) on objects, morphisms and 2-morphisms.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory

universe w w₁ w₂ w₃ w₄

/-- The underlying category of a supercategory (Brundan–Ellis, Definition 1.1(v)): the same
objects, with only the even morphisms. -/
@[ext]
structure Underlying (R : Type w) (C : Type w₁) where
  /-- The object of `C`. -/
  obj : C

namespace Underlying

variable {R : Type w} [CommRing R] {C : Type w₁} [Category.{w₂} C] [Preadditive C] [Linear R C]
  [Supercategory R C]

instance : Category (Underlying R C) where
  Hom X Y := parity (R := R) X.obj Y.obj 0
  id X := ⟨𝟙 X.obj, id_mem X.obj⟩
  comp f g := ⟨f.1 ≫ g.1, by simpa using comp_mem f.2 g.2⟩
  id_comp f := Subtype.ext (Category.id_comp f.1)
  comp_id f := Subtype.ext (Category.comp_id f.1)
  assoc f g h := Subtype.ext (Category.assoc f.1 g.1 h.1)

@[ext] theorem hom_ext {X Y : Underlying R C} {f g : X ⟶ Y} (h : f.1 = g.1) : f = g :=
  Subtype.ext h

@[simp] theorem id_val (X : Underlying R C) : (𝟙 X : X ⟶ X).1 = 𝟙 X.obj := rfl

@[simp] theorem comp_val {X Y Z : Underlying R C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).1 = f.1 ≫ g.1 := rfl

instance : Preadditive (Underlying R C) where
  homGroup X Y := inferInstanceAs (AddCommGroup (parity (R := R) X.obj Y.obj 0))
  add_comp _ _ _ f f' g := Subtype.ext (Preadditive.add_comp _ _ _ f.1 f'.1 g.1)
  comp_add _ _ _ f g g' := Subtype.ext (Preadditive.comp_add _ _ _ f.1 g.1 g'.1)

instance : Linear R (Underlying R C) where
  homModule X Y := inferInstanceAs (Module R (parity (R := R) X.obj Y.obj 0))
  smul_comp _ _ _ r f g := Subtype.ext (Linear.smul_comp _ _ _ r f.1 g.1)
  comp_smul _ _ _ f r g := Subtype.ext (Linear.comp_smul _ _ _ f.1 r g.1)

@[simp] theorem add_val {X Y : Underlying R C} (f g : X ⟶ Y) : (f + g).1 = f.1 + g.1 := rfl

@[simp] theorem neg_val {X Y : Underlying R C} (f : X ⟶ Y) : (-f).1 = -f.1 := rfl

@[simp] theorem zero_val {X Y : Underlying R C} : (0 : X ⟶ Y).1 = 0 := rfl

@[simp] theorem sub_val {X Y : Underlying R C} (f g : X ⟶ Y) : (f - g).1 = f.1 - g.1 := rfl

@[simp] theorem smul_val {X Y : Underlying R C} (r : R) (f : X ⟶ Y) : (r • f).1 = r • f.1 := rfl

variable (R C) in
/-- The inclusion of the underlying category. -/
@[simps]
def ι : Underlying R C ⥤ C where
  obj X := X.obj
  map f := f.1

instance : (ι R C).Faithful where
  map_injective h := Subtype.ext h

/-- An even isomorphism gives an isomorphism of the underlying category. -/
@[simps]
def isoMk {X Y : C} (e : X ≅ Y) (he : e.hom ∈ parity (R := R) X Y 0) :
    (⟨X⟩ : Underlying R C) ≅ ⟨Y⟩ where
  hom := ⟨e.hom, he⟩
  inv := ⟨e.inv, inv_mem e he⟩
  hom_inv_id := Subtype.ext e.hom_inv_id
  inv_hom_id := Subtype.ext e.inv_hom_id

variable {D : Type w₃} [Category.{w₄} D] [Preadditive D] [Linear R D] [Supercategory R D]

/-- The restriction `F̲ : A̲ ⥤ B̲` of a superfunctor (Brundan–Ellis, Definition 1.1(v)). -/
@[simps]
def map (F : C ⥤ D) [F.Additive] [F.Linear R] [IsSuperfunctor R F] :
    Underlying R C ⥤ Underlying R D where
  obj X := ⟨F.obj X.obj⟩
  map f := ⟨F.map f.1, Supercategory.map_mem F f.2⟩
  map_id X := Subtype.ext (F.map_id X.obj)
  map_comp f g := Subtype.ext (F.map_comp f.1 g.1)

@[simp] theorem map_map_val (F : C ⥤ D) [F.Additive] [F.Linear R] [IsSuperfunctor R F]
    {X Y : Underlying R C}
    (f : X ⟶ Y) : ((map (R := R) F).map f).1 = F.map f.1 := rfl

instance (F : C ⥤ D) [F.Additive] [F.Linear R] [IsSuperfunctor R F] :
    (map (R := R) F).Additive where
  map_add := Subtype.ext F.map_add

instance (F : C ⥤ D) [F.Additive] [F.Linear R] [IsSuperfunctor R F] :
    (map (R := R) F).Linear R where
  map_smul f r := Subtype.ext (Functor.Linear.map_smul (F := F) f.1 r)

/-! ## The underlying Π-category of a Π-supercategory -/

section Pi

variable [PiSupercategory R C]

/-- `ξ := ζζ` as an isomorphism of the underlying category. -/
def ξUnd (X : Underlying R C) :
    (map (R := R) (PiSupercategory.pi (R := R))).obj
      ((map (R := R) (PiSupercategory.pi (R := R))).obj X) ≅ X :=
  isoMk (PiSupercategory.ξ (R := R) X.obj) (PiSupercategory.ξ_hom_mem X.obj)

/-- **Brundan–Ellis, (1.5) and Corollary 3.3(i).** The underlying category of a
Π-supercategory `(A, Π, ζ)` is a Π-category `(A̲, Π̲, ξ)` with `ξ := ζζ`. -/
instance instPiCategory : PiCategory R (Underlying R C) where
  pi := map (R := R) (PiSupercategory.pi (R := R))
  ξ := NatIso.ofComponents ξUnd fun f => Subtype.ext (PiSupercategory.ξ_naturality f.1)
  ξ_pi X := Subtype.ext (PiSupercategory.ξ_pi X.obj)

@[simp] theorem pi_obj (X : Underlying R C) :
    (PiCategory.pi (R := R)).obj X = ⟨(PiSupercategory.pi (R := R)).obj X.obj⟩ := rfl

@[simp] theorem pi_map_val {X Y : Underlying R C} (f : X ⟶ Y) :
    ((PiCategory.pi (R := R)).map f).1 = (PiSupercategory.pi (R := R)).map f.1 := rfl

@[simp] theorem ξ_hom_app_val (X : Underlying R C) :
    ((PiCategory.ξ (R := R)).hom.app X).1 = (PiSupercategory.ξ (R := R) X.obj).hom := rfl

@[simp] theorem ξApp_hom_val (X : Underlying R C) :
    (PiCategory.ξApp (R := R) X).hom.1 = (PiSupercategory.ξ (R := R) X.obj).hom := rfl

@[simp] theorem ξ_inv_app_val (X : Underlying R C) :
    ((PiCategory.ξ (R := R)).inv.app X).1 = (PiSupercategory.ξ (R := R) X.obj).inv := rfl

variable [PiSupercategory R D]

/-- **Brundan–Ellis, (1.5), (5.1) and Corollary 3.3(ii).** A superfunctor between
Π-supercategories gives a Π-functor `(F̲, β_F)` between the underlying Π-categories. -/
def piFunctor (F : C ⥤ D) [F.Additive] [F.Linear R] [IsSuperfunctor R F] :
    PiFunctor R (map (R := R) F) where
  β := NatIso.ofComponents
    (fun X => isoMk (PiSupercategory.β R F X.obj) (PiSupercategory.β_hom_mem F X.obj))
    fun f => Subtype.ext (PiSupercategory.β_naturality F f.1)
  comm X := Subtype.ext (PiSupercategory.β_comm F X.obj)

@[simp] theorem piFunctor_β_hom_app_val (F : C ⥤ D) [F.Additive] [F.Linear R]
    [IsSuperfunctor R F] (X : Underlying R C) :
    ((piFunctor F).β.hom.app X).1 = (PiSupercategory.β R F X.obj).hom := rfl

/-- **Corollary 3.3(iii).** An even supernatural transformation gives a Π-natural
transformation of the underlying Π-functors. -/
def natTrans {F G : C ⥤ D} [F.Additive] [F.Linear R] [IsSuperfunctor R F] [G.Additive]
    [G.Linear R] [IsSuperfunctor R G] {x : ∀ X, F.obj X ⟶ G.obj X} (hx : IsSupernatural R 0 x) :
    map (R := R) F ⟶ map (R := R) G where
  app X := ⟨x X.obj, hx.mem X.obj⟩
  naturality _ _ f := Subtype.ext (hx.naturality_zero f.1)

theorem isPiNatural {F G : C ⥤ D} [F.Additive] [F.Linear R] [IsSuperfunctor R F] [G.Additive]
    [G.Linear R] [IsSuperfunctor R G] {x : ∀ X, F.obj X ⟶ G.obj X} (hx : IsSupernatural R 0 x) :
    PiFunctor.IsPiNatural R (piFunctor F) (piFunctor G) (natTrans hx) := fun X =>
  Subtype.ext (PiSupercategory.β_naturality_supernatural F G hx X.obj).symm

end Pi

end Underlying

end StringDiagrams

end
