import StringDiagrams.Super.PiCatBicategory
import StringDiagrams.Super.AssociatedTwoMap

/-!
# `E₁ : E₂(Π-𝔖ℭ𝔞𝔱) → Π-ℭ𝔞𝔱` is a Π-2-functor and a local equivalence (Theorem 5.3)

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, (5.3),
Theorem 5.3 and the proof of Corollary 5.6.

* `PiSCat.E₁Pseudo`: the strict 2-functor `E₁` of (5.3) from the underlying 2-category of
  `Π-𝔖ℭ𝔞𝔱` (even supernatural transformations, `Underlying2 R (PiSCat R)`) to the bicategory
  `Π-ℭ𝔞𝔱` (`StringDiagrams.Super.PiCatBicategory`): `A ↦ A̲`, `F ↦ (F̲, β_F)`, `x ↦ x̲`, with
  identity coherence isomorphisms.
* `PiSCat.E₁PiTwoFunctor`: `E₁` is a (strict) Π-2-functor with `j = 1` (Definition 5.2(ii));
  the axioms are `β_Π = -1` and the strictness of `E₁` on `β` and `ξ`
  (`PiSCat.underlying_piFunctor_β`, `PiSCat.underlying_ξ`).
* **Theorem 5.3, `E₁` is a Π-2-equivalence** (in the local form used in the proof of
  Corollary 5.6): the functors `Hom(A, B) → Hom(E₁A, E₁B)` are full (`E₁_homFunctor_full`: a
  Π-natural transformation between the underlying Π-functors of superfunctors is automatically
  natural with respect to odd morphisms, `PiSupercategory.naturality_of_isPiNatural`), faithful
  and essentially surjective (`E₁_homFunctor_essSurj`: every Π-functor `H : A̲ → B̲` is
  Π-naturally isomorphic to `E₁` of the superfunctor `T_B ∘ Ĥ ∘ T_A⁻¹`, `PiSCat.liftPiFunctor`);
  and every Π-category `C` is isomorphic to `E₁(D₁ C)` (`PiCat.unitIsoApp`, Lemma 5.1).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Bicategory Supercategory

universe w v u

variable {R : Type w} [CommRing R]

/-! ## Π-natural transformations of superfunctors are supernatural -/

namespace PiSupercategory

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear R A] [Supercategory R A]
  [PiSupercategory R A] {B : Type u} [Category.{v} B] [Preadditive B] [Linear R B]
  [Supercategory R B] [PiSupercategory R B]
  (F G : A ⥤ B) [F.Additive] [F.Linear R] [IsSuperfunctor R F] [G.Additive] [G.Linear R]
  [IsSuperfunctor R G]

omit [F.Linear R] [IsSuperfunctor R F] [G.Linear R] [IsSuperfunctor R G] in
/-- A family of even morphisms `y_λ : F λ → G λ` which is natural with respect to even morphisms
and Π-natural (`y Π ∘ β_F = β_G ∘ Π y`) is natural with respect to all morphisms. This is the
fullness of `E₁` on 2-morphisms in Theorem 5.3. -/
theorem naturality_of_isPiNatural (y : ∀ X, F.obj X ⟶ G.obj X)
    (hmem : ∀ X, y X ∈ parity (R := R) (F.obj X) (G.obj X) 0)
    (hnat : ∀ {X Y : A} (f : X ⟶ Y), f ∈ parity (R := R) X Y 0 → F.map f ≫ y Y = y X ≫ G.map f)
    (hpi : ∀ X, (β R F X).hom ≫ y ((pi (R := R)).obj X) =
      (pi (R := R)).map (y X) ≫ (β R G X).hom)
    {X Y : A} (f : X ⟶ Y) : F.map f ≫ y Y = y X ≫ G.map f := by
  -- naturality with respect to `ζ_Y`
  have hζ : ∀ Y : A, F.map (ζ (R := R) Y).hom ≫ y Y = y ((pi (R := R)).obj Y) ≫
      G.map (ζ (R := R) Y).hom := by
    intro Y
    have h1 := hpi Y
    have h2 := ζ_naturality_of_mem (R := R) (hmem Y)
    rw [sign_zero, one_smul] at h2
    rw [β_hom, β_hom, Category.assoc, reassoc_of% h2] at h1
    have h3 := (cancel_epi _).1 h1
    rw [← cancel_epi (F.map (ζ (R := R) Y).inv), ← F.map_comp_assoc, Iso.inv_hom_id,
      F.map_id, Category.id_comp, reassoc_of% h3, ← G.map_comp, Iso.inv_hom_id, G.map_id,
      Category.comp_id]
  have hodd : ∀ {X Y : A} (f : X ⟶ Y), f ∈ parity (R := R) X Y 1 →
      F.map f ≫ y Y = y X ≫ G.map f := by
    intro X Y f hf
    have hg : f ≫ (ζ (R := R) Y).inv ∈ parity (R := R) X ((pi (R := R)).obj Y) 0 := by
      have h := comp_mem hf (ζ_inv_mem (R := R) Y)
      rwa [show (1 : ZMod 2) + 1 = 0 from rfl] at h
    have e : f = (f ≫ (ζ (R := R) Y).inv) ≫ (ζ (R := R) Y).hom := by simp
    rw [e, F.map_comp, G.map_comp, Category.assoc, hζ, ← Category.assoc, hnat _ hg,
      Category.assoc]
  rw [← proj_add_proj (R := R) f, F.map_add, G.map_add, Preadditive.add_comp,
    Preadditive.comp_add, hnat _ (proj_mem 0 f), hodd _ (proj_mem 1 f)]

end PiSupercategory

/-! ## `β` of `T⁻¹` -/

namespace Associated

variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear R A] [Supercategory R A]
  [PiSupercategory R A]

set_option backward.isDefEq.respectTransparency false in
theorem Tinv_map_ζ_inv (X : A) :
    (Tinv R A).map (PiSupercategory.ζ (R := R) X).inv =
      (PiSupercategory.ζ (R := R) ((Tinv R A).obj X)).inv := by
  apply T_map_injective
  rw [T_map_Tinv_map]
  have h : (T R A).mapIso (PiSupercategory.ζ (R := R) ((Tinv R A).obj X)) =
      PiSupercategory.ζ (R := R) X := Iso.ext (T_map_ζ _)
  exact (congrArg Iso.inv h).symm

set_option backward.isDefEq.respectTransparency false in
/-- `β_{T⁻¹} = 1`. -/
theorem β_Tinv (X : A) : (PiSupercategory.β R (Tinv R A) X).hom = 𝟙 _ := by
  rw [PiSupercategory.β_hom, Tinv_map_ζ_inv, Iso.hom_inv_id]

set_option backward.isDefEq.respectTransparency false in
/-- `T⁻¹` on an even morphism. -/
theorem Tinv_map_of_mem {X Y : A} {f : X ⟶ Y} (hf : f ∈ parity (R := R) X Y 0) :
    (Tinv R A).map f = homMk (X := (Tinv R A).obj X) (Y := (Tinv R A).obj Y)
      ((⟨f, hf⟩ : parity (R := R) X Y 0) : (⟨X⟩ : Underlying R A) ⟶ ⟨Y⟩) 0 := by
  apply T_map_injective
  rw [T_map_Tinv_map, T_map_homMk]

variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear R B] [Supercategory R B]
  [PiSupercategory R B] {H : Underlying R A ⥤ Underlying R B} [H.Additive] [H.Linear R]
  (hH : PiFunctor R H)

/-- The superfunctor `T_B ∘ Ĥ ∘ T_A⁻¹ : A → B` of a Π-functor `H : A̲ → B̲` between the underlying
Π-categories of Π-supercategories. -/
def liftFunctor : A ⥤ B := Tinv R A ⋙ map hH ⋙ T R B

instance : (liftFunctor hH).Additive := inferInstanceAs (Tinv R A ⋙ map hH ⋙ T R B).Additive

instance : (liftFunctor hH).Linear R := inferInstanceAs ((Tinv R A ⋙ map hH ⋙ T R B).Linear R)

instance : IsSuperfunctor R (liftFunctor hH) :=
  inferInstanceAs (IsSuperfunctor R (Tinv R A ⋙ map hH ⋙ T R B))

set_option backward.isDefEq.respectTransparency false in
omit [H.Linear R] in
/-- `T_B ∘ Ĥ ∘ T_A⁻¹` is `H` on even morphisms. -/
theorem liftFunctor_map_of_mem {X Y : A} {f : X ⟶ Y} (hf : f ∈ parity (R := R) X Y 0) :
    (liftFunctor hH).map f =
      (H.map ((⟨f, hf⟩ : parity (R := R) X Y 0) : (⟨X⟩ : Underlying R A) ⟶ ⟨Y⟩)).1 := by
  change (T R B).map ((map hH).map ((Tinv R A).map f)) = _
  rw [Tinv_map_of_mem hf]
  simp

set_option backward.isDefEq.respectTransparency false in
omit [H.Linear R] in
/-- `β` of `T_B ∘ Ĥ ∘ T_A⁻¹` is `β_H`. -/
theorem liftFunctor_β (X : A) :
    (PiSupercategory.β R (liftFunctor hH) X).hom = (hH.β.hom.app ⟨X⟩).1 := by
  change (PiSupercategory.β R (Tinv R A ⋙ map hH ⋙ T R B) X).hom = _
  rw [PiSupercategory.β_comp, PiSupercategory.β_comp, β_T, β_map, β_Tinv]
  simp only [Functor.comp_obj, Functor.comp_map, T_map_homMk, CategoryTheory.Functor.map_id,
    Category.id_comp]
  exact Category.comp_id _

end Associated

/-! ## The Π-2-functor `E₁` -/

namespace PiSCat

variable {A B C : Underlying2 R (PiSCat.{w, v, u} R)}

/-- An even supernatural transformation, as a 2-morphism of the underlying 2-category of
`Π-𝔖ℭ𝔞𝔱`, is supernatural of parity `0`. -/
theorem isSupernatural_hom₂ {F G : A ⟶ B} (η : F ⟶ G) :
    IsSupernatural R 0 (F := F.obj.toFunctor) (G := G.obj.toFunctor)
      ((Superfunctor.toSuperNatTrans η.1).app 0) :=
  (Superfunctor.toSuperNatTrans η.1).isSupernatural 0

/-- `E₁` on 1-morphisms: the Π-functor `(F̲, β_F)` (as `PiSCat.E₁.map`). -/
abbrev E₁map (F : A ⟶ B) :
    PiCat.of R (Underlying R A.obj.carrier) ⟶ PiCat.of R (Underlying R B.obj.carrier) :=
  ⟨Underlying.map F.obj.toFunctor, Underlying.piFunctor F.obj.toFunctor⟩

/-- `E₁` on 2-morphisms (5.3): `x ↦ x̲` (Corollary 3.3(iii)). -/
def E₁map₂ {F G : A ⟶ B} (η : F ⟶ G) : E₁map F ⟶ E₁map G :=
  PiCat.hom₂Mk (Underlying.natTrans (isSupernatural_hom₂ η)) (Underlying.isPiNatural _)

@[simp] theorem E₁map₂_app_val {F G : A ⟶ B} (η : F ⟶ G) (X : Underlying R A.obj.carrier) :
    ((PiCat.Hom₂.natTrans (E₁map₂ η)).app X).1 = η.1.app 0 X.obj := rfl

set_option backward.isDefEq.respectTransparency false in
variable (R) in
/-- **Brundan–Ellis, (5.3).** The strict 2-functor `E₁ : E₂(Π-𝔖ℭ𝔞𝔱) → Π-ℭ𝔞𝔱`: `A ↦ A̲`,
`F ↦ (F̲, β_F)`, `x ↦ x̲`, with identity coherence isomorphisms. -/
def E₁Pseudo : Pseudofunctor (Underlying2 R (PiSCat.{w, v, u} R)) (PiCat.{w, v, u} R) where
  obj A := PiCat.of R (Underlying R A.obj.carrier)
  map F := E₁map F
  map₂ η := E₁map₂ η
  map₂_id _ := PiCat.hom₂_ext fun _ => rfl
  map₂_comp η θ := PiCat.hom₂_ext fun X => Underlying.hom_ext (by
    simp [E₁map₂, Underlying.natTrans,
      Superfunctor.app_eq_zero_of_mem η.2 (show (1 : ZMod 2) ≠ 0 by decide)])
  mapId A := PiCat.iso₂Mk (Iso.refl _) fun X => by
    refine Underlying.hom_ext ?_
    simp [PiFunctor.id]
    exact PiSupercategory.β_id (R := R) X.obj
  mapComp F G := PiCat.iso₂Mk (Iso.refl _) fun X => by
    refine Underlying.hom_ext ?_
    simp [PiFunctor.comp]
    exact PiSupercategory.β_comp (R := R) F.obj.toFunctor G.obj.toFunctor X.obj
  map₂_whisker_left F _ _ η := PiCat.hom₂_ext fun X => Underlying.hom_ext (by
    simp [E₁map₂, Underlying.natTrans]
    exact (Category.comp_id _).symm)
  map₂_whisker_right η H := PiCat.hom₂_ext fun X => Underlying.hom_ext (by
    simp [E₁map₂, Underlying.natTrans]
    exact (Category.comp_id _).symm)
  map₂_associator F G H := PiCat.hom₂_ext fun X => Underlying.hom_ext (by
    simp [E₁map₂, Underlying.natTrans]
    erw [Category.id_comp, Category.id_comp]
    rfl)
  map₂_left_unitor F := PiCat.hom₂_ext fun X => Underlying.hom_ext (by
    simp [E₁map₂, Underlying.natTrans]
    rfl)
  map₂_right_unitor F := PiCat.hom₂_ext fun X => Underlying.hom_ext (by
    simp [E₁map₂, Underlying.natTrans]
    rfl)

set_option backward.isDefEq.respectTransparency false in
theorem j_isPiNatural (A : Underlying2 R (PiSCat.{w, v, u} R)) :
    PiFunctor.IsPiNatural R (PiCat.piHom ((E₁Pseudo R).obj A)).piFunctor
      ((E₁Pseudo R).map (PiTwoCategory.pi (R := R) A)).piFunctor
      (Iso.refl (PiCat.piHom ((E₁Pseudo R).obj A)).toFunctor).hom := fun X => by
  refine Underlying.hom_ext ?_
  simp [PiFunctor.pi, E₁Pseudo]
  exact (PiSCat.β_pi A.obj X.obj).symm

@[simp] theorem E₁Pseudo_map₂_app_val {F G : A ⟶ B} (η : F ⟶ G) (X : Underlying R A.obj.carrier) :
    ((PiCat.Hom₂.natTrans ((E₁Pseudo R).map₂ η)).app X).1 = η.1.app 0 X.obj := rfl

@[simp] theorem E₁Pseudo_mapComp_hom_app (F : A ⟶ B) (G : B ⟶ C)
    (X : Underlying R A.obj.carrier) :
    (PiCat.Hom₂.natTrans ((E₁Pseudo R).mapComp F G).hom).app X = 𝟙 _ := rfl

@[simp] theorem E₁Pseudo_mapComp_inv_app (F : A ⟶ B) (G : B ⟶ C)
    (X : Underlying R A.obj.carrier) :
    (PiCat.Hom₂.natTrans ((E₁Pseudo R).mapComp F G).inv).app X = 𝟙 _ := rfl

@[simp] theorem E₁Pseudo_mapId_hom_app (A : Underlying2 R (PiSCat.{w, v, u} R))
    (X : Underlying R A.obj.carrier) :
    (PiCat.Hom₂.natTrans ((E₁Pseudo R).mapId A).hom).app X = 𝟙 _ := rfl

@[simp] theorem E₁Pseudo_mapId_inv_app (A : Underlying2 R (PiSCat.{w, v, u} R))
    (X : Underlying R A.obj.carrier) :
    (PiCat.Hom₂.natTrans ((E₁Pseudo R).mapId A).inv).app X = 𝟙 _ := rfl

theorem E₁Pseudo_map (F : A ⟶ B) : (E₁Pseudo R).map F = E₁map F := rfl

/-- On objects, `E₁Pseudo` is the functor `E₁ : Π-SCat → Π-Cat` of (5.1). -/
theorem E₁Pseudo_obj_eq (A : Underlying2 R (PiSCat.{w, v, u} R)) :
    (E₁Pseudo R).obj A = E₁.obj A.obj := rfl

/-- On 1-morphisms, `E₁Pseudo` is the functor `E₁ : Π-SCat → Π-Cat` of (5.1). -/
theorem E₁Pseudo_map_eq (F : A ⟶ B) : (E₁Pseudo R).map F = E₁.map F.obj := rfl

set_option backward.isDefEq.respectTransparency false in
variable (R) in
/-- **Brundan–Ellis, (5.3).** `E₁` is a strict Π-2-functor (`j = 1`). -/
def E₁PiTwoFunctor : PiTwoFunctor R (E₁Pseudo.{w, v, u} R) where
  map₂_add _ _ := PiCat.hom₂_ext fun _ => rfl
  map₂_smul _ _ := PiCat.hom₂_ext fun _ => rfl
  j A := PiCat.iso₂Mk (Iso.refl _) (j_isPiNatural A)
  β_comm F := PiCat.hom₂_ext fun X => Underlying.hom_ext (by
    simp [E₁Pseudo_map, β_app_zero])
  ξ_comm A := PiCat.hom₂_ext fun X => Underlying.hom_ext (by
    simp [E₁Pseudo_map, ξ_app_zero]
    rfl)

/-! ## `E₁` is a local equivalence -/

/-- The functor `Hom(A, B) → Hom(E₁A, E₁B)` of `E₁`. -/
abbrev E₁homFunctor (A B : Underlying2 R (PiSCat.{w, v, u} R)) :=
  (E₁PiTwoFunctor R).homFunctor A B

set_option backward.isDefEq.respectTransparency false in
instance E₁_homFunctor_faithful (A B : Underlying2 R (PiSCat.{w, v, u} R)) :
    (E₁homFunctor A B).Faithful where
  map_injective {F G} η θ h := by
    have h0 : ∀ X, η.1.app 0 X = θ.1.app 0 X := fun X =>
      congrArg Subtype.val (congrFun (congrArg NatTrans.app (congrArg Subtype.val h)) ⟨X⟩)
    refine Subtype.ext (Superfunctor.hom_ext_parity h0 fun X => ?_)
    rw [Superfunctor.app_eq_zero_of_mem η.2 (by decide), Superfunctor.app_eq_zero_of_mem θ.2
      (by decide)]

set_option backward.isDefEq.respectTransparency false in
instance E₁_homFunctor_full (A B : Underlying2 R (PiSCat.{w, v, u} R)) :
    (E₁homFunctor A B).Full where
  map_surjective {F G} y := by
    let y' : ∀ X, F.obj.obj X ⟶ G.obj.obj X := fun X => ((PiCat.Hom₂.natTrans y).app ⟨X⟩).1
    have hmem : ∀ X, y' X ∈ parity (R := R) _ _ 0 := fun X => ((PiCat.Hom₂.natTrans y).app ⟨X⟩).2
    have hnat : ∀ {X Y : A.obj.carrier} (f : X ⟶ Y), F.obj.map f ≫ y' Y = y' X ≫ G.obj.map f :=
      PiSupercategory.naturality_of_isPiNatural F.obj.toFunctor G.obj.toFunctor y' hmem
        (fun {X Y} f hf => congrArg Subtype.val
          ((PiCat.Hom₂.natTrans y).naturality (X := ⟨X⟩) (Y := ⟨Y⟩) ⟨f, hf⟩))
        (fun X => congrArg Subtype.val (PiCat.Hom₂.isPiNatural y ⟨X⟩))
    have hx : IsSupernatural R 0 (F := F.obj.toFunctor) (G := G.obj.toFunctor) y' :=
      isSupernatural_of_natTrans (F := F.obj.toFunctor) (G := G.obj.toFunctor)
        ⟨y', fun _ _ f => hnat f⟩ hmem
    refine ⟨⟨Superfunctor.homMk hx.toSuperNatTrans,
      Superfunctor.IsSupernatural.toSuperNatTrans_mem hx⟩, ?_⟩
    refine PiCat.hom₂_ext fun X => Underlying.hom_ext ?_
    change hx.toSuperNatTrans.app 0 X.obj = y' X.obj
    rw [IsSupernatural.toSuperNatTrans_app]

variable {A B : Underlying2 R (PiSCat.{w, v, u} R)}

/-- The superfunctor `T_B ∘ Ĥ ∘ T_A⁻¹ : A → B` of a Π-functor `H : A̲ → B̲` between the underlying
Π-categories, as a 1-morphism of `E₂(Π-𝔖ℭ𝔞𝔱)`. -/
def liftPiFunctor (H : PiCat.of R (Underlying R A.obj.carrier) ⟶
    PiCat.of R (Underlying R B.obj.carrier)) : A ⟶ B :=
  letI := H.additive
  letI := H.linear
  ⟨(⟨Associated.liftFunctor H.piFunctor⟩ : Superfunctor R A.obj.carrier B.obj.carrier)⟩

set_option backward.isDefEq.respectTransparency false in
/-- Every Π-functor `H : A̲ → B̲` is Π-naturally isomorphic to `E₁(T_B ∘ Ĥ ∘ T_A⁻¹)`. -/
def liftPiFunctorIso (H : PiCat.of R (Underlying R A.obj.carrier) ⟶
    PiCat.of R (Underlying R B.obj.carrier)) :
    (E₁homFunctor A B).obj (liftPiFunctor H) ≅ H :=
  letI := H.additive
  letI := H.linear
  (PiCat.iso₂Mk (F := H) (G := (E₁Pseudo R).map (liftPiFunctor H))
    (NatIso.ofComponents (fun X => Iso.refl _) fun {X Y} f => Underlying.hom_ext (by
      change (H.toFunctor.map f).1 ≫ 𝟙 _ = 𝟙 _ ≫ (Associated.liftFunctor H.piFunctor).map f.1
      rw [Associated.liftFunctor_map_of_mem H.piFunctor f.2]
      simp))
    fun X => by
      simp only [NatIso.ofComponents_hom_app, Iso.refl_hom, CategoryTheory.Functor.map_id,
        Category.id_comp]
      refine Underlying.hom_ext ?_
      change (H.piFunctor.β.hom.app X).1 ≫ 𝟙 _ =
        (PiSupercategory.β R (Associated.liftFunctor H.piFunctor) X.obj).hom
      rw [Category.comp_id, Associated.liftFunctor_β]).symm

instance E₁_homFunctor_essSurj (A B : Underlying2 R (PiSCat.{w, v, u} R)) :
    (E₁homFunctor A B).EssSurj where
  mem_essImage H := ⟨liftPiFunctor H, ⟨liftPiFunctorIso H⟩⟩

end PiSCat

end StringDiagrams

end
