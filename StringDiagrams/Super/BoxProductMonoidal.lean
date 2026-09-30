import StringDiagrams.Super.BoxProduct
import StringDiagrams.Super.PiCat

/-!
# The monoidal category `(SCat, ⊠)`

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, the
paragraph after Example 1.2: the product `A ⊠ B` of supercategories (`BoxProd`, in
`StringDiagrams.Super.BoxProduct`) is functorial in superfunctors, `F ⊠ G : A ⊠ B → A' ⊠ B'`,
`(λ, μ) ↦ (F λ, G μ)`, `f ⊗ g ↦ F f ⊗ G g`.

## Main definitions

* `BoxProd.map F G : Superfunctor k (BoxProd k C D) (BoxProd k C' D')`: the superfunctor
  `F ⊠ G`, with `BoxProd.map_id` (`id ⊠ id = id`) and `BoxProd.map_comp`
  (`(F ≫ F') ⊠ (G ≫ G') = (F ⊠ G) ≫ (F' ⊠ G')`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory TensorProduct

universe u w₁ w₂ w₃ w₄ w₅ w₆

variable {k : Type u} [CommRing k]

namespace Supercategory.Superfunctor

variable {A : Type w₁} [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  {E : Type w₂} [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (obj : A → E) (hom : ∀ X Y : A, (X ⟶ Y) →ₗ[k] (obj X ⟶ obj Y))
  (map_id : ∀ X, hom X X (𝟙 X) = 𝟙 (obj X))
  (map_comp : ∀ {X Y Z : A} (x : X ⟶ Y) (y : Y ⟶ Z), hom X Z (x ≫ y) = hom X Y x ≫ hom Y Z y)

/-- The functor given by an object map and linear maps on morphism modules preserving
identities and composition. -/
@[simps]
def functorOfLinearMaps : A ⥤ E where
  obj := obj
  map {X Y} x := hom X Y x
  map_id := map_id
  map_comp := map_comp

instance : (functorOfLinearMaps obj hom map_id map_comp).Additive where
  map_add {X Y x y} := (hom X Y).map_add x y

instance : (functorOfLinearMaps obj hom map_id map_comp).Linear k where
  map_smul {X Y} x r := (hom X Y).map_smul r x

/-- The superfunctor given by an object map and parity-preserving linear maps on morphism
superspaces preserving identities and composition. -/
def ofLinearMaps
    (map_mem : ∀ {X Y : A} {p : ZMod 2} {x : X ⟶ Y}, x ∈ parity (R := k) X Y p →
      hom X Y x ∈ parity (R := k) (obj X) (obj Y) p) : Superfunctor k A E where
  toFunctor := functorOfLinearMaps obj hom map_id map_comp
  isSuperfunctor := ⟨map_mem⟩

end Supercategory.Superfunctor

namespace BoxProd

variable {C : Type w₁} [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  {D : Type w₂} [Category.{u} D] [Preadditive D] [Linear k D] [Supercategory k D]
  {C' : Type w₃} [Category.{u} C'] [Preadditive C'] [Linear k C'] [Supercategory k C']
  {D' : Type w₄} [Category.{u} D'] [Preadditive D'] [Linear k D'] [Supercategory k D']
  {C'' : Type w₅} [Category.{u} C''] [Preadditive C''] [Linear k C''] [Supercategory k C'']
  {D'' : Type w₆} [Category.{u} D''] [Preadditive D''] [Linear k D''] [Supercategory k D'']

/-! ## Superfunctors out of `C ⊠ D` -/

/-- Superfunctors out of `C ⊠ D` agreeing on objects and on the morphisms `f ⊗ g` are equal. -/
theorem superfunctor_ext {E : Type w₃} [Category.{u} E] [Preadditive E] [Linear k E]
    [Supercategory k E] {Φ Ψ : Superfunctor k (BoxProd k C D) E}
    (hobj : ∀ X, Φ.obj X = Ψ.obj X)
    (hmap : ∀ (X Y : BoxProd k C D) (f : X.fst ⟶ Y.fst) (g : X.snd ⟶ Y.snd),
      Φ.map (tmulHom f g) ≍ Ψ.map (tmulHom f g)) :
    Φ = Ψ := by
  refine Superfunctor.ext (CategoryTheory.Functor.ext hobj fun X Y x => ?_)
  induction x using TensorProduct.inductionOn with
  | tmul f g => exact (conj_eqToHom_iff_heq _ _ (hobj X) (hobj Y)).2 (hmap X Y f g)
  | add x y hx hy =>
    change Φ.toFunctor.map (x + y : X ⟶ Y) = eqToHom (hobj X) ≫ Ψ.toFunctor.map (x + y : X ⟶ Y) ≫
      eqToHom (hobj Y).symm
    rw [Functor.map_add, Functor.map_add, hx, hy, Preadditive.add_comp, Preadditive.comp_add]

/-! ## `F ⊠ G` -/

section Map

variable (F : Superfunctor k C C') (G : Superfunctor k D D')

/-- The objects `(F λ, G μ)` of `C' ⊠ D'`. -/
abbrev mapObj (X : BoxProd k C D) : BoxProd k C' D' := ⟨F.obj X.fst, G.obj X.snd⟩

/-- The linear map `f ⊗ g ↦ F f ⊗ G g` on morphism superspaces. -/
def mapHom (X Y : BoxProd k C D) : (X ⟶ Y) →ₗ[k] (mapObj F G X ⟶ mapObj F G Y) :=
  TensorProduct.map (F.toFunctor.mapLinearMap k) (G.toFunctor.mapLinearMap k)

theorem mapHom_tmul {X Y : BoxProd k C D} (f : X.fst ⟶ Y.fst) (g : X.snd ⟶ Y.snd) :
    mapHom F G X Y (tmulHom f g) = tmulHom (F.map f) (G.map g) := rfl

theorem mapHom_comp {X Y Z : BoxProd k C D} (x : X ⟶ Y) (y : Y ⟶ Z) :
    mapHom F G X Z (x ≫ y) = mapHom F G X Y x ≫ mapHom F G Y Z y := by
  induction x using induction_on_homogeneous with
  | zero => rw [Limits.zero_comp, map_zero, map_zero, Limits.zero_comp]
  | add x x' hx hx' => rw [Preadditive.add_comp, map_add, map_add, Preadditive.add_comp, hx, hx']
  | tmul a b f g hf hg =>
    induction y using induction_on_homogeneous with
    | zero => rw [Limits.comp_zero, map_zero, map_zero, Limits.comp_zero]
    | add y y' hy hy' => rw [Preadditive.comp_add, map_add, map_add, Preadditive.comp_add, hy, hy']
    | tmul c d h l hh hl =>
      change mapHom F G X Z (tmulHom f g ≫ tmulHom h l) =
        mapHom F G X Y (tmulHom f g) ≫ mapHom F G Y Z (tmulHom h l)
      rw [mapHom_tmul, mapHom_tmul, tmulHom_comp_tmulHom hf g h hl,
        tmulHom_comp_tmulHom (F.map_mem hf) _ _ (G.map_mem hl), map_zsmul, mapHom_tmul]
      simp only [Superfunctor.map, Functor.map_comp]

theorem mapHom_proj {X Y : BoxProd k C D} (p : ZMod 2) (x : X ⟶ Y) :
    mapHom F G X Y ((homObj k X Y).proj p x) =
      (homObj k (mapObj F G X) (mapObj F G Y)).proj p (mapHom F G X Y x) := by
  induction x using induction_on_homogeneous with
  | zero => simp only [map_zero]
  | add x x' hx hx' => simp only [map_add, hx, hx']
  | tmul a b f g hf hg =>
    have h := SVec.proj_apply_of_mem_part (homObj k (mapObj F G X) (mapObj F G Y)) (p := p)
      (tmul_mem_part (X := mapObj F G X) (Y := mapObj F G Y) (F.map_mem hf) (G.map_mem hg))
    rw [SVec.proj_apply_of_mem_part _ (tmul_mem_part hf hg)]
    change _ = (homObj k (mapObj F G X) (mapObj F G Y)).proj p (F.map f ⊗ₜ[k] G.map g)
    rw [h]
    split_ifs
    · rfl
    · exact map_zero _

/-- **Brundan–Ellis, after Example 1.2.** The superfunctor `F ⊠ G : C ⊠ D → C' ⊠ D'`,
`(λ, μ) ↦ (F λ, G μ)`, `f ⊗ g ↦ F f ⊗ G g`. -/
def map : Superfunctor k (BoxProd k C D) (BoxProd k C' D') :=
  Superfunctor.ofLinearMaps (mapObj F G) (mapHom F G)
    (fun X => by
      change mapHom F G X X (tmulHom (𝟙 X.fst) (𝟙 X.snd)) = tmulHom (𝟙 _) (𝟙 _)
      rw [mapHom_tmul, Superfunctor.map, Superfunctor.map, F.toFunctor.map_id,
        G.toFunctor.map_id])
    (fun x y => mapHom_comp F G x y)
    (fun {X Y p x} hx => by
      change mapHom F G X Y x ∈ (homObj k (mapObj F G X) (mapObj F G Y)).part p
      rw [SVec.mem_part_iff, ← mapHom_proj, (SVec.mem_part_iff _).1 hx])

@[simp] theorem map_obj (X : BoxProd k C D) : (map F G).obj X = ⟨F.obj X.fst, G.obj X.snd⟩ :=
  rfl

theorem map_map {X Y : BoxProd k C D} (x : X ⟶ Y) : (map F G).map x = mapHom F G X Y x := rfl

@[simp] theorem map_tmulHom {X Y : BoxProd k C D} (f : X.fst ⟶ Y.fst) (g : X.snd ⟶ Y.snd) :
    (map F G).map (tmulHom f g) = tmulHom (F.map f) (G.map g) := rfl

end Map

/-- **Brundan–Ellis, after Example 1.2.** `id ⊠ id = id`. -/
theorem map_id : map (Superfunctor.id k C) (Superfunctor.id k D) = Superfunctor.id k _ :=
  superfunctor_ext (fun _ => rfl) fun _ _ _ _ => HEq.rfl

/-- **Brundan–Ellis, after Example 1.2.** `⊠` is compatible with composition of
superfunctors: `(F ≫ F') ⊠ (G ≫ G') = (F ⊠ G) ≫ (F' ⊠ G')`. -/
theorem map_comp (F : Superfunctor k C C') (F' : Superfunctor k C' C'')
    (G : Superfunctor k D D') (G' : Superfunctor k D' D'') :
    map (F.comp F') (G.comp G') = (map F G).comp (map F' G') :=
  superfunctor_ext (fun _ => rfl) fun _ _ _ _ => HEq.rfl

end BoxProd

end StringDiagrams

end
