import StringDiagrams.Super.BoxProduct
import StringDiagrams.Super.PiCat
import StringDiagrams.Super.Superalgebra

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
* `BoxUnit k`: the unit supercategory `I` (one object, endomorphism superalgebra `k` in even
  parity), with its object in an arbitrary universe.
* `BoxProd.assoc C D E : (C ⊠ D) ⊠ E → C ⊠ (D ⊠ E)`, `(f ⊗ g) ⊗ h ↦ f ⊗ (g ⊗ h)`, with inverse
  `BoxProd.assocInv` (`assoc_comp_assocInv`, `assocInv_comp_assoc`), natural in the three
  arguments (`map_map_comp_assoc`).
* `BoxProd.lunit C : I ⊠ C → C`, `r ⊗ f ↦ r f`, and `BoxProd.runit C : C ⊠ I → C`,
  `f ⊗ r ↦ r f`, with inverses `lunitInv`, `runitInv` (`f ↦ 1 ⊗ f`, `f ↦ f ⊗ 1`), natural
  (`map_comp_lunit`, `map_comp_runit`).

These are isomorphisms of supercategories (superfunctors with inverse superfunctors), as in
the paper, where the coherence maps of the monoidal category `SCat` are "obvious". The
morphism modules of all supercategories involved live in the universe of `k`, as for `BoxProd`.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory TensorProduct

universe w u w₁ w₂ w₃ w₄ w₅ w₆

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

/-- A linear map on morphism superspaces commuting with the parity projections preserves
parities. -/
theorem mem_parity_of_proj {X Y : A} {X' Y' : E} (φ : (X ⟶ Y) →ₗ[k] (X' ⟶ Y'))
    (h : ∀ (p : ZMod 2) (x : X ⟶ Y), φ (proj k p x) = proj k p (φ x)) {p : ZMod 2} {x : X ⟶ Y}
    (hx : x ∈ parity (R := k) X Y p) : φ x ∈ parity (R := k) X' Y' p := by
  rw [mem_iff_proj] at hx ⊢
  rw [← h, hx]

/-- A linear map sending a homogeneous `x` to a morphism of the same parity commutes with the
parity projections at `x`. -/
theorem map_proj_of_mem {X Y : A} {X' Y' : E} (φ : (X ⟶ Y) →ₗ[k] (X' ⟶ Y')) {q : ZMod 2}
    {x : X ⟶ Y} (hx : x ∈ parity (R := k) X Y q) (hφ : φ x ∈ parity (R := k) X' Y' q)
    (p : ZMod 2) : φ (proj k p x) = proj k p (φ x) := by
  by_cases h : q = p
  · subst h; rw [proj_of_mem hx, proj_of_mem hφ]
  · rw [proj_of_mem_ne hx h, proj_of_mem_ne hφ h, map_zero]

end Supercategory.Superfunctor

/-! ## The unit supercategory -/

/-- **Brundan–Ellis, after Example 1.2.** The unit supercategory `I`: one object, with
endomorphism superalgebra `k` concentrated in even parity. This is the supercategory
`UnitSupercat k` of `StringDiagrams.Super.Superalgebra`, with its object in an arbitrary
universe `w` (so that it is an object of `SCat` in every universe). -/
@[nolint unusedArguments]
def BoxUnit (k : Type u) [CommRing k] : Type w := PUnit.{w + 1}

namespace BoxUnit

/-- The only object. -/
def star : BoxUnit.{w, u} k := PUnit.unit

instance : Category.{u} (BoxUnit.{w, u} k) where
  Hom _ _ := k
  id _ := (1 : k)
  comp f g := (g : k) * f
  id_comp f := mul_one (f : k)
  comp_id f := one_mul (f : k)
  assoc f g h := (mul_assoc (h : k) g f).symm

instance : Preadditive (BoxUnit.{w, u} k) where
  homGroup _ _ := inferInstanceAs (AddCommGroup k)
  add_comp _ _ _ f f' g := mul_add (g : k) f f'
  comp_add _ _ _ f g g' := add_mul (g : k) g' f

instance : Linear k (BoxUnit.{w, u} k) where
  homModule _ _ := inferInstanceAs (Module k k)
  smul_comp _ _ _ r f g := mul_smul_comm r (g : k) f
  comp_smul _ _ _ f r g := smul_mul_assoc r (g : k) f

instance : Supercategory k (BoxUnit.{w, u} k) where
  parity _ _ p := trivialGrading k p
  isInternal _ _ := isInternal_trivialGrading
  id_mem _ := by rw [trivialGrading_zero]; trivial
  comp_mem {_ _ _ p q f g} hf hg := by
    rw [add_comm]; exact SetLike.GradedMul.mul_mem (A := trivialGrading k) hg hf

theorem comp_eq {X Y Z : BoxUnit.{w, u} k} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g : k) = (g : k) * (f : k) := rfl

theorem id_eq (X : BoxUnit.{w, u} k) : (𝟙 X : k) = 1 := rfl

/-- Every morphism of `I` is even. -/
theorem mem_parity_zero {X Y : BoxUnit.{w, u} k} (f : X ⟶ Y) : f ∈ parity (R := k) X Y 0 := by
  change (f : k) ∈ trivialGrading k 0
  rw [trivialGrading_zero]; trivial

end BoxUnit

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

/-- `f ⊗ g` has parity `|f| + |g|`. -/
theorem tmulHom_mem_parity {X Y : BoxProd k C D} {p q : ZMod 2} {f : X.fst ⟶ Y.fst}
    {g : X.snd ⟶ Y.snd} (hf : f ∈ parity (R := k) X.fst Y.fst p)
    (hg : g ∈ parity (R := k) X.snd Y.snd q) : tmulHom f g ∈ parity (R := k) X Y (p + q) :=
  tmul_mem_parity hf hg

theorem tmulHom_zsmul_left {X Y : BoxProd k C D} (n : ℤ) (f : X.fst ⟶ Y.fst)
    (g : X.snd ⟶ Y.snd) : tmulHom (n • f) g = n • tmulHom f g := by
  rw [← Int.cast_smul_eq_zsmul k, ← Int.cast_smul_eq_zsmul k, tmulHom_smul_left]

theorem tmulHom_zsmul_right {X Y : BoxProd k C D} (n : ℤ) (f : X.fst ⟶ Y.fst)
    (g : X.snd ⟶ Y.snd) : tmulHom f (n • g) = n • tmulHom f g := by
  rw [← Int.cast_smul_eq_zsmul k, ← Int.cast_smul_eq_zsmul k, tmulHom_smul_right]

/-! ## The associator `(C ⊠ D) ⊠ E ≅ C ⊠ (D ⊠ E)` -/

section Assoc

variable {E : Type w₅} [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  {E' : Type w₆} [Category.{u} E'] [Preadditive E'] [Linear k E'] [Supercategory k E']

/-- Induction on `Hom(((X₁, X₂), X₃), ((Y₁, Y₂), Y₃))` with homogeneous generators
`(f ⊗ g) ⊗ h`. -/
theorem induction_on_homogeneous₃ {X Y : BoxProd k (BoxProd k C D) E} {P : (X ⟶ Y) → Prop}
    (x : X ⟶ Y) (zero : P 0)
    (tmul : ∀ (a b c : ZMod 2) (f : X.fst.fst ⟶ Y.fst.fst) (g : X.fst.snd ⟶ Y.fst.snd)
      (h : X.snd ⟶ Y.snd), f ∈ parity (R := k) _ _ a → g ∈ parity (R := k) _ _ b →
      h ∈ parity (R := k) _ _ c → P (tmulHom (tmulHom (X := X.fst) (Y := Y.fst) f g) h))
    (add : ∀ x y, P x → P y → P (x + y)) : P x := by
  induction x using induction_on_homogeneous with
  | zero => exact zero
  | add x y hx hy => exact add x y hx hy
  | tmul p c y h hy hh =>
    clear hy
    induction y using induction_on_homogeneous with
    | zero => convert zero using 1; exact zero_tmul _ _
    | add y y' h₁ h₂ => convert add _ _ h₁ h₂ using 1; exact add_tmul _ _ _
    | tmul a b f g hf hg => exact tmul a b c f g h hf hg hh

/-- Induction on `Hom((X₁, (X₂, X₃)), (Y₁, (Y₂, Y₃)))` with homogeneous generators
`f ⊗ (g ⊗ h)`. -/
theorem induction_on_homogeneous₃' {X Y : BoxProd k C (BoxProd k D E)} {P : (X ⟶ Y) → Prop}
    (x : X ⟶ Y) (zero : P 0)
    (tmul : ∀ (a b c : ZMod 2) (f : X.fst ⟶ Y.fst) (g : X.snd.fst ⟶ Y.snd.fst)
      (h : X.snd.snd ⟶ Y.snd.snd), f ∈ parity (R := k) _ _ a → g ∈ parity (R := k) _ _ b →
      h ∈ parity (R := k) _ _ c → P (tmulHom (X := X) (Y := Y) f (tmulHom (X := X.snd) (Y := Y.snd) g h)))
    (add : ∀ x y, P x → P y → P (x + y)) : P x := by
  induction x using induction_on_homogeneous with
  | zero => exact zero
  | add x y hx hy => exact add x y hx hy
  | tmul a p f y hf hy =>
    clear hy
    induction y using induction_on_homogeneous with
    | zero => convert zero using 1; exact tmul_zero _ _
    | add y y' h₁ h₂ => convert add _ _ h₁ h₂ using 1; exact tmul_add _ _ _
    | tmul b c g h hg hh => exact tmul a b c f g h hf hg hh

variable (C D E) in
/-- The objects `(λ, (μ, ν))` of `C ⊠ (D ⊠ E)`. -/
abbrev assocObj (X : BoxProd k (BoxProd k C D) E) : BoxProd k C (BoxProd k D E) :=
  ⟨X.fst.fst, ⟨X.fst.snd, X.snd⟩⟩

variable (C D E) in
/-- The objects `((λ, μ), ν)` of `(C ⊠ D) ⊠ E`. -/
abbrev assocInvObj (X : BoxProd k C (BoxProd k D E)) : BoxProd k (BoxProd k C D) E :=
  ⟨⟨X.fst, X.snd.fst⟩, X.snd.snd⟩

/-- `(f ⊗ g) ⊗ h ↦ f ⊗ (g ⊗ h)` on morphism superspaces. -/
def assocHom (X Y : BoxProd k (BoxProd k C D) E) :
    (X ⟶ Y) →ₗ[k] (assocObj C D E X ⟶ assocObj C D E Y) :=
  (TensorProduct.assoc k (X.fst.fst ⟶ Y.fst.fst) (X.fst.snd ⟶ Y.fst.snd)
    (X.snd ⟶ Y.snd)).toLinearMap

/-- `f ⊗ (g ⊗ h) ↦ (f ⊗ g) ⊗ h` on morphism superspaces. -/
def assocInvHom (X Y : BoxProd k C (BoxProd k D E)) :
    (X ⟶ Y) →ₗ[k] (assocInvObj C D E X ⟶ assocInvObj C D E Y) :=
  (TensorProduct.assoc k (X.fst ⟶ Y.fst) (X.snd.fst ⟶ Y.snd.fst)
    (X.snd.snd ⟶ Y.snd.snd)).symm.toLinearMap

theorem assocHom_tmul {X Y : BoxProd k (BoxProd k C D) E} (f : X.fst.fst ⟶ Y.fst.fst)
    (g : X.fst.snd ⟶ Y.fst.snd) (h : X.snd ⟶ Y.snd) :
    assocHom X Y (tmulHom (tmulHom (X := X.fst) (Y := Y.fst) f g) h) =
      tmulHom (X := assocObj C D E X) (Y := assocObj C D E Y) f
        (tmulHom (X := (assocObj C D E X).snd) (Y := (assocObj C D E Y).snd) g h) :=
  TensorProduct.assoc_tmul f g h

theorem assocInvHom_tmul {X Y : BoxProd k C (BoxProd k D E)} (f : X.fst ⟶ Y.fst)
    (g : X.snd.fst ⟶ Y.snd.fst) (h : X.snd.snd ⟶ Y.snd.snd) :
    assocInvHom X Y (tmulHom (X := X) (Y := Y) f (tmulHom (X := X.snd) (Y := Y.snd) g h)) =
      tmulHom (tmulHom (X := (assocInvObj C D E X).fst) (Y := (assocInvObj C D E Y).fst) f g) h :=
  TensorProduct.assoc_symm_tmul f g h

theorem assocHom_assocInvHom {X Y : BoxProd k C (BoxProd k D E)} (x : X ⟶ Y) :
    assocHom (assocInvObj C D E X) (assocInvObj C D E Y) (assocInvHom X Y x) = x :=
  (TensorProduct.assoc k _ _ _).apply_symm_apply x

theorem assocInvHom_assocHom {X Y : BoxProd k (BoxProd k C D) E} (x : X ⟶ Y) :
    assocInvHom (assocObj C D E X) (assocObj C D E Y) (assocHom X Y x) = x :=
  (TensorProduct.assoc k _ _ _).symm_apply_apply x

theorem assocInvHom_assocHom' {X Y : BoxProd k C (BoxProd k D E)}
    (x : assocInvObj C D E X ⟶ assocInvObj C D E Y) :
    assocInvHom X Y (assocHom (assocInvObj C D E X) (assocInvObj C D E Y) x) = x :=
  (TensorProduct.assoc k _ _ _).symm_apply_apply x

/-- `(f ⊗ g) ⊗ h` has parity `|f| + |g| + |h|`. -/
theorem tmul_tmul_mem_parity {X Y : BoxProd k (BoxProd k C D) E} {a b c : ZMod 2}
    {f : X.fst.fst ⟶ Y.fst.fst} {g : X.fst.snd ⟶ Y.fst.snd} {h : X.snd ⟶ Y.snd}
    (hf : f ∈ parity (R := k) _ _ a) (hg : g ∈ parity (R := k) _ _ b)
    (hh : h ∈ parity (R := k) _ _ c) :
    tmulHom (tmulHom (X := X.fst) (Y := Y.fst) f g) h ∈ parity (R := k) X Y (a + b + c) :=
  tmul_mem_parity (tmul_mem_parity (X := X.fst) (Y := Y.fst) hf hg) hh

/-- `f ⊗ (g ⊗ h)` has parity `|f| + |g| + |h|`. -/
theorem tmul_tmul_mem_parity' {X Y : BoxProd k C (BoxProd k D E)} {a b c : ZMod 2}
    {f : X.fst ⟶ Y.fst} {g : X.snd.fst ⟶ Y.snd.fst} {h : X.snd.snd ⟶ Y.snd.snd}
    (hf : f ∈ parity (R := k) _ _ a) (hg : g ∈ parity (R := k) _ _ b)
    (hh : h ∈ parity (R := k) _ _ c) :
    tmulHom (X := X) (Y := Y) f (tmulHom (X := X.snd) (Y := Y.snd) g h) ∈
      parity (R := k) X Y (a + b + c) := by
  rw [add_assoc]; exact tmul_mem_parity hf (tmul_mem_parity (X := X.snd) (Y := Y.snd) hg hh)

theorem assocHom_comp {X Y Z : BoxProd k (BoxProd k C D) E} (x : X ⟶ Y) (y : Y ⟶ Z) :
    assocHom X Z (x ≫ y) = assocHom X Y x ≫ assocHom Y Z y := by
  induction x using induction_on_homogeneous₃ with
  | zero => rw [Limits.zero_comp, map_zero, map_zero, Limits.zero_comp]
  | add x x' hx hx' => rw [Preadditive.add_comp, map_add, map_add, Preadditive.add_comp, hx, hx']
  | tmul a b c f g h hf hg hh =>
    induction y using induction_on_homogeneous₃ with
    | zero => rw [Limits.comp_zero, map_zero, map_zero, Limits.comp_zero]
    | add y y' hy hy' => rw [Preadditive.comp_add, map_add, map_add, Preadditive.comp_add, hy, hy']
    | tmul a' b' c' f' g' h' hf' hg' hh' =>
      rw [tmulHom_comp_tmulHom (tmulHom_mem_parity (X := X.fst) (Y := Y.fst) hf hg) _ _ hh',
        tmulHom_comp_tmulHom hf _ _ hg', assocHom_tmul, assocHom_tmul,
        tmulHom_comp_tmulHom (X := assocObj C D E X) (Y := assocObj C D E Y)
          (Z := assocObj C D E Z) hf _ _ (tmulHom_mem_parity (X := (assocObj C D E Y).snd) (Y := (assocObj C D E Z).snd) hg' hh'),
        tmulHom_comp_tmulHom (X := (assocObj C D E X).snd) (Y := (assocObj C D E Y).snd)
          (Z := (assocObj C D E Z).snd) hg _ _ hh']
      rw [tmulHom_zsmul_left, map_zsmul, map_zsmul, assocHom_tmul, tmulHom_zsmul_right, smul_smul,
        smul_smul, koszulSign_add_left, koszulSign_add_right]
      congr 1
      ring

theorem assocHom_proj {X Y : BoxProd k (BoxProd k C D) E} (p : ZMod 2) (x : X ⟶ Y) :
    assocHom X Y (proj k p x) = proj k p (assocHom X Y x) := by
  induction x using induction_on_homogeneous₃ with
  | zero => simp only [map_zero]
  | add x x' hx hx' => simp only [map_add, hx, hx']
  | tmul a b c f g h hf hg hh =>
    refine Superfunctor.map_proj_of_mem _ (tmul_tmul_mem_parity hf hg hh) ?_ p
    rw [assocHom_tmul]
    exact tmul_tmul_mem_parity' hf hg hh

theorem assocInvHom_comp {X Y Z : BoxProd k C (BoxProd k D E)} (x : X ⟶ Y) (y : Y ⟶ Z) :
    assocInvHom X Z (x ≫ y) = assocInvHom X Y x ≫ assocInvHom Y Z y := by
  have h := assocHom_comp (assocInvHom X Y x) (assocInvHom Y Z y)
  rw [assocHom_assocInvHom, assocHom_assocInvHom] at h
  rw [← h, assocInvHom_assocHom']

theorem assocInvHom_proj {X Y : BoxProd k C (BoxProd k D E)} (p : ZMod 2) (x : X ⟶ Y) :
    assocInvHom X Y (proj k p x) = proj k p (assocInvHom X Y x) := by
  have h := assocHom_proj p (assocInvHom X Y x)
  rw [assocHom_assocInvHom] at h
  rw [← h, assocInvHom_assocHom']

variable (C D E) in
/-- **Brundan–Ellis, after Example 1.2.** The associator superfunctor
`(C ⊠ D) ⊠ E → C ⊠ (D ⊠ E)`, `((λ, μ), ν) ↦ (λ, (μ, ν))`, `(f ⊗ g) ⊗ h ↦ f ⊗ (g ⊗ h)`. -/
def assoc : Superfunctor k (BoxProd k (BoxProd k C D) E) (BoxProd k C (BoxProd k D E)) :=
  Superfunctor.ofLinearMaps (assocObj C D E) assocHom
    (fun X => assocHom_tmul (𝟙 X.fst.fst) (𝟙 X.fst.snd) (𝟙 X.snd)) assocHom_comp
    (Superfunctor.mem_parity_of_proj _ fun p x => assocHom_proj p x)

variable (C D E) in
/-- The inverse `C ⊠ (D ⊠ E) → (C ⊠ D) ⊠ E` of the associator. -/
def assocInv : Superfunctor k (BoxProd k C (BoxProd k D E)) (BoxProd k (BoxProd k C D) E) :=
  Superfunctor.ofLinearMaps (assocInvObj C D E) assocInvHom
    (fun X => assocInvHom_tmul (𝟙 X.fst) (𝟙 X.snd.fst) (𝟙 X.snd.snd)) assocInvHom_comp
    (Superfunctor.mem_parity_of_proj _ fun p x => assocInvHom_proj p x)

@[simp] theorem assoc_obj (X : BoxProd k (BoxProd k C D) E) :
    (assoc C D E).obj X = ⟨X.fst.fst, ⟨X.fst.snd, X.snd⟩⟩ := rfl

@[simp] theorem assocInv_obj (X : BoxProd k C (BoxProd k D E)) :
    (assocInv C D E).obj X = ⟨⟨X.fst, X.snd.fst⟩, X.snd.snd⟩ := rfl

@[simp] theorem assoc_map_tmulHom {X Y : BoxProd k (BoxProd k C D) E}
    (f : X.fst.fst ⟶ Y.fst.fst) (g : X.fst.snd ⟶ Y.fst.snd) (h : X.snd ⟶ Y.snd) :
    (assoc C D E).map (tmulHom (tmulHom (X := X.fst) (Y := Y.fst) f g) h) =
      tmulHom (X := assocObj C D E X) (Y := assocObj C D E Y) f
        (tmulHom (X := (assocObj C D E X).snd) (Y := (assocObj C D E Y).snd) g h) :=
  assocHom_tmul f g h

@[simp] theorem assocInv_map_tmulHom {X Y : BoxProd k C (BoxProd k D E)}
    (f : X.fst ⟶ Y.fst) (g : X.snd.fst ⟶ Y.snd.fst) (h : X.snd.snd ⟶ Y.snd.snd) :
    (assocInv C D E).map (tmulHom (X := X) (Y := Y) f (tmulHom (X := X.snd) (Y := Y.snd) g h)) =
      tmulHom (tmulHom (X := (assocInvObj C D E X).fst) (Y := (assocInvObj C D E Y).fst) f g) h :=
  assocInvHom_tmul f g h

/-- The associator is an isomorphism of supercategories: `α ≫ α⁻¹ = id`. -/
theorem assoc_comp_assocInv : (assoc C D E).comp (assocInv C D E) = Superfunctor.id k _ :=
  Superfunctor.ext (CategoryTheory.Functor.hext (fun _ => rfl) fun _ _ x =>
    heq_of_eq (assocInvHom_assocHom x))

/-- The associator is an isomorphism of supercategories: `α⁻¹ ≫ α = id`. -/
theorem assocInv_comp_assoc : (assocInv C D E).comp (assoc C D E) = Superfunctor.id k _ :=
  Superfunctor.ext (CategoryTheory.Functor.hext (fun _ => rfl) fun _ _ x =>
    heq_of_eq (assocHom_assocInvHom x))

/-- **Naturality of the associator**: `((F ⊠ G) ⊠ H) ≫ α = α ≫ (F ⊠ (G ⊠ H))`. -/
theorem map_map_comp_assoc (F : Superfunctor k C C') (G : Superfunctor k D D')
    (H : Superfunctor k E E') :
    (map (map F G) H).comp (assoc C' D' E') = (assoc C D E).comp (map F (map G H)) := by
  refine Superfunctor.ext (CategoryTheory.Functor.hext (fun _ => rfl) fun X Y x => heq_of_eq ?_)
  change assocHom _ _ (mapHom (map F G) H X Y x) = mapHom F (map G H) _ _ (assocHom X Y x)
  induction x using induction_on_homogeneous₃ with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]; rfl
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]; rfl
  | tmul a b c f g h _ _ _ => rfl

end Assoc

/-! ## The unitors `I ⊠ C ≅ C` and `C ⊠ I ≅ C` -/

section Unitors

/-- The linear map `r ⊗ f ↦ r f` on morphism superspaces of `I ⊠ C`. -/
def lunitHom (X Y : BoxProd k (BoxUnit.{w, u} k) C) : (X ⟶ Y) →ₗ[k] (X.snd ⟶ Y.snd) :=
  (TensorProduct.lid k (X.snd ⟶ Y.snd)).toLinearMap

/-- The linear map `f ↦ 1 ⊗ f` on morphism superspaces of `C`. -/
def lunitInvHom (X Y : C) :
    (X ⟶ Y) →ₗ[k] ((⟨BoxUnit.star, X⟩ : BoxProd k (BoxUnit.{w, u} k) C) ⟶ ⟨BoxUnit.star, Y⟩) :=
  (TensorProduct.lid k (X ⟶ Y)).symm.toLinearMap

/-- The linear map `f ⊗ r ↦ r f` on morphism superspaces of `C ⊠ I`. -/
def runitHom (X Y : BoxProd k C (BoxUnit.{w, u} k)) : (X ⟶ Y) →ₗ[k] (X.fst ⟶ Y.fst) :=
  (TensorProduct.rid k (X.fst ⟶ Y.fst)).toLinearMap

/-- The linear map `f ↦ f ⊗ 1` on morphism superspaces of `C`. -/
def runitInvHom (X Y : C) :
    (X ⟶ Y) →ₗ[k] ((⟨X, BoxUnit.star⟩ : BoxProd k C (BoxUnit.{w, u} k)) ⟶ ⟨Y, BoxUnit.star⟩) :=
  (TensorProduct.rid k (X ⟶ Y)).symm.toLinearMap

theorem lunitHom_tmul {X Y : BoxProd k (BoxUnit.{w, u} k) C} (r : X.fst ⟶ Y.fst)
    (f : X.snd ⟶ Y.snd) : lunitHom X Y (tmulHom r f) = (r : k) • f :=
  TensorProduct.lid_tmul f r

theorem lunitInvHom_apply {X Y : C} (f : X ⟶ Y) :
    lunitInvHom.{w} (k := k) X Y f = tmulHom (X := ⟨BoxUnit.star, X⟩) (Y := ⟨BoxUnit.star, Y⟩) (1 : k) f :=
  TensorProduct.lid_symm_apply f

theorem runitHom_tmul {X Y : BoxProd k C (BoxUnit.{w, u} k)} (f : X.fst ⟶ Y.fst)
    (r : X.snd ⟶ Y.snd) : runitHom X Y (tmulHom f r) = (r : k) • f :=
  TensorProduct.rid_tmul f r

theorem runitInvHom_apply {X Y : C} (f : X ⟶ Y) :
    runitInvHom.{w} (k := k) X Y f = tmulHom (X := ⟨X, BoxUnit.star⟩) (Y := ⟨Y, BoxUnit.star⟩) f (1 : k) :=
  TensorProduct.rid_symm_apply f

theorem lunitHom_lunitInvHom {X Y : C} (f : X ⟶ Y) : lunitHom _ _ (lunitInvHom.{w} (k := k) X Y f) = f :=
  (TensorProduct.lid k (X ⟶ Y)).apply_symm_apply f

theorem lunitInvHom_lunitHom' {X Y : C}
    (x : (⟨BoxUnit.star, X⟩ : BoxProd k (BoxUnit.{w, u} k) C) ⟶ ⟨BoxUnit.star, Y⟩) :
    lunitInvHom X Y (lunitHom _ _ x) = x :=
  (TensorProduct.lid k (X ⟶ Y)).symm_apply_apply x

theorem lunitInvHom_lunitHom {X Y : BoxProd k (BoxUnit.{w, u} k) C} (x : X ⟶ Y) :
    lunitInvHom X.snd Y.snd (lunitHom X Y x) = x :=
  (TensorProduct.lid k (X.snd ⟶ Y.snd)).symm_apply_apply x

theorem runitHom_runitInvHom {X Y : C} (f : X ⟶ Y) : runitHom _ _ (runitInvHom.{w} (k := k) X Y f) = f :=
  (TensorProduct.rid k (X ⟶ Y)).apply_symm_apply f

theorem runitInvHom_runitHom' {X Y : C}
    (x : (⟨X, BoxUnit.star⟩ : BoxProd k C (BoxUnit.{w, u} k)) ⟶ ⟨Y, BoxUnit.star⟩) :
    runitInvHom X Y (runitHom _ _ x) = x :=
  (TensorProduct.rid k (X ⟶ Y)).symm_apply_apply x

theorem runitInvHom_runitHom {X Y : BoxProd k C (BoxUnit.{w, u} k)} (x : X ⟶ Y) :
    runitInvHom X.fst Y.fst (runitHom X Y x) = x :=
  (TensorProduct.rid k (X.fst ⟶ Y.fst)).symm_apply_apply x

theorem lunitHom_comp {X Y Z : BoxProd k (BoxUnit.{w, u} k) C} (x : X ⟶ Y) (y : Y ⟶ Z) :
    lunitHom X Z (x ≫ y) = lunitHom X Y x ≫ lunitHom Y Z y := by
  induction x using induction_on_homogeneous with
  | zero => rw [Limits.zero_comp, map_zero, map_zero, Limits.zero_comp]
  | add x x' hx hx' => rw [Preadditive.add_comp, map_add, map_add, Preadditive.add_comp, hx, hx']
  | tmul a b r f _ _ =>
    induction y using induction_on_homogeneous with
    | zero => rw [Limits.comp_zero, map_zero, map_zero, Limits.comp_zero]
    | add y y' hy hy' => rw [Preadditive.comp_add, map_add, map_add, Preadditive.comp_add, hy, hy']
    | tmul c d s g _ hg =>
      rw [← tmulHom_def, ← tmulHom_def, tmulHom_comp_tmulHom (BoxUnit.mem_parity_zero r) f s hg,
        koszulSign_zero_left, one_smul, lunitHom_tmul, lunitHom_tmul, lunitHom_tmul,
        Linear.smul_comp, Linear.comp_smul, smul_smul, BoxUnit.comp_eq, mul_comm]

theorem runitHom_comp {X Y Z : BoxProd k C (BoxUnit.{w, u} k)} (x : X ⟶ Y) (y : Y ⟶ Z) :
    runitHom X Z (x ≫ y) = runitHom X Y x ≫ runitHom Y Z y := by
  induction x using induction_on_homogeneous with
  | zero => rw [Limits.zero_comp, map_zero, map_zero, Limits.zero_comp]
  | add x x' hx hx' => rw [Preadditive.add_comp, map_add, map_add, Preadditive.add_comp, hx, hx']
  | tmul a b f r hf _ =>
    induction y using induction_on_homogeneous with
    | zero => rw [Limits.comp_zero, map_zero, map_zero, Limits.comp_zero]
    | add y y' hy hy' => rw [Preadditive.comp_add, map_add, map_add, Preadditive.comp_add, hy, hy']
    | tmul c d g s _ _ =>
      rw [← tmulHom_def, ← tmulHom_def, tmulHom_comp_tmulHom hf r g (BoxUnit.mem_parity_zero s),
        koszulSign_zero_right, one_smul, runitHom_tmul, runitHom_tmul, runitHom_tmul,
        Linear.smul_comp, Linear.comp_smul, smul_smul, BoxUnit.comp_eq, mul_comm]

theorem lunitHom_proj {X Y : BoxProd k (BoxUnit.{w, u} k) C} (p : ZMod 2) (x : X ⟶ Y) :
    lunitHom X Y (proj k p x) = proj k p (lunitHom X Y x) := by
  induction x using induction_on_homogeneous with
  | zero => simp only [map_zero]
  | add x x' hx hx' => simp only [map_add, hx, hx']
  | tmul a b r f _ hf =>
    have h := tmulHom_mem_parity (X := X) (Y := Y) (BoxUnit.mem_parity_zero r) hf
    rw [zero_add] at h
    refine Superfunctor.map_proj_of_mem _ h ?_ p
    rw [lunitHom_tmul]
    exact Submodule.smul_mem _ _ hf

theorem runitHom_proj {X Y : BoxProd k C (BoxUnit.{w, u} k)} (p : ZMod 2) (x : X ⟶ Y) :
    runitHom X Y (proj k p x) = proj k p (runitHom X Y x) := by
  induction x using induction_on_homogeneous with
  | zero => simp only [map_zero]
  | add x x' hx hx' => simp only [map_add, hx, hx']
  | tmul a b f r hf _ =>
    have h := tmulHom_mem_parity (X := X) (Y := Y) hf (BoxUnit.mem_parity_zero r)
    rw [add_zero] at h
    refine Superfunctor.map_proj_of_mem _ h ?_ p
    rw [runitHom_tmul]
    exact Submodule.smul_mem _ _ hf

theorem lunitInvHom_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    lunitInvHom.{w} (k := k) X Z (f ≫ g) = lunitInvHom X Y f ≫ lunitInvHom Y Z g := by
  have h := lunitHom_comp (lunitInvHom.{w} (k := k) X Y f) (lunitInvHom Y Z g)
  rw [lunitHom_lunitInvHom, lunitHom_lunitInvHom] at h
  rw [← h, lunitInvHom_lunitHom']

theorem runitInvHom_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    runitInvHom.{w} (k := k) X Z (f ≫ g) = runitInvHom X Y f ≫ runitInvHom Y Z g := by
  have h := runitHom_comp (runitInvHom.{w} (k := k) X Y f) (runitInvHom Y Z g)
  rw [runitHom_runitInvHom, runitHom_runitInvHom] at h
  rw [← h, runitInvHom_runitHom']

theorem lunitInvHom_proj {X Y : C} (p : ZMod 2) (f : X ⟶ Y) :
    lunitInvHom.{w} (k := k) X Y (proj k p f) = proj k p (lunitInvHom X Y f) := by
  have h := lunitHom_proj p (lunitInvHom.{w} (k := k) X Y f)
  rw [lunitHom_lunitInvHom] at h
  rw [← h, lunitInvHom_lunitHom']

theorem runitInvHom_proj {X Y : C} (p : ZMod 2) (f : X ⟶ Y) :
    runitInvHom.{w} (k := k) X Y (proj k p f) = proj k p (runitInvHom X Y f) := by
  have h := runitHom_proj p (runitInvHom.{w} (k := k) X Y f)
  rw [runitHom_runitInvHom] at h
  rw [← h, runitInvHom_runitHom']

variable (C) in
/-- **Brundan–Ellis, after Example 1.2.** The left unitor `I ⊠ C → C`, `(⋆, λ) ↦ λ`,
`r ⊗ f ↦ r f`. -/
def lunit : Superfunctor k (BoxProd k (BoxUnit.{w, u} k) C) C :=
  Superfunctor.ofLinearMaps (fun X => X.snd) lunitHom
    (fun X => (lunitHom_tmul (𝟙 X.fst) (𝟙 X.snd)).trans (one_smul k _)) lunitHom_comp
    (Superfunctor.mem_parity_of_proj _ fun p x => lunitHom_proj p x)

variable (C) in
/-- The inverse `C → I ⊠ C`, `λ ↦ (⋆, λ)`, `f ↦ 1 ⊗ f`, of the left unitor. -/
def lunitInv : Superfunctor k C (BoxProd k (BoxUnit.{w, u} k) C) :=
  Superfunctor.ofLinearMaps (fun X => ⟨BoxUnit.star, X⟩) lunitInvHom.{w}
    (fun X => lunitInvHom_apply (𝟙 X)) lunitInvHom_comp
    (Superfunctor.mem_parity_of_proj _ fun p x => lunitInvHom_proj.{w} p x)

variable (C) in
/-- **Brundan–Ellis, after Example 1.2.** The right unitor `C ⊠ I → C`, `(λ, ⋆) ↦ λ`,
`f ⊗ r ↦ r f`. -/
def runit : Superfunctor k (BoxProd k C (BoxUnit.{w, u} k)) C :=
  Superfunctor.ofLinearMaps (fun X => X.fst) runitHom
    (fun X => (runitHom_tmul (𝟙 X.fst) (𝟙 X.snd)).trans (one_smul k _)) runitHom_comp
    (Superfunctor.mem_parity_of_proj _ fun p x => runitHom_proj p x)

variable (C) in
/-- The inverse `C → C ⊠ I`, `λ ↦ (λ, ⋆)`, `f ↦ f ⊗ 1`, of the right unitor. -/
def runitInv : Superfunctor k C (BoxProd k C (BoxUnit.{w, u} k)) :=
  Superfunctor.ofLinearMaps (fun X => ⟨X, BoxUnit.star⟩) runitInvHom.{w}
    (fun X => runitInvHom_apply (𝟙 X)) runitInvHom_comp
    (Superfunctor.mem_parity_of_proj _ fun p x => runitInvHom_proj.{w} p x)

@[simp] theorem lunit_map_tmulHom {X Y : BoxProd k (BoxUnit.{w, u} k) C} (r : X.fst ⟶ Y.fst)
    (f : X.snd ⟶ Y.snd) : (lunit C).map (tmulHom r f) = (r : k) • f :=
  lunitHom_tmul r f

@[simp] theorem runit_map_tmulHom {X Y : BoxProd k C (BoxUnit.{w, u} k)} (f : X.fst ⟶ Y.fst)
    (r : X.snd ⟶ Y.snd) : (runit C).map (tmulHom f r) = (r : k) • f :=
  runitHom_tmul f r

/-- The left unitor is an isomorphism of supercategories: `λ ≫ λ⁻¹ = id`. -/
theorem lunit_comp_lunitInv : (lunit.{w} C).comp (lunitInv C) = Superfunctor.id k _ :=
  Superfunctor.ext (CategoryTheory.Functor.hext (fun _ => rfl) fun _ _ x =>
    heq_of_eq (lunitInvHom_lunitHom x))

/-- The left unitor is an isomorphism of supercategories: `λ⁻¹ ≫ λ = id`. -/
theorem lunitInv_comp_lunit : (lunitInv.{w} C).comp (lunit C) = Superfunctor.id k _ :=
  Superfunctor.ext (CategoryTheory.Functor.hext (fun _ => rfl) fun _ _ x =>
    heq_of_eq (lunitHom_lunitInvHom x))

/-- The right unitor is an isomorphism of supercategories: `ρ ≫ ρ⁻¹ = id`. -/
theorem runit_comp_runitInv : (runit.{w} C).comp (runitInv C) = Superfunctor.id k _ :=
  Superfunctor.ext (CategoryTheory.Functor.hext (fun _ => rfl) fun _ _ x =>
    heq_of_eq (runitInvHom_runitHom x))

/-- The right unitor is an isomorphism of supercategories: `ρ⁻¹ ≫ ρ = id`. -/
theorem runitInv_comp_runit : (runitInv.{w} C).comp (runit C) = Superfunctor.id k _ :=
  Superfunctor.ext (CategoryTheory.Functor.hext (fun _ => rfl) fun _ _ x =>
    heq_of_eq (runitHom_runitInvHom x))

/-- **Naturality of the left unitor**: `(id_I ⊠ F) ≫ λ = λ ≫ F`. -/
theorem map_comp_lunit (F : Superfunctor k C C') :
    (map (Superfunctor.id k (BoxUnit.{w, u} k)) F).comp (lunit C') = (lunit C).comp F := by
  refine Superfunctor.ext (CategoryTheory.Functor.hext (fun _ => rfl) fun X Y x => heq_of_eq ?_)
  change lunitHom _ _ (mapHom _ F X Y x) = F.map (lunitHom X Y x)
  induction x using induction_on_homogeneous with
  | zero => rw [map_zero, map_zero, map_zero]; exact (F.toFunctor.map_zero _ _).symm
  | add x y hx hy =>
    rw [map_add, map_add, map_add, hx, hy]; exact (F.toFunctor.map_add).symm
  | tmul a b r f _ _ =>
    rw [← tmulHom_def, mapHom_tmul, lunitHom_tmul, lunitHom_tmul]
    exact (F.toFunctor.map_smul _ _).symm

/-- **Naturality of the right unitor**: `(F ⊠ id_I) ≫ ρ = ρ ≫ F`. -/
theorem map_comp_runit (F : Superfunctor k C C') :
    (map F (Superfunctor.id k (BoxUnit.{w, u} k))).comp (runit C') = (runit C).comp F := by
  refine Superfunctor.ext (CategoryTheory.Functor.hext (fun _ => rfl) fun X Y x => heq_of_eq ?_)
  change runitHom _ _ (mapHom F _ X Y x) = F.map (runitHom X Y x)
  induction x using induction_on_homogeneous with
  | zero => rw [map_zero, map_zero, map_zero]; exact (F.toFunctor.map_zero _ _).symm
  | add x y hx hy =>
    rw [map_add, map_add, map_add, hx, hy]; exact (F.toFunctor.map_add).symm
  | tmul a b f r _ _ =>
    rw [← tmulHom_def, mapHom_tmul, runitHom_tmul, runitHom_tmul]
    exact (F.toFunctor.map_smul _ _).symm

end Unitors

end BoxProd

end StringDiagrams

end
