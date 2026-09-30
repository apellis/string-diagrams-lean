import StringDiagrams.Super.BoxProductMonoidal
import StringDiagrams.Super.GSCat
import StringDiagrams.Super.GSVecMonoidal

/-!
# The product `A ⊠ B` of graded supercategories

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §6 (after
Definition 6.1): the product `⊠` of graded supercategories is "defined in just the same way as
was explained after Example 1.2". For graded supercategories `C` and `D`, the morphism superspace
`Hom_C(X₁, Y₁) ⊗ Hom_D(X₂, Y₂)` of `C ⊠ D` is the tensor product of graded superspaces, with
`(X ⟶ Y)ₙ = ⨁_{r+s=n} Hom_C(X₁, Y₁)ᵣ ⊗ Hom_D(X₂, Y₂)ₛ`.

## Main definitions

* `GradedSupercategory.homGSpace k C X Y`: the morphism graded superspace `Hom(X, Y)`.
* `BoxProd.homDeg X Y n`: the span of the `f ⊗ g` with `deg f + deg g = n`
  (`BoxProd.tmulHom_mem_homDeg`); `BoxProd.instGradedSupercategory`: `C ⊠ D` is a graded
  supercategory with morphisms of degree `n` the `homDeg X Y n` (the internal direct sum is
  `GradedSuperspace.isInternal_tensorDeg`).
* The unit supercategory `I` is graded, all its morphisms of degree `0`
  (`BoxUnit.instGradedSupercategory`, `BoxUnit.mem_degree_zero`).
* `F ⊠ G` of graded superfunctors, the associator, the unitors and their inverses are graded
  superfunctors (`IsGradedSuperfunctor` instances; bundled: `BoxProd.gradedMap`,
  `BoxProd.gradedAssoc`, `BoxProd.gradedAssocInv`, `BoxProd.gradedLunit`, …).

The category `GSCat` and its monoidal structure `⊠` are in `StringDiagrams.Super.GSCatMonoidal`.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory GradedSupercategory TensorProduct

universe w u w₁ w₂ w₃ w₄ w₅

variable {k : Type u} [CommRing k]

namespace GradedSupercategory

variable (k) (C : Type w₁) [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [GradedSupercategory k C]

/-- The morphism graded superspace `Hom(X, Y)` of a graded supercategory whose morphism modules
live in the universe of `k`. -/
abbrev homGSpace (X Y : C) : GradedSuperspace k where
  toSVec := homSVec k C X Y
  deg := degree (R := k) X Y
  isInternal_deg := isInternal_degree X Y
  odd_mem hv := proj_mem_degree 1 hv

end GradedSupercategory

/-! ## The graded supercategory `C ⊠ D` -/

namespace BoxProd

variable {C : Type w₁} [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [GradedSupercategory k C]
  {D : Type w₂} [Category.{u} D] [Preadditive D] [Linear k D] [Supercategory k D]
  [GradedSupercategory k D]

/-- The morphisms of degree `n` of `C ⊠ D`: `⨁_{r+s=n} Hom_C(X₁, Y₁)ᵣ ⊗ Hom_D(X₂, Y₂)ₛ`, the
component of degree `n` of the tensor product of graded superspaces. -/
def homDeg (X Y : BoxProd k C D) (n : ℤ) : Submodule k (X ⟶ Y) :=
  (homGSpace k C X.fst Y.fst).tensorDeg (homGSpace k D X.snd Y.snd) n

/-- `f ⊗ g` has degree `deg f + deg g`. -/
theorem tmulHom_mem_homDeg {X Y : BoxProd k C D} {r s : ℤ} {f : X.fst ⟶ Y.fst}
    {g : X.snd ⟶ Y.snd} (hf : f ∈ degree (R := k) X.fst Y.fst r)
    (hg : g ∈ degree (R := k) X.snd Y.snd s) : tmulHom f g ∈ homDeg X Y (r + s) :=
  GradedSuperspace.tmul_mem_tensorDeg _ _ hf hg

/-- `homDeg X Y n` is spanned by the `f ⊗ g` with `deg f + deg g = n`. -/
theorem homDeg_le_iff {X Y : BoxProd k C D} {n : ℤ} {S : Submodule k (X ⟶ Y)} :
    homDeg X Y n ≤ S ↔ ∀ (r s : ℤ), r + s = n → ∀ f ∈ degree (R := k) X.fst Y.fst r,
      ∀ g ∈ degree (R := k) X.snd Y.snd s, tmulHom f g ∈ S :=
  GradedSuperspace.tensorDeg_le_iff _ _

/-- A linear map sending the `f ⊗ g` with `deg f + deg g = n` into `S` sends `homDeg X Y n`
into `S`. -/
theorem map_mem_of_homDeg {X Y : BoxProd k C D} {n : ℤ} {M : Type*} [AddCommGroup M]
    [Module k M] (φ : (X ⟶ Y) →ₗ[k] M) (S : Submodule k M)
    (h : ∀ (r s : ℤ), r + s = n → ∀ f ∈ degree (R := k) X.fst Y.fst r,
      ∀ g ∈ degree (R := k) X.snd Y.snd s, φ (tmulHom f g) ∈ S)
    {x : X ⟶ Y} (hx : x ∈ homDeg X Y n) : φ x ∈ S :=
  (homDeg_le_iff (S := S.comap φ)).2 h hx

omit [GradedSupercategory k C] [GradedSupercategory k D] in
/-- The parity projections of `C ⊠ D` are those of the tensor product of superspaces. -/
theorem proj_eq_homObj_proj {X Y : BoxProd k C D} (p : ZMod 2) (x : X ⟶ Y) :
    proj k p x = (homObj k X Y).proj p x := by
  refine proj_eq_of_add ?_ (mem_parity_iff.2 (SVec.proj_mem_part (homObj k X Y) p x))
    (mem_parity_iff.2 (SVec.proj_mem_part (homObj k X Y) (p + 1) x))
  rcases parity_eq_zero_or_one p with rfl | rfl
  · exact (LinearMap.congr_fun (SVec.proj_add_proj (homObj k X Y)) x).symm
  · rw [SVec.zmod2_one_add_one]
    exact (LinearMap.congr_fun (SVec.proj_add_proj (homObj k X Y)) x).symm.trans (add_comm _ _)

theorem proj_mem_homDeg {X Y : BoxProd k C D} {n : ℤ} {x : X ⟶ Y} (p : ZMod 2)
    (hx : x ∈ homDeg X Y n) : proj k p x ∈ homDeg X Y n := by
  rw [proj_eq_homObj_proj]
  exact ((homGSpace k C X.fst Y.fst).tensorObj (homGSpace k D X.snd Y.snd)).proj_mem p hx

omit [GradedSupercategory k C] [GradedSupercategory k D] in
/-- The composition rule of `C ⊠ D` for arbitrary `f`, `l`:
`(f ⊗ g) ≫ (h ⊗ l) = (f₀ ≫ h) ⊗ (g ≫ l) + (f₁ ≫ h) ⊗ (g ≫ (l₀ - l₁))`. -/
theorem tmulHom_comp_tmulHom_eq {X Y Z : BoxProd k C D} (f : X.fst ⟶ Y.fst) (g : X.snd ⟶ Y.snd)
    (h : Y.fst ⟶ Z.fst) (l : Y.snd ⟶ Z.snd) :
    tmulHom f g ≫ tmulHom h l =
      tmulHom (proj k 0 f ≫ h) (g ≫ l) + tmulHom (proj k 1 f ≫ h) (g ≫ twist k 1 l) :=
  compMap_tmul_tmul X Y Z f g h l

/-- Composition in `C ⊠ D` adds degrees. -/
theorem comp_mem_homDeg {X Y Z : BoxProd k C D} {m n : ℤ} {x : X ⟶ Y} {y : Y ⟶ Z}
    (hx : x ∈ homDeg X Y m) (hy : y ∈ homDeg Y Z n) : x ≫ y ∈ homDeg X Z (m + n) := by
  refine map_mem_of_homDeg ((compMap X Y Z).flip y) _ (fun r s hrs f hf g hg => ?_) hx
  change compMap X Y Z (tmulHom f g) y ∈ _
  refine map_mem_of_homDeg (compMap X Y Z (tmulHom f g)) _
    (fun r' s' hrs' h hh l hl => ?_) hy
  change tmulHom f g ≫ tmulHom h l ∈ _
  rw [tmulHom_comp_tmulHom_eq, show m + n = (r + r') + (s + s') by omega]
  exact Submodule.add_mem _
    (tmulHom_mem_homDeg (X := X) (Y := Z) (comp_mem_degree (proj_mem_degree 0 hf) hh)
      (comp_mem_degree hg hl))
    (tmulHom_mem_homDeg (X := X) (Y := Z) (comp_mem_degree (proj_mem_degree 1 hf) hh)
      (comp_mem_degree hg (twist_mem_degree 1 hl)))

/-- **Brundan–Ellis, §6 (after Definition 6.1).** For graded supercategories `C` and `D`,
`C ⊠ D` is a graded supercategory: the morphisms of degree `n` are the elements of
`⨁_{r+s=n} Hom_C(X₁, Y₁)ᵣ ⊗ Hom_D(X₂, Y₂)ₛ`. -/
instance instGradedSupercategory : GradedSupercategory k (BoxProd k C D) where
  degree := homDeg
  isInternal_degree X Y := GradedSuperspace.isInternal_tensorDeg _ _
  proj_mem_degree p hx := proj_mem_homDeg p hx
  id_mem_degree X := by
    have := tmulHom_mem_homDeg (X := X) (Y := X) (id_mem_degree (R := k) X.fst)
      (id_mem_degree (R := k) X.snd)
    rwa [add_zero, ← id_eq_tmulHom] at this
  comp_mem_degree hx hy := comp_mem_homDeg hx hy

theorem mem_degree_iff {X Y : BoxProd k C D} {n : ℤ} {x : X ⟶ Y} :
    x ∈ degree (R := k) X Y n ↔ x ∈ homDeg X Y n := Iff.rfl

/-- `f ⊗ g` has degree `deg f + deg g`. -/
theorem tmulHom_mem_degree {X Y : BoxProd k C D} {r s : ℤ} {f : X.fst ⟶ Y.fst}
    {g : X.snd ⟶ Y.snd} (hf : f ∈ degree (R := k) X.fst Y.fst r)
    (hg : g ∈ degree (R := k) X.snd Y.snd s) : tmulHom f g ∈ degree (R := k) X Y (r + s) :=
  tmulHom_mem_homDeg hf hg

/-- `f ⊗ g` of bihomogeneous `f`, `g` has parity `|f| + |g|` and degree `deg f + deg g`. -/
theorem tmulHom_mem_bidegree {X Y : BoxProd k C D} {r s : ℤ} {p q : ZMod 2}
    {f : X.fst ⟶ Y.fst} {g : X.snd ⟶ Y.snd} (hf : f ∈ bidegree (R := k) X.fst Y.fst (r, p))
    (hg : g ∈ bidegree (R := k) X.snd Y.snd (s, q)) :
    tmulHom f g ∈ bidegree (R := k) X Y (r + s, p + q) :=
  ⟨tmulHom_mem_degree hf.1 hg.1, tmulHom_mem_parity hf.2 hg.2⟩

end BoxProd

/-! ## The graded unit supercategory -/

namespace BoxUnit

/-- The grading of `k`: everything in degree `0`. -/
def unitDeg (n : ℤ) : Submodule k k := if n = 0 then ⊤ else ⊥

theorem mem_unitDeg {n : ℤ} {r : k} : r ∈ unitDeg n ↔ n = 0 ∨ r = 0 := by
  by_cases hn : n = 0 <;> simp [unitDeg, hn]

/-- **Brundan–Ellis, §6.** The unit supercategory `I` is a graded supercategory, with all
morphisms of degree `0`. -/
instance instGradedSupercategory : GradedSupercategory k (BoxUnit.{w, u} k) where
  degree _ _ := unitDeg
  isInternal_degree _ _ := (GradedSuperspace.unit (k := k)).isInternal_deg
  proj_mem_degree {X Y n f} p hf := by
    rcases mem_unitDeg.1 hf with hn | hf
    · exact mem_unitDeg.2 (Or.inl hn)
    · exact mem_unitDeg.2 (Or.inr (by rw [hf, map_zero]))
  id_mem_degree _ := mem_unitDeg.2 (Or.inl rfl)
  comp_mem_degree {X Y Z m n f g} hf hg := by
    rcases mem_unitDeg.1 hf with hm | hf
    · rcases mem_unitDeg.1 hg with hn | hg
      · exact mem_unitDeg.2 (Or.inl (by rw [hm, hn, add_zero]))
      · exact mem_unitDeg.2 (Or.inr (by rw [hg, Limits.comp_zero]))
    · exact mem_unitDeg.2 (Or.inr (by rw [hf, Limits.zero_comp]))

theorem mem_degree_iff {X Y : BoxUnit.{w, u} k} {n : ℤ} {f : X ⟶ Y} :
    f ∈ degree (R := k) X Y n ↔ n = 0 ∨ f = 0 :=
  mem_unitDeg

/-- Every morphism of `I` has degree `0`. -/
theorem mem_degree_zero {X Y : BoxUnit.{w, u} k} (f : X ⟶ Y) : f ∈ degree (R := k) X Y 0 :=
  mem_degree_iff.2 (Or.inl rfl)

end BoxUnit

/-! ## Graded superfunctors -/

namespace BoxProd

variable {C : Type w₁} [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [GradedSupercategory k C]
  {D : Type w₂} [Category.{u} D] [Preadditive D] [Linear k D] [Supercategory k D]
  [GradedSupercategory k D]
  {C' : Type w₃} [Category.{u} C'] [Preadditive C'] [Linear k C'] [Supercategory k C']
  [GradedSupercategory k C']
  {D' : Type w₄} [Category.{u} D'] [Preadditive D'] [Linear k D'] [Supercategory k D']
  [GradedSupercategory k D']

section Map

variable (F : GradedSuperfunctor k C C') (G : GradedSuperfunctor k D D')

/-- **Brundan–Ellis, §6.** `F ⊠ G` of graded superfunctors is a graded superfunctor. -/
instance isGradedSuperfunctor_map :
    IsGradedSuperfunctor k (map F.toSuperfunctor G.toSuperfunctor).toFunctor where
  map_mem_degree {X Y n x} hx :=
    map_mem_of_homDeg (mapHom F.toSuperfunctor G.toSuperfunctor X Y) _
      (fun r s hrs f hf g hg => by
        rw [mapHom_tmul, ← hrs]
        exact tmulHom_mem_degree (X := mapObj F.toSuperfunctor G.toSuperfunctor X)
          (Y := mapObj F.toSuperfunctor G.toSuperfunctor Y) (map_mem_degree F.toFunctor hf)
          (map_mem_degree G.toFunctor hg)) hx

/-- The graded superfunctor `F ⊠ G : C ⊠ D → C' ⊠ D'`. -/
def gradedMap : GradedSuperfunctor k (BoxProd k C D) (BoxProd k C' D') :=
  ⟨map F.toSuperfunctor G.toSuperfunctor⟩

@[simp] theorem gradedMap_toSuperfunctor :
    (gradedMap F G).toSuperfunctor = map F.toSuperfunctor G.toSuperfunctor := rfl

end Map

section Assoc

variable {E : Type w₅} [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  [GradedSupercategory k E]

/-- A linear map sending the `(f ⊗ g) ⊗ h` with `deg f + deg g + deg h = n` into `S` sends the
morphisms of degree `n` of `(C ⊠ D) ⊠ E` into `S`. -/
theorem map_mem_of_degree₃ {X Y : BoxProd k (BoxProd k C D) E} {n : ℤ} {M : Type*}
    [AddCommGroup M] [Module k M] (φ : (X ⟶ Y) →ₗ[k] M) (S : Submodule k M)
    (h : ∀ (a b c : ℤ), a + b + c = n → ∀ f ∈ degree (R := k) X.fst.fst Y.fst.fst a,
      ∀ g ∈ degree (R := k) X.fst.snd Y.fst.snd b, ∀ l ∈ degree (R := k) X.snd Y.snd c,
      φ (tmulHom (tmulHom (X := X.fst) (Y := Y.fst) f g) l) ∈ S)
    {x : X ⟶ Y} (hx : x ∈ degree (R := k) X Y n) : φ x ∈ S :=
  map_mem_of_homDeg φ S (fun r c hrc v hv l hl =>
    map_mem_of_homDeg (X := X.fst) (Y := Y.fst)
      (φ ∘ₗ (TensorProduct.mk k (X.fst ⟶ Y.fst) (X.snd ⟶ Y.snd)).flip l) S
      (fun a b hab f hf g hg => h a b c (by rw [hab, hrc]) f hf g hg l hl) hv) hx

/-- A linear map sending the `f ⊗ (g ⊗ h)` with `deg f + deg g + deg h = n` into `S` sends the
morphisms of degree `n` of `C ⊠ (D ⊠ E)` into `S`. -/
theorem map_mem_of_degree₃' {X Y : BoxProd k C (BoxProd k D E)} {n : ℤ} {M : Type*}
    [AddCommGroup M] [Module k M] (φ : (X ⟶ Y) →ₗ[k] M) (S : Submodule k M)
    (h : ∀ (a b c : ℤ), a + b + c = n → ∀ f ∈ degree (R := k) X.fst Y.fst a,
      ∀ g ∈ degree (R := k) X.snd.fst Y.snd.fst b, ∀ l ∈ degree (R := k) X.snd.snd Y.snd.snd c,
      φ (tmulHom (X := X) (Y := Y) f (tmulHom (X := X.snd) (Y := Y.snd) g l)) ∈ S)
    {x : X ⟶ Y} (hx : x ∈ degree (R := k) X Y n) : φ x ∈ S :=
  map_mem_of_homDeg φ S (fun a r har f hf v hv =>
    map_mem_of_homDeg (X := X.snd) (Y := Y.snd)
      (φ ∘ₗ TensorProduct.mk k (X.fst ⟶ Y.fst) (X.snd ⟶ Y.snd) f) S
      (fun b c hbc g hg l hl => h a b c (by rw [add_assoc, hbc, har]) f hf g hg l hl) hv) hx

variable (C D E)

/-- **Brundan–Ellis, §6.** The associator `(C ⊠ D) ⊠ E → C ⊠ (D ⊠ E)` of graded
supercategories preserves degrees. -/
instance isGradedSuperfunctor_assoc : IsGradedSuperfunctor k (assoc (k := k) C D E).toFunctor where
  map_mem_degree {X Y n x} hx :=
    map_mem_of_degree₃ (assocHom X Y) _ (fun a b c habc f hf g hg l hl => by
      rw [assocHom_tmul, ← habc, add_assoc]
      exact tmulHom_mem_degree (X := assocObj C D E X) (Y := assocObj C D E Y) hf
        (tmulHom_mem_degree (X := (assocObj C D E X).snd) (Y := (assocObj C D E Y).snd) hg hl))
      hx

/-- The inverse of the associator preserves degrees. -/
instance isGradedSuperfunctor_assocInv :
    IsGradedSuperfunctor k (assocInv (k := k) C D E).toFunctor where
  map_mem_degree {X Y n x} hx :=
    map_mem_of_degree₃' (assocInvHom X Y) _ (fun a b c habc f hf g hg l hl => by
      rw [assocInvHom_tmul, ← habc]
      exact tmulHom_mem_degree (X := assocInvObj C D E X) (Y := assocInvObj C D E Y)
        (tmulHom_mem_degree (X := (assocInvObj C D E X).fst) (Y := (assocInvObj C D E Y).fst)
          hf hg) hl)
      hx

/-- The associator of graded supercategories, as a graded superfunctor. -/
def gradedAssoc :
    GradedSuperfunctor k (BoxProd k (BoxProd k C D) E) (BoxProd k C (BoxProd k D E)) :=
  ⟨assoc (k := k) C D E⟩

/-- The inverse of the associator of graded supercategories, as a graded superfunctor. -/
def gradedAssocInv :
    GradedSuperfunctor k (BoxProd k C (BoxProd k D E)) (BoxProd k (BoxProd k C D) E) :=
  ⟨assocInv (k := k) C D E⟩

@[simp] theorem gradedAssoc_toSuperfunctor :
    (gradedAssoc (k := k) C D E).toSuperfunctor = assoc (k := k) C D E :=
  rfl

@[simp] theorem gradedAssocInv_toSuperfunctor :
    (gradedAssocInv (k := k) C D E).toSuperfunctor = assocInv (k := k) C D E := rfl

end Assoc

section Unitors

variable (C)

/-- **Brundan–Ellis, §6.** The left unitor `I ⊠ C → C` preserves degrees. -/
instance isGradedSuperfunctor_lunit : IsGradedSuperfunctor k (lunit.{w} (k := k) C).toFunctor where
  map_mem_degree {X Y n x} hx :=
    map_mem_of_homDeg (lunitHom X Y) _ (fun a b hab r hr f hf => by
      rw [lunitHom_tmul]
      rcases BoxUnit.mem_degree_iff.1 hr with ha | hr
      · rw [← hab, ha, zero_add]; exact Submodule.smul_mem _ _ hf
      · rw [hr, zero_smul]; exact Submodule.zero_mem _) hx

/-- The inverse of the left unitor preserves degrees. -/
instance isGradedSuperfunctor_lunitInv :
    IsGradedSuperfunctor k (lunitInv.{w} (k := k) C).toFunctor where
  map_mem_degree {X Y n f} hf := by
    change lunitInvHom X Y f ∈ _
    rw [lunitInvHom_apply, ← zero_add n]
    exact tmulHom_mem_degree (BoxUnit.mem_degree_zero _) hf

/-- **Brundan–Ellis, §6.** The right unitor `C ⊠ I → C` preserves degrees. -/
instance isGradedSuperfunctor_runit : IsGradedSuperfunctor k (runit.{w} (k := k) C).toFunctor where
  map_mem_degree {X Y n x} hx :=
    map_mem_of_homDeg (runitHom X Y) _ (fun a b hab f hf r hr => by
      rw [runitHom_tmul]
      rcases BoxUnit.mem_degree_iff.1 hr with hb | hr
      · rw [← hab, hb, add_zero]; exact Submodule.smul_mem _ _ hf
      · rw [hr, zero_smul]; exact Submodule.zero_mem _) hx

/-- The inverse of the right unitor preserves degrees. -/
instance isGradedSuperfunctor_runitInv :
    IsGradedSuperfunctor k (runitInv.{w} (k := k) C).toFunctor where
  map_mem_degree {X Y n f} hf := by
    change runitInvHom X Y f ∈ _
    rw [runitInvHom_apply, ← add_zero n]
    exact tmulHom_mem_degree hf (BoxUnit.mem_degree_zero _)

/-- The left unitor of graded supercategories, as a graded superfunctor. -/
def gradedLunit : GradedSuperfunctor k (BoxProd k (BoxUnit.{w, u} k) C) C := ⟨lunit.{w} (k := k) C⟩

/-- The inverse of the left unitor, as a graded superfunctor. -/
def gradedLunitInv : GradedSuperfunctor k C (BoxProd k (BoxUnit.{w, u} k) C) :=
  ⟨lunitInv.{w} (k := k) C⟩

/-- The right unitor of graded supercategories, as a graded superfunctor. -/
def gradedRunit : GradedSuperfunctor k (BoxProd k C (BoxUnit.{w, u} k)) C := ⟨runit.{w} (k := k) C⟩

/-- The inverse of the right unitor, as a graded superfunctor. -/
def gradedRunitInv : GradedSuperfunctor k C (BoxProd k C (BoxUnit.{w, u} k)) :=
  ⟨runitInv.{w} (k := k) C⟩

@[simp] theorem gradedLunit_toSuperfunctor :
    (gradedLunit.{w} (k := k) C).toSuperfunctor = lunit (k := k) C := rfl

@[simp] theorem gradedLunitInv_toSuperfunctor :
    (gradedLunitInv.{w} (k := k) C).toSuperfunctor = lunitInv (k := k) C := rfl

@[simp] theorem gradedRunit_toSuperfunctor :
    (gradedRunit.{w} (k := k) C).toSuperfunctor = runit (k := k) C := rfl

@[simp] theorem gradedRunitInv_toSuperfunctor :
    (gradedRunitInv.{w} (k := k) C).toSuperfunctor = runitInv (k := k) C := rfl

end Unitors

end BoxProd

end StringDiagrams

end
