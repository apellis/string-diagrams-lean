import StringDiagrams.Super.Basic
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.Data.ZMod.Basic

/-!
# Superfunctors and supernatural transformations

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Definition 1.1(ii)–(iii) and (v).

* A *superfunctor* `F : A → B` between supercategories is an `SVec`-enriched functor: each
  map `Hom_A(λ, μ) → Hom_B(Fλ, Fμ)` is an even linear map. In the unpacked form of
  `StringDiagrams.Supercategory`, this is an `R`-linear functor (`Functor.Linear R F`)
  preserving the parity of homogeneous morphisms (`Supercategory.IsSuperfunctor`).
* A *supernatural transformation* `x : F ⇒ G` is a family `x_λ = x_{λ,0} + x_{λ,1}` with
  `|x_{λ,p}| = p` and `x_{μ,p} ∘ F f = (-1)^{p|f|} G f ∘ x_{λ,p}` for all `p` and all
  homogeneous `f`. Since the decomposition `x_λ = x_{λ,0} + x_{λ,1}` is unique, we record the
  two homogeneous components as data (`Supercategory.SuperNatTrans.app p`); the morphism
  `x_λ` itself is `SuperNatTrans.total`. In diagrammatic order the sign rule reads
  `F.map f ≫ x_{μ,p} = (-1)^{p|f|} • (x_{λ,p} ≫ G.map f)`.
* Even supernatural transformations are the natural transformations with even components
  (Definition 1.1(v)): `SuperNatTrans.ofNatTrans`, `SuperNatTrans.toNatTrans`.

The sign `(-1)^{pq}` for parities `p q : ZMod 2` is `Supercategory.koszulSign p q : ℤ`, acting
on morphisms by `ℤ`-scalar multiplication.

## Main definitions

* `Supercategory.koszulSign`, with `koszulSign_natCast`: `koszulSign n m = (-1)^(n m)`.
* `Supercategory.IsSuperfunctor R F`; instances for the identity and for composites.
* `Supercategory.SuperNatTrans R F G`, `SuperNatTrans.id`, `SuperNatTrans.vcomp` (vertical
  composition, adding parities), `SuperNatTrans.total`.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory

universe w u₁ v₁ u₂ v₂ u₃ v₃

namespace Supercategory

/-! ## The Koszul sign -/

/-- A parity is `0` or `1`. -/
theorem parity_eq_zero_or_one (p : ZMod 2) : p = 0 ∨ p = 1 := by
  revert p; decide

/-- The Koszul sign `(-1)^{pq}` of two parities. -/
def koszulSign (p q : ZMod 2) : ℤ := if p = 1 ∧ q = 1 then -1 else 1

@[simp] theorem koszulSign_zero_left (q : ZMod 2) : koszulSign 0 q = 1 := by
  simp [koszulSign]

@[simp] theorem koszulSign_zero_right (p : ZMod 2) : koszulSign p 0 = 1 := by
  simp [koszulSign]

@[simp] theorem koszulSign_one_one : koszulSign 1 1 = -1 := by
  simp [koszulSign]

theorem koszulSign_comm (p q : ZMod 2) : koszulSign p q = koszulSign q p := by
  revert p q; decide

theorem koszulSign_add_left (p p' q : ZMod 2) :
    koszulSign (p + p') q = koszulSign p q * koszulSign p' q := by
  revert p p' q; decide

theorem koszulSign_add_right (p q q' : ZMod 2) :
    koszulSign p (q + q') = koszulSign p q * koszulSign p q' := by
  revert p q q'; decide

theorem koszulSign_mul_self (p q : ZMod 2) : koszulSign p q * koszulSign p q = 1 := by
  revert p q; decide

theorem koszulSign_eq_one_or (p q : ZMod 2) : koszulSign p q = 1 ∨ (p = 1 ∧ q = 1) := by
  revert p q; decide

/-- The Koszul sign of two natural numbers, viewed as parities, is `(-1)^(n m)`. -/
theorem koszulSign_natCast (n m : ℕ) : koszulSign (n : ZMod 2) (m : ZMod 2) = (-1) ^ (n * m) := by
  rcases Nat.even_or_odd n with hn | hn <;> rcases Nat.even_or_odd m with hm | hm
  · rw [(ZMod.eq_zero_iff_even.mpr hn), koszulSign_zero_left, (hn.mul_right m).neg_one_pow]
  · rw [(ZMod.eq_zero_iff_even.mpr hn), koszulSign_zero_left, (hn.mul_right m).neg_one_pow]
  · rw [(ZMod.eq_zero_iff_even.mpr hm), koszulSign_zero_right, (hm.mul_left n).neg_one_pow]
  · rw [(ZMod.eq_one_iff_odd.mpr hn), (ZMod.eq_one_iff_odd.mpr hm), koszulSign_one_one,
      (hn.mul hm).neg_one_pow]

theorem koszulSign_smul_smul {M : Type*} [AddCommGroup M] (p q : ZMod 2) (x : M) :
    koszulSign p q • koszulSign p q • x = x := by
  rw [smul_smul, koszulSign_mul_self, one_smul]

variable {R : Type w} [CommRing R]

/-! ## Superfunctors -/

section Functor

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear R C] [Supercategory R C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear R D] [Supercategory R D]
  {E : Type u₃} [Category.{v₃} E] [Preadditive E] [Linear R E] [Supercategory R E]

variable (R) in
/-- A superfunctor (Brundan–Ellis, Definition 1.1(ii)): an `R`-linear functor whose maps on
morphism spaces are even, i.e. preserve the parity of homogeneous morphisms. -/
class IsSuperfunctor (F : C ⥤ D) [F.Additive] [F.Linear R] : Prop where
  /-- `F` preserves parities. -/
  map_mem : ∀ {X Y : C} {p : ZMod 2} {f : X ⟶ Y}, f ∈ parity (R := R) X Y p →
    F.map f ∈ parity (R := R) (F.obj X) (F.obj Y) p

theorem IsSuperfunctor.map_isHomogeneous (F : C ⥤ D) [F.Additive] [F.Linear R]
    [IsSuperfunctor R F] {X Y : C} {p : ZMod 2} {f : X ⟶ Y}
    (hf : IsHomogeneous (R := R) f p) : IsHomogeneous (R := R) (F.map f) p :=
  IsSuperfunctor.map_mem hf

instance IsSuperfunctor.id : IsSuperfunctor R (𝟭 C) where
  map_mem hf := hf

instance IsSuperfunctor.comp (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [F.Linear R] [G.Additive]
    [G.Linear R] [IsSuperfunctor R F] [IsSuperfunctor R G] : IsSuperfunctor R (F ⋙ G) where
  map_mem hf := IsSuperfunctor.map_mem (R := R) (F := G) (IsSuperfunctor.map_mem (F := F) hf)

end Functor

/-! ## Supernatural transformations -/

section NatTrans

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear R C] [Supercategory R C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear R D] [Supercategory R D]

variable (R) in
/-- A supernatural transformation `x : F ⇒ G` (Brundan–Ellis, Definition 1.1(iii)), given by
its homogeneous components `app p X = x_{X,p}`: each `app p X` has parity `p`, and for every
homogeneous `f : X ⟶ Y` of parity `q`,
`F.map f ≫ app p Y = (-1)^{pq} • (app p X ≫ G.map f)`.
(The definition is stated for superfunctors `F` and `G`; the conditions make sense for any
functors between supercategories.) -/
@[ext]
structure SuperNatTrans (F G : C ⥤ D) where
  /-- The component of parity `p` at `X`. -/
  app : ZMod 2 → ∀ X : C, F.obj X ⟶ G.obj X
  /-- The component `app p X` has parity `p`. -/
  app_mem : ∀ (p : ZMod 2) (X : C), app p X ∈ parity (R := R) (F.obj X) (G.obj X) p
  /-- The signed naturality condition. -/
  naturality : ∀ (p : ZMod 2) {X Y : C} {q : ZMod 2} (f : X ⟶ Y), f ∈ parity (R := R) X Y q →
    F.map f ≫ app p Y = koszulSign p q • (app p X ≫ G.map f)

namespace SuperNatTrans

variable {F G H : C ⥤ D}

/-- The morphism `x_X = x_{X,0} + x_{X,1}`. -/
def total (x : SuperNatTrans R F G) (X : C) : F.obj X ⟶ G.obj X := x.app 0 X + x.app 1 X

/-- A supernatural transformation is homogeneous of parity `p` if its component of the other
parity vanishes. -/
def IsHomogeneous (x : SuperNatTrans R F G) (p : ZMod 2) : Prop := ∀ q, q ≠ p → x.app q = 0

/-- The identity supernatural transformation: even, with components the identities. -/
def id (F : C ⥤ D) : SuperNatTrans R F F where
  app p X := if p = 0 then 𝟙 (F.obj X) else 0
  app_mem p X := by
    split_ifs with h
    · subst h; exact id_mem _
    · exact Submodule.zero_mem _
  naturality p X Y q f _ := by
    split_ifs with h
    · subst h; simp
    · simp

@[simp] theorem id_app_zero (F : C ⥤ D) (X : C) : (id (R := R) F).app 0 X = 𝟙 (F.obj X) := rfl

@[simp] theorem id_app_one (F : C ⥤ D) (X : C) : (id (R := R) F).app 1 X = 0 := rfl

theorem id_total (F : C ⥤ D) (X : C) : (id (R := R) F).total X = 𝟙 (F.obj X) := by
  simp [total]

/-- Vertical composition: the component of parity `r` of `x ≫ y` is
`∑_{p} x_{p} ≫ y_{r - p}`. -/
def vcomp (x : SuperNatTrans R F G) (y : SuperNatTrans R G H) : SuperNatTrans R F H where
  app r X := x.app 0 X ≫ y.app r X + x.app 1 X ≫ y.app (r + 1) X
  app_mem r X := by
    refine Submodule.add_mem _ ?_ ?_
    · simpa using comp_mem (x.app_mem 0 X) (y.app_mem r X)
    · have := comp_mem (x.app_mem 1 X) (y.app_mem (r + 1) X)
      have e : ∀ r : ZMod 2, 1 + (r + 1) = r := by decide
      rwa [e] at this
  naturality r X Y q f hf := by
    have key : ∀ (p s : ZMod 2),
        F.map f ≫ x.app p Y ≫ y.app s Y = koszulSign (p + s) q • ((x.app p X ≫ y.app s X) ≫ H.map f) := by
      intro p s
      rw [← Category.assoc, x.naturality p f hf, Linear.smul_comp, Category.assoc,
        y.naturality s f hf, Linear.comp_smul, smul_smul, koszulSign_add_left, Category.assoc]
    have e : ∀ r : ZMod 2, 1 + (r + 1) = r := by decide
    rw [Preadditive.comp_add, key, key, Preadditive.add_comp, smul_add, zero_add, e]

theorem vcomp_total (x : SuperNatTrans R F G) (y : SuperNatTrans R G H) (X : C) :
    (x.vcomp y).total X = x.total X ≫ y.total X := by
  simp only [total, vcomp, Preadditive.add_comp, Preadditive.comp_add]
  rw [(by decide : (0 : ZMod 2) + 1 = 1), (by decide : (1 : ZMod 2) + 1 = 0)]
  abel

/-- An even supernatural transformation defines a natural transformation (Definition 1.1(v)). -/
def toNatTrans [F.Additive] [G.Additive] (x : SuperNatTrans R F G) : F ⟶ G where
  app X := x.app 0 X
  naturality X Y f := by
    have hf : f ∈ ⨆ q, parity (R := R) X Y q := by
      rw [(isInternal (R := R) X Y).submodule_iSup_eq_top]; exact Submodule.mem_top
    refine Submodule.iSup_induction (parity (R := R) X Y)
      (motive := fun g => F.map g ≫ x.app 0 Y = x.app 0 X ≫ G.map g) hf ?_ ?_ ?_
    · intro q g hg
      rw [x.naturality 0 g hg, koszulSign_zero_left, one_smul]
    · simp
    · intro g₁ g₂ h₁ h₂
      simp only [Functor.map_add, Preadditive.add_comp, Preadditive.comp_add, h₁, h₂]

@[simp] theorem toNatTrans_app [F.Additive] [G.Additive] (x : SuperNatTrans R F G) (X : C) : x.toNatTrans.app X = x.app 0 X :=
  rfl

/-- A natural transformation with even components is an even supernatural transformation
(Definition 1.1(v)). -/
def ofNatTrans [F.Additive] [F.Linear R] [G.Additive] [G.Linear R] (α : F ⟶ G)
    (h : ∀ X, α.app X ∈ parity (R := R) (F.obj X) (G.obj X) 0) : SuperNatTrans R F G where
  app p X := if p = 0 then α.app X else 0
  app_mem p X := by
    split_ifs with hp
    · subst hp; exact h X
    · exact Submodule.zero_mem _
  naturality p X Y q f _ := by
    split_ifs with hp
    · subst hp; simp [α.naturality]
    · simp

theorem ofNatTrans_isHomogeneous [F.Additive] [F.Linear R] [G.Additive] [G.Linear R]
    (α : F ⟶ G) (h : ∀ X, α.app X ∈ parity (R := R) (F.obj X) (G.obj X) 0) :
    (ofNatTrans α h).IsHomogeneous 0 := by
  intro q hq
  funext X
  simp [ofNatTrans, hq]

@[simp] theorem ofNatTrans_toNatTrans [F.Additive] [F.Linear R] [G.Additive] [G.Linear R]
    (α : F ⟶ G) (h : ∀ X, α.app X ∈ parity (R := R) (F.obj X) (G.obj X) 0) :
    (ofNatTrans α h).toNatTrans = α := by
  ext X; simp [ofNatTrans, toNatTrans]

end SuperNatTrans

end NatTrans

end Supercategory

end StringDiagrams

end
