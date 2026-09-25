import StringDiagrams.Whisker
import StringDiagrams.Generation
import Mathlib.Algebra.DirectSum.Decomposition
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Graded presentations

A *grading* of a signature `S` by an additive commutative monoid `A` is a function
`deg : S.Gen → A` assigning a degree to every generator (for example, for KLR algebras,
`deg (dot) = 2` and `deg (crossing_{ij}) = -i·j`). The degree of a layered diagram is the sum
of the degrees of its generators (`Diagram.degree`); it is additive under composition and
invariant under whiskering and retyping.

A presentation is *homogeneous* for `deg` (`Presentation.IsHomogeneous`) if every defining
relation is a linear combination of diagrams of a single degree. The interchange law is
automatically homogeneous (`InterchangeData.rel_mem_homDeg`). For a homogeneous presentation
the tensor ideal is homogeneous (`Presentation.homogeneousComponent_mem_ideal`), so every
Hom-space of the presented category is the internal direct sum of its homogeneous parts.

## Main definitions and results

* `Diagram.degree deg f`, with `degree_comp`, `degree_whisker`, `degree_cast`.
* `LinDiagram.homDeg R deg a b d`: linear combinations of diagrams of degree `d`, and
  `LinDiagram.homogeneousComponent deg d`: the (linear) projection onto it.
* `Presentation.homDeg deg a b d : Submodule R (P.obj a ⟶ P.obj b)`: the image of
  `LinDiagram.homDeg R deg a b d` in the presented category.
* `Presentation.comp_mem_homDeg` (`homDeg d ≫ homDeg e ⊆ homDeg (d + e)`),
  `Presentation.id_mem_homDeg`, `Presentation.whisk_mem_homDeg`.
* `Presentation.isInternal_homDeg`: for a homogeneous presentation,
  `DirectSum.IsInternal (P.homDeg deg a b)`; `Presentation.decomposition` is the resulting
  `DirectSum.Decomposition`, whose components are computed by `decompose_apply` as the
  well-defined projections `Presentation.homogeneousComponent`.
* `Presentation.gradedAlgebra`: the endomorphism algebra of every object is an `A`-graded
  `R`-algebra.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory

universe w v u₀ u₁ u₂

variable {S : Signature.{u₀, u₁, u₂}} {A : Type*} [AddCommMonoid A]

section Degree

variable (deg : S.Gen → A)

/-! ## Degrees of diagrams -/

namespace Diagram

variable {a b c : Obj S}

/-- The degree of a diagram: the sum of the degrees of the generators in its layers. -/
def degree (f : a ⟶ b) : A := ((layers f).map fun L => deg L.gen).sum

theorem degree_mk (ls : List (Layer S)) (h : Chain a ls b) :
    degree deg (mk ls h) = (ls.map fun L => deg L.gen).sum := rfl

@[simp] theorem degree_id (a : Obj S) : degree deg (𝟙 a) = 0 := by
  simp [degree]

@[simp] theorem degree_comp (f : a ⟶ b) (g : b ⟶ c) :
    degree deg (f ≫ g) = degree deg f + degree deg g := by
  simp [degree]

@[simp] theorem degree_eqToHom (h : a = b) : degree deg (eqToHom h) = 0 := by
  simp [degree]

@[simp] theorem degree_ofLayer (L : Layer S) (hv : L.Valid) :
    degree deg (ofLayer L hv) = deg L.gen := by
  simp [degree]

@[simp] theorem degree_layer (L : Layer S) (hv : L.Valid) (ha : L.dom = a) (hb : L.cod = b) :
    degree deg (layer L hv ha hb) = deg L.gen := by
  simp [degree]

@[simp] theorem degree_cast {a' b' : Obj S} (f : a ⟶ b) (ha : a = a') (hb : b = b') :
    degree deg (cast f ha hb) = degree deg f := rfl

@[simp] theorem degree_whisker (f : a ⟶ b) (u : Obj S) (v : List S.Colour)
    (hw : a.WhiskerOK u v) : degree deg (whisker f u v hw) = degree deg f := by
  simp [degree, Function.comp_def, Layer.whisker]

end Diagram

namespace InterchangeData

variable {x : InterchangeData S}

@[simp] theorem degree_ghDiagram (hx : x.Valid) :
    Diagram.degree deg (ghDiagram hx) = deg x.g + deg x.h := by
  simp [ghDiagram, Diagram.degree_mk, gh₁, gh₂]

@[simp] theorem degree_hgDiagram (hx : x.Valid) :
    Diagram.degree deg (hgDiagram hx) = deg x.g + deg x.h := by
  simp [hgDiagram, Diagram.degree_mk, hg₁, hg₂, add_comm]

end InterchangeData

end Degree

/-! ## Homogeneous linear combinations of diagrams -/

namespace LinDiagram

variable (R : Type w) [CommRing R] (deg : S.Gen → A)

/-- The linear combinations of diagrams from `a` to `b` of degree `d`: those supported on
diagrams of degree `d`. -/
def homDeg (a b : Obj S) (d : A) : Submodule R (LinDiagram R a b) :=
  Finsupp.supported R R {f : a ⟶ b | Diagram.degree deg f = d}

variable {R} {deg}
variable {a b c : Obj S}

/-- A linear combination of diagrams, viewed as a finitely supported function on diagrams. -/
abbrev toFinsupp (f : LinDiagram R a b) : (a ⟶ b) →₀ R := f

theorem mem_homDeg_iff {f : LinDiagram R a b} {d : A} :
    f ∈ homDeg R deg a b d ↔
      ∀ g : a ⟶ b, f.toFinsupp g ≠ 0 → Diagram.degree deg g = d := by
  rw [homDeg, Finsupp.mem_supported]
  exact ⟨fun h g hg => h (Finsupp.mem_support_iff.mpr hg),
    fun h g hg => h g (Finsupp.mem_support_iff.mp hg)⟩

theorem single_mem_homDeg (g : a ⟶ b) (r : R) :
    (Finsupp.single g r : LinDiagram R a b) ∈ homDeg R deg a b (Diagram.degree deg g) :=
  Finsupp.single_mem_supported R r rfl

theorem of_mem_homDeg (g : a ⟶ b) :
    (of g : LinDiagram R a b) ∈ homDeg R deg a b (Diagram.degree deg g) :=
  single_mem_homDeg g 1

theorem of_mem_homDeg' {g : a ⟶ b} {d : A} (h : Diagram.degree deg g = d) :
    (of g : LinDiagram R a b) ∈ homDeg R deg a b d :=
  h ▸ of_mem_homDeg g

theorem id_mem_homDeg (a : Obj S) : 𝟙 (Free.of R a) ∈ homDeg R deg a a 0 :=
  of_mem_homDeg' (g := 𝟙 a) (Diagram.degree_id deg a)

/-- Composition of homogeneous linear combinations adds degrees. -/
theorem comp_mem_homDeg {f : LinDiagram R a b} {g : LinDiagram R b c} {d e : A}
    (hf : f ∈ homDeg R deg a b d) (hg : g ∈ homDeg R deg b c e) :
    f ≫ g ∈ homDeg R deg a c (d + e) := by
  rw [homDeg, Finsupp.supported_eq_span_single] at hf hg
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, rfl⟩ := hx
    induction hg using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨q, hq, rfl⟩ := hy
      have := of_comp (R := R) p q
      refine this ▸ of_mem_homDeg' ?_
      rw [Diagram.degree_comp]
      exact congrArg₂ _ hp hq
    | zero => rw [Limits.comp_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [Preadditive.comp_add]; exact Submodule.add_mem _ hy hz
    | smul r y _ hy => rw [Linear.comp_smul]; exact Submodule.smul_mem _ r hy
  | zero => rw [Limits.zero_comp]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [Preadditive.add_comp]; exact Submodule.add_mem _ hy hz
  | smul r y _ hy => rw [Linear.smul_comp]; exact Submodule.smul_mem _ r hy

/-- Relabelling the diagrams of a linear combination by a degree-preserving map preserves
homogeneity. -/
theorem mapDomain_mem_homDeg {a' b' : Obj S} (φ : (a ⟶ b) → (a' ⟶ b'))
    (hφ : ∀ g, Diagram.degree deg (φ g) = Diagram.degree deg g) {f : LinDiagram R a b} {d : A}
    (hf : f ∈ homDeg R deg a b d) :
    (Finsupp.mapDomain φ f : LinDiagram R a' b') ∈ homDeg R deg a' b' d := by
  classical
  rw [homDeg, Finsupp.mem_supported] at hf ⊢
  intro g hg
  obtain ⟨g', hg', rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hg)
  show Diagram.degree deg (φ g') = d
  rw [hφ]; exact hf hg'

theorem whisker_mem_homDeg {f : LinDiagram R a b} {d : A} (hf : f ∈ homDeg R deg a b d)
    (u : Obj S) (v : List S.Colour) (hw : a.WhiskerOK u v) :
    whisker f u v hw ∈ homDeg R deg _ _ d :=
  mapDomain_mem_homDeg _ (fun g => Diagram.degree_whisker deg g u v hw) hf

theorem whisk_mem_homDeg {f : LinDiagram R a b} {d : A} (hf : f ∈ homDeg R deg a b d)
    (u : Obj S) (v : List S.Colour) : whisk f u v ∈ homDeg R deg _ _ d := by
  by_cases h : a.WhiskerOK u v
  · rw [whisk_of_ok _ h]; exact whisker_mem_homDeg hf u v h
  · rw [whisk_of_not_ok _ h]; exact Submodule.zero_mem _

theorem cast_mem_homDeg {a' b' : Obj S} {f : LinDiagram R a b} {d : A}
    (hf : f ∈ homDeg R deg a b d) (ha : a = a') (hb : b = b') :
    cast f ha hb ∈ homDeg R deg a' b' d :=
  mapDomain_mem_homDeg _ (fun g => Diagram.degree_cast deg g ha hb) hf

variable (deg) in
open Classical in
/-- The degree-`d` component of a linear combination of diagrams: the terms whose diagram has
degree `d`. -/
def homogeneousComponent (d : A) : LinDiagram R a b →ₗ[R] LinDiagram R a b where
  toFun f := Finsupp.filter (fun g => Diagram.degree deg g = d) f
  map_add' _ _ := Finsupp.filter_add
  map_smul' _ _ := Finsupp.filter_smul

open Classical in
theorem homogeneousComponent_apply (d : A) (f : LinDiagram R a b) :
    homogeneousComponent deg d f = Finsupp.filter (fun g => Diagram.degree deg g = d) f := rfl

theorem homogeneousComponent_mem (d : A) (f : LinDiagram R a b) :
    homogeneousComponent deg d f ∈ homDeg R deg a b d := by
  classical
  rw [mem_homDeg_iff]
  intro g hg
  by_contra h
  exact hg (Finsupp.filter_apply_neg _ _ h)

theorem homogeneousComponent_of_mem {f : LinDiagram R a b} {d : A}
    (hf : f ∈ homDeg R deg a b d) : homogeneousComponent deg d f = f := by
  classical
  rw [homogeneousComponent_apply, Finsupp.filter_eq_self_iff]
  exact (mem_homDeg_iff.mp hf)

theorem homogeneousComponent_of_mem_of_ne {f : LinDiagram R a b} {d e : A}
    (hf : f ∈ homDeg R deg a b e) (h : e ≠ d) : homogeneousComponent deg d f = 0 := by
  classical
  rw [homogeneousComponent_apply, Finsupp.filter_eq_zero_iff]
  intro g hg
  by_contra h'
  exact h ((mem_homDeg_iff.mp hf g h').symm.trans hg)

/-- A linear combination of diagrams is the sum of its homogeneous components. -/
theorem sum_homogeneousComponent [DecidableEq A] (f : LinDiagram R a b) :
    ∑ d ∈ (Finsupp.support f.toFinsupp).image (Diagram.degree deg),
      homogeneousComponent deg d f = f := by
  classical
  refine Finsupp.ext fun g => ?_
  erw [Finsupp.finset_sum_apply]
  simp only [homogeneousComponent_apply, Finsupp.filter_apply]
  by_cases hg : g ∈ Finsupp.support f.toFinsupp
  · rw [Finset.sum_eq_single (Diagram.degree deg g)]
    · simp
    · intro d _ hd; simp [Ne.symm hd]
    · intro h; exact absurd (Finset.mem_image_of_mem _ hg) h
  · rw [Finsupp.not_mem_support_iff.mp hg]
    simp

end LinDiagram

namespace InterchangeData

/-- The interchange relation is homogeneous. -/
theorem rel_mem_homDeg (deg : S.Gen → A) (R : Type w) [CommRing R] {x : InterchangeData S}
    (hx : x.Valid) :
    rel R hx ∈ LinDiagram.homDeg R deg x.dom x.cod (deg x.g + deg x.h) :=
  Submodule.sub_mem _ (LinDiagram.of_mem_homDeg' (degree_ghDiagram deg hx))
    (Submodule.smul_mem _ _ (LinDiagram.of_mem_homDeg' (degree_hgDiagram deg hx)))

end InterchangeData

/-! ## Homogeneous presentations -/

namespace Presentation

variable {R : Type w} [CommRing R] (P : Presentation.{w, v} S R) (deg : S.Gen → A)

/-- A presentation is homogeneous for `deg` if every defining relation is a linear combination
of diagrams of one degree. -/
def IsHomogeneous : Prop :=
  ∀ i, ∃ d, P.rel i ∈ LinDiagram.homDeg R deg (P.dom i) (P.cod i) d

variable {P} {deg}

theorem IsHomogeneous.allRel (hP : P.IsHomogeneous deg) (k : P.AllRel) :
    ∃ d, k.rel ∈ LinDiagram.homDeg R deg k.dom k.cod d := by
  cases k with
  | user i => exact hP i
  | interchange x hx => exact ⟨_, InterchangeData.rel_mem_homDeg deg R hx⟩

variable {a b c : Obj S}

/-- An element of the ideal that is homogeneous, composed on both sides with arbitrary linear
combinations: all its homogeneous components lie in the ideal. -/
theorem homogeneousComponent_comp_comp_mem_ideal {a' b' : Obj S} {W : LinDiagram R a' b'}
    {e : A} (hW : W ∈ LinDiagram.homDeg R deg a' b' e) (hWI : W ∈ P.ideal a' b')
    (pre : LinDiagram R a a') (post : LinDiagram R b' b) (d : A) :
    LinDiagram.homogeneousComponent deg d (pre ≫ W ≫ post) ∈ P.ideal a b := by
  induction pre using Finsupp.induction_linear with
  | zero => erw [Limits.zero_comp, map_zero]; exact Submodule.zero_mem _
  | add f₁ f₂ h₁ h₂ =>
    erw [Preadditive.add_comp, map_add]; exact Submodule.add_mem _ h₁ h₂
  | single p r =>
    induction post using Finsupp.induction_linear with
    | zero => erw [Limits.comp_zero, Limits.comp_zero, map_zero]; exact Submodule.zero_mem _
    | add g₁ g₂ h₁ h₂ =>
      erw [Preadditive.comp_add, Preadditive.comp_add, map_add]; exact Submodule.add_mem _ h₁ h₂
    | single q s =>
      have hX := LinDiagram.comp_mem_homDeg (LinDiagram.single_mem_homDeg (deg := deg) p r)
        (LinDiagram.comp_mem_homDeg hW (LinDiagram.single_mem_homDeg (deg := deg) q s))
      have hXI : (Finsupp.single p r : LinDiagram R a a') ≫ W ≫
          (Finsupp.single q s : LinDiagram R b' b) ∈ P.ideal a b :=
        P.comp_mem_ideal _ (P.mem_ideal_comp hWI _)
      by_cases hd : Diagram.degree deg p + (e + Diagram.degree deg q) = d
      · have key := LinDiagram.homogeneousComponent_of_mem (hd ▸ hX)
        erw [key]; exact hXI
      · have key := LinDiagram.homogeneousComponent_of_mem_of_ne hX hd
        erw [key]; exact Submodule.zero_mem _

/-- For a homogeneous presentation, the tensor ideal is homogeneous: it is closed under taking
homogeneous components. -/
theorem homogeneousComponent_mem_ideal (hP : P.IsHomogeneous deg) {f : LinDiagram R a b}
    (hf : f ∈ P.ideal a b) (d : A) : LinDiagram.homogeneousComponent deg d f ∈ P.ideal a b := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, u, v, hw, pre, post⟩ := hx
    obtain ⟨e, he⟩ := hP.allRel k
    exact homogeneousComponent_comp_comp_mem_ideal (LinDiagram.whisker_mem_homDeg he u v hw)
      (P.whisker_rel_mem_ideal k u v hw) pre post d
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx

/-! ## Graded Hom-spaces of the presented category -/

variable (P)

/-- The class map `P.lin` as an `R`-linear map. -/
def linMap (a b : Obj S) : LinDiagram R a b →ₗ[R] (P.obj a ⟶ P.obj b) where
  toFun := P.lin
  map_add' := P.lin_add
  map_smul' := P.lin_smul

@[simp] theorem linMap_apply (f : LinDiagram R a b) : P.linMap a b f = P.lin f := rfl

variable (deg)

/-- The degree-`d` part of the Hom-space from `a` to `b` of the presented category: the classes
of linear combinations of diagrams of degree `d`. -/
def homDeg (a b : Obj S) (d : A) : Submodule R (P.obj a ⟶ P.obj b) :=
  (LinDiagram.homDeg R deg a b d).map (P.linMap a b)

variable {P deg}

theorem mem_homDeg_iff {x : P.obj a ⟶ P.obj b} {d : A} :
    x ∈ P.homDeg deg a b d ↔ ∃ f ∈ LinDiagram.homDeg R deg a b d, P.lin f = x :=
  Submodule.mem_map

theorem lin_mem_homDeg {f : LinDiagram R a b} {d : A}
    (hf : f ∈ LinDiagram.homDeg R deg a b d) : P.lin f ∈ P.homDeg deg a b d :=
  mem_homDeg_iff.mpr ⟨f, hf, rfl⟩

variable (P) in
theorem diag_mem_homDeg (g : a ⟶ b) : P.diag g ∈ P.homDeg deg a b (Diagram.degree deg g) :=
  lin_mem_homDeg (LinDiagram.of_mem_homDeg g)

theorem diag_mem_homDeg' {g : a ⟶ b} {d : A} (h : Diagram.degree deg g = d) :
    P.diag g ∈ P.homDeg deg a b d :=
  h ▸ P.diag_mem_homDeg g

variable (P deg) in
theorem id_mem_homDeg (a : Obj S) : 𝟙 (P.obj a) ∈ P.homDeg deg a a 0 :=
  P.lin_id a ▸ lin_mem_homDeg (LinDiagram.id_mem_homDeg a)

/-- Composition in the presented category adds degrees:
`homDeg d ≫ homDeg e ⊆ homDeg (d + e)`. -/
theorem comp_mem_homDeg {f : P.obj a ⟶ P.obj b} {g : P.obj b ⟶ P.obj c} {d e : A}
    (hf : f ∈ P.homDeg deg a b d) (hg : g ∈ P.homDeg deg b c e) :
    f ≫ g ∈ P.homDeg deg a c (d + e) := by
  obtain ⟨f, hf', rfl⟩ := mem_homDeg_iff.mp hf
  obtain ⟨g, hg', rfl⟩ := mem_homDeg_iff.mp hg
  rw [← lin_comp]
  exact lin_mem_homDeg (LinDiagram.comp_mem_homDeg hf' hg')

/-- Whiskering preserves degrees. -/
theorem whisk_mem_homDeg {f : P.obj a ⟶ P.obj b} {d : A} (hf : f ∈ P.homDeg deg a b d)
    (u : Obj S) (v : List S.Colour) : P.whisk f u v ∈ P.homDeg deg _ _ d := by
  obtain ⟨f, hf', rfl⟩ := mem_homDeg_iff.mp hf
  rw [whisk_lin]
  exact lin_mem_homDeg (LinDiagram.whisk_mem_homDeg hf' u v)

variable (P deg) in
/-- Without any hypothesis on the presentation, the homogeneous parts span each Hom-space. -/
theorem iSup_homDeg (a b : Obj S) : ⨆ d, P.homDeg deg a b d = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  induction x using P.hom_induction with
  | diag g => exact Submodule.mem_iSup_of_mem _ (P.diag_mem_homDeg g)
  | zero => exact Submodule.zero_mem _
  | add f g hf hg => exact Submodule.add_mem _ hf hg
  | smul r f hf => exact Submodule.smul_mem _ r hf

/-- The projection onto the degree-`d` part of a Hom-space of the presented category of a
homogeneous presentation, induced by `LinDiagram.homogeneousComponent`. -/
def homogeneousComponent (hP : P.IsHomogeneous deg) (d : A) :
    (P.obj a ⟶ P.obj b) →ₗ[R] (P.obj a ⟶ P.obj b) where
  toFun x := Quot.lift (fun g : LinDiagram R a b => P.lin (LinDiagram.homogeneousComponent deg d g))
    (fun g₁ g₂ h => by
      have h' : P.homRel g₁ g₂ := by
        rwa [CategoryTheory.Quotient.compClosure_eq_self] at h
      rw [lin_eq_iff, ← map_sub]
      exact homogeneousComponent_mem_ideal hP h' d) x
  map_add' x y := by
    obtain ⟨x, rfl⟩ := P.lin_surjective x
    obtain ⟨y, rfl⟩ := P.lin_surjective y
    rw [← lin_add]
    show P.lin _ = P.lin _ + P.lin _
    rw [map_add, lin_add]
  map_smul' r x := by
    obtain ⟨x, rfl⟩ := P.lin_surjective x
    rw [← lin_smul]
    show P.lin _ = r • P.lin _
    rw [map_smul, lin_smul]

@[simp] theorem homogeneousComponent_lin (hP : P.IsHomogeneous deg) (d : A)
    (f : LinDiagram R a b) :
    homogeneousComponent hP d (P.lin f) = P.lin (LinDiagram.homogeneousComponent deg d f) := rfl

theorem homogeneousComponent_mem (hP : P.IsHomogeneous deg) (d : A) (x : P.obj a ⟶ P.obj b) :
    homogeneousComponent hP d x ∈ P.homDeg deg a b d := by
  obtain ⟨x, rfl⟩ := P.lin_surjective x
  rw [homogeneousComponent_lin]
  exact lin_mem_homDeg (LinDiagram.homogeneousComponent_mem d x)

theorem homogeneousComponent_of_mem (hP : P.IsHomogeneous deg) {d : A}
    {x : P.obj a ⟶ P.obj b} (hx : x ∈ P.homDeg deg a b d) :
    homogeneousComponent hP d x = x := by
  obtain ⟨f, hf, rfl⟩ := mem_homDeg_iff.mp hx
  rw [homogeneousComponent_lin, LinDiagram.homogeneousComponent_of_mem hf]

theorem homogeneousComponent_of_mem_of_ne (hP : P.IsHomogeneous deg) {d e : A}
    {x : P.obj a ⟶ P.obj b} (hx : x ∈ P.homDeg deg a b e) (h : e ≠ d) :
    homogeneousComponent hP d x = 0 := by
  obtain ⟨f, hf, rfl⟩ := mem_homDeg_iff.mp hx
  rw [homogeneousComponent_lin, LinDiagram.homogeneousComponent_of_mem_of_ne hf h, lin_zero]

/-- For a homogeneous presentation, the homogeneous parts of a Hom-space are independent. -/
theorem iSupIndep_homDeg (hP : P.IsHomogeneous deg) (a b : Obj S) :
    iSupIndep (P.homDeg deg a b) := by
  intro d
  rw [Submodule.disjoint_def]
  intro x hx hx'
  have hker : (⨆ (e) (_ : e ≠ d), P.homDeg deg a b e) ≤
      LinearMap.ker (homogeneousComponent hP d) :=
    iSup₂_le fun e he y hy => homogeneousComponent_of_mem_of_ne hP hy he
  rw [← homogeneousComponent_of_mem hP hx]
  exact hker hx'

/-- **Graded Hom-spaces.** For a homogeneous presentation, every Hom-space of the presented
category is the internal direct sum of its homogeneous parts `P.homDeg deg a b d`. -/
theorem isInternal_homDeg [DecidableEq A] (hP : P.IsHomogeneous deg) (a b : Obj S) :
    DirectSum.IsInternal (P.homDeg deg a b) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (iSupIndep_homDeg hP a b)
    (iSup_homDeg P deg a b)

/-- The decomposition of a Hom-space of the presented category of a homogeneous presentation
into its homogeneous parts. -/
def decomposition [DecidableEq A] (hP : P.IsHomogeneous deg) (a b : Obj S) :
    DirectSum.Decomposition (P.homDeg deg a b) :=
  (isInternal_homDeg hP a b).chooseDecomposition

/-- The components of the decomposition are the projections `homogeneousComponent`. -/
theorem decompose_apply [DecidableEq A] (hP : P.IsHomogeneous deg) (x : P.obj a ⟶ P.obj b)
    (d : A) :
    letI := decomposition hP a b
    (DirectSum.decompose (P.homDeg deg a b) x d : P.obj a ⟶ P.obj b) =
      homogeneousComponent hP d x := by
  letI := decomposition hP a b
  induction x using P.hom_induction with
  | diag g =>
    by_cases h : Diagram.degree deg g = d
    · rw [DirectSum.decompose_of_mem_same _ (h ▸ P.diag_mem_homDeg g),
        homogeneousComponent_of_mem hP (h ▸ P.diag_mem_homDeg g)]
    · rw [DirectSum.decompose_of_mem_ne _ (P.diag_mem_homDeg g) h,
        homogeneousComponent_of_mem_of_ne hP (P.diag_mem_homDeg g) h]
  | zero => simp
  | add f g hf hg =>
    rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add, hf, hg, map_add]
  | smul r f hf =>
    rw [DirectSum.decompose_smul, DirectSum.smul_apply, Submodule.coe_smul, hf, map_smul]

/-! ## Graded endomorphism algebras -/

variable (P deg) in
/-- The degree-`d` part of the endomorphism algebra of `P.obj a`. -/
abbrev endDeg (a : Obj S) (d : A) : Submodule R (End (P.obj a)) := P.homDeg deg a a d

instance (a : Obj S) : SetLike.GradedMonoid (P.endDeg deg a) where
  one_mem := P.id_mem_homDeg deg a
  mul_mem i j x y hx hy := by
    rw [End.mul_def, add_comm]
    exact comp_mem_homDeg hy hx

/-- For a homogeneous presentation, the endomorphism algebra of every object of the presented
category is an `A`-graded `R`-algebra. -/
def gradedAlgebra [DecidableEq A] (hP : P.IsHomogeneous deg) (a : Obj S) :
    GradedAlgebra (P.endDeg deg a) :=
  { decomposition hP a a with }

end Presentation

end StringDiagrams

end
