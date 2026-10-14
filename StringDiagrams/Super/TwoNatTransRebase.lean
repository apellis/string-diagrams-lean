import StringDiagrams.Super.TwoFunctorPostcompositionComposition
import StringDiagrams.Super.TwoFunctorPrecomposition

/-!
# Transport of 2-natural transformations along equalities of 2-superfunctors

For 2-superfunctors `F = F'` and `G = G'`, a transformation `θ : F ⟹ G` is transported to
`TwoNatTrans.rebase h j θ : F' ⟹ G'`. Its components agree with those of `θ` up to `HEq`, and
strength and grading are preserved.

The section on heterogeneous equality compares transformations whose endpoints differ by
the associativity and unit equalities of composition of 2-superfunctors
(`TwoSuperfunctor.comp_assoc`, `TwoSuperfunctor.comp_id`, `TwoSuperfunctor.id_comp`):
* `TwoNatTrans.hext`: two transformations are `HEq` once their components are;
* `postcompose_comp_heq`: `(H ⋙ K) ∘ θ` and `K ∘ (H ∘ θ)`;
* `precompose_postcompose_heq`: `(H ∘ θ) ∘ P` and `H ∘ (θ ∘ P)`;
* `precompose_precompose_heq`: `(θ ∘ Q) ∘ P` and `θ ∘ (P ⋙ Q)`.

These are the bookkeeping steps used when pasting the zigzags of a unit and counit of a
biequivalence of 2-supercategories (see `StringDiagrams.Super.TwoNatTransZigzag`).
-/

noncomputable section
namespace StringDiagrams.TwoNatTrans
open CategoryTheory Supercategory BicategoryStruct
universe r u v w u' v' w' u'' v'' w'' u''' v''' w'''
variable {R : Type r} [CommRing R]
  {A : Type u} [BicategoryStruct.{w, v} A]
  [∀ a b : A, Preadditive (a ⟶ b)] [∀ a b : A, Linear R (a ⟶ b)]
  [∀ a b : A, Supercategory R (a ⟶ b)]
  {B : Type u'} [BicategoryStruct.{w', v'} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)]
  {C : Type u''} [BicategoryStruct.{w'', v''} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)]
  [∀ a b : C, Supercategory R (a ⟶ b)]

section Rebase
variable {F F' G G' : TwoSuperfunctor R A B}

/-- Transport a transformation along equalities of its source and target. -/
def rebase (h : F = F') (j : G = G') (θ : TwoNatTrans F G) : TwoNatTrans F' G' := by
  cases h
  cases j
  exact θ

theorem rebase_X (h : F = F') (j : G = G') (θ : TwoNatTrans F G) (a : A) :
    HEq ((rebase h j θ).X a) (θ.X a) := by
  subst h j
  rfl

theorem rebase_x (h : F = F') (j : G = G') (θ : TwoNatTrans F G)
    {a b : A} (f : a ⟶ b) : HEq ((rebase h j θ).x f) (θ.x f) := by
  subst h j
  rfl

theorem rebase_heq (h : F = F') (j : G = G') (θ : TwoNatTrans F G) :
    HEq (rebase h j θ) θ := by
  subst h j
  rfl

theorem rebase_isStrong (h : F = F') (j : G = G') (θ : TwoNatTrans F G)
    (hθ : θ.IsStrong) : (rebase h j θ).IsStrong := by
  subst h j
  exact hθ

theorem rebase_isGraded [∀ a b : B, GradedSupercategory R (a ⟶ b)]
    (h : F = F') (j : G = G') (θ : TwoNatTrans F G)
    (hθ : θ.IsGraded) : (rebase h j θ).IsGraded := by
  subst h j
  exact hθ

/-- Transformations with equal endpoints are heterogeneously equal once their object
components and naturality cells are. -/
theorem hext (hF : F = F') (hG : G = G') (θ : TwoNatTrans F G) (ψ : TwoNatTrans F' G')
    (hX : ∀ a, HEq (θ.X a) (ψ.X a))
    (hx : ∀ {a b : A} (f : a ⟶ b), HEq (θ.x f) (ψ.x f)) : HEq θ ψ := by
  subst F' G'
  obtain ⟨X, x, _, _, _, _⟩ := θ
  obtain ⟨Y, y, _, _, _, _⟩ := ψ
  have h : X = Y := funext fun a => eq_of_heq (hX a)
  subst Y
  have h : @x = @y := by
    funext a b f
    exact eq_of_heq (hx f)
  subst y
  rfl

theorem postcompose_heq [TwoSupercategory R C] (hF : F = F') (hG : G = G')
    (H : TwoSuperfunctor R B C)
    {θ : TwoNatTrans F G} {ψ : TwoNatTrans F' G'} (h : HEq θ ψ) :
    HEq (postcompose H θ) (postcompose H ψ) := by
  subst F' G'
  cases eq_of_heq h
  rfl
end Rebase

theorem precompose_heq [TwoSupercategory R C] (P : TwoSuperfunctor R A B)
    {F G F' G' : TwoSuperfunctor R B C} (hF : F = F') (hG : G = G')
    {θ : TwoNatTrans F G} {ψ : TwoNatTrans F' G'} (h : HEq θ ψ) :
    HEq (precompose P θ) (precompose P ψ) := by
  subst F' G'
  cases eq_of_heq h
  rfl

section Composition
variable {D : Type u'''} [BicategoryStruct.{w''', v'''} D]
  [∀ a b : D, Preadditive (a ⟶ b)] [∀ a b : D, Linear R (a ⟶ b)]
  [∀ a b : D, Supercategory R (a ⟶ b)] [TwoSupercategory R D]

theorem postcompose_comp_heq [TwoSupercategory R C] {F G : TwoSuperfunctor R A B}
    (H : TwoSuperfunctor R B C) (K : TwoSuperfunctor R C D) (θ : TwoNatTrans F G) :
    HEq (postcompose (H.comp K) θ) (postcompose K (postcompose H θ)) := by
  apply hext (TwoSuperfunctor.comp_assoc F H K).symm
    (TwoSuperfunctor.comp_assoc G H K).symm
  · intro a
    rfl
  · intro a b f
    apply heq_of_eq
    change ((K.mapComp _ _).hom ≫ K.map₂ (H.mapComp _ _).hom) ≫
      K.map₂ (H.map₂ (θ.x f)) ≫
      (K.map₂ (H.mapComp _ _).inv ≫ (K.mapComp _ _).inv) =
      (K.mapComp _ _).hom ≫
      K.map₂ ((H.mapComp _ _).hom ≫ H.map₂ (θ.x f) ≫ (H.mapComp _ _).inv) ≫
      (K.mapComp _ _).inv
    simp only [K.map₂_comp, Category.assoc]

theorem precompose_postcompose_heq [TwoSupercategory R C] (P : TwoSuperfunctor R A B)
    {F G : TwoSuperfunctor R B C} (H : TwoSuperfunctor R C D) (θ : TwoNatTrans F G) :
    HEq (precompose P (postcompose H θ)) (postcompose H (precompose P θ)) := by
  apply hext (TwoSuperfunctor.comp_assoc P F H).symm
    (TwoSuperfunctor.comp_assoc P G H).symm
  · intro a
    rfl
  · intro a b f
    rfl

theorem precompose_precompose_heq [TwoSupercategory R C] (P : TwoSuperfunctor R A B) (Q : TwoSuperfunctor R B C)
    {F G : TwoSuperfunctor R C D} (θ : TwoNatTrans F G) :
    HEq (precompose P (precompose Q θ)) (precompose (P.comp Q) θ) := by
  apply hext (TwoSuperfunctor.comp_assoc P Q F).symm
    (TwoSuperfunctor.comp_assoc P Q G).symm
  · intro a
    rfl
  · intro a b f
    rfl
end Composition
end StringDiagrams.TwoNatTrans
