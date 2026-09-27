import StringDiagrams.Monoidal
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Transport along equalities of objects

Objects of the free 2-category are words, and equalities between them (for instance
`strands (i + 2 + j) = strands n`) are frequent when diagrams are placed at symbolic positions.
This file provides one family of lemmas for moving morphisms of a presented category, and
equalities between them, along such equalities.

* `Presentation.castHom ha hb f = eqToHom ≫ f ≫ eqToHom`: a morphism
  `P.obj a ⟶ P.obj b` retyped along `a = a'` and `b = b'`. It sends classes of diagrams to
  classes of retyped diagrams (`castHom_diag`), is compatible with composition and identities
  (`castHom_comp`, `castHom_id`), and is an `R`-linear equivalence (`castLinearEquiv`); on
  endomorphisms it is an isomorphism of `R`-algebras (`endCast`).
* `Presentation.diag_eq_castHom_of_layers_eq`: diagrams with the same list of layers have the
  same class up to retyping; hence an equality (or any linear relation) between classes of
  diagrams transfers to diagrams with the same layers between equal objects
  (`Presentation.diag_transfer`, `Presentation.diag_eq_diag_iff_of_layers_eq`).
* `Presentation.lin_cast`: retyping linear combinations of diagrams.
* `Presentation.mem_subalgebra_of_layers`: if every layer with source `a` has target `a`, then
  `End (P.obj a)` is generated as an `R`-algebra by the classes of the single layers.

The basic retyping lemma `Presentation.diag_cast` is in `StringDiagrams.Monoidal`.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory

universe w v u₀ u₁ u₂

variable {S : Signature.{u₀, u₁, u₂}}

namespace Presentation

variable {R : Type w} [CommRing R] (P : Presentation.{w, v} S R)

variable {a b c a' b' c' a'' b'' : Obj S}

/-- Retyping of linear combinations of diagrams. -/
theorem lin_cast (f : LinDiagram R a b) (ha : a = a') (hb : b = b') :
    P.lin (LinDiagram.cast f ha hb) =
      eqToHom (congrArg P.obj ha.symm) ≫ P.lin f ≫ eqToHom (congrArg P.obj hb) := by
  subst ha hb; simp

/-- A morphism of the presented category retyped along equalities of its boundary objects. -/
def castHom (ha : a = a') (hb : b = b') (f : P.obj a ⟶ P.obj b) : P.obj a' ⟶ P.obj b' :=
  eqToHom (congrArg P.obj ha.symm) ≫ f ≫ eqToHom (congrArg P.obj hb)

@[simp] theorem castHom_rfl (f : P.obj a ⟶ P.obj b) : P.castHom rfl rfl f = f := by
  simp [castHom]

@[simp] theorem castHom_diag (f : a ⟶ b) (ha : a = a') (hb : b = b') :
    P.castHom ha hb (P.diag f) = P.diag (Diagram.cast f ha hb) :=
  (P.diag_cast f ha hb).symm

@[simp] theorem castHom_lin (f : LinDiagram R a b) (ha : a = a') (hb : b = b') :
    P.castHom ha hb (P.lin f) = P.lin (LinDiagram.cast f ha hb) :=
  (P.lin_cast f ha hb).symm

@[simp] theorem castHom_castHom (ha : a = a') (hb : b = b') (ha' : a' = a'') (hb' : b' = b'')
    (f : P.obj a ⟶ P.obj b) :
    P.castHom ha' hb' (P.castHom ha hb f) = P.castHom (ha.trans ha') (hb.trans hb') f := by
  subst ha hb ha' hb'; simp

theorem castHom_comp (ha : a = a') (hb : b = b') (hc : c = c') (f : P.obj a ⟶ P.obj b)
    (g : P.obj b ⟶ P.obj c) :
    P.castHom ha hc (f ≫ g) = P.castHom ha hb f ≫ P.castHom hb hc g := by
  subst ha hb hc; simp

@[simp] theorem castHom_id (ha : a = a') : P.castHom ha ha (𝟙 (P.obj a)) = 𝟙 _ := by
  subst ha; simp

theorem castHom_eqToHom (ha : a = a') (hb : b = b') (h : P.obj a = P.obj b) :
    P.castHom ha hb (eqToHom h) = eqToHom (by rw [← ha, ← hb, h]) := by
  subst ha hb; simp

theorem castHom_eq_iff (ha : a = a') (hb : b = b') (f : P.obj a ⟶ P.obj b)
    (g : P.obj a' ⟶ P.obj b') : P.castHom ha hb f = g ↔ f = P.castHom ha.symm hb.symm g := by
  subst ha hb; simp

theorem castHom_injective (ha : a = a') (hb : b = b') : Function.Injective (P.castHom ha hb) := by
  intro f g h
  subst ha hb
  simpa using h

@[simp] theorem castHom_inj (ha : a = a') (hb : b = b') {f g : P.obj a ⟶ P.obj b} :
    P.castHom ha hb f = P.castHom ha hb g ↔ f = g :=
  (P.castHom_injective ha hb).eq_iff

/-- Whiskering commutes with retyping. -/
theorem whisk_castHom (ha : a = a') (hb : b = b') (f : P.obj a ⟶ P.obj b) (u : Obj S)
    (v : List S.Colour) :
    P.whisk (P.castHom ha hb f) u v =
      P.castHom (congrArg (Obj.whisker · u v) ha) (congrArg (Obj.whisker · u v) hb)
        (P.whisk f u v) := by
  subst ha hb; simp

/-- Retyping as an `R`-linear equivalence of Hom modules. -/
def castLinearEquiv (ha : a = a') (hb : b = b') :
    (P.obj a ⟶ P.obj b) ≃ₗ[R] (P.obj a' ⟶ P.obj b') where
  toFun := P.castHom ha hb
  invFun := P.castHom ha.symm hb.symm
  map_add' f g := by simp [castHom]
  map_smul' r f := by simp [castHom]
  left_inv f := by simp
  right_inv f := by simp

@[simp] theorem castLinearEquiv_apply (ha : a = a') (hb : b = b') (f : P.obj a ⟶ P.obj b) :
    P.castLinearEquiv ha hb f = P.castHom ha hb f := rfl

@[simp] theorem castLinearEquiv_symm_apply (ha : a = a') (hb : b = b')
    (f : P.obj a' ⟶ P.obj b') :
    (P.castLinearEquiv ha hb).symm f = P.castHom ha.symm hb.symm f := rfl

theorem castHom_add (ha : a = a') (hb : b = b') (f g : P.obj a ⟶ P.obj b) :
    P.castHom ha hb (f + g) = P.castHom ha hb f + P.castHom ha hb g :=
  (P.castLinearEquiv ha hb).map_add f g

theorem castHom_sub (ha : a = a') (hb : b = b') (f g : P.obj a ⟶ P.obj b) :
    P.castHom ha hb (f - g) = P.castHom ha hb f - P.castHom ha hb g :=
  (P.castLinearEquiv ha hb).map_sub f g

theorem castHom_neg (ha : a = a') (hb : b = b') (f : P.obj a ⟶ P.obj b) :
    P.castHom ha hb (-f) = -P.castHom ha hb f :=
  (P.castLinearEquiv ha hb).map_neg f

@[simp] theorem castHom_zero (ha : a = a') (hb : b = b') :
    P.castHom ha hb (0 : P.obj a ⟶ P.obj b) = 0 :=
  (P.castLinearEquiv ha hb).map_zero

theorem castHom_smul (ha : a = a') (hb : b = b') (r : R) (f : P.obj a ⟶ P.obj b) :
    P.castHom ha hb (r • f) = r • P.castHom ha hb f :=
  (P.castLinearEquiv ha hb).map_smul r f

/-- Retyping of endomorphisms as an isomorphism of `R`-algebras. -/
def endCast (h : a = a') : End (P.obj a) ≃ₐ[R] End (P.obj a') where
  toFun := P.castHom h h
  invFun := P.castHom h.symm h.symm
  left_inv f := by simp
  right_inv f := by simp
  map_mul' f g := by
    rw [End.mul_def, End.mul_def, P.castHom_comp h h h]
  map_add' f g := P.castHom_add h h f g
  commutes' r := by
    subst h
    simp

@[simp] theorem endCast_apply (h : a = a') (f : End (P.obj a)) : P.endCast h f = P.castHom h h f :=
  rfl

@[simp] theorem endCast_symm_apply (h : a = a') (f : End (P.obj a')) :
    (P.endCast h).symm f = P.castHom h.symm h.symm f := rfl

/-! ## Diagrams with the same layers -/

/-- Diagrams with the same layers have the same class, up to retyping. -/
theorem diag_eq_castHom_of_layers_eq (f : a ⟶ b) (g : a' ⟶ b') (ha : a' = a) (hb : b' = b)
    (h : Diagram.layers f = Diagram.layers g) : P.diag f = P.castHom ha hb (P.diag g) := by
  rw [castHom_diag]
  exact P.diag_eq_of_layers_eq h

/-- Transfer of an equality of classes of diagrams to diagrams with the same layers between
equal objects. -/
theorem diag_transfer (A B : a ⟶ b) (A' B' : a' ⟶ b') (ha : a = a') (hb : b = b')
    (hA : Diagram.layers A = Diagram.layers A') (hB : Diagram.layers B = Diagram.layers B')
    (h : P.diag A' = P.diag B') : P.diag A = P.diag B := by
  rw [P.diag_eq_castHom_of_layers_eq A A' ha.symm hb.symm hA,
    P.diag_eq_castHom_of_layers_eq B B' ha.symm hb.symm hB, h]

theorem diag_eq_diag_iff_of_layers_eq (A B : a ⟶ b) (A' B' : a' ⟶ b') (ha : a = a')
    (hb : b = b') (hA : Diagram.layers A = Diagram.layers A')
    (hB : Diagram.layers B = Diagram.layers B') : P.diag A = P.diag B ↔ P.diag A' = P.diag B' :=
  ⟨P.diag_transfer A' B' A B ha.symm hb.symm hA.symm hB.symm,
    P.diag_transfer A B A' B' ha hb hA hB⟩

/-! ## Generation of endomorphism algebras by layers -/

/-- **Generation of an endomorphism algebra by layers.** If every layer with source `a` has
target `a` (for instance, `a` is the object of `n` strands in a one-colour signature whose
generators preserve the number of strands), then every endomorphism of `a` lies in any
subalgebra containing the classes of all single layers with source `a`. -/
theorem mem_subalgebra_of_layers {a : Obj S}
    (ha : ∀ (L : Layer S), L.Valid → L.dom = a → L.cod = a) (A : Subalgebra R (End (P.obj a)))
    (hA : ∀ (L : Layer S) (hv : L.Valid) (hd : L.dom = a), P.layer L hv hd (ha L hv hd) ∈ A)
    (f : End (P.obj a)) : f ∈ A := by
  let M : ∀ x y : Obj S, Submodule R (P.obj x ⟶ P.obj y) := fun x y =>
    { carrier := {g | ∀ (hx : x = a) (hy : y = a), P.castHom hx hy g ∈ A}
      add_mem' := fun hf hg hx hy => by
        rw [castHom_add]; exact A.add_mem (hf hx hy) (hg hx hy)
      zero_mem' := fun hx hy => by rw [castHom_zero]; exact A.zero_mem
      smul_mem' := fun r g hg hx hy => by rw [castHom_smul]; exact A.smul_mem (hg hx hy) r }
  have key := P.mem_of_layers {x | x = a} (fun L hv hL => ha L hv hL) M
    (fun x hx hx' _ => by rw [castHom_id]; exact A.one_mem)
    (fun {x y z} _ hy _ g g' hg hg' hx hz => by
      rw [P.castHom_comp hx hy hz]; exact A.mul_mem (hg' hy hz) (hg hx hy))
    (fun L hv hL hx hy => by
      rw [castHom_diag]
      exact hA L hv hx) rfl rfl f
  simpa using key rfl rfl

end Presentation

end StringDiagrams

end
