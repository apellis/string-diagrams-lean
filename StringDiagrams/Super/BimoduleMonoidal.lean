import StringDiagrams.Super.BalancedTensor
import StringDiagrams.Super.MonoidalPi

/-!
# The monoidal Π-supercategory `A-SMod-A`

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3,
Example 1.5(i) and Example 1.13(i), for an arbitrary superalgebra `A` over the commutative
ground ring `k`.

* **Example 1.5(i).** `A-SMod-A` is a monoidal supercategory with tensor functor the balanced
  tensor product `- ⊗_A -` (`StringDiagrams.Super.BalancedTensor`) and unit object the regular
  superbimodule `A` (`SuperBimodule.instMonoidalSupercategory`). The tensor product of
  morphisms carries the Koszul sign: for the paper's `f ⊗ g = (f ⊗ 1) ∘ (1 ⊗ g)`,
  `(f ⊗ g)(m ⊗ n) = (-1)^{|g||m|} f(m) ⊗ g(n)` (`SuperBimodule.superTensorHom_btmul`).
* **Example 1.13(i).** `A-SMod-A` is a monoidal Π-supercategory with `π := Π A` and
  `ζ : Π A → A` the identity function (`SuperBimodule.instMonoidalPiSupercategory`).

For `A = k` (concentrated in even parity) these recover the structures on `SVec k`
(`StringDiagrams.Super.SVec`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory MonoidalCategory Supercategory

universe u

namespace SuperBimodule

variable {k : Type u} [CommRing k] {A : Type u} [Ring A] [Algebra k A]
  {𝒜 : ZMod 2 → Submodule k A} [GradedAlgebra 𝒜]

instance instMonoidalCategoryStruct : MonoidalCategoryStruct (SuperBimodule 𝒜 𝒜) where
  tensorObj := tensor
  whiskerLeft := whiskerLeft
  whiskerRight := whiskerRight
  tensorUnit := regular 𝒜
  associator := assoc
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor

theorem tensorObj_def (M N : SuperBimodule 𝒜 𝒜) : M ⊗ N = tensor M N := rfl

theorem tensorUnit_def : 𝟙_ (SuperBimodule 𝒜 𝒜) = regular 𝒜 := rfl

theorem whiskerLeft_def (M : SuperBimodule 𝒜 𝒜) {N N' : SuperBimodule 𝒜 𝒜} (g : N ⟶ N') :
    M ◁ g = whiskerLeft M g := rfl

theorem whiskerRight_def {M M' : SuperBimodule 𝒜 𝒜} (f : M ⟶ M') (N : SuperBimodule 𝒜 𝒜) :
    f ▷ N = whiskerRight f N := rfl

theorem associator_def (M N P : SuperBimodule 𝒜 𝒜) : α_ M N P = assoc M N P := rfl

theorem leftUnitor_def (M : SuperBimodule 𝒜 𝒜) : λ_ M = leftUnitor M := rfl

theorem rightUnitor_def (M : SuperBimodule 𝒜 𝒜) : ρ_ M = rightUnitor M := rfl

/-- **Brundan–Ellis, Example 1.5(i).** For a superalgebra `A`, `A-SMod-A` is a monoidal
supercategory, with tensor functor the tensor product of superbimodules over `A` and unit
object the regular superbimodule `A`. -/
instance instMonoidalSupercategory : MonoidalSupercategory k (SuperBimodule 𝒜 𝒜) where
  tensorHom_def _ _ := rfl
  whiskerLeft_id := whiskerLeft_id
  id_whiskerRight := id_whiskerRight
  whiskerLeft_comp M _ _ _ f g := whiskerLeft_comp M f g
  comp_whiskerRight f g N := comp_whiskerRight f N g
  whiskerLeft_add M _ _ f g := whiskerLeft_add M f g
  add_whiskerRight f g N := add_whiskerRight f N g
  whiskerLeft_smul M _ _ r f := whiskerLeft_smul M f r
  smul_whiskerRight r f N := smul_whiskerRight f N r
  whiskerLeft_mem M _ _ _ _ hg := whiskerLeft_mem M _ hg
  whiskerRight_mem N hf := whiskerRight_mem _ hf N
  super_interchange hf hg := super_interchange _ _ hf hg
  associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} f₁ f₂ f₃ := by
    change (whiskerRight (whiskerRight f₁ X₂ ≫ whiskerLeft Y₁ f₂) X₃ ≫
        whiskerLeft (tensor Y₁ Y₂) f₃) ≫ (assoc Y₁ Y₂ Y₃).hom =
      (assoc X₁ X₂ X₃).hom ≫
        (whiskerRight f₁ (tensor X₂ X₃) ≫ whiskerLeft Y₁ (whiskerRight f₂ X₃ ≫ whiskerLeft Y₂ f₃))
    rw [comp_whiskerRight, Category.assoc, Category.assoc, assoc_naturality_right,
      ← Category.assoc (whiskerRight (whiskerLeft Y₁ f₂) X₃), assoc_naturality_middle]
    simp only [Category.assoc]
    rw [← Category.assoc (whiskerRight (whiskerRight f₁ X₂) X₃), assoc_naturality_left,
      whiskerLeft_comp]
    simp only [Category.assoc]
  leftUnitor_naturality f := leftUnitor_naturality _ f
  rightUnitor_naturality f := rightUnitor_naturality _ f
  pentagon W X Y Z := pentagon W X Y Z
  triangle X Y := triangle X Y
  associator_hom_mem X Y Z := assoc_hom_mem X Y Z
  leftUnitor_hom_mem := leftUnitor_hom_mem
  rightUnitor_hom_mem := rightUnitor_hom_mem

/-- **The Koszul sign rule** in `A-SMod-A`: the paper's tensor product of superbimodule
homomorphisms `f ⊗ g = (f ⊗ 1) ∘ (1 ⊗ g)` is `(f ⊗ g)(m ⊗ n) = (-1)^{|g||m|} f(m) ⊗ g(n)`. -/
theorem superTensorHom_btmul {M M' N N' : SuperBimodule 𝒜 𝒜} (f : M ⟶ M') {q : ZMod 2}
    {g : N ⟶ N'} (hg : g ∈ parity (R := k) N N' q) {p : ZMod 2} {m : M.toSVec}
    (hm : m ∈ M.toSVec.part p) (n : N.toSVec) :
    (MonoidalSupercategory.superTensorHom f g).1 (btmul M N m n) =
      sign k (q * p) • btmul M' N' (f.1 m) (g.1 n) := by
  change (whiskerLeft M g ≫ whiskerRight f N').1 (btmul M N m n) = _
  rw [comp_val, SVec.comp_apply, whiskerLeft_btmul M g hg hm, SVec.hom_map_smul,
    whiskerRight_btmul, mul_comm]

/-- **Brundan–Ellis, Example 1.13(i).** `A-SMod-A` is a monoidal Π-supercategory with
`π := Π A` and `ζ : Π A → A` the identity function. -/
instance instMonoidalPiSupercategory : MonoidalPiSupercategory k (SuperBimodule 𝒜 𝒜) where
  pi := piObj (regular 𝒜)
  ζ := ζIso (regular 𝒜)
  ζ_hom_mem := ζIso_hom_mem (regular 𝒜)

theorem monoidalPi_pi_def : MonoidalPiSupercategory.pi (R := k) (C := SuperBimodule 𝒜 𝒜) =
    piObj (regular 𝒜) := rfl

theorem monoidalPi_ζ_def : MonoidalPiSupercategory.ζ (R := k) (C := SuperBimodule 𝒜 𝒜) =
    ζIso (regular 𝒜) := rfl

end SuperBimodule

end StringDiagrams

end
