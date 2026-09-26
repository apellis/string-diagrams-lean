import StringDiagrams.Super.QPiTwoCategory
import StringDiagrams.Super.QPiCategory

/-!
# The hom categories of a (Q, Π)-2-category are (Q, Π)-categories

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §6: for a
`(Q, Π)`-2-category `𝔄` (Definition 6.14), each hom category `Hom(λ, μ)` is a `(Q, Π)`-category
(Definition 6.12) with `Π := π_μ -`, `Q := q_μ -`, `Q⁻¹ := q_μ⁻¹ -` (in diagrammatic order,
`F ↦ F ≫ π_μ` etc.), `ξ_F = F ξ_μ`, `ii_F = F ii_μ`, `jj_F = F jj_μ` and `β_{Q, F} = F β_{q_μ}`
(with associators and unitors inserted), extending `PiTwoCategory.homPiCategory`
(`QPiTwoCategory.homQPiCategory`). This is the structure used for the Grothendieck ring of the
additive Karoubi envelope of a graded 2-supercategory (`StringDiagrams.Super.K0Ring`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Bicategory

universe w w₁ v₁ u₁

namespace QPiTwoCategory

variable {R : Type w} [CommRing R] {B : Type u₁} [Bicategory.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)] [PreadditiveBicategory B]
  [LinearBicategory R B] [QPiTwoCategory R B]

local notation "𝛑" => PiTwoCategory.pi (R := R)
local notation "𝛃" => PiTwoCategory.β (R := R)
local notation "𝛏" => PiTwoCategory.ξ (R := R)
local notation "𝐪" => QPiTwoCategory.q (R := R)
local notation "𝐪⁻¹" => QPiTwoCategory.qinv (R := R)

variable {a b : B}

/-- `ii_F := F ii_μ : (F ≫ q_μ) ≫ q_μ⁻¹ ≅ F` (with associator and unitor). -/
def iiHom (f : a ⟶ b) : (f ≫ 𝐪 b) ≫ 𝐪⁻¹ b ≅ f :=
  α_ f (𝐪 b) (𝐪⁻¹ b) ≪≫ whiskerLeftIso f (ii (R := R) b) ≪≫ ρ_ f

/-- `jj_F := F jj_μ : (F ≫ q_μ⁻¹) ≫ q_μ ≅ F` (with associator and unitor). -/
def jjHom (f : a ⟶ b) : (f ≫ 𝐪⁻¹ b) ≫ 𝐪 b ≅ f :=
  α_ f (𝐪⁻¹ b) (𝐪 b) ≪≫ whiskerLeftIso f (jj (R := R) b) ≪≫ ρ_ f

theorem iiHom_hom (f : a ⟶ b) : (iiHom (R := R) f).hom =
    (α_ f (𝐪 b) (𝐪⁻¹ b)).hom ≫ f ◁ (ii (R := R) b).hom ≫ (ρ_ f).hom := rfl

theorem iiHom_inv (f : a ⟶ b) : (iiHom (R := R) f).inv =
    (ρ_ f).inv ≫ f ◁ (ii (R := R) b).inv ≫ (α_ f (𝐪 b) (𝐪⁻¹ b)).inv := by
  simp [iiHom]

theorem jjHom_hom (f : a ⟶ b) : (jjHom (R := R) f).hom =
    (α_ f (𝐪⁻¹ b) (𝐪 b)).hom ≫ f ◁ (jj (R := R) b).hom ≫ (ρ_ f).hom := rfl

theorem jjHom_inv (f : a ⟶ b) : (jjHom (R := R) f).inv =
    (ρ_ f).inv ≫ f ◁ (jj (R := R) b).inv ≫ (α_ f (𝐪⁻¹ b) (𝐪 b)).inv := by
  simp [jjHom]

@[reassoc]
theorem iiHom_naturality {f g : a ⟶ b} (η : f ⟶ g) :
    η ▷ 𝐪 b ▷ 𝐪⁻¹ b ≫ (iiHom (R := R) g).hom = (iiHom (R := R) f).hom ≫ η := by
  rw [iiHom_hom, iiHom_hom, associator_naturality_left_assoc, ← whisker_exchange_assoc,
    rightUnitor_naturality]
  simp only [Category.assoc]

@[reassoc]
theorem jjHom_naturality {f g : a ⟶ b} (η : f ⟶ g) :
    η ▷ 𝐪⁻¹ b ▷ 𝐪 b ≫ (jjHom (R := R) g).hom = (jjHom (R := R) f).hom ≫ η := by
  rw [jjHom_hom, jjHom_hom, associator_naturality_left_assoc, ← whisker_exchange_assoc,
    rightUnitor_naturality]
  simp only [Category.assoc]

/-- `β_{Q, F} := F β_{q_μ} : (F ≫ q_μ) ≫ π_μ ≅ (F ≫ π_μ) ≫ q_μ` (with associators). -/
def βQHom (f : a ⟶ b) : (f ≫ 𝐪 b) ≫ 𝛑 b ≅ (f ≫ 𝛑 b) ≫ 𝐪 b :=
  α_ f (𝐪 b) (𝛑 b) ≪≫ whiskerLeftIso f (𝛃 (𝐪 b)) ≪≫ (α_ f (𝛑 b) (𝐪 b)).symm

theorem βQHom_hom (f : a ⟶ b) : (βQHom (R := R) f).hom =
    (α_ f (𝐪 b) (𝛑 b)).hom ≫ f ◁ (𝛃 (𝐪 b)).hom ≫ (α_ f (𝛑 b) (𝐪 b)).inv := rfl

@[reassoc]
theorem βQHom_naturality {f g : a ⟶ b} (η : f ⟶ g) :
    η ▷ 𝐪 b ▷ 𝛑 b ≫ (βQHom (R := R) g).hom = (βQHom (R := R) f).hom ≫ η ▷ 𝛑 b ▷ 𝐪 b := by
  rw [βQHom_hom, βQHom_hom, associator_naturality_left_assoc, ← whisker_exchange_assoc,
    associator_inv_naturality_left]
  simp only [Category.assoc]

/-- The paper's `q_μ jj_μ = ii_μ q_μ` in the form used for the triangle identity. -/
theorem whiskerLeft_jj (b : B) :
    𝐪 b ◁ (jj (R := R) b).hom = (α_ (𝐪 b) (𝐪⁻¹ b) (𝐪 b)).inv ≫ (ii (R := R) b).hom ▷ 𝐪 b ≫
      (λ_ (𝐪 b)).hom ≫ (ρ_ (𝐪 b)).inv := by
  rw [← cancel_mono (ρ_ (𝐪 b)).hom, ← cancel_epi (α_ (𝐪 b) (𝐪⁻¹ b) (𝐪 b)).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id_assoc]
  exact (q_ii (R := R) b).symm

/-- The paper's `ii_μ q_μ⁻¹ = q_μ⁻¹ jj_μ` in the form used for the triangle identity. -/
theorem whiskerLeft_ii (b : B) :
    𝐪⁻¹ b ◁ (ii (R := R) b).hom = (α_ (𝐪⁻¹ b) (𝐪 b) (𝐪⁻¹ b)).inv ≫ (jj (R := R) b).hom ▷ 𝐪⁻¹ b ≫
      (λ_ (𝐪⁻¹ b)).hom ≫ (ρ_ (𝐪⁻¹ b)).inv := by
  rw [← cancel_mono (ρ_ (𝐪⁻¹ b)).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact ii_qinv (R := R) b

theorem left_triangle_aux (f : a ⟶ b) :
    (iiHom (R := R) f).inv ▷ 𝐪 b ≫ (jjHom (R := R) (f ≫ 𝐪 b)).hom = 𝟙 (f ≫ 𝐪 b) := by
  rw [iiHom_inv, jjHom_hom, comp_whiskerLeft, whiskerLeft_jj]
  calc _ = (ρ_ f).inv ▷ 𝐪 b ≫ (α_ f (𝟙 b) (𝐪 b)).hom ≫
        f ◁ (((ii (R := R) b).inv ≫ (ii (R := R) b).hom) ▷ 𝐪 b) ≫ (α_ f (𝟙 b) (𝐪 b)).inv ≫
        (ρ_ f).hom ▷ 𝐪 b := by
        simp only [comp_whiskerRight, Bicategory.whiskerLeft_comp, Category.assoc]
        bicategory
    _ = 𝟙 (f ≫ 𝐪 b) := by
        rw [Iso.inv_hom_id, id_whiskerRight, Bicategory.whiskerLeft_id, Category.id_comp,
          Iso.hom_inv_id_assoc, ← comp_whiskerRight, Iso.inv_hom_id, id_whiskerRight]

theorem right_triangle_aux (f : a ⟶ b) :
    (iiHom (R := R) (f ≫ 𝐪⁻¹ b)).inv ≫ (jjHom (R := R) f).hom ▷ 𝐪⁻¹ b = 𝟙 (f ≫ 𝐪⁻¹ b) := by
  rw [iiHom_inv, jjHom_hom, comp_whiskerLeft]
  have h := whiskerLeft_ii (R := R) b
  rw [← cancel_mono (ρ_ (𝐪⁻¹ b)).hom] at h
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h
  have h' : 𝐪⁻¹ b ◁ (ii (R := R) b).inv = (ρ_ (𝐪⁻¹ b)).hom ≫ (λ_ (𝐪⁻¹ b)).inv ≫
      (jj (R := R) b).inv ▷ 𝐪⁻¹ b ≫ (α_ (𝐪⁻¹ b) (𝐪 b) (𝐪⁻¹ b)).hom := by
    rw [← cancel_epi (𝐪⁻¹ b ◁ (ii (R := R) b).hom), ← Bicategory.whiskerLeft_comp, Iso.hom_inv_id,
      Bicategory.whiskerLeft_id, reassoc_of% h]
    simp
  rw [h']
  calc _ = (ρ_ f).inv ▷ 𝐪⁻¹ b ≫ (α_ f (𝟙 b) (𝐪⁻¹ b)).hom ≫
        f ◁ (((jj (R := R) b).inv ≫ (jj (R := R) b).hom) ▷ 𝐪⁻¹ b) ≫
        (α_ f (𝟙 b) (𝐪⁻¹ b)).inv ≫ (ρ_ f).hom ▷ 𝐪⁻¹ b := by
        simp only [comp_whiskerRight, Bicategory.whiskerLeft_comp, Category.assoc]
        bicategory
    _ = 𝟙 (f ≫ 𝐪⁻¹ b) := by
        rw [Iso.inv_hom_id, id_whiskerRight, Bicategory.whiskerLeft_id, Category.id_comp,
          Iso.hom_inv_id_assoc, ← comp_whiskerRight, Iso.inv_hom_id, id_whiskerRight]

open PiTwoCategory in
theorem βQHom_comm (f : a ⟶ b) :
    (ξHom (R := R) (f ≫ 𝐪 b)).hom ≫ (ξHom (R := R) f).inv ▷ 𝐪 b =
      (βQHom (R := R) f).hom ▷ 𝛑 b ≫ (βQHom (R := R) (f ≫ 𝛑 b)).hom := by
  rw [ξHom_hom, ξHom_inv, βQHom_hom, βQHom_hom]
  calc _ = (α_ (f ≫ 𝐪 b) (𝛑 b) (𝛑 b)).hom ≫ (α_ f (𝐪 b) (𝛑 b ≫ 𝛑 b)).hom ≫
        f ◁ (𝐪 b ◁ (𝛏 b).hom ≫ (ρ_ (𝐪 b)).hom ≫ (λ_ (𝐪 b)).inv ≫ (𝛏 b).inv ▷ 𝐪 b) ≫
        (α_ f (𝛑 b ≫ 𝛑 b) (𝐪 b)).inv ≫ (α_ f (𝛑 b) (𝛑 b)).inv ▷ 𝐪 b := by
        simp only [comp_whiskerRight, Bicategory.whiskerLeft_comp, Category.assoc]
        bicategory
    _ = (α_ (f ≫ 𝐪 b) (𝛑 b) (𝛑 b)).hom ≫ (α_ f (𝐪 b) (𝛑 b ≫ 𝛑 b)).hom ≫
        f ◁ ((α_ (𝐪 b) (𝛑 b) (𝛑 b)).inv ≫ (𝛃 (𝐪 b)).hom ▷ 𝛑 b ≫ (α_ (𝛑 b) (𝐪 b) (𝛑 b)).hom ≫
          𝛑 b ◁ (𝛃 (𝐪 b)).hom ≫ (α_ (𝛑 b) (𝛑 b) (𝐪 b)).inv) ≫
        (α_ f (𝛑 b ≫ 𝛑 b) (𝐪 b)).inv ≫ (α_ f (𝛑 b) (𝛑 b)).inv ▷ 𝐪 b := by
        rw [ξ_comm (R := R) (𝐪 b)]
    _ = _ := by
        simp only [comp_whiskerRight, Bicategory.whiskerLeft_comp, Category.assoc]
        bicategory

/-- The Π-functor structure `β_Q := F β_{q_μ}` on `Q = - ≫ q_μ`. -/
def homQPiFunctor (a b : B) : PiFunctor R (postcomp a (𝐪 b)) where
  β := NatIso.ofComponents (fun f => βQHom (R := R) f) fun η => βQHom_naturality η
  comm f := βQHom_comm f

variable (R B) in
/-- **Brundan–Ellis, §6.** Each hom category of a `(Q, Π)`-2-category is a `(Q, Π)`-category,
with `Π := - ≫ π_μ`, `Q := - ≫ q_μ`, `Q⁻¹ := - ≫ q_μ⁻¹`, `ii_F = F ii_μ`, `jj_F = F jj_μ` and
`β_{Q, F} = F β_{q_μ}`, extending `PiTwoCategory.homPiCategory`. -/
instance homQPiCategory (a b : B) : QPiCategory R (a ⟶ b) where
  Q := postcomp a (𝐪 b)
  Qinv := postcomp a (𝐪⁻¹ b)
  ii := NatIso.ofComponents (fun f => iiHom (R := R) f) fun η => iiHom_naturality η
  jj := NatIso.ofComponents (fun f => jjHom (R := R) f) fun η => jjHom_naturality η
  left_triangle f := left_triangle_aux f
  right_triangle f := right_triangle_aux f
  Q_pi := homQPiFunctor a b

@[simp] theorem Q_obj (f : a ⟶ b) : (QPiCategory.Q (R := R)).obj f = f ≫ 𝐪 b := rfl

@[simp] theorem Q_map {f g : a ⟶ b} (η : f ⟶ g) : (QPiCategory.Q (R := R)).map η = η ▷ 𝐪 b := rfl

@[simp] theorem Qinv_obj (f : a ⟶ b) : (QPiCategory.Qinv (R := R)).obj f = f ≫ 𝐪⁻¹ b := rfl

@[simp] theorem Qinv_map {f g : a ⟶ b} (η : f ⟶ g) :
    (QPiCategory.Qinv (R := R)).map η = η ▷ 𝐪⁻¹ b := rfl

@[simp] theorem ii_hom_app (f : a ⟶ b) :
    (QPiCategory.ii (R := R) (C := a ⟶ b)).hom.app f = (iiHom (R := R) f).hom := rfl

@[simp] theorem jj_hom_app (f : a ⟶ b) :
    (QPiCategory.jj (R := R) (C := a ⟶ b)).hom.app f = (jjHom (R := R) f).hom := rfl

@[simp] theorem Q_pi_β_hom_app (f : a ⟶ b) :
    (QPiCategory.Q_pi (R := R) (C := a ⟶ b)).β.hom.app f = (βQHom (R := R) f).hom := rfl

end QPiTwoCategory

end StringDiagrams

end
