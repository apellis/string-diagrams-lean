import StringDiagrams.Super.AssociatedTwoMap

/-!
# The strict 2-functors `𝔼₂`, `𝔻₂` on 2-morphisms, and Theorem 5.5

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, (5.6) and
Theorem 5.5.

* `𝔼₂` on 2-natural transformations is `TwoNatTrans.toOplaxTrans`, which is Π-2-natural
  (`TwoNatTrans.isPiTwoNatural`, in `StringDiagrams.Super.PiTwoCategory`).
* `𝔻₂` on Π-2-natural transformations (`PiTwoFunctor.mapTwoNat`): a Π-2-natural transformation
  `(Y, y) : ℝ ⇒ 𝕊` gives the 2-natural transformation `(Ŷ, ŷ) : ℝ̂ ⇒ 𝕊̂` with `ŷ_F = (y_F, 0)`.
  Its supernaturality on odd 2-morphisms is the Π-naturality of the components `y_F`
  (`PiTwoFunctor.natHom_isPiNatural`), which uses the axiom of Definition 5.2(iii).
* **Theorem 5.5**: `𝔼₂ ∘ 𝔻₂ = 𝕀` on 2-morphisms (`PiTwoFunctor.toOplax_mapTwoNat_app`,
  `PiTwoFunctor.toOplax_mapTwoNat_naturality`), and `𝕋` is natural in 2-morphisms:
  `𝕋_{𝔄'}(𝔻₂ 𝔼₂ (X, x)) = (X, x) 𝕋_𝔄` (`Associated2.T_map₂_mapTwoNat`). Together with Lemma 5.4
  (`StringDiagrams.Super.AssociatedTwoT`, `StringDiagrams.Super.AssociatedTwoMap`) this is the
  content of Theorem 5.5 on objects, 1-morphisms and 2-morphisms.

## Not formalized

The strict 2-categories `Π-2-𝔖ℭ𝔄𝔗` and `Π-2-ℭ𝔄𝔗` themselves (composition of Π-2-functors and of
(Π-)2-natural transformations, and the 2-functoriality of `𝔼₂` and `𝔻₂` with respect to it) are
not constructed, so Theorem 5.5 is not stated as a 2-equivalence of Lean bicategories.
Corollary 5.6 (a 2-superequivalence between the 2-supercategories `Π-2-𝔖ℭ𝔄𝔗` and
`D₂(Π-2-ℭ𝔄𝔗)`) and Remark 5.7 (a 3-equivalence, stated without proof in the paper) are not
formalized.
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Bicategory Supercategory

universe w w₁ v₁ u₁ w₂ v₂ u₂

namespace PiTwoFunctor

variable {R : Type w} [CommRing R] {B : Type u₁} [Bicategory.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)] [PreadditiveBicategory B]
  [LinearBicategory R B] [PiTwoCategory R B]
  {C : Type u₂} [Bicategory.{w₂, v₂} C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear R (a ⟶ b)] [PreadditiveBicategory C]
  [LinearBicategory R C] [PiTwoCategory R C]
  {F G : Pseudofunctor B C} {hF : PiTwoFunctor R F} {hG : PiTwoFunctor R G}
  {η : Oplax.OplaxTrans F.toOplax G.toOplax}

open PiTwoCategory

local notation "𝛑" => PiTwoCategory.pi (R := R)
local notation "𝛃" => PiTwoCategory.β (R := R)

variable (hF hG η) in
/-- The components `x_F : X_μ(ℝF) ⇒ (𝕊F)X_λ` of an oplax natural transformation, as a natural
transformation between functors `ℋom(λ, μ) → ℋom(ℝλ, 𝕊μ)`. -/
def natHom (a b : B) :
    hF.homFunctor a b ⋙ postcomp (F.obj a) (η.app b) ⟶
      hG.homFunctor a b ⋙ precomp (G.obj b) (η.app a) where
  app f := η.naturality f
  naturality _ _ θ := η.naturality_naturality θ

/-- **Brundan–Ellis, (5.6).** The components of a Π-2-natural transformation form a Π-natural
transformation (this is where the axiom of Definition 5.2(iii) is used). -/
theorem natHom_isPiNatural (hη : hF.IsPiTwoNatural hG η) (a b : B) :
    PiFunctor.IsPiNatural R ((hF.homPi R a b).comp (postcompPi R (F.obj a) (η.app b)))
      ((hG.homPi R a b).comp (precompPi R (G.obj b) (η.app a))) (natHom hF hG η a b) :=
  fun f => by
  have hc : (F.mapComp f (𝛑 b)).inv ▷ η.app b ≫ η.naturality (f ≫ 𝛑 b) =
      (α_ (F.map f) (F.map (𝛑 b)) (η.app b)).hom ≫ F.map f ◁ η.naturality (𝛑 b) ≫
        (α_ (F.map f) (η.app b) (G.map (𝛑 b))).inv ≫ η.naturality f ▷ G.map (𝛑 b) ≫
          (α_ (η.app a) (G.map f) (G.map (𝛑 b))).hom ≫ η.app a ◁ (G.mapComp f (𝛑 b)).inv := by
    have e := η.naturality_comp f (𝛑 b)
    simp only [Pseudofunctor.toOplax_mapComp, Pseudofunctor.toOplax_toPrelaxFunctor] at e
    rw [← cancel_mono (η.app a ◁ (G.mapComp f (𝛑 b)).hom)]
    simp only [Category.assoc, Bicategory.whiskerLeft_inv_hom, Category.comp_id]
    rw [e, Bicategory.inv_hom_whiskerRight_assoc]
  simp only [natHom, PiFunctor.comp_β, NatIso.ofComponents_hom_app, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom, Functor.comp_obj, homFunctor_obj, homFunctor_map, postcomp_obj,
    postcomp_map, precomp_obj, precomp_map, postcompPi_β_hom_app, precompPi_β_hom_app,
    homPi_β_hom_app, βHom_hom, pi_obj, pi_map, βR_hom, Bicategory.comp_whiskerRight,
    Category.assoc]
  rw [hc]
  simp only [Pseudofunctor.toOplax_toPrelaxFunctor]
  have c1 : (α_ (F.map f) (η.app b) (𝛑 (G.obj b))).hom ≫ F.map f ◁ (𝛃 (η.app b)).hom ≫
      (α_ (F.map f) (𝛑 (F.obj b)) (η.app b)).inv ≫ (F.map f ◁ (hF.j b).hom) ▷ η.app b ≫
        (α_ (F.map f) (F.map (𝛑 b)) (η.app b)).hom ≫ F.map f ◁ η.naturality (𝛑 b) =
      (α_ (F.map f) (η.app b) (𝛑 (G.obj b))).hom ≫
        F.map f ◁ ((𝛃 (η.app b)).hom ≫ (hF.j b).hom ▷ η.app b ≫ η.naturality (𝛑 b)) := by
    bicategory
  rw [reassoc_of% c1, hη b]
  have c2 : (α_ (F.map f) (η.app b) (𝛑 (G.obj b))).hom ≫ F.map f ◁ η.app b ◁ (hG.j b).hom ≫
      (α_ (F.map f) (η.app b) (G.map (𝛑 b))).inv =
      (F.map f ≫ η.app b) ◁ (hG.j b).hom := by bicategory
  rw [reassoc_of% c2, whisker_exchange_assoc, associator_naturality_right_assoc,
    Bicategory.whiskerLeft_comp]

open Associated2 in
variable (hF hG) in
/-- **Brundan–Ellis, (5.6), `𝔻₂` on Π-2-natural transformations.** A Π-2-natural transformation
`(Y, y) : ℝ ⇒ 𝕊` gives a 2-natural transformation `(Ŷ, ŷ) : ℝ̂ ⇒ 𝕊̂` with `Ŷ_λ := Y_λ` and
`ŷ_F := y_F` viewed as even 2-morphisms; the supernaturality of `ŷ` on odd 2-morphisms is the
Π-naturality `natHom_isPiNatural`. -/
@[simps]
def mapTwoNat (hη : hF.IsPiTwoNatural hG η) : TwoNatTrans hF.mapTwo hG.mapTwo where
  X a := ⟨η.app a.obj⟩
  x f := Associated.homMk (η.naturality f.obj) 0
  x_mem _ := Associated.mem_parity_zero.2 rfl
  naturality {a b f g} θ := by
    have e := Associated.map_naturality (natHom_isPiNatural (R := R) hη a.obj b.obj) θ
    rw [← map_map_map, ← map_map_map] at e
    exact e
  x_comp {a b c} f g := by
    apply hom₂_ext
    · have e := η.naturality_comp f.obj g.obj
      simp only [Pseudofunctor.toOplax_mapComp, Pseudofunctor.toOplax_toPrelaxFunctor] at e
      simp only [comp₂_fst, whiskerLeft_fst, whiskerRight_fst, whiskerLeft_snd, whiskerRight_snd,
        mapTwo_mapComp, Associated.evenIso_hom, Associated.homMk_fst, Associated.homMk_snd,
        associator_hom_fst, associator_hom_snd, associator_inv_fst, associator_inv_snd,
        Iso.symm_hom, PreadditiveBicategory.zero_whiskerRight,
        PreadditiveBicategory.whiskerLeft_zero, Limits.zero_comp, sub_zero, Category.assoc,
        mapTwo_map_obj, comp_obj]
      rw [← cancel_mono (η.app a.obj ◁ (G.mapComp f.obj g.obj).hom)]
      simp only [Category.assoc, Bicategory.whiskerLeft_inv_hom, Category.comp_id]
      rw [e, Bicategory.inv_hom_whiskerRight_assoc]
    · simp only [comp₂_snd, whiskerLeft_fst, whiskerRight_fst, whiskerLeft_snd, whiskerRight_snd,
        mapTwo_mapComp, Associated.evenIso_hom, Associated.homMk_fst, Associated.homMk_snd,
        associator_hom_fst, associator_hom_snd, associator_inv_fst, associator_inv_snd,
        Iso.symm_hom, PreadditiveBicategory.zero_whiskerRight,
        PreadditiveBicategory.whiskerLeft_zero, Limits.zero_comp, Limits.comp_zero, add_zero,
        zero_add, pi_map]
  x_id a := by
    apply hom₂_ext
    · have e := η.naturality_id a.obj
      simp only [Pseudofunctor.toOplax_mapId, Pseudofunctor.toOplax_toPrelaxFunctor] at e
      simp only [comp₂_fst, whiskerLeft_fst, whiskerRight_fst, whiskerLeft_snd, whiskerRight_snd,
        mapTwo_mapId, Associated.evenIso_hom, Associated.homMk_fst, Associated.homMk_snd,
        leftUnitor_inv_fst, leftUnitor_inv_snd, rightUnitor_hom_fst, rightUnitor_hom_snd,
        Iso.symm_hom, PreadditiveBicategory.zero_whiskerRight,
        PreadditiveBicategory.whiskerLeft_zero, Limits.zero_comp, sub_zero, Category.assoc,
        mapTwo_map_obj, id_obj, mapTwo_obj_obj]
      rw [← cancel_mono (η.app a.obj ◁ (G.mapId a.obj).hom)]
      simp only [Category.assoc, Bicategory.whiskerLeft_inv_hom, Category.comp_id]
      rw [e]
      simp
    · simp only [comp₂_snd, whiskerLeft_fst, whiskerRight_fst, whiskerLeft_snd, whiskerRight_snd,
        mapTwo_mapId, Associated.evenIso_hom, Associated.homMk_fst, Associated.homMk_snd,
        leftUnitor_inv_fst, leftUnitor_inv_snd, rightUnitor_hom_fst, rightUnitor_hom_snd,
        Iso.symm_hom, PreadditiveBicategory.zero_whiskerRight,
        PreadditiveBicategory.whiskerLeft_zero, Limits.zero_comp, Limits.comp_zero, add_zero,
        zero_add, pi_map]

/-- **Theorem 5.5, `𝔼₂ ∘ 𝔻₂ = 𝕀` on 2-morphisms.** The components of `𝔼₂(𝔻₂(Y, y))` are those of
`(Y, y)`, under the identification `Associated2.unit` of Lemma 5.4. -/
theorem toOplax_mapTwoNat_naturality (hη : hF.IsPiTwoNatural hG η) {a b : B} (f : a ⟶ b) :
    ((mapTwoNat hF hG hη).toOplaxTrans).naturality ((Associated2.unit R B).map f) =
      (Associated2.unit R C).map₂ (η.naturality f) := rfl

theorem toOplax_mapTwoNat_app (hη : hF.IsPiTwoNatural hG η) (a : B) :
    ((mapTwoNat hF hG hη).toOplaxTrans).app ((Associated2.unit R B).obj a) =
      (Associated2.unit R C).map (η.app a) := rfl

end PiTwoFunctor

namespace Associated2

open BicategoryStruct TwoSupercategory

variable {R : Type w} [CommRing R] {A : Type u₁} [BicategoryStruct.{w₁, v₁} A]
  [∀ a b : A, Preadditive (a ⟶ b)] [∀ a b : A, Linear R (a ⟶ b)]
  [∀ a b : A, Supercategory R (a ⟶ b)] [TwoSupercategory R A] [PiTwoSupercategory R A]
  {A' : Type u₂} [BicategoryStruct.{w₂, v₂} A']
  [∀ a b : A', Preadditive (a ⟶ b)] [∀ a b : A', Linear R (a ⟶ b)]
  [∀ a b : A', Supercategory R (a ⟶ b)] [TwoSupercategory R A'] [PiTwoSupercategory R A']
  {G G' : TwoSuperfunctor R A A'}

/-- **Theorem 5.5, naturality of `𝕋` in 2-morphisms.** For a 2-natural transformation
`(X, x) : ℝ ⇒ 𝕊`, `𝕋_{𝔄'} (𝔻₂ 𝔼₂ (X, x)) = (X, x) 𝕋_𝔄`: the components `X_λ` agree (by
definition) and `𝕋_{𝔄'}` sends `ŷ_F = (x_F, 0)` to `x_F`. -/
theorem T_map₂_mapTwoNat (θ : TwoNatTrans G G') {a b : Associated2 R (Underlying2 R A)}
    (f : a ⟶ b) :
    (T R A').map₂ ((PiTwoFunctor.mapTwoNat G.toPiTwoFunctor G'.toPiTwoFunctor
      θ.isPiTwoNatural).x f) = θ.x f.obj.obj := by
  simp [T_map₂]

end Associated2

end StringDiagrams

end
