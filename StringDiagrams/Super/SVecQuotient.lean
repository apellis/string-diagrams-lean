import StringDiagrams.Super.SVec

/-!
# Quotients of superspaces

A graded submodule of a superspace `V` (`StringDiagrams.SVec`) is a submodule stable under the
projection onto the odd part (`SVec.GradedSubmodule`). The quotient `SVec.quot V U` by a graded
submodule is a superspace, with the quotient map `SVec.quotMk` an even linear map. A linear map
`f : V → W` carrying `U` into `U'` descends to `SVec.quotMap f hf : V ⧸ U → W ⧸ U'`; the descent
is compatible with identities, composition, sums, scalars, parity components
(`homProj_quotMap`, `twist_quotMap`) and parities (`quotMap_mem`).

This is used for the balanced tensor product of superbimodules
(`StringDiagrams.Super.BalancedTensor`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory

universe u

namespace SVec

variable {k : Type u} [CommRing k]

/-- A graded submodule of a superspace: a submodule stable under the projection onto the odd
part (equivalently, spanned by homogeneous vectors). -/
structure GradedSubmodule (V : SVec k) where
  /-- The underlying submodule. -/
  toSubmodule : Submodule k V
  odd_mem : ∀ v ∈ toSubmodule, V.odd v ∈ toSubmodule

namespace GradedSubmodule

variable {V : SVec k}

instance : SetLike (GradedSubmodule V) V where
  coe U := U.toSubmodule
  coe_injective' U U' h := by
    cases U; cases U'
    congr
    exact SetLike.coe_injective h

theorem toSubmodule_injective :
    Function.Injective (toSubmodule : GradedSubmodule V → Submodule k V) := by
  rintro ⟨U, _⟩ ⟨U', _⟩ h
  cases h; rfl

theorem mem_toSubmodule {U : GradedSubmodule V} {v : V} : v ∈ U.toSubmodule ↔ v ∈ U := Iff.rfl

theorem zero_mem (U : GradedSubmodule V) : (0 : V) ∈ U := U.toSubmodule.zero_mem

theorem add_mem (U : GradedSubmodule V) {v w : V} (hv : v ∈ U) (hw : w ∈ U) : v + w ∈ U :=
  U.toSubmodule.add_mem hv hw

theorem sub_mem (U : GradedSubmodule V) {v w : V} (hv : v ∈ U) (hw : w ∈ U) : v - w ∈ U :=
  U.toSubmodule.sub_mem hv hw

theorem smul_mem (U : GradedSubmodule V) (r : k) {v : V} (hv : v ∈ U) : r • v ∈ U :=
  U.toSubmodule.smul_mem r hv

theorem zsmul_mem (U : GradedSubmodule V) (n : ℤ) {v : V} (hv : v ∈ U) : n • v ∈ U :=
  U.toSubmodule.smul_of_tower_mem n hv

theorem proj_mem (U : GradedSubmodule V) (q : ZMod 2) {v : V} (hv : v ∈ U) : V.proj q v ∈ U := by
  rcases parity_eq_zero_or_one q with rfl | rfl
  · rw [proj_zero, LinearMap.sub_apply, LinearMap.id_apply]; exact U.sub_mem hv (U.odd_mem v hv)
  · rw [proj_one]; exact U.odd_mem v hv

end GradedSubmodule

section Quot

/-- The quotient of a superspace by a graded submodule. -/
def quot (V : SVec k) (U : GradedSubmodule V) : SVec k where
  carrier := V ⧸ U.toSubmodule
  odd := U.toSubmodule.mapQ U.toSubmodule V.odd fun v hv => U.odd_mem v hv
  odd_comp_odd := by
    refine Submodule.linearMap_qext _ ?_
    ext v
    simp [Submodule.mapQ_apply, odd_apply_odd]

variable (V : SVec k) (U : GradedSubmodule V)

/-- The class of a vector in the quotient superspace. -/
def quotMkFun (v : V) : quot V U := Submodule.Quotient.mk v

/-- The quotient map, as a morphism of `SVec k`. -/
def quotMk : V ⟶ quot V U := ofHom U.toSubmodule.mkQ

theorem quotMk_apply (v : V) : quotMk V U v = quotMkFun V U v := rfl

theorem quotMkFun_surjective : Function.Surjective (quotMkFun V U) :=
  Submodule.mkQ_surjective U.toSubmodule

theorem quotMkFun_add (v w : V) : quotMkFun V U (v + w) = quotMkFun V U v + quotMkFun V U w := rfl

theorem quotMkFun_sub (v w : V) : quotMkFun V U (v - w) = quotMkFun V U v - quotMkFun V U w := rfl

theorem quotMkFun_smul (r : k) (v : V) : quotMkFun V U (r • v) = r • quotMkFun V U v := rfl

theorem quotMkFun_zsmul (n : ℤ) (v : V) : quotMkFun V U (n • v) = n • quotMkFun V U v := rfl

theorem quotMkFun_zero : quotMkFun V U 0 = 0 := rfl

theorem quotMkFun_eq_quotMkFun {v w : V} : quotMkFun V U v = quotMkFun V U w ↔ v - w ∈ U :=
  Submodule.Quotient.eq U.toSubmodule

theorem quotMkFun_eq_zero {v : V} : quotMkFun V U v = 0 ↔ v ∈ U :=
  Submodule.Quotient.mk_eq_zero U.toSubmodule

theorem quot_odd_mk (v : V) : (quot V U).odd (quotMkFun V U v) = quotMkFun V U (V.odd v) := rfl

theorem quot_proj_mk (p : ZMod 2) (v : V) :
    (quot V U).proj p (quotMkFun V U v) = quotMkFun V U (V.proj p v) := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [proj_zero, proj_zero, LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.id_apply,
      LinearMap.id_apply, quot_odd_mk, quotMkFun_sub]
  · rw [proj_one, proj_one, quot_odd_mk]

theorem quotMk_mem : quotMk V U ∈ parityHom V (quot V U) 0 := by
  intro q
  ext v
  rw [add_zero, LinearMap.comp_apply, LinearMap.comp_apply]
  exact (quot_proj_mk V U q v).symm

theorem quotMkFun_mem_part {p : ZMod 2} {v : V} (hv : v ∈ V.part p) :
    quotMkFun V U v ∈ (quot V U).part p := by
  simpa using apply_mem_part (quotMk_mem V U) (v := v) hv

variable {V U}

/-- Induction on the classes of a quotient superspace. -/
theorem quot_induction_on {P : quot V U → Prop} (x : quot V U) (h : ∀ v : V, P (quotMkFun V U v)) :
    P x :=
  Submodule.Quotient.induction_on U.toSubmodule x h

variable (V U) in
/-- Linear maps out of a quotient superspace are determined by their values on classes. -/
theorem quot_hom_ext {W : SVec k} {f g : quot V U ⟶ W}
    (h : ∀ v : V, f (quotMkFun V U v) = g (quotMkFun V U v)) : f = g :=
  hom_ext fun x => quot_induction_on (P := fun x => f x = g x) x h

end Quot

/-! ## Descended maps -/

section QuotMap

variable {V W X : SVec k} {U : GradedSubmodule V} {U' : GradedSubmodule W} {U'' : GradedSubmodule X}

/-- A linear map carrying `U` into `U'` descends to the quotients. -/
def quotMap (f : V ⟶ W) (hf : ∀ v ∈ U, f v ∈ U') : quot V U ⟶ quot W U' :=
  ofHom (U.toSubmodule.mapQ U'.toSubmodule (toLinearMap f) fun v hv => hf v hv)

@[simp] theorem quotMap_mk (f : V ⟶ W) (hf : ∀ v ∈ U, f v ∈ U') (v : V) :
    quotMap f hf (quotMkFun V U v) = quotMkFun W U' (f v) :=
  rfl

theorem quotMk_comp_quotMap (f : V ⟶ W) (hf : ∀ v ∈ U, f v ∈ U') :
    quotMk V U ≫ quotMap f hf = f ≫ quotMk W U' := rfl

theorem quotMap_id : quotMap (U := U) (U' := U) (𝟙 V) (fun _ hv => hv) = 𝟙 (quot V U) :=
  quot_hom_ext V U fun _ => rfl

theorem quotMap_comp (f : V ⟶ W) (hf : ∀ v ∈ U, f v ∈ U') (g : W ⟶ X)
    (hg : ∀ w ∈ U', g w ∈ U'') :
    quotMap (U := U) (U' := U'') (f ≫ g) (fun v hv => hg _ (hf v hv)) =
      quotMap f hf ≫ quotMap g hg :=
  quot_hom_ext V U fun _ => rfl

theorem quotMap_add (f g : V ⟶ W) (hf : ∀ v ∈ U, f v ∈ U') (hg : ∀ v ∈ U, g v ∈ U') :
    quotMap (f + g) (fun v hv => U'.add_mem (hf v hv) (hg v hv)) = quotMap f hf + quotMap g hg :=
  quot_hom_ext V U fun _ => rfl

theorem quotMap_smul (r : k) (f : V ⟶ W) (hf : ∀ v ∈ U, f v ∈ U') :
    quotMap (r • f) (fun v hv => U'.smul_mem r (hf v hv)) = r • quotMap f hf :=
  quot_hom_ext V U fun _ => rfl

theorem quotMap_zsmul (n : ℤ) (f : V ⟶ W) (hf : ∀ v ∈ U, f v ∈ U') :
    quotMap (n • f) (fun v hv => U'.zsmul_mem n (hf v hv)) = n • quotMap f hf :=
  quot_hom_ext V U fun _ => rfl

theorem quotMap_zero : quotMap (U := U) (U' := U') (0 : V ⟶ W) (fun _ _ => U'.zero_mem) = 0 :=
  quot_hom_ext V U fun _ => rfl

theorem quotMap_congr {f g : V ⟶ W} (h : f = g) (hf : ∀ v ∈ U, f v ∈ U') :
    quotMap f hf = quotMap g (h ▸ hf) := by
  subst h; rfl

/-- The parity components of a map carrying `U` into `U'` carry `U` into `U'`. -/
theorem homProj_mem_of_mem (p : ZMod 2) {f : V ⟶ W} (hf : ∀ v ∈ U, f v ∈ U') :
    ∀ v ∈ U, homProj p f v ∈ U' := fun v hv => by
  rw [homProj_apply]
  exact U'.add_mem (U'.proj_mem _ (hf _ (U.proj_mem 0 hv))) (U'.proj_mem _ (hf _ (U.proj_mem 1 hv)))

/-- A descended map has the parity of the original map. -/
theorem quotMap_mem {p : ZMod 2} {f : V ⟶ W} (hfp : f ∈ parityHom V W p)
    (hf : ∀ v ∈ U, f v ∈ U') : quotMap f hf ∈ parityHom (quot V U) (quot W U') p := by
  intro q
  refine quot_hom_ext V U fun v => ?_
  change quotMap f hf ((quot V U).proj q (quotMkFun V U v)) =
    (quot W U').proj (q + p) (quotMap f hf (quotMkFun V U v))
  rw [quot_proj_mk, quotMap_mk, quotMap_mk, quot_proj_mk, apply_proj_of_mem hfp]

theorem homProj_quotMap (p : ZMod 2) (f : V ⟶ W) (hf : ∀ v ∈ U, f v ∈ U') :
    homProj p (quotMap f hf) = quotMap (homProj p f) (homProj_mem_of_mem p hf) := by
  have e : f = homProj p f + homProj (p + 1) f := by
    rcases parity_eq_zero_or_one p with rfl | rfl
    · rw [zero_add, homProj_add_homProj]
    · rw [zmod2_one_add_one, add_comm, homProj_add_homProj]
  refine homProj_eq_of_add ?_ (quotMap_mem (homProj_mem p f) _)
    (quotMap_mem (homProj_mem (p + 1) f) (homProj_mem_of_mem _ hf))
  rw [← quotMap_add]
  exact quotMap_congr e hf

theorem twist_mem_of_mem (p : ZMod 2) {f : V ⟶ W} (hf : ∀ v ∈ U, f v ∈ U') :
    ∀ v ∈ U, twist k p f v ∈ U' := fun v hv => by
  rw [twist_apply, proj_eq_homProj, proj_eq_homProj]
  exact U'.add_mem (homProj_mem_of_mem 0 hf v hv) (U'.smul_mem _ (homProj_mem_of_mem 1 hf v hv))

theorem twist_quotMap (p : ZMod 2) (f : V ⟶ W) (hf : ∀ v ∈ U, f v ∈ U') :
    twist k p (quotMap f hf) = quotMap (twist k p f) (twist_mem_of_mem p hf) := by
  rw [twist_apply, proj_eq_homProj, proj_eq_homProj, homProj_quotMap, homProj_quotMap,
    ← quotMap_smul, ← quotMap_add]
  exact (quotMap_congr (by rw [twist_apply, proj_eq_homProj, proj_eq_homProj]) _).symm

end QuotMap

end SVec

end StringDiagrams

end
