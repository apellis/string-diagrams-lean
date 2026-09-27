import StringDiagrams.Super.QPiTwoHom
import StringDiagrams.Super.GSKar
import StringDiagrams.Super.KarBicategory
import Mathlib.Algebra.DirectSum.Module

/-!
# The Grothendieck ring of an additive 2-category

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, the end of
§6 (and J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133, (1.32)).

For a bicategory `B` whose hom categories are additive (preadditive with binary biproducts) and
whose whiskerings are additive, the *Grothendieck ring* is

  `K₀Ring B := ⨁_{(λ, μ)} K₀ (λ ⟶ μ)`,

the direct sum of the split Grothendieck groups of the hom categories, with the multiplication
induced by horizontal composition: for `F : λ → μ` and `G : μ → ν`, `[G] · [F] = [F ≫ G]`
(the composite `λ → ν`; classes of non-composable 1-morphisms multiply to zero). It is a
(non-unital, associative) ring (`K₀Ring.instNonUnitalRing`) with the distinguished mutually
orthogonal idempotents `1_λ := [𝟙 λ]` (`K₀Ring.one`, `K₀Ring.one_mul_one_self`,
`K₀Ring.one_mul_one_of_ne`); it is *locally unital*: `1_μ · x = x = x · 1_λ` for
`x ∈ K₀ (λ ⟶ μ)` (`K₀Ring.one_mul_of`, `K₀Ring.of_mul_one`), and every element is fixed by
left and right multiplication by a finite sum of the `1_λ` (`K₀Ring.exists_finset_one_mul`).

For a `(Q, Π)`-2-category (Definition 6.14) `K₀Ring B` is a `Zπ[q, q⁻¹]`-module
(`K₀Ring.moduleLaurent`, componentwise via `K₀.moduleLaurent` of the hom `(Q, Π)`-categories),
`π` and `q` acting on `1_μ K₀ 1_λ = K₀ (λ ⟶ μ)` by left multiplication by `[π_μ]` and `[q_μ]`
(`K₀Ring.C_π_smul_of`, `K₀Ring.T_smul_of`), equivalently by right multiplication by `[π_λ]` and
`[q_λ]` (`K₀Ring.C_π_smul_of'`, `K₀Ring.T_smul_of'`; the equivalence uses the isomorphisms
`β_F : F π_μ ≅ π_λ F` and `γ_F : F q_μ ≅ q_λ F`); the module structure is compatible with the
multiplication (`K₀Ring.smul_mul`, `K₀Ring.mul_smul`), so `K₀Ring B` is a locally unital
`Zπ[q, q⁻¹]`-algebra. Applied to `GSKAR(𝔄)` (`StringDiagrams.Super.KarBicategory`) this is the
Grothendieck ring `K₀(GSKAR(𝔄))` at the end of §6.

Compositions of 1-morphisms are written in diagrammatic order (`F ≫ G` is the paper's `GF`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Bicategory Limits

universe w v u w₁

section Ring

variable {B : Type u} [Bicategory.{w, v} B] [∀ a b : B, Preadditive (a ⟶ b)]
  [PreadditiveBicategory B] [∀ a b : B, HasBinaryBiproducts (a ⟶ b)]

/-! ## Horizontal composition on `K₀` -/

namespace K₀

/-- The natural isomorphism `precomp c f ≅ precomp c f'` induced by `f ≅ f'`. -/
@[simps!]
def precompIso {a b c : B} {f f' : a ⟶ b} (e : f ≅ f') : precomp c f ≅ precomp c f' :=
  NatIso.ofComponents (fun g => whiskerRightIso e g) fun η => by
    dsimp
    exact whisker_exchange _ _

variable (a b c : B)

/-- **Horizontal composition on `K₀`**: the bilinear map `K₀ (a ⟶ b) →+ K₀ (b ⟶ c) →+ K₀ (a ⟶ c)`
with `[f] · [g] = [f ≫ g]`. -/
def hcompK : K₀ (a ⟶ b) →+ K₀ (b ⟶ c) →+ K₀ (a ⟶ c) :=
  lift (fun f => map (precomp c f)) (fun _ _ e => map_eq_of_iso (precompIso e)) fun f f' =>
    hom_ext fun g => by
      simp only [map_mk, AddMonoidHom.add_apply]
      change mk ((postcomp a g).obj (f ⊞ f')) = mk ((postcomp a g).obj f) + mk ((postcomp a g).obj f')
      rw [mk_eq_mk_of_iso (mapBiprodIso (postcomp a g) f f'), mk_biprod]

variable {a b c}

@[simp] theorem hcompK_mk_mk (f : a ⟶ b) (g : b ⟶ c) : hcompK a b c (mk f) (mk g) = mk (f ≫ g) := by
  simp [hcompK]

end K₀

/-! ## The Grothendieck ring -/

variable (B) in
/-- **Brundan–Ellis, end of §6; Super Kac–Moody 2-categories (1.32).** The Grothendieck ring
`K₀(B) := ⨁_{(λ, μ)} K₀ (λ ⟶ μ)` of an additive 2-category. -/
abbrev K₀Ring := DirectSum (B × B) fun p => K₀ (p.1 ⟶ p.2)

namespace K₀Ring

open scoped Classical

variable (a b : B)

/-- The inclusion of `K₀ (a ⟶ b)`, the summand `1_b K₀ 1_a`. -/
def of : K₀ (a ⟶ b) →+ K₀Ring B := DirectSum.of (fun p : B × B => K₀ (p.1 ⟶ p.2)) (a, b)

omit [PreadditiveBicategory B] in
theorem of_injective : Function.Injective (of a b) := DirectSum.of_injective (a, b)

variable {a b}

/-- The class `[f]` of a 1-morphism. -/
def mk (f : a ⟶ b) : K₀Ring B := of a b (K₀.mk f)

omit [PreadditiveBicategory B] in
theorem mk_eq_mk_of_iso {f f' : a ⟶ b} (e : f ≅ f') : mk f = mk f' := by
  rw [mk, mk, K₀.mk_eq_mk_of_iso e]

omit [PreadditiveBicategory B] in
theorem mk_biprod (f f' : a ⟶ b) : mk (f ⊞ f') = mk f + mk f' := by
  rw [mk, mk, mk, K₀.mk_biprod, map_add]

omit [PreadditiveBicategory B] in
/-- Additive homomorphisms out of `K₀Ring B` are determined by their values on the summands. -/
theorem addHom_ext {G : Type w₁} [AddCommGroup G] {φ ψ : K₀Ring B →+ G}
    (h : ∀ (a b : B) (x : K₀ (a ⟶ b)), φ (of a b x) = ψ (of a b x)) : φ = ψ :=
  DirectSum.addHom_ext fun p x => h p.1 p.2 x

omit [PreadditiveBicategory B] in
/-- Induction on elements of `K₀Ring B`. -/
@[elab_as_elim]
theorem induction_on {P : K₀Ring B → Prop} (x : K₀Ring B) (zero : P 0)
    (of : ∀ (a b : B) (x : K₀ (a ⟶ b)), P (of a b x)) (add : ∀ x y, P x → P y → P (x + y)) :
    P x :=
  DirectSum.induction_on x zero (fun p x => of p.1 p.2 x) add

/-! ### The multiplication -/

/-- Transport of `K₀ (c ⟶ d)` along an equality of objects `d = a`. -/
def castHom {c d a : B} (h : d = a) : K₀ (c ⟶ d) →+ K₀ (c ⟶ a) := by
  subst h; exact AddMonoidHom.id _

omit [PreadditiveBicategory B] in
theorem castHom_rfl (c d : B) : castHom (c := c) (rfl : d = d) = AddMonoidHom.id _ := rfl

variable (B) in
/-- The product of the summands `K₀ (p.1 ⟶ p.2)` and `K₀ (q.1 ⟶ q.2)`: zero unless
`q.2 = p.1`, and then `[f] · [g] = [g ≫ f]`. -/
def mulOf (p q : B × B) : K₀ (p.1 ⟶ p.2) →+ K₀ (q.1 ⟶ q.2) →+ K₀Ring B :=
  if h : q.2 = p.1 then
    ((K₀.hcompK q.1 p.1 p.2).flip.compl₂ (castHom h)).compr₂ (of q.1 p.2)
  else 0

theorem mulOf_of_ne {a b c d : B} (h : d ≠ a) (x : K₀ (a ⟶ b)) (y : K₀ (c ⟶ d)) :
    mulOf B (a, b) (c, d) x y = 0 := by
  rw [mulOf, dite_eq_right h]
  rfl

theorem mulOf_self (a b c : B) (x : K₀ (a ⟶ b)) (y : K₀ (c ⟶ a)) :
    mulOf B (a, b) (c, a) x y = of c b (K₀.hcompK c a b y x) := by
  rw [mulOf, dite_eq_left rfl]
  rfl

variable (B) in
/-- The multiplication of `K₀Ring B`, as a bilinear map. -/
def mulHom : K₀Ring B →+ K₀Ring B →+ K₀Ring B :=
  DirectSum.toAddMonoid fun p => (DirectSum.toAddMonoid fun q => (mulOf B p q).flip).flip

instance : Mul (K₀Ring B) := ⟨fun x y => mulHom B x y⟩

theorem mul_def (x y : K₀Ring B) : x * y = mulHom B x y := rfl

theorem of_mul_of {a b c d : B} (x : K₀ (a ⟶ b)) (y : K₀ (c ⟶ d)) :
    of a b x * of c d y = mulOf B (a, b) (c, d) x y := by
  rw [mul_def, mulHom, of, of, DirectSum.toAddMonoid_of, AddMonoidHom.flip_apply,
    DirectSum.toAddMonoid_of, AddMonoidHom.flip_apply]

/-- `[f] · [g] = [g ≫ f]` for `g : c → a`, `f : a → b`. -/
theorem mk_mul_mk (f : a ⟶ b) {c : B} (g : c ⟶ a) : mk f * mk g = mk (g ≫ f) := by
  rw [mk, mk, of_mul_of, mulOf_self, K₀.hcompK_mk_mk]
  rfl

/-- Classes of non-composable 1-morphisms multiply to zero. -/
theorem mk_mul_mk_of_ne (f : a ⟶ b) {c d : B} (g : c ⟶ d) (h : d ≠ a) : mk f * mk g = 0 := by
  rw [mk, mk, of_mul_of, mulOf_of_ne h]

protected theorem mul_add (x y z : K₀Ring B) : x * (y + z) = x * y + x * z :=
  map_add (mulHom B x) y z

protected theorem add_mul (x y z : K₀Ring B) : (x + y) * z = x * z + y * z := by
  simp only [mul_def, map_add, AddMonoidHom.add_apply]

protected theorem mul_zero (x : K₀Ring B) : x * 0 = 0 := map_zero (mulHom B x)

protected theorem zero_mul (x : K₀Ring B) : 0 * x = 0 := by
  simp only [mul_def, map_zero, AddMonoidHom.zero_apply]

protected theorem mul_neg (x y : K₀Ring B) : x * -y = -(x * y) := map_neg (mulHom B x) y

protected theorem neg_mul (x y : K₀Ring B) : -x * y = -(x * y) := by
  simp only [mul_def, map_neg, AddMonoidHom.neg_apply]

theorem mul_assoc_mk {a b c d e e' : B} (f : a ⟶ b) (g : c ⟶ d) (h : e ⟶ e') :
    mk f * mk g * mk h = mk f * (mk g * mk h) := by
  by_cases h1 : d = a
  · subst h1
    rw [mk_mul_mk]
    by_cases h2 : e' = c
    · subst h2
      rw [mk_mul_mk, mk_mul_mk, mk_mul_mk]
      exact mk_eq_mk_of_iso (α_ h g f).symm
    · rw [mk_mul_mk_of_ne _ _ h2, mk_mul_mk_of_ne _ _ h2, K₀Ring.mul_zero]
  · rw [mk_mul_mk_of_ne _ _ h1, K₀Ring.zero_mul]
    by_cases h2 : e' = c
    · subst h2
      rw [mk_mul_mk, mk_mul_mk_of_ne _ _ h1]
    · rw [mk_mul_mk_of_ne _ _ h2, K₀Ring.mul_zero]

theorem mul_assoc_of {a b c d e e' : B} (x : K₀ (a ⟶ b)) (y : K₀ (c ⟶ d)) (z : K₀ (e ⟶ e')) :
    of a b x * of c d y * of e e' z = of a b x * (of c d y * of e e' z) := by
  induction x using K₀.induction_on with
  | mk f =>
    induction y using K₀.induction_on with
    | mk g =>
      induction z using K₀.induction_on with
      | mk h => exact mul_assoc_mk f g h
      | zero => simp only [map_zero, K₀Ring.mul_zero]
      | add z z' hz hz' => simp only [map_add, K₀Ring.mul_add, hz, hz']
      | neg z hz => simp only [map_neg, K₀Ring.mul_neg, hz]
    | zero => simp only [map_zero, K₀Ring.mul_zero, K₀Ring.zero_mul]
    | add y y' hy hy' => simp only [map_add, K₀Ring.mul_add, K₀Ring.add_mul, hy, hy']
    | neg y hy => simp only [map_neg, K₀Ring.mul_neg, K₀Ring.neg_mul, hy]
  | zero => simp only [map_zero, K₀Ring.zero_mul]
  | add x x' hx hx' => simp only [map_add, K₀Ring.add_mul, hx, hx']
  | neg x hx => simp only [map_neg, K₀Ring.neg_mul, hx]

protected theorem mul_assoc (x y z : K₀Ring B) : x * y * z = x * (y * z) := by
  induction x using induction_on with
  | zero => simp only [K₀Ring.zero_mul]
  | of a b x =>
    induction y using induction_on with
    | zero => simp only [K₀Ring.zero_mul, K₀Ring.mul_zero]
    | of c d y =>
      induction z using induction_on with
      | zero => simp only [K₀Ring.mul_zero]
      | of e e' z => exact mul_assoc_of x y z
      | add z z' hz hz' => simp only [K₀Ring.mul_add, hz, hz']
    | add y y' hy hy' => simp only [K₀Ring.mul_add, K₀Ring.add_mul, hy, hy']
  | add x x' hx hx' => simp only [K₀Ring.add_mul, hx, hx']

/-- **Brundan–Ellis, end of §6.** The Grothendieck ring of an additive 2-category is a
(non-unital, associative) ring, with `[G] · [F] = [F ≫ G]`. -/
instance instNonUnitalRing : NonUnitalRing (K₀Ring B) :=
  { (inferInstance : AddCommGroup (K₀Ring B)) with
    mul_assoc := K₀Ring.mul_assoc
    left_distrib := K₀Ring.mul_add
    right_distrib := K₀Ring.add_mul
    zero_mul := K₀Ring.zero_mul
    mul_zero := K₀Ring.mul_zero }

/-! ### The distinguished idempotents `1_λ` -/

/-- The idempotent `1_λ := [𝟙 λ]`. -/
def one (a : B) : K₀Ring B := mk (𝟙 a)

theorem one_mul_of (x : K₀ (a ⟶ b)) : one b * of a b x = of a b x := by
  induction x using K₀.induction_on with
  | mk f =>
    change mk (𝟙 b) * mk f = mk f
    rw [mk_mul_mk]
    exact mk_eq_mk_of_iso (ρ_ f)
  | zero => simp only [map_zero, K₀Ring.mul_zero]
  | add x x' hx hx' => simp only [map_add, K₀Ring.mul_add, hx, hx']
  | neg x hx => simp only [map_neg, K₀Ring.mul_neg, hx]

theorem of_mul_one (x : K₀ (a ⟶ b)) : of a b x * one a = of a b x := by
  induction x using K₀.induction_on with
  | mk f =>
    change mk f * mk (𝟙 a) = mk f
    rw [mk_mul_mk]
    exact mk_eq_mk_of_iso (λ_ f)
  | zero => simp only [map_zero, K₀Ring.zero_mul]
  | add x x' hx hx' => simp only [map_add, K₀Ring.add_mul, hx, hx']
  | neg x hx => simp only [map_neg, K₀Ring.neg_mul, hx]

theorem one_mul_of_of_ne {c : B} (h : c ≠ b) (x : K₀ (a ⟶ b)) : one c * of a b x = 0 := by
  rw [one, mk, of_mul_of, mulOf_of_ne (Ne.symm h)]

theorem of_mul_one_of_ne {c : B} (h : c ≠ a) (x : K₀ (a ⟶ b)) : of a b x * one c = 0 := by
  rw [one, mk, of_mul_of, mulOf_of_ne h]

/-- `1_λ` is idempotent. -/
theorem one_mul_one_self (a : B) : one a * one a = one a := one_mul_of (K₀.mk (𝟙 a))

/-- The `1_λ` are mutually orthogonal. -/
theorem one_mul_one_of_ne {a b : B} (h : a ≠ b) : one a * one b = 0 :=
  one_mul_of_of_ne h (K₀.mk (𝟙 b))

theorem finset_sum_one_mul_of (s : Finset B) (hb : b ∈ s) (x : K₀ (a ⟶ b)) :
    (∑ c ∈ s, one c) * of a b x = of a b x := by
  rw [Finset.sum_mul, Finset.sum_eq_single b (fun c _ hc => one_mul_of_of_ne hc x)
    (fun h => absurd hb h), one_mul_of]

theorem of_mul_finset_sum_one (s : Finset B) (ha : a ∈ s) (x : K₀ (a ⟶ b)) :
    of a b x * ∑ c ∈ s, one c = of a b x := by
  rw [Finset.mul_sum, Finset.sum_eq_single a (fun c _ hc => of_mul_one_of_ne hc x)
    (fun h => absurd ha h), of_mul_one]

/-- **Local unitality.** Every element of `K₀Ring B` is fixed by left and right multiplication
by the sum of the idempotents `1_λ` over any large enough finite set of objects. -/
theorem exists_finset_one_mul (x : K₀Ring B) :
    ∃ s : Finset B, ∀ t : Finset B, s ⊆ t →
      (∑ c ∈ t, one c) * x = x ∧ x * ∑ c ∈ t, one c = x := by
  induction x using induction_on with
  | zero => exact ⟨∅, fun _ _ => by simp⟩
  | of a b x =>
    exact ⟨{a, b}, fun t ht => ⟨finset_sum_one_mul_of t (ht (by simp)) x,
      of_mul_finset_sum_one t (ht (by simp)) x⟩⟩
  | add x y hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨s', hs'⟩ := hy
    refine ⟨s ∪ s', fun t ht => ?_⟩
    obtain ⟨h1, h2⟩ := hs t (Finset.union_subset_left ht)
    obtain ⟨h1', h2'⟩ := hs' t (Finset.union_subset_right ht)
    exact ⟨by rw [mul_add, h1, h1'], by rw [add_mul, h2, h2']⟩

/-! ## The `Zπ[q, q⁻¹]`-algebra structure for `(Q, Π)`-2-categories -/

section Module

open LaurentPolynomial

variable {R : Type w₁} [CommRing R] [∀ a b : B, Linear R (a ⟶ b)] [LinearBicategory R B]
  [QPiTwoCategory R B]

local notation "𝛑" => PiTwoCategory.pi (R := R)
local notation "𝛃" => PiTwoCategory.β (R := R)
local notation "𝐪" => QPiTwoCategory.q (R := R)
local notation "𝐪⁻¹" => QPiTwoCategory.qinv (R := R)
local notation "𝛄" => QPiTwoCategory.γ (R := R)

/-- The endomorphism of `K₀Ring B` acting on `K₀ (a ⟶ b)` by `[F] ↦ [F ≫ t_b]`, for a family
of 1-morphisms `t_b : b → b` (`π`, `q`, `q⁻¹`). -/
def tEnd (t : ∀ b : B, b ⟶ b) : AddMonoid.End (K₀Ring B) :=
  DirectSum.map fun p : B × B => K₀.map (postcomp p.1 (t p.2))

theorem tEnd_of (t : ∀ b : B, b ⟶ b) (x : K₀ (a ⟶ b)) :
    tEnd t (of a b x) = of a b (K₀.map (postcomp a (t b)) x) :=
  DirectSum.map_of _ _ _

theorem tEnd_mk (t : ∀ b : B, b ⟶ b) (f : a ⟶ b) : tEnd t (mk f) = mk (f ≫ t b) := by
  rw [mk, tEnd_of, K₀.map_mk]
  rfl

/-- `[F ≫ t] = [t ≫ F]`-type endomorphisms commute with the multiplication. -/
theorem tEnd_mul (t : ∀ b : B, b ⟶ b) (x y : K₀Ring B) : tEnd t (x * y) = tEnd t x * y := by
  induction x using induction_on with
  | zero => simp only [K₀Ring.zero_mul, map_zero]
  | of a b x =>
    induction y using induction_on with
    | zero => simp only [K₀Ring.mul_zero, map_zero]
    | of c d y =>
      induction x using K₀.induction_on with
      | mk f =>
        induction y using K₀.induction_on with
        | mk g =>
          change tEnd t (mk f * mk g) = tEnd t (mk f) * mk g
          by_cases h : d = a
          · subst h
            rw [mk_mul_mk, tEnd_mk, tEnd_mk, mk_mul_mk]
            exact mk_eq_mk_of_iso (α_ g f (t b))
          · rw [mk_mul_mk_of_ne _ _ h, tEnd_mk, mk_mul_mk_of_ne _ _ h, map_zero]
        | zero => simp only [map_zero, K₀Ring.mul_zero]
        | add y y' hy hy' => simp only [map_add, K₀Ring.mul_add, hy, hy']
        | neg y hy => simp only [map_neg, K₀Ring.mul_neg, hy]
      | zero => simp only [map_zero, K₀Ring.zero_mul]
      | add x x' hx hx' => simp only [map_add, K₀Ring.add_mul, hx, hx']
      | neg x hx => simp only [map_neg, K₀Ring.neg_mul, hx]
    | add y y' hy hy' => simp only [K₀Ring.mul_add, map_add, hy, hy']
  | add x x' hx hx' => simp only [K₀Ring.add_mul, map_add, hx, hx']

theorem mul_tEnd (t : ∀ b : B, b ⟶ b) (τ : ∀ {a b : B} (f : a ⟶ b), f ≫ t b ≅ t a ≫ f)
    (x y : K₀Ring B) : tEnd t (x * y) = x * tEnd t y := by
  induction x using induction_on with
  | zero => simp only [K₀Ring.zero_mul, map_zero]
  | of a b x =>
    induction y using induction_on with
    | zero => simp only [K₀Ring.mul_zero, map_zero]
    | of c d y =>
      induction x using K₀.induction_on with
      | mk f =>
        induction y using K₀.induction_on with
        | mk g =>
          change tEnd t (mk f * mk g) = mk f * tEnd t (mk g)
          by_cases h : d = a
          · subst h
            rw [mk_mul_mk, tEnd_mk, tEnd_mk, mk_mul_mk]
            exact mk_eq_mk_of_iso (α_ g f _ ≪≫ whiskerLeftIso g (τ f) ≪≫ (α_ g _ f).symm)
          · rw [mk_mul_mk_of_ne _ _ h, tEnd_mk, mk_mul_mk_of_ne _ _ h, map_zero]
        | zero => simp only [map_zero, K₀Ring.mul_zero]
        | add y y' hy hy' => simp only [map_add, K₀Ring.mul_add, hy, hy']
        | neg y hy => simp only [map_neg, K₀Ring.mul_neg, hy]
      | zero => simp only [map_zero, K₀Ring.zero_mul]
      | add x x' hx hx' => simp only [map_add, K₀Ring.add_mul, hx, hx']
      | neg x hx => simp only [map_neg, K₀Ring.neg_mul, hx]
    | add y y' hy hy' => simp only [K₀Ring.mul_add, map_add, hy, hy']
  | add x x' hx hx' => simp only [K₀Ring.add_mul, map_add, hx, hx']

/-- `[F ≫ t_μ] = [t_μ] · [F]`: the endomorphism `tEnd t` is left multiplication by `[t_μ]` on
`K₀ (λ ⟶ μ)`. -/
theorem tEnd_of_eq_mk_mul (t : ∀ b : B, b ⟶ b) (x : K₀ (a ⟶ b)) :
    tEnd t (of a b x) = mk (t b) * of a b x := by
  induction x using K₀.induction_on with
  | mk f =>
    change tEnd t (mk f) = mk (t b) * mk f
    rw [tEnd_mk, mk_mul_mk]
  | zero => simp only [map_zero, K₀Ring.mul_zero]
  | add x x' hx hx' => simp only [map_add, K₀Ring.mul_add, hx, hx']
  | neg x hx => simp only [map_neg, K₀Ring.mul_neg, hx]

/-- `[F ≫ t_μ] = [F] · [t_λ]` when `F t_μ ≅ t_λ F`: the endomorphism `tEnd t` is right
multiplication by `[t_λ]` on `K₀ (λ ⟶ μ)`. -/
theorem tEnd_of_eq_mul_mk (t : ∀ b : B, b ⟶ b) (τ : ∀ {a b : B} (f : a ⟶ b), f ≫ t b ≅ t a ≫ f)
    (x : K₀ (a ⟶ b)) : tEnd t (of a b x) = of a b x * mk (t a) := by
  induction x using K₀.induction_on with
  | mk f =>
    change tEnd t (mk f) = mk f * mk (t a)
    rw [tEnd_mk, mk_mul_mk]
    exact mk_eq_mk_of_iso (τ f)
  | zero => simp only [map_zero, K₀Ring.zero_mul]
  | add x x' hx hx' => simp only [map_add, K₀Ring.add_mul, hx, hx']
  | neg x hx => simp only [map_neg, K₀Ring.neg_mul, hx]

/-- The isomorphism `F q_μ⁻¹ ≅ q_λ⁻¹ F` derived from `γ_F`, `ii` and `jj`. -/
def γinvIso (f : a ⟶ b) : f ≫ 𝐪⁻¹ b ≅ 𝐪⁻¹ a ≫ f :=
  (λ_ _).symm ≪≫ whiskerRightIso (QPiTwoCategory.jj (R := R) a).symm _ ≪≫ α_ _ _ _ ≪≫
    whiskerLeftIso _ ((α_ _ _ _).symm ≪≫ whiskerRightIso (𝛄 f).symm _ ≪≫ α_ _ _ _ ≪≫
      whiskerLeftIso _ (QPiTwoCategory.ii (R := R) b) ≪≫ ρ_ _)

variable (R) in
/-- The ring homomorphism `Zπ[q, q⁻¹] → End(K₀Ring B)` acting on each summand `K₀ (λ ⟶ μ)`
through the `Zπ[q, q⁻¹]`-module structure of `K₀` of the `(Q, Π)`-category `Hom(λ, μ)`
(`K₀.laurentEnd`). -/
def laurentEnd : LaurentPolynomial Zπ →+* AddMonoid.End (K₀Ring B) where
  toFun r := DirectSum.map fun p : B × B => K₀.laurentEnd R (p.1 ⟶ p.2) r
  map_one' := AddMonoidHom.ext fun x => DirectSum.ext _ fun p => by
    rw [DirectSum.map_apply, map_one]
    rfl
  map_mul' r s := AddMonoidHom.ext fun x => DirectSum.ext _ fun p => by
    show (DirectSum.map _ x) p = (DirectSum.map _ (DirectSum.map _ x)) p
    rw [DirectSum.map_apply, DirectSum.map_apply, DirectSum.map_apply, map_mul]
    rfl
  map_zero' := AddMonoidHom.ext fun x => DirectSum.ext _ fun p => by
    rw [DirectSum.map_apply, map_zero]
    rfl
  map_add' r s := AddMonoidHom.ext fun x => DirectSum.ext _ fun p => by
    rw [AddMonoidHom.add_apply, DirectSum.add_apply, DirectSum.map_apply, DirectSum.map_apply,
      DirectSum.map_apply, map_add]
    rfl

theorem laurentEnd_apply (r : LaurentPolynomial Zπ) (x : K₀Ring B) (p : B × B) :
    laurentEnd R r x p = K₀.laurentEnd R (p.1 ⟶ p.2) r (x p) :=
  DirectSum.map_apply _ _ _

theorem laurentEnd_of (r : LaurentPolynomial Zπ) (x : K₀ (a ⟶ b)) :
    laurentEnd R r (of a b x) = of a b (K₀.laurentEnd R (a ⟶ b) r x) :=
  DirectSum.map_of _ _ _

theorem laurentEnd_C_π : laurentEnd R (B := B) (C Zπ.π) = tEnd 𝛑 :=
  AddMonoidHom.ext fun x => DirectSum.ext _ fun p => by
    rw [laurentEnd_apply, K₀.laurentEnd_C, Zπ.toEnd_π, tEnd, DirectSum.map_apply]
    rfl

theorem laurentEnd_T_one : laurentEnd R (B := B) (T 1) = tEnd 𝐪 :=
  AddMonoidHom.ext fun x => DirectSum.ext _ fun p => by
    rw [laurentEnd_apply, K₀.laurentEnd_T, zpow_one, tEnd, DirectSum.map_apply]
    rfl

theorem laurentEnd_T_neg_one : laurentEnd R (B := B) (T (-1)) = tEnd 𝐪⁻¹ :=
  AddMonoidHom.ext fun x => DirectSum.ext _ fun p => by
    rw [laurentEnd_apply, K₀.laurentEnd_T, zpow_neg_one, tEnd, DirectSum.map_apply]
    rfl

variable (R) in
/-- **Brundan–Ellis, end of §6.** The Grothendieck ring of a `(Q, Π)`-2-category is a module
over `Zπ[q, q⁻¹]`, with `π` and `q` acting on the summand `K₀ (λ ⟶ μ)` by `[F] ↦ [F ≫ π_μ]`
and `[F] ↦ [F ≫ q_μ]` (the paper's `[π_μ F]`, `[q_μ F]`). -/
def moduleLaurent : Module (LaurentPolynomial Zπ) (K₀Ring B) :=
  Module.compHom (K₀Ring B) (laurentEnd R (B := B))

theorem smul_def (r : LaurentPolynomial Zπ) (x : K₀Ring B) :
    letI := moduleLaurent R (B := B)
    r • x = laurentEnd R r x := rfl

/-- The module structure restricts on each summand to that of `K₀ (λ ⟶ μ)`
(`K₀.moduleLaurent` for the `(Q, Π)`-category `Hom(λ, μ)`). -/
theorem smul_of (r : LaurentPolynomial Zπ) (x : K₀ (a ⟶ b)) :
    letI := moduleLaurent R (B := B)
    letI := K₀.moduleLaurent R (a ⟶ b)
    r • of a b x = of a b (r • x) :=
  laurentEnd_of r x

/-- `π` acts on `1_μ K₀ 1_λ` by left multiplication by `[π_μ]`. -/
theorem C_π_smul_of (x : K₀ (a ⟶ b)) :
    letI := moduleLaurent R (B := B)
    (C Zπ.π : LaurentPolynomial Zπ) • of a b x = mk (𝛑 b) * of a b x := by
  show laurentEnd R (C Zπ.π) (of a b x) = _
  rw [laurentEnd_C_π, tEnd_of_eq_mk_mul]

/-- `π` acts on `1_μ K₀ 1_λ` by right multiplication by `[π_λ]` (via `β`). -/
theorem C_π_smul_of' (x : K₀ (a ⟶ b)) :
    letI := moduleLaurent R (B := B)
    (C Zπ.π : LaurentPolynomial Zπ) • of a b x = of a b x * mk (𝛑 a) := by
  show laurentEnd R (C Zπ.π) (of a b x) = _
  rw [laurentEnd_C_π, tEnd_of_eq_mul_mk 𝛑 (fun f => 𝛃 f)]

/-- `q` acts on `1_μ K₀ 1_λ` by left multiplication by `[q_μ]`. -/
theorem T_smul_of (x : K₀ (a ⟶ b)) :
    letI := moduleLaurent R (B := B)
    (T 1 : LaurentPolynomial Zπ) • of a b x = mk (𝐪 b) * of a b x := by
  show laurentEnd R (T 1) (of a b x) = _
  rw [laurentEnd_T_one, tEnd_of_eq_mk_mul]

/-- `q` acts on `1_μ K₀ 1_λ` by right multiplication by `[q_λ]` (via `γ`). -/
theorem T_smul_of' (x : K₀ (a ⟶ b)) :
    letI := moduleLaurent R (B := B)
    (T 1 : LaurentPolynomial Zπ) • of a b x = of a b x * mk (𝐪 a) := by
  show laurentEnd R (T 1) (of a b x) = _
  rw [laurentEnd_T_one, tEnd_of_eq_mul_mk 𝐪 (fun f => 𝛄 f)]

/-- `q⁻¹` acts on `1_μ K₀ 1_λ` by left multiplication by `[q_μ⁻¹]`. -/
theorem T_neg_one_smul_of (x : K₀ (a ⟶ b)) :
    letI := moduleLaurent R (B := B)
    (T (-1) : LaurentPolynomial Zπ) • of a b x = mk (𝐪⁻¹ b) * of a b x := by
  show laurentEnd R (T (-1)) (of a b x) = _
  rw [laurentEnd_T_neg_one, tEnd_of_eq_mk_mul]

/-- `q⁻¹` acts on `1_μ K₀ 1_λ` by right multiplication by `[q_λ⁻¹]`. -/
theorem T_neg_one_smul_of' (x : K₀ (a ⟶ b)) :
    letI := moduleLaurent R (B := B)
    (T (-1) : LaurentPolynomial Zπ) • of a b x = of a b x * mk (𝐪⁻¹ a) := by
  show laurentEnd R (T (-1)) (of a b x) = _
  rw [laurentEnd_T_neg_one, tEnd_of_eq_mul_mk 𝐪⁻¹ (fun f => γinvIso f)]

/-! ### Compatibility of the module structure with the multiplication -/

/-- An endomorphism commuting with left and right multiplications. -/
def IsCentral (φ : AddMonoid.End (K₀Ring B)) : Prop :=
  ∀ x y : K₀Ring B, φ (x * y) = φ x * y ∧ φ (x * y) = x * φ y

theorem isCentral_one : IsCentral (1 : AddMonoid.End (K₀Ring B)) := fun _ _ => ⟨rfl, rfl⟩

theorem isCentral_zero : IsCentral (0 : AddMonoid.End (K₀Ring B)) := fun x y =>
  ⟨by rw [AddMonoid.End.zero_apply, AddMonoid.End.zero_apply, zero_mul],
    by rw [AddMonoid.End.zero_apply, AddMonoid.End.zero_apply, mul_zero]⟩

theorem IsCentral.add {φ ψ : AddMonoid.End (K₀Ring B)} (hφ : IsCentral φ) (hψ : IsCentral ψ) :
    IsCentral (φ + ψ) := fun x y => by
  obtain ⟨h1, h2⟩ := hφ x y
  obtain ⟨h3, h4⟩ := hψ x y
  exact ⟨by change φ (x * y) + ψ (x * y) = (φ x + ψ x) * y; rw [h1, h3, add_mul],
    by change φ (x * y) + ψ (x * y) = x * (φ y + ψ y); rw [h2, h4, mul_add]⟩

theorem IsCentral.neg {φ : AddMonoid.End (K₀Ring B)} (hφ : IsCentral φ) : IsCentral (-φ) :=
  fun x y => by
  obtain ⟨h1, h2⟩ := hφ x y
  exact ⟨by change -φ (x * y) = -φ x * y; rw [h1, neg_mul],
    by change -φ (x * y) = x * -φ y; rw [h2, mul_neg]⟩

theorem IsCentral.mul {φ ψ : AddMonoid.End (K₀Ring B)} (hφ : IsCentral φ) (hψ : IsCentral ψ) :
    IsCentral (φ * ψ) := fun x y => by
  obtain ⟨h3, h4⟩ := hψ x y
  obtain ⟨h1, _⟩ := hφ (ψ x) y
  obtain ⟨_, h2⟩ := hφ x (ψ y)
  exact ⟨by change φ (ψ (x * y)) = φ (ψ x) * y; rw [h3, h1],
    by change φ (ψ (x * y)) = x * φ (ψ y); rw [h4, h2]⟩

theorem isCentral_intCast (n : ℤ) : IsCentral ((n : ℤ) : AddMonoid.End (K₀Ring B)) := by
  induction n using Int.induction_on with
  | hz => rw [Int.cast_zero]; exact isCentral_zero
  | hp n ih => rw [Int.cast_add, Int.cast_one]; exact ih.add isCentral_one
  | hn n ih => rw [Int.cast_sub, Int.cast_one, sub_eq_add_neg]; exact ih.add isCentral_one.neg

theorem isCentral_tEnd_π : IsCentral (tEnd (B := B) 𝛑) := fun x y =>
  ⟨tEnd_mul 𝛑 x y, mul_tEnd 𝛑 (fun f => 𝛃 f) x y⟩

theorem isCentral_tEnd_q : IsCentral (tEnd (B := B) 𝐪) := fun x y =>
  ⟨tEnd_mul 𝐪 x y, mul_tEnd 𝐪 (fun f => 𝛄 f) x y⟩

theorem isCentral_tEnd_qinv : IsCentral (tEnd (B := B) 𝐪⁻¹) := fun x y =>
  ⟨tEnd_mul 𝐪⁻¹ x y, mul_tEnd 𝐪⁻¹ (fun f => γinvIso f) x y⟩

theorem isCentral_laurentEnd_T (n : ℤ) : IsCentral (laurentEnd R (B := B) (T n)) := by
  induction n using Int.induction_on with
  | hz => rw [T_zero, map_one]; exact isCentral_one
  | hp n ih => rw [T_add, map_mul, laurentEnd_T_one]; exact ih.mul (isCentral_tEnd_q (R := R))
  | hn n ih =>
    rw [T_sub, map_mul, laurentEnd_T_neg_one]; exact ih.mul (isCentral_tEnd_qinv (R := R))

theorem isCentral_laurentEnd_C (r : Zπ) : IsCentral (laurentEnd R (B := B) (C r)) := by
  obtain ⟨i, j, rfl⟩ := Zπ.exists_eq_add_mul_π r
  rw [map_add, map_mul, map_intCast, map_intCast, map_add, map_mul, map_intCast, map_intCast,
    laurentEnd_C_π]
  exact (isCentral_intCast i).add ((isCentral_intCast j).mul (isCentral_tEnd_π (R := R)))

theorem isCentral_laurentEnd (r : LaurentPolynomial Zπ) : IsCentral (laurentEnd R (B := B) r) := by
  induction r using LaurentPolynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | C_mul_T n a => rw [map_mul]; exact (isCentral_laurentEnd_C a).mul (isCentral_laurentEnd_T n)

/-- **Brundan–Ellis, end of §6.** The `Zπ[q, q⁻¹]`-module structure is compatible with the
multiplication: `K₀Ring B` is a `Zπ[q, q⁻¹]`-algebra. -/
theorem smul_mul (r : LaurentPolynomial Zπ) (x y : K₀Ring B) :
    letI := moduleLaurent R (B := B)
    (r • x) * y = r • (x * y) :=
  ((isCentral_laurentEnd r) x y).1.symm

theorem mul_smul (r : LaurentPolynomial Zπ) (x y : K₀Ring B) :
    letI := moduleLaurent R (B := B)
    x * (r • y) = r • (x * y) :=
  ((isCentral_laurentEnd r) x y).2.symm

end Module

end K₀Ring

end Ring

/-! ## The Grothendieck ring of `GSKAR(𝔄)` -/

section GSKAR

open LaurentPolynomial

variable (R : Type w₁) [CommRing R] (B : Type u) [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [∀ a b : B, GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R B] [GradedTwoSupercategory R B]

namespace GSKAR

/-- **Brundan–Ellis, end of §6.** The Grothendieck ring `K₀(GSKAR(𝔄))` of the graded super
Karoubi envelope of a graded 2-supercategory is a locally unital ring with the distinguished
idempotents `1_λ` (`K₀Ring.one`). -/
example : NonUnitalRing (K₀Ring (GSKAR R B)) := inferInstance

/-- The summand `1_μ K₀(GSKAR(𝔄)) 1_λ` is `K₀(GSKar(Hom_𝔄(λ, μ)))`. -/
theorem K₀_hom_eq (a b : B) : K₀ (mkObj R B a ⟶ mkObj R B b) = K₀ (GSKar R (a ⟶ b)) := rfl

/-- **Brundan–Ellis, end of §6.** `K₀(GSKAR(𝔄))` is a `Zπ[q, q⁻¹]`-algebra. -/
def moduleLaurent : Module (LaurentPolynomial Zπ) (K₀Ring (GSKAR R B)) :=
  K₀Ring.moduleLaurent R

theorem smul_mul (r : LaurentPolynomial Zπ) (x y : K₀Ring (GSKAR R B)) :
    letI := moduleLaurent R B
    (r • x) * y = r • (x * y) :=
  K₀Ring.smul_mul r x y

theorem mul_smul (r : LaurentPolynomial Zπ) (x y : K₀Ring (GSKAR R B)) :
    letI := moduleLaurent R B
    x * (r • y) = r • (x * y) :=
  K₀Ring.mul_smul r x y

variable {R B}

/-- `π` acts on `1_μ K₀ 1_λ` by left multiplication by `[π_μ]`, equivalently by right
multiplication by `[π_λ]`. -/
theorem C_π_smul_of {a b : B} (x : K₀ (mkObj R B a ⟶ mkObj R B b)) :
    letI := moduleLaurent R B
    (C Zπ.π : LaurentPolynomial Zπ) • K₀Ring.of _ _ x =
        K₀Ring.mk (PiTwoCategory.pi (R := R) (mkObj R B b)) * K₀Ring.of _ _ x ∧
      (C Zπ.π : LaurentPolynomial Zπ) • K₀Ring.of _ _ x =
        K₀Ring.of _ _ x * K₀Ring.mk (PiTwoCategory.pi (R := R) (mkObj R B a)) :=
  ⟨K₀Ring.C_π_smul_of x, K₀Ring.C_π_smul_of' x⟩

/-- `q` acts on `1_μ K₀ 1_λ` by left multiplication by `[q_μ]`, equivalently by right
multiplication by `[q_λ]`. -/
theorem T_smul_of {a b : B} (x : K₀ (mkObj R B a ⟶ mkObj R B b)) :
    letI := moduleLaurent R B
    (T 1 : LaurentPolynomial Zπ) • K₀Ring.of _ _ x =
        K₀Ring.mk (QPiTwoCategory.q (R := R) (mkObj R B b)) * K₀Ring.of _ _ x ∧
      (T 1 : LaurentPolynomial Zπ) • K₀Ring.of _ _ x =
        K₀Ring.of _ _ x * K₀Ring.mk (QPiTwoCategory.q (R := R) (mkObj R B a)) :=
  ⟨K₀Ring.T_smul_of x, K₀Ring.T_smul_of' x⟩

end GSKAR

end GSKAR

end StringDiagrams

end
