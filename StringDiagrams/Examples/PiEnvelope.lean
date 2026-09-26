import StringDiagrams.Super.Envelope
import StringDiagrams.Examples.OddBrauer

/-!
# Example: the Π-envelope of the odd Brauer supercategory

The odd Brauer supercategory `SB` of Brundan–Ellis, Example 1.5(iii)
(`StringDiagrams.Examples.OddBrauer`) is a presented supercategory
(`Presentation.supercategory`), so its Π-envelope `SB_π` (Definition 1.10) is a
Π-supercategory. In `SB_π` the odd cup `1 → · ⊗ ·` becomes an *even* morphism
`Π⁰ 1 → Π¹(· ⊗ ·)` (`cupShift_mem`), and the zigzag relations continue to hold for the shifted
cups and caps (`cupShift_comp_capShift`). Every superfunctor from `SB` to a Π-supercategory
extends along `J : SB → SB_π` (`extend_J`), uniquely up to even supernatural isomorphism
(`Envelope.extendRestrictIso`).
-/

noncomputable section

namespace StringDiagrams.OddBrauer

open CategoryTheory Supercategory

variable (R : Type*) [CommRing R]

instance : Supercategory R (pres R).Presented := (pres R).supercategory (isParityHomogeneous R)

/-- The Π-envelope of the odd Brauer supercategory is a Π-supercategory. -/
example : PiSupercategory R (Envelope (pres R).Presented) := inferInstance

/-- The odd cup, as a morphism `Π⁰(n) → Π¹(n + 2)` of the Π-envelope. -/
def cupShift (n i : ℕ) :
    (⟨0, (pres R).obj (strands n)⟩ : Envelope (pres R).Presented) ⟶
      ⟨1, (pres R).obj (strands (n + 2))⟩ :=
  Envelope.ofHom (cup R n i)

/-- The odd cap, as a morphism `Π¹(n + 2) → Π⁰(n)` of the Π-envelope. -/
def capShift (n i : ℕ) :
    (⟨1, (pres R).obj (strands (n + 2))⟩ : Envelope (pres R).Presented) ⟶
      ⟨0, (pres R).obj (strands n)⟩ :=
  Envelope.ofHom (cap R n i)

theorem cup_mem (n i : ℕ) :
    cup R n i ∈
      parity (R := R) ((pres R).obj (strands n)) ((pres R).obj (strands (n + 2))) 1 := by
  by_cases h : i ≤ n
  · rw [cup_def (R := R) h]
    have := Presentation.diag_isHomogeneous (isParityHomogeneous R) (dcup h)
    convert this using 1
  · simp [cup, h, Submodule.zero_mem]

theorem cap_mem (n i : ℕ) :
    cap R n i ∈
      parity (R := R) ((pres R).obj (strands (n + 2))) ((pres R).obj (strands n)) 1 := by
  by_cases h : i ≤ n
  · rw [cap_def (R := R) h]
    have := Presentation.diag_isHomogeneous (isParityHomogeneous R) (dcap h)
    convert this using 1
  · simp [cap, h, Submodule.zero_mem]

/-- In the Π-envelope, the shifted cup is even. -/
theorem cupShift_mem (n i : ℕ) :
    cupShift R n i ∈ parity (R := R)
      (⟨0, (pres R).obj (strands n)⟩ : Envelope (pres R).Presented)
      ⟨1, (pres R).obj (strands (n + 2))⟩ 0 := by
  have := Envelope.ofHom_mem (X := (⟨0, (pres R).obj (strands n)⟩ : Envelope (pres R).Presented))
    (Y := ⟨1, (pres R).obj (strands (n + 2))⟩) (cup_mem R n i)
  rwa [show (1 : ZMod 2) + (0 + 1) = 0 by decide] at this

/-- In the Π-envelope, the shifted cap is even. -/
theorem capShift_mem (n i : ℕ) :
    capShift R n i ∈ parity (R := R)
      (⟨1, (pres R).obj (strands (n + 2))⟩ : Envelope (pres R).Presented)
      ⟨0, (pres R).obj (strands n)⟩ 0 := by
  have := Envelope.ofHom_mem
    (X := (⟨1, (pres R).obj (strands (n + 2))⟩ : Envelope (pres R).Presented))
    (Y := ⟨0, (pres R).obj (strands n)⟩) (cap_mem R n i)
  rwa [show (1 : ZMod 2) + (1 + 0) = 0 by decide] at this

/-- The zigzag relation `cup ≫ cap = 1` holds for the shifted (even) cup and cap. -/
theorem cupShift_comp_capShift {n i : ℕ} (h : i + 1 ≤ n) :
    cupShift R n (i + 1) ≫ capShift R n i = 𝟙 _ :=
  zigzagA_at (R := R) h

/-- Superfunctors out of `SB` into a Π-supercategory extend along `J : SB → SB_π`
(Lemma 4.2(i)). -/
theorem extend_J {B : Type*} [Category B] [Preadditive B] [Linear R B] [Supercategory R B]
    [PiSupercategory R B] (F : (pres R).Presented ⥤ B) [F.Additive] [F.Linear R]
    [IsSuperfunctor R F] :
    Envelope.J _ ⋙ Envelope.extend R F = F :=
  Envelope.J_comp_extend R F

end StringDiagrams.OddBrauer

end
