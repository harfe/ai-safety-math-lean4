module

public import Mathlib

set_option linter.style.header false

/-!
Definitions of `AISafetyMath/Targets/ConverseLawvere.lean` (copied verbatim), and the theorems
relating `HasLawvereDomainDiag` to the fixed point property.

`HasFixedPoints D ↔ HasLawvereDomainDiag D`:
* `→`: take `X = C(D, D)`, topologized by pulling back along a fixed-point selector `fp`, and
  `f h k = h (fp k)`. The diagonal `h ↦ h (fp h) = fp h` is continuous by construction. Every
  continuous `k : X → D` factors through `fp`, as `k = k' ∘ fp` with `k' t = k (const t)`, since
  points with equal `fp` are inseparable and `D` is T0 (`t0Space_of_hasFixedPoints`). Then
  `f k' = k`.
* `←`: Lawvere's diagonal argument; a code `x` of `g ∘ diag` gives the fixed point `f x x`.
-/

@[expose] public section


namespace ConverseLawvere

open Topology

section Basics

variable {X D : Type} [TopologicalSpace X] [TopologicalSpace D]
variable (f : X → X → D)

def ContinuousDiag : Prop := Continuous (fun x => f x x)

def JointlyContinuous : Prop := Continuous f.uncurry

def SurjectivityCondition {X D : Type} [TopologicalSpace X] [TopologicalSpace D]
    (f : X → X → D) : Prop := (∀ (h : C(X, D)), ∃ x, f x = h)

end Basics

/-- Definition:
We say that a topological space D has a Lawvere domain X
if there is a f that is jointly continuous and surjective onto continuous functions
-/
def HasLawvereDomain (D : Type) [TopologicalSpace D] : Prop :=
  ∃ (X : Type) (_ : TopologicalSpace X),
  ∃ (f : X → X → D),
  JointlyContinuous f ∧ SurjectivityCondition f

/-- Definition:
Same as `HasLawvereDomain` but we only require that the diagonal of f is continuous.
-/
def HasLawvereDomainDiag (D : Type) [TopologicalSpace D] : Prop :=
  ∃ (X : Type) (_ : TopologicalSpace X),
  ∃ (f : X → X → D),
  ContinuousDiag f ∧ SurjectivityCondition f

def HasFixedPoints (D : Type) [TopologicalSpace D] : Prop :=
 ∀ (f : C(D, D)), ∃ x, f x = x

/-- sanity check: -/
lemma diag_of_main (D : Type) [TopologicalSpace D] :
    HasLawvereDomain D → HasLawvereDomainDiag D := by
  rintro ⟨X, _, f, hf, hcov⟩
  exact ⟨X, inferInstance, f, hf.comp (continuous_id.prodMk continuous_id), hcov⟩

/-- A space with the fixed point property is T0: if `a ≠ b` were inseparable, the map sending
`a` to `b` and everything else to `a` would be continuous without fixed points. -/
theorem t0Space_of_hasFixedPoints (D : Type) [TopologicalSpace D] (hD : HasFixedPoints D) :
    T0Space D := by
  classical
  refine t0Space_iff_inseparable D |>.mpr fun a b hab => ?_
  by_contra hne
  let g : C(D, D) := ⟨fun x => if x = a then b else a, continuous_def.mpr fun U hU => by
    by_cases ha : a ∈ U
    · have hb : b ∈ U := (hab.mem_open_iff hU).mp ha
      convert isOpen_univ
      ext x; simp only [Set.mem_preimage, Set.mem_univ, iff_true]; split_ifs <;> assumption
    · have hb : b ∉ U := fun hb => ha ((hab.mem_open_iff hU).mpr hb)
      convert isOpen_empty
      ext x; simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
      split_ifs <;> assumption⟩
  obtain ⟨x, hx⟩ := hD g
  by_cases hxa : x = a
  · exact hne (by simp [g, hxa] at hx; exact hx.symm)
  · exact hxa (by simpa [g, hxa] using hx.symm)

/-- `C(D, D)`, to be topologized by pulling back along a fixed-point selector. -/
structure Code (D : Type) [TopologicalSpace D] where
  val : C(D, D)

theorem lawvereDomDiag_of_fp (D : Type) [TopologicalSpace D] :
    HasFixedPoints D → HasLawvereDomainDiag D := by
  intro hD
  have := t0Space_of_hasFixedPoints D hD
  let fp : C(D, D) → D := fun h => (hD h).choose
  have hfp (h : C(D, D)) : h (fp h) = fp h := (hD h).choose_spec
  have hconst (t : D) : fp (ContinuousMap.const D t) = t := (hfp _).symm
  let : TopologicalSpace (Code D) := .induced (fun x => fp x.val) inferInstance
  have hind : IsInducing (fun x : Code D => fp x.val) := ⟨rfl⟩
  refine ⟨Code D, inferInstance, fun x y => x.val (fp y.val), ?_, fun k => ?_⟩
  · have : (fun x : Code D => x.val (fp x.val)) = fun x => fp x.val := funext fun x => hfp x.val
    unfold ContinuousDiag
    simpa [this] using hind.continuous
  · have hc : Continuous fun t : D => Code.mk (ContinuousMap.const D t) :=
      hind.continuous_iff.mpr (by simp only [Function.comp_def, hconst]; exact continuous_id')
    refine ⟨⟨⟨fun t => k ⟨ContinuousMap.const D t⟩, k.continuous.comp hc⟩⟩, funext fun y => ?_⟩
    refine Inseparable.eq (Inseparable.map ?_ k.continuous)
    exact hind.inseparable_iff.mp (by simp only [hconst]; rfl)

/-- Every continuous self-map of `[0,1]` has a fixed point. -/
theorem hasFixedPoints_unitInterval : HasFixedPoints unitInterval := by
  intro h
  have hc : Continuous fun t : unitInterval => (h t : ℝ) - t := by fun_prop
  have h0 : (0 : ℝ) ∈ Set.Icc ((h 1 : ℝ) - (1 : unitInterval)) ((h 0 : ℝ) - (0 : unitInterval)) :=
    ⟨by simpa using (h 1).2.2, by simpa using (h 0).2.1⟩
  obtain ⟨t, ht⟩ := intermediate_value_univ (1 : unitInterval) 0 hc h0
  exact ⟨t, Subtype.ext (sub_eq_zero.mp ht)⟩

/-- corollary -/
theorem lawvereDomDiag_unitInterval : HasLawvereDomainDiag unitInterval :=
  lawvereDomDiag_of_fp _ hasFixedPoints_unitInterval

theorem lawvereDomDiag_iff_fp (D : Type) [TopologicalSpace D] :
    HasFixedPoints D ↔ HasLawvereDomainDiag D := by
  refine ⟨lawvereDomDiag_of_fp D, ?_⟩
  rintro ⟨X, _, f, hdiag, hcov⟩ g
  obtain ⟨x, hx⟩ := hcov ⟨fun x => g (f x x), g.continuous.comp hdiag⟩
  exact ⟨f x x, (congrFun hx x).symm⟩

section MainConjecture

def MainConjecture : Prop := HasLawvereDomain unitInterval

end MainConjecture

end ConverseLawvere
