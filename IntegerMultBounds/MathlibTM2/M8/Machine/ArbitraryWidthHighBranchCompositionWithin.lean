module

public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighBranchComposition
public import IntegerMultBounds.Machine.HoareWithinFiniteFlow

/-! The real descriptor selector and its selected terminal block share one
head interval, including the tape-preserving branch-entry transition. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighBranchCompositionWithin
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
noncomputable section
variable {t a h s : ℕ}
open ArbitraryWidthHighBranchComposition

theorem runs_within (rho width flag : Fin t)
    (hrw : rho ≠ width) (hrf : rho ≠ flag) (hwf : width ≠ flag)
    (high : Program t h a) (fallback : Program t s a)
    (v highOut fallbackOut : Tapes t a) (highCost fallbackCost : ℕ)
    (rs es : List Bool) (cr : GrowingCounterData.Canonical rs)
    (hrr : v.tape rho = BinaryDescriptorStack.descriptor rs) (hrh : v.head rho = 1)
    (her : v.tape width = BinaryDescriptorStack.descriptor es) (heh : v.head width = 1)
    (hfr : v.tape flag = fun _ => blank) (hfh : v.head flag = 0)
    (lo hi : ℤ)
    (hmargin : ∀ j, lo+(ArbitraryWidthHighBranch.cost rs es : ℕ) ≤ v.head j ∧
      v.head j+(ArbitraryWidthHighBranch.cost rs es : ℕ) ≤ hi)
    (highRuns : (1 ≤ Counter.value rs ∧ Counter.value rs < Counter.value es) →
      HoareWithin high (fun w => w = v) (fun w => w = highOut) highCost (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi))
    (fallbackRuns : ¬(1 ≤ Counter.value rs ∧ Counter.value rs < Counter.value es) →
      HoareWithin fallback (fun w => w = v) (fun w => w = fallbackOut) fallbackCost (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi)) :
    HoareWithin (program rho width flag hrw hrf hwf high fallback)
      (fun w => w = v)
      (fun w => w = if 1 ≤ Counter.value rs ∧ Counter.value rs < Counter.value es
        then highOut else fallbackOut)
      (ArbitraryWidthHighBranch.cost rs es+1+
        if 1 ≤ Counter.value rs ∧ Counter.value rs < Counter.value es then highCost else fallbackCost) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) := by
  obtain ⟨n,hn,c,hr,hh,ht,hstate⟩ :=
    ArbitraryWidthHighBranchPlacement.selects rho width flag hrw hrf hwf v rs es cr
      hrr hrh her heh hfr hfh
  let fam := family rho width flag hrw hrf hwf high fallback
  have hrs := RunWithin.heads_of_run_le hr hn lo hi hmargin
  change RunWithin (fam 0) _ n (v.start (fam 0)) c at hrs
  by_cases hg : 1 ≤ Counter.value rs ∧ Counter.value rs < Counter.value es
  · have hedge : next (h := h) (s := s) 0 c.state = some 1 := by
      rw [hstate,next_selected]
      simp [hg]
    have hc := FiniteFlow.jump_then_halt_within fam next 0 1 hrs hh hedge
      ((highRuns hg).consequence (fun _ hw => hw.trans ht) (fun _ hw => hw) le_rfl (fun _ hw => hw)) (by intro st; rfl)
    apply hc.consequence (fun _ h => h) _ _ (fun _ h => h)
    · intro w hw
      simpa only [ite_eq_left hg] using hw
    · rw [ite_eq_left hg]
      omega
  · have hedge : next (h := h) (s := s) 0 c.state = some 2 := by
      rw [hstate,next_selected]
      simp [hg]
    have hc := FiniteFlow.jump_then_halt_within fam next 0 2 hrs hh hedge
      ((fallbackRuns hg).consequence (fun _ hw => hw.trans ht) (fun _ hw => hw) le_rfl (fun _ hw => hw)) (by intro st; rfl)
    apply hc.consequence (fun _ h => h) _ _ (fun _ h => h)
    · intro w hw
      simpa only [ite_eq_right hg] using hw
    · rw [ite_eq_right hg]
      omega

end
end IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighBranchCompositionWithin
