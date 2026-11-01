module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNativeWordStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingHeaderData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseReplicaCouplingNative

/-! The generated coupling bank contains nine ordinary headers and three
scalar counters. Its owned-word bound is independent of RHS payloads/replicas. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

def replicaCouplingNativeWordBound (P q w s t u band a b : ℕ) :=
  P+2*q+2*w+s+t+u+band+a+b+Schoenhage.Schedule.topN w

theorem replicaCouplingNative_wordStock_le {A : ℕ}
    (rs : List (Fin 117)) (hnd : rs.Nodup) (howned : ∀ i ∈ rs, i ≠ 93 ∧ i ≠ 110)
    (P q w s t u band a b : ℕ) (borrowed output : List (Fin (A+4)))
    (inp : List (Bool ⊕ Bool)) (out : List Bool) :
    (rs.map (fun i => (counterR q w (replicaCouplingUnaryBank A P q w s t u band a b borrowed output inp out).R i).length)).sum ≤
      replicaCouplingNativeWordBound P q w s t u band a b := by
  let B := releasedCellBank (A := A) [] borrowed output inp out
  have hzero : (rs.map (fun i => (B.R i).length)).sum = 0 := by
    have hm : rs.map (fun i => (B.R i).length) = rs.map (fun _ => 0) := by
      apply List.map_congr_left
      intro i hi
      obtain ⟨h93,h110⟩ := howned i hi
      have hv93 : i.val ≠ 93 := by intro h; exact h93 (Fin.ext h)
      have hv110 : i.val ≠ 110 := by intro h; exact h110 (Fin.ext h)
      simp [B,releasedCellBank,hv93,hv110]
    rw [hm]
    simp
  have hh := sum_wordLengths_unaryCopies_le rs hnd (replicaCouplingMasterValue P q w s t u band a b)
    replicaCouplingHeaderCopies B.R
  have hc := sum_wordLengths_counterR_le rs hnd q w
    (replicaCouplingUnaryBank A P q w s t u band a b borrowed output inp out).R
  rw [hzero] at hh
  have hheaders : (replicaCouplingHeaderCopies.map (fun r => replicaCouplingMasterValue P q w s t u band a b r.1)).sum =
      P+q+s+t+u+band+a+b+w := by
    simp [replicaCouplingHeaderCopies,replicaCouplingMasterValue]
    omega
  rw [hheaders] at hh
  change (rs.map (fun i => ((replicaCouplingUnaryBank A P q w s t u band a b borrowed output inp out).R i).length)).sum ≤ _ at hh
  unfold replicaCouplingNativeWordBound
  omega

def replicaCouplingNativeCleanupBound (P q w s t u band a b : ℕ) :=
  2*replicaCouplingNativeWordBound P q w s t u band a b+235

theorem releaseReplicaCouplingNativeCost_le_of_generated {A : ℕ} (S : Stacks 248 A)
    (P q w s t u band a b : ℕ) (borrowed output : List (Fin (A+4)))
    (inp : List (Bool ⊕ Bool)) (out : List Bool)
    (hgenerated : ∀ i : Fin 117, S.R (Fin.castLE (by decide) i) =
      counterR q w (replicaCouplingUnaryBank A P q w s t u band a b borrowed output inp out).R i) :
    releaseReplicaCouplingNativeCost S ≤ replicaCouplingNativeCleanupBound P q w s t u band a b := by
  have hnd : replicaCouplingNativeIndices.Nodup := (List.nodup_finRange 117).filter _
  have howned : ∀ i ∈ replicaCouplingNativeIndices, i ≠ 93 ∧ i ≠ 110 := by
    intro i hi; simpa [replicaCouplingNativeIndices] using hi
  have hs := replicaCouplingNative_wordStock_le replicaCouplingNativeIndices hnd howned
    P q w s t u band a b borrowed output inp out
  have hmap : replicaCouplingNativePorts.map (fun k => (S.R k).length) =
      replicaCouplingNativeIndices.map (fun i =>
        (counterR q w (replicaCouplingUnaryBank A P q w s t u band a b borrowed output inp out).R i).length) := by
    unfold replicaCouplingNativePorts
    rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    exact congrArg List.length (hgenerated i)
  have hlen : replicaCouplingNativePorts.length ≤ 117 := by
    simp only [replicaCouplingNativePorts,List.length_map]
    exact (List.length_filter_le _ _).trans (by simp)
  unfold releaseReplicaCouplingNativeCost replicaCouplingNativeCleanupBound
  rw [hmap]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
