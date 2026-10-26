module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloPublicationSchedule
public import IntegerMultBounds.NLogN.PhaseCellHaloGroupVolume

/-! Generate the clipped publication controls from the actual gather controls,
with a linear bound and exact restoration of the source controls and count. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

theorem haloPublicationControls_exec {count savedCount control savedControl counter window zero acc dst trash tmp : Fin T}
    (hreg : [count,savedCount,control,savedControl,counter,window,zero,acc,dst,trash,tmp].Nodup)
    {s t : ℕ} [NeZero s] (hst : s < t) (band a b L w : ℕ) (hwpos : 1 ≤ w)
    (hgroup : 0 < (haloLengthGroup s t band a b L).length)
    (borrowed : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hc : S.R count = List.replicate (haloLengthGroup s t band a b L).length tick)
    (hs : S.R control = haloGatherControls A s t band a b L w++borrowed)
    (hw : (S.R window).length = L*w)
    (hz : ∀ k ∈ [savedCount,savedControl,counter,zero,acc,trash,tmp], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 33*s*w+21 ∧
      Exec body (publicationControls count savedCount control savedControl counter window zero acc dst trash tmp)
        (mk v S) n
        (mk v' { S with R := (Function.update S.R dst
          (gatherControls A (haloScatterGaps s t band a b L w)++S.R dst)) }) := by
  cases he : haloOrigins s t band a b L with
  | nil => have hh := haloOrigins_length s t band a b L; rw [he] at hh; simp only [List.length_nil] at hh; omega
  | cons p ps =>
    let ds := originAdvances w p ps
    have hB : (haloLengthGroup s t band a b L).length = ps.length+1 := by
      simpa only [he,List.length_cons] using (haloOrigins_length s t band a b L).symm
    have hds : ds.length = ps.length := originAdvances_length w p ps
    have hadv : originAdvances w 0 (haloOrigins s t band a b L) = p*w::ds := by
      simp [he,originAdvances,ds]
    have hdisjoint : (p::ps).Pairwise (fun p q => p+L ≤ q) := by
      rw [← he]; exact haloOrigins_disjoint s t band a b L
    have hLd : ∀ d ∈ ds, L*w ≤ d := originAdvances_lower L w p ps hdisjoint
    have hsrc : S.R control = gatherControls A (p*w::ds)++([blank]++borrowed) := by
      rw [hs,← originAdvances_haloControls A s t band a b L w hgroup,hadv,gatherControls_append]
      simp [gatherControls,List.append_assoc]
    obtain ⟨v',n,hu,hn,hx⟩ := publicationControls_exec (body := body) hreg (L*w) (p*w) ds hLd
      tick (List.replicate ps.length tick) ([blank]++borrowed) (by simp [hds]) v S
      (by simpa [hB,List.replicate_succ] using hc) hsrc hw hz
    have hgaps : p*w::ds.map (·-L*w) = haloScatterGaps s t band a b L w := by
      have hh := haloPublicationGaps s t band a b L w
      rw [hadv] at hh
      exact hh
    refine ⟨v',n,hu,?_,by simpa only [hgaps] using hx⟩
    have hvol := haloOriginAdvances_volume s t band a b L w
    rw [hadv,List.sum_cons] at hvol
    have hL : 0 < L := ((mem_haloLengthGroup s t band a b L _).mp
      (haloGroupPhase_mem s t band a b L ⟨0,hgroup⟩)).2.1
    have hBvol := haloGroup_volume_le hst band a b L
    have hBs : ps.length+1 ≤ s := by rw [hB] at hBvol; nlinarith only [hBvol,hL]
    have hsw : s ≤ s*w := by simpa using Nat.mul_le_mul_left s hwpos
    rw [hds] at hn
    nlinarith only [hn,hvol,hBs,hsw]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
