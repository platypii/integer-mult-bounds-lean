module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCoreRecoveryLocalVolume
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRawRecoveryCoreClassProfiles

/-! Ordered raw-job lists inherit the actual core-halo volume estimate. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open scoped BigOperators

theorem coreClassJobLocalVolume_le {s t : ℕ} [NeZero s] (hst : s < t)
    (p width band n L : ℕ) (hw : 0 < width) (hwidth : width ≤ s)
    (hr : n*band ≤ width) (hband : 1 ≤ band) (hcell : s/(t-s)+1 ≤ width)
    (hprepare : p^2+band^2 ≤ width)
    (jobs : Fin (coreGatherIndices s width (n*band) L).length → RawRecoveryJob s)
    (hparams : ∀ i, let k := (coreGatherIndices s width (n*band) L)[i.val]
      (jobs i).problem.p = p ∧ (jobs i).problem.t = t ∧ (jobs i).problem.band = band ∧
      (jobs i).problem.origin = (coreHaloEndpoints s width k band n).1 ∧
      (jobs i).problem.span = (coreHaloEndpoints s width k band n).2-(coreHaloEndpoints s width k band n).1) :
    ((List.ofFn jobs).map (fun r => replicaRecoveryLocalVolume r.problem)).sum ≤
      600*(s+(t-s)*band^2) := by
  let indices := coreGatherIndices s width (n*band) L
  let volume := fun k => haloRecoveryLocalVolume p s t band
    (coreHaloEndpoints s width k band n).1 (coreHaloEndpoints s width k band n).2
  have heq : (List.ofFn jobs).map (fun r => replicaRecoveryLocalVolume r.problem) = indices.map volume := by
    rw [List.map_ofFn]
    calc
      _ = List.ofFn (fun i : Fin indices.length => volume indices[i.val]) := by
        congr 1
        funext i
        change replicaRecoveryLocalVolume (jobs i).problem = volume indices[i.val]
        obtain ⟨hp,ht,hB,ha,hspan⟩ := hparams i
        rw [replicaRecoveryLocalVolume_eq_halo,hp,ht,hB,ha,hspan,
          Nat.add_sub_of_le (coreHaloEndpoints_bounds s width indices[i.val] band n).1]
      _ = _ := List.ofFn_getElem_eq_map indices volume
  have hnodup : indices.Nodup := (coreIndices_nodup s width).filter _
  have hsub : indices.toFinset ⊆ (coreIndices s width).toFinset := by
    intro k hk
    exact List.mem_toFinset.mpr ((List.mem_filter.mp (List.mem_toFinset.mp hk)).1)
  rw [heq,←List.sum_toFinset _ hnodup]
  exact (Finset.sum_le_sum_of_subset hsub).trans
    (coreHalo_recoveryLocalVolume_amortized_le hst p width band n hw hwidth hr hband hcell hprepare)

variable {p u l targetOut s t width L : ℕ} [NeZero s] {α gap : ℝ} {C : ZMod s → GaussianInt}

theorem rawCoreClassJobs_localVolume_le (hp : 2 ≤ p) (hpacket : 8*p ≤ 2^u) (hα : 0 < α)
    (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ gap*((t : ℝ)/s-1))
    (hbudget : α^2*gap ≤ p) (hband : PhaseCellBand.width p u ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (hC : ∀ a b, a ≤ b → b ≤ s → a < s →
      ∀ j, ‖value (packedHaloPrecision p l s t u (targetOut+1) 2 a b) (C j)‖ ≤ (2 : ℝ)^2)
    (hdom : SchurDominance.DominatesOn (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ))))
    (hwidth : 0 < width) (hsep : L+PhaseCellBand.width p u ≤ s)
    (Fs : List (ZMod s → GaussianInt))
    (hF : ∀ F ∈ Fs, ∀ j, ‖value p (F j)‖ ≤ 1)
    (W : ℕ)
    (hW : ∀ k ∈ coreGatherIndices s width (localityDepth p targetOut*PhaseCellBand.width p u) L,
      2*packedHaloPrecision p l s t u (targetOut+1) 2
        (coreHaloEndpoints s width k (PhaseCellBand.width p u) (localityDepth p targetOut)).1
        (coreHaloEndpoints s width k (PhaseCellBand.width p u) (localityDepth p targetOut)).2+8 ≤ W)
    (hwidthLe : width ≤ s) (hguard : localityDepth p targetOut*PhaseCellBand.width p u ≤ width)
    (hcell : s/(t-s)+1 ≤ width) (hprepare : p^2+(PhaseCellBand.width p u)^2 ≤ width) :
    let jobs := RawRecoveryJob.coreClassJobs hp hpacket hα hst hu hαu hθ hgap hbudget hband hpad hC hdom hwidth hsep Fs hF W hW
    ((List.ofFn jobs).map (fun r => replicaRecoveryLocalVolume r.problem)).sum ≤
      600*(s+(t-s)*(PhaseCellBand.width p u)^2) := by
  dsimp only
  apply coreClassJobLocalVolume_le hst p width (PhaseCellBand.width p u) (localityDepth p targetOut) L
    hwidth hwidthLe hguard (PhaseCellBand.width_pos p u) hcell hprepare
  intro i
  obtain ⟨hp',_,ht',_,_,ha,hspan,hB,_⟩ := RawRecoveryJob.coreClassJobs_profile hp hpacket hα hst hu hαu hθ hgap hbudget hband hpad hC hdom hwidth hsep Fs hF W hW i
  exact ⟨hp',ht',hB,ha,hspan⟩

end IntegerMultBounds.MathlibTM2.Cost
