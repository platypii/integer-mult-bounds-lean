module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageRelease
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryPermanentBound
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryUnfoldHeaderVolume
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryPublicationControls

/-! Bound all owned setup bytes before shared-page release, including retained inverse-fold headers and scatter advances. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix

theorem sharedPageAdvances_volume {A : ℕ} (s : ℕ) [NeZero s] (B : Finset (ZMod s))
    (w : ℕ) (hw : 1 ≤ w) :
    (gatherControls A (originAdvances w 0 (boundaryScatterOrigins s B)++[0])).length ≤ 2*s*w+1 := by
  have hv := boundaryOriginAdvances_volume s B w
  have hN : B.card ≤ s*w := by
    have hh := boundaryScatterGaps_volume s B w
    have hn : B.card ≤ B.card*w := by simpa using Nat.mul_le_mul_left B.card hw
    omega
  have hlen : (boundaryScatterOrigins s B).length = B.card := by simp [boundaryScatterOrigins,bOrder_length]
  simp only [length_gatherControls,List.sum_append,List.sum_singleton,Nat.add_zero,
    List.length_append,List.length_singleton,originAdvances_length,hlen]
  nlinarith only [hv,hN,hlen]

def sharedPageOwnedVolumeBound (s w V N D H : ℕ) : ℕ :=
  sharedPageOwnedRegs.length*(N*V+V+N+D+H+2*s*w+1)

theorem sharedPageOwnedVolume_le {A s w V N D H : ℕ} (S : Stacks 240 A)
    (hperm : BoundaryPermanentBound (boundaryFactorState (embStk sharedPageRecoveryReg S)) D)
    (hheaders : boundaryUnfoldHeaderVolume (boundaryFactorState (embStk sharedPageRecoveryReg S)) ≤ H)
    (h109 : (S.R 109).length ≤ N*V) (h115 : (S.R 115).length ≤ V) (h116 : (S.R 116).length ≤ N)
    (h239 : (S.R 239).length ≤ 2*s*w+1)
    (h206 : S.R 206 = []) (h217 : S.R 217 = []) (h184 : S.R 184 = []) (h223 : S.R 223 = []) :
    (sharedPageOwnedRegs.map fun i => (S.R i).length).sum ≤ sharedPageOwnedVolumeBound s w V N D H := by
  let σ := boundaryFactorState (embStk sharedPageRecoveryReg S)
  let F := N*V+V+N+D+H+2*s*w+1
  have hH : (σ .m2wn).length+(σ .kn).length+(σ .tK).length+(σ .sel).length ≤ H := hheaders
  have hbound (i : Fin 240) (hi : i ∈ sharedPageOwnedRegs) : (S.R i).length ≤ F := by
    rw [sharedPageOwnedRegs_mem] at hi
    rcases hi with rfl | rfl | rfl | rfl | ⟨hi154,hi224⟩
    · dsimp only [F]; omega
    · dsimp only [F]; omega
    · dsimp only [F]; omega
    · dsimp only [F]; omega
    by_cases hi184 : i = 184
    · subst i; simp [h184]
    by_cases hi223 : i = 223
    · subst i; simp [h223]
    let j : Fin 224 := ⟨i.val,hi224⟩
    have hj184 : j ≠ 184 := by intro he; apply hi184; exact Fin.ext (congrArg (fun k : Fin 224 => k.val) he)
    have hj223 : j ≠ 223 := by intro he; apply hi223; exact Fin.ext (congrArg (fun k : Fin 224 => k.val) he)
    obtain ⟨r,hr⟩ := boundaryFactorReg_cover j hi154 hj184 hj223
    have he : sharedPageRecoveryReg (boundaryFactorReg r) = i := by rw [hr]; exact Fin.ext rfl
    have hrsrc : r ≠ .src := by
      intro h
      subst r
      have hh := congrArg (fun k : Fin 224 => k.val) hr
      change 140 = i.val at hh
      omega
    rw [← he]
    change (σ r).length ≤ F
    by_cases hrt : r ∈ boundaryTransientRoles
    · simp only [boundaryTransientRoles,List.mem_cons,List.not_mem_nil,or_false] at hrt
      rcases hrt with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact False.elim (hrsrc rfl)
      · dsimp only [F]; omega
      · dsimp only [F]; omega
      · dsimp only [F]; omega
      · dsimp only [F]; omega
      · change (S.R 206).length ≤ F; simp [h206]
      · change (S.R 217).length ≤ F; simp [h217]
    · have hh : (σ r).length ≤ D := hperm r hrt
      dsimp only [F]
      omega
  have hsum (is : List (Fin 240)) (his : ∀ i ∈ is, i ∈ sharedPageOwnedRegs) :
      (is.map fun i => (S.R i).length).sum ≤ is.length*F := by
    induction is with
    | nil => simp
    | cons i is ih =>
      have hi := hbound i (his i (by simp))
      have ht := ih (fun j hj => his j (by simp [hj]))
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
  exact hsum sharedPageOwnedRegs (fun _ hi => hi)

def sharedPageReleaseCostBound (s N W w V D H : ℕ) : ℕ :=
  retirePackedBandTableCost N W w+12*s*w+9*s+12+
    2*sharedPageOwnedVolumeBound s w V N D H+2*sharedPageOwnedRegs.length+1

theorem sharedPageReleaseCost_le {A s N W w V D H : ℕ} (S : Stacks 240 A)
    (hvolume : (sharedPageOwnedRegs.map fun i => (S.R i).length).sum ≤ sharedPageOwnedVolumeBound s w V N D H) :
    sharedPageReleaseCost s N W w S ≤ sharedPageReleaseCostBound s N W w V D H := by
  dsimp only [sharedPageReleaseCost,sharedPageReleaseCostBound]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
