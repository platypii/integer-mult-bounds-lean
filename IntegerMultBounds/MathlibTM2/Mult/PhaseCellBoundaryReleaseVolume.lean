module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryPermanentBound
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseBoundaryWorkspace

/-! Convert the persistent register bound into a bound for the entire released bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast

theorem boundaryReleaseVolume_le {A V N D : ℕ} (S : Stacks 224 A)
    (hperm : BoundaryPermanentBound (boundaryFactorState S) D)
    (h115 : (S.R 115).length ≤ V) (h116 : (S.R 116).length ≤ N)
    (htransient : ∀ r ∈ boundaryTransientRoles, r ≠ .src → (boundaryFactorState S) r = [])
    (h184 : S.R 184 = []) (h223 : S.R 223 = []) :
    (boundaryOwnedRegs.map fun i => (S.R i).length).sum ≤ boundaryOwnedRegs.length*(V+N+D) := by
  have hbound (i : Fin 224) (hi : i ∈ boundaryOwnedRegs) : (S.R i).length ≤ V+N+D := by
    rw [boundaryOwnedRegs_mem] at hi
    rcases hi with rfl | rfl | hi
    · omega
    · omega
    by_cases hi184 : i = 184
    · subst i; simp [h184]
    by_cases hi223 : i = 223
    · subst i; simp [h223]
    obtain ⟨r,hr⟩ := boundaryFactorReg_cover i hi hi184 hi223
    have hrsrc : r ≠ .src := by
      intro he
      subst r
      have hh := congrArg (fun k : Fin 224 => k.val) hr
      change 140 = i.val at hh
      omega
    rw [← hr]
    change ((boundaryFactorState S) r).length ≤ V+N+D
    by_cases hrt : r ∈ boundaryTransientRoles
    · rw [htransient r hrt hrsrc]
      simp
    · have hh := hperm r hrt
      omega
  have hsum (is : List (Fin 224)) (his : ∀ i ∈ is, i ∈ boundaryOwnedRegs) :
      (is.map fun i => (S.R i).length).sum ≤ is.length*(V+N+D) := by
    induction is with
    | nil => simp
    | cons i is ih =>
      have hi := hbound i (his i (by simp))
      have ht := ih (fun j hj => his j (by simp [hj]))
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
  exact hsum boundaryOwnedRegs (fun _ hi => hi)

def releaseBoundaryWorkspaceCostBound (s w V N D : ℕ) : ℕ :=
  12*s*w+9*s+12+2*(boundaryOwnedRegs.length*(V+N+D))+2*boundaryOwnedRegs.length+1

theorem releaseBoundaryWorkspaceCost_le {A s w V N D : ℕ} (S : Stacks 224 A)
    (hvolume : (boundaryOwnedRegs.map fun i => (S.R i).length).sum ≤ boundaryOwnedRegs.length*(V+N+D)) :
    releaseBoundaryWorkspaceCost s w S ≤ releaseBoundaryWorkspaceCostBound s w V N D := by
  dsimp only [releaseBoundaryWorkspaceCost,releaseBoundaryWorkspaceCostBound]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
