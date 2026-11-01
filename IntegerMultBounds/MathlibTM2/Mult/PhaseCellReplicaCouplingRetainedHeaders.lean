module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializeReplicaCouplingPage
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRecoveryRetainedPorts

/-! Shared coupling regenerates binary geometry while retaining the numerical
master language. The actual setup frame transports every master once. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host ScalarPlacement

theorem PackedHaloRetainedHeaders.of_coupling_setup
    {A P stage q l s t u band a b V' w : ℕ} {S F : Stacks 168 A}
    (hmasters : CouplingMasterHeaders P q w s t u band a b S)
    (hstage : (S.R 118).length = stage) (hlevel : (S.R 120).length = l)
    (hgeometry : CouplingIntervalMetadata V' s t band a b a (b-a) F)
    (hframe : ∀ k : Fin 168, 117 ≤ k.val → k ∉ replicaCouplingSetupPorts → F.R k = S.R k) :
    PackedHaloRetainedHeaders P stage q l s t u band a b V' w F := by
  constructor
  · apply hmasters.of_frame
    intro k hk
    apply hframe
    · simp only [couplingMasterPorts,List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff] at hk
      norm_num at hk
      omega
    · simp only [couplingMasterPorts,replicaCouplingSetupPorts,List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff] at hk ⊢
      norm_num at hk ⊢
      omega
  · exact hgeometry
  · rw [hframe 118 (by decide) (by decide)]; exact hstage
  · rw [hframe 120 (by decide) (by decide)]; exact hlevel

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
