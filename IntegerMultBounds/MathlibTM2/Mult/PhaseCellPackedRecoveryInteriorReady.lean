module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRecoveryInteriorPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRecoveryCoupling
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloReady

/-! Derive the second interior initializer's input from retained solver state.
The relocated runtime roles are blank, while the original pages stay owned. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node ScalarPlacement

structure PackedRecoveryInteriorReady {A : ℕ} (precision stage q l s t u band a b V w : ℕ)
    (input E outputTail : List (Fin (A+4))) (S : Stacks 248 A) : Prop where
  native : embStk packedCellCoreReg (embStk packedRecoveryInteriorReg S) =
    releasedCellBank [] input (S.R 93) S.inp S.out
  masters : ∀ r ∈ groupHeaderCopies,
    ((embStk packedRecoveryInteriorReg S).R (packedHeaderReg r.1)).length =
      groupHeaderValue precision stage q l s t u band 0 r.1
  lower : (S.R 141).length = a
  upper : (S.R 142).length = b
  metadata : CouplingIntervalMetadata V s t band a b a (b-a) (embStk packedRecoveryInteriorReg S)
  binaryLengthBound : ((embStk packedRecoveryInteriorReg S).R 157).length ≤ V
  output : S.R 132 = E++outputTail
  length : E.length = (b-a)*w
  fresh : ∀ k ∈ ([(125 : Fin 168),127,130,133,138,129,131,134,135,136,140,153,166]),
    (embStk packedRecoveryInteriorReg S).R k = []

theorem packedRecoveryInteriorReady_of_retained {A precision stage q l s t u band a b V w : ℕ}
    (input E outputTail : List (Fin (A+4))) (S : Stacks 248 A)
    (hwork : PackedBoundarySolveWorkspace q (embStk packedBoundaryRecoveryBase S))
    (hheaders : CouplingMasterHeaders precision q w s t u band a b (embStk packedRecoveryRuntimeReg S))
    (hstage : (S.R 118).length = stage) (hlevel : (S.R 120).length = l)
    (hnative : ∀ i : Fin 117, i ≠ 93 → i ≠ 110 → S.R ⟨i.val,by omega⟩ = [])
    (hsource : S.R 110 = input)
    (hmeta : CouplingIntervalMetadata V s t band a b a (b-a) (embStk packedRecoveryRuntimeReg S))
    (houtput : S.R 132 = E++outputTail) (hE : E.length = (b-a)*w)
    (hclean : ∀ k ∈ ([127,129,131,133,134,135,136,153,158,166] : List (Fin 248)), S.R k = [])
    (hfresh : ∀ k : Fin 248, 242 ≤ k.val → S.R k = []) :
    PackedRecoveryInteriorReady precision stage q l s t u band a b V w input E outputTail S := by
  have hfixed (k : Fin 168) (hn : k ∉ ([125,128,130,138,140,157] : List (Fin 168))) :
      (embStk packedRecoveryInteriorReg S).R k = S.R ⟨k.val,by omega⟩ :=
    congrArg S.R (packedRecoveryInteriorReg_fixed k hn)
  constructor
  · refine Stacks.ext rfl rfl ?_ ?_
    · funext i
      change S.L (packedRecoveryInteriorReg (packedCellCoreReg i)) = []
      rw [packedRecoveryInteriorReg_low _ i.isLt]
      have hi := i.isLt
      simpa [embStk,packedCellCoreReg,packedBoundaryRecoveryBase,preparedBoundaryCoreReg,
        packedBoundaryFactorReg,Fin.ext_iff,show i.val ≠ 140 by omega,
        show i.val ≠ 143 by omega,show i.val ≠ 206 by omega,show i.val < 154 by omega]
        using hwork.left ⟨i.val,by omega⟩
    · funext i
      by_cases h93 : i = 93
      · subst i; rfl
      by_cases h110 : i = 110
      · subst i; exact hsource
      have hh := hnative i h93 h110
      have hv93 : i.val ≠ 93 := fun he => h93 (Fin.ext he)
      have hv110 : i.val ≠ 110 := fun he => h110 (Fin.ext he)
      change S.R (packedRecoveryInteriorReg (packedCellCoreReg i)) = _
      rw [packedRecoveryInteriorReg_low _ i.isLt]
      simpa [packedCellCoreReg,releasedCellBank,hv93,hv110] using hh
  · intro r hr
    simp only [groupHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change ((embStk packedRecoveryInteriorReg S).R 117).length = precision
      rw [hfixed 117 (by decide)]
      exact hheaders.precision
    · change ((embStk packedRecoveryInteriorReg S).R 118).length = stage
      rw [hfixed 118 (by decide)]
      exact hstage
    · change ((embStk packedRecoveryInteriorReg S).R 119).length = q
      rw [hfixed 119 (by decide)]
      exact hheaders.fraction
    · change ((embStk packedRecoveryInteriorReg S).R 120).length = l
      rw [hfixed 120 (by decide)]
      exact hlevel
    · change ((embStk packedRecoveryInteriorReg S).R 121).length = s
      rw [hfixed 121 (by decide)]
      exact hheaders.axis
    · change ((embStk packedRecoveryInteriorReg S).R 122).length = t
      rw [hfixed 122 (by decide)]
      exact hheaders.period
    · change ((embStk packedRecoveryInteriorReg S).R 123).length = u
      rw [hfixed 123 (by decide)]
      exact hheaders.parameter
    · change ((embStk packedRecoveryInteriorReg S).R 124).length = band
      rw [hfixed 124 (by decide)]
      exact hheaders.bandwidth
    · change (S.R (packedRecoveryInteriorReg 128)).length = 0
      rw [packedRecoveryInteriorReg_128,hfresh 243 (by decide)]; rfl
    · change (S.R (packedRecoveryInteriorReg 128)).length = 0
      rw [packedRecoveryInteriorReg_128,hfresh 243 (by decide)]; rfl
  · exact hheaders.lower
  · exact hheaders.upper
  · constructor
    · rw [hfixed 163 (by decide)]
      exact hmeta.width
    · intro k hk
      have hn : k ∉ ([125,128,130,138,140,157] : List (Fin 168)) := by
        simp only [couplingIntervalPorts,List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [hfixed k hn]
      exact hmeta.encoded k hk
  · change (S.R (packedRecoveryInteriorReg 157)).length ≤ V
    rw [packedRecoveryInteriorReg_157,hfresh 247 (by decide)]
    simp
  · exact houtput
  · exact hE
  · intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change S.R (packedRecoveryInteriorReg 125) = []
      rw [packedRecoveryInteriorReg_125]
      exact hfresh 242 (by decide)
    · rw [hfixed 127 (by decide)]
      exact hclean 127 (by decide)
    · change S.R (packedRecoveryInteriorReg 130) = []
      rw [packedRecoveryInteriorReg_130]
      exact hfresh 244 (by decide)
    · rw [hfixed 133 (by decide)]
      exact hclean 133 (by decide)
    · change S.R (packedRecoveryInteriorReg 138) = []
      rw [packedRecoveryInteriorReg_138]
      exact hfresh 245 (by decide)
    · rw [hfixed 129 (by decide)]
      exact hclean 129 (by decide)
    · rw [hfixed 131 (by decide)]
      exact hclean 131 (by decide)
    · rw [hfixed 134 (by decide)]
      exact hclean 134 (by decide)
    · rw [hfixed 135 (by decide)]
      exact hclean 135 (by decide)
    · rw [hfixed 136 (by decide)]
      exact hclean 136 (by decide)
    · change S.R (packedRecoveryInteriorReg 140) = []
      rw [packedRecoveryInteriorReg_140]
      exact hfresh 246 (by decide)
    · rw [hfixed 153 (by decide)]
      exact hclean 153 (by decide)
    · rw [hfixed 166 (by decide)]
      exact hclean 166 (by decide)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
