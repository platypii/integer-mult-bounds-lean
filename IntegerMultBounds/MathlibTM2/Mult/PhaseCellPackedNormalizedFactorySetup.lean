module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedNormalizedFactoryPacket
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloInput

/-! Construct complete factory setup from mathematical bounds and ordinary
words. Storage readiness is proved from the sparse bank, not assumed. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

/-- Mathematical hypotheses of the packed factory, independent of tape storage. -/
structure PackedHaloParameterBounds {p l s t u target rhsExp a b V : ℕ} [NeZero s]
    (α d : ℝ) (C : ZMod s → GaussianInt) : Prop where
  hp : 2 ≤ p
  hwidth : 8*p ≤ 2^u
  hα : 0 < α
  hst : s < t
  hu : 1 ≤ u
  hαu : α^2 = (u : ℝ)
  hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1
  hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)
  hbudget : α^2*d ≤ p
  hband : PhaseCellBand.width p u ≤ s
  has : a ≤ s
  hbs : b ≤ s
  hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1
  hfitV : a+((b-a)+2*PhaseCellBand.width p u)+s < 2^V
  hab : a ≤ b
  haLt : a < s
  hsep : b-a+PhaseCellBand.width p u ≤ s
  hwide : 8*(t+1)^2+4*PhaseCellBand.width p u+8 < 2^V
  hVeq : V = weightWorkspaceWidth (2^15*p) (executionPrecision p l (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp) (2*(executionPrecision p l (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp)+8) t u
  hwV : (executionWidth p l (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp) < 2^V
  hcoords : b < 2^V
  hunits : b*(executionWidth p l (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp) < 2^V
  hC : ∀ k, ‖value (executionPrecision p l (boundaryHaloTarget p u (boundaryRecoveryTarget p target) rhsExp (haloBoundary s t (PhaseCellBand.width p u) a b).card) rhsExp) (C k)‖ ≤ (2 : ℝ)^rhsExp
  hdom : SchurDominance.DominatesOn (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ)))

theorem packedNormalizedFactoryBank_setup {A p l s t u targetOut a b V : ℕ} [NeZero s]
    {α d : ℝ} {C : ZMod s → GaussianInt} (H : Stacks 242 A)
    (h : PackedHaloParameterBounds (p := p) (l := l) (t := t) (u := u)
      (target := targetOut+1) (rhsExp := 2) (a := a) (b := b) (V := V) α d C) :
    PackedHaloSetup (p := p) (l := l) (t := t) (u := u)
      (target := targetOut+1) (rhsExp := 2) (a := a) (b := b) (V := V) α d C
      (packedNormalizedFactoryBank H p u l targetOut s t a b V) := by
  let band := PhaseCellBand.width p u
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (targetOut+1)) 2
    (haloBoundary s t band a b).card
  let target := initialSchurTarget p u bits 2
  let N := executionStagePrecision p l target 2+1
  let q := executionPrecision p l target 2
  let S := packedFactoryInputBank H (2^15*p) N q l s t u band a b V
  change PackedHaloSetup (p := p) (l := l) (t := t) (u := u)
    (target := targetOut+1) (rhsExp := 2) (a := a) (b := b) (V := V) α d C S
  have hblank (k : Fin 242) (hk : k ∉ packedFactoryLivePorts) : S.R k = [] :=
    packedFactoryInputBank_blank_of_not_mem H (2^15*p) N q l s t u band a b V k hk
  have hleft (k : Fin 242) : S.L k = [] :=
    packedFactoryInputBank_left H (2^15*p) N q l s t u band a b V k
  have hnative := packedFactoryInputBank_native H (2^15*p) N q l s t u band a b V
  have hn (i : Fin 224) (hi : ∀ j, inverseMasterCorePort j ≠ i) :
      (embStk preparedBoundaryCoreReg (embStk packedBoundaryFactorReg
        (embStk packedBoundaryTableRouting S))).R i = [] := by
    have hv := congrArg (fun S : Stacks 224 A => S.R i) hnative
    exact hv.trans (by
      rw [masterHeaderBank_off (masterHeaderValues (2^15*p) N q l s t u band a b) [] i hi]
      simp)
  have hmasters (j : Fin 10) : (inverseMasterCorePort j).val < 154 := by
    fin_cases j <;> decide
  have hgeometry := packedFactoryInputBank_geometry H (2^15*p) N q l s t u band a b V
  have ha := congrArg List.length (packedFactoryInputBank_headers H (2^15*p) N q l s t u band a b V 8)
  have hb := congrArg List.length (packedFactoryInputBank_headers H (2^15*p) N q l s t u band a b V 9)
  refine {
    hp := h.hp
    hwidth := h.hwidth
    hα := h.hα
    hst := h.hst
    hu := h.hu
    hαu := h.hαu
    hθ := h.hθ
    hgap := h.hgap
    hbudget := h.hbudget
    hband := h.hband
    has := h.has
    hbs := h.hbs
    hpad := h.hpad
    hfitV := h.hfitV
    hab := h.hab
    haLt := h.haLt
    hsep := h.hsep
    hwide := h.hwide
    hVeq := h.hVeq
    hwV := h.hwV
    hcoords := h.hcoords
    hunits := h.hunits
    hC := h.hC
    hdom := h.hdom
    h109 := hn 109 (by intro j; fin_cases j <;> decide)
    h115 := hn 115 (by intro j; fin_cases j <;> decide)
    h116 := hn 116 (by intro j; fin_cases j <;> decide)
    h0 := hn 0 (by intro j; fin_cases j <;> decide)
    h139 := hn 139 (by intro j; fin_cases j <;> decide)
    h127 := hn 127 (by intro j; fin_cases j <;> decide)
    h138 := hn 138 (by intro j; fin_cases j <;> decide)
    h143 := hn 143 (by intro j; fin_cases j <;> decide)
    h147 := hn 147 (by intro j; fin_cases j <;> decide)
    h151 := hn 151 (by intro j; fin_cases j <;> decide)
    h153 := hn 153 (by intro j; fin_cases j <;> decide)
    h152 := hn 152 (by intro j; fin_cases j <;> decide)
    hleft := fun i => hleft _
    hreadyBase := packedNormalizedFactoryBank_native_ready H p u l targetOut s t a b V
    haMaster := by
      dsimp [inverseMasterCorePort, masterHeaderValues, packedFactoryNativeReg] at ha
      simpa [S, embStk, packedBoundaryTableRouting, packedBoundaryFactorReg, preparedBoundaryCoreReg] using ha
    hbMaster := by
      dsimp [inverseMasterCorePort, masterHeaderValues, packedFactoryNativeReg] at hb
      simpa [S, embStk, packedBoundaryTableRouting, packedBoundaryFactorReg, preparedBoundaryCoreReg] using hb
    hnew := by
      intro i hi
      apply hn i
      intro j he
      have hv := congrArg Fin.val he
      have := hmasters j
      omega
    h132left := hleft 132
    hV := by simpa only [List.length_replicate] using congrArg List.length hgeometry.2.2
    h155 := hgeometry.1
    h165 := hgeometry.2.1
    hgeometry := ?_
    h239 := hblank 239 (by decide)
    h157 := by rw [hblank 157 (by decide)]; simp
    h158 := hblank 158 (by decide)
    h167 := hblank 167 (by decide)
    hfresh := ?_ }
  · have hc : ([(145 : Fin 242),146,147,148,149,151,154,156,164]).all
        (fun k => decide (k ∉ packedFactoryLivePorts)) = true := by decide +kernel
    intro k hk
    exact hblank k (of_decide_eq_true (List.all_eq_true.mp hc k hk))
  · have hc : ([(125 : Fin 168),127,130,133,138,129,131,134,135,136,140,153,166]).all
        (fun k => decide (packedHaloRuntimeReg k ∉ packedFactoryLivePorts)) = true := by decide +kernel
    intro k hk
    exact hblank (packedHaloRuntimeReg k) (of_decide_eq_true (List.all_eq_true.mp hc k hk))

/-- The numerical caller's additional scratch requirement follows from the
same sparse bank, independently of the mathematical parameter bounds. -/
theorem packedNormalizedFactoryBank_scratch {A p l s t u targetOut a b V : ℕ} [NeZero s]
    (H : Stacks 242 A) :
    ∀ i ∈ ([(125 : Fin 242),127,128,129,130,131,133,134,135,136,138,139,140,143,153,158,166,167]),
      (packedNormalizedFactoryBank H p u l targetOut s t a b V).R i = [] := by
  have hc : ([(125 : Fin 242),127,128,129,130,131,133,134,135,136,138,139,140,143,153,158,166,167]).all
      (fun k => decide (k ∉ packedFactoryLivePorts)) = true := by decide +kernel
  intro i hi
  dsimp only [packedNormalizedFactoryBank]
  apply packedFactoryInputBank_blank_of_not_mem
  exact of_decide_eq_true (List.all_eq_true.mp hc i hi)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
