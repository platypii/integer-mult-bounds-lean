module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExecutedCyclicComplexCore
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicComplexCoreInput
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedActualFittingCyclicComplexCore

/-! The executed cyclic core supplies the existing packed-output certificate
and its named time bill under arbitrary caller placement. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

noncomputable def placedCyclicComplexCore (bank : Fin 909 → Fin T)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  embProg bank Empty.elim (executedCyclicComplexCore (P := Empty) hR hQ)

theorem placedCyclicComplexCore_exec (bank : Fin 909 → Fin T) (hbank : Function.Injective bank)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a n : ℕ} [NeZero s] {α d : ℝ}
    (axis : RecoveryAxisBounds s t p u l α d) (ha : a < s) (hn : n ≤ s)
    (hleftRoom : min n (s-a)+PhaseCellBand.width p u ≤ s)
    (hrightRoom : n-min n (s-a)+PhaseCellBand.width p u ≤ s)
    (coreWidth k radius : ℕ) (hleft : radius ≤ coreStart coreWidth k)
    (haCore : a = coreStart coreWidth k-radius) (hnCore : n = coreLength s coreWidth k+2*radius)
    (hright : coreStart coreWidth k+coreLength s coreWidth k+radius ≤ s) :
    let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
    let solveTarget := boundaryRecoveryTarget p (target+1)
    let stage := initialSchurTarget p u (boundaryTableBits p solveTarget 2 B.card) 2
    let q := executionPrecision p l stage 2
    let hqp : p+1 ≤ q := by dsimp only [q,executionPrecision,executionExponent,inputExponent]; omega
    ∀ (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1),
    let Rs := (complexComponentFields Fs).map (fun F i => (2 : GaussianInt)^(q-p-1)*F i)
    let hRs := shiftedComplexComponents_bound p q hqp Fs hF
    let H := axis.cyclicLeftReplicaProblem stage 2 a n ha Rs hRs
    let K := axis.cyclicRightReplicaProblem stage 2 a n hn Rs hRs
    ∀ (W : ℕ), 2*p+13 ≤ W →
    ∀ (buffersL buffersR : ReplicaLoopBuffers A) (v : HS T Q A U) (S : Stacks T A) (I : Stacks 834 A),
    CachedReplicaPassInput H CyclicReplicaPlacement.left buffersL I →
    CachedReplicaPassInput K CyclicReplicaPlacement.right buffersR I →
    CyclicResidualBatchInput p l s t u solveTarget a n [] [] (embStk CyclicReplicaPlacement.factorReg I) →
    I.R (CyclicReplicaPlacement.factorReg 226) = [] → I.R (CyclicReplicaPlacement.factorReg 229) = [] →
    embStk bank S = cyclicComplexCoreInput I (List.replicate W tick)
      (List.replicate radius tick) (List.replicate (coreLength s coreWidth k) tick) →
    ∀ (localityTarget qRef : ℕ) (Y : (ZMod s → GaussianInt) → ZMod s → ℝ),
    p+1 ≤ qRef →
    cyclicPrincipalVertices s a n = (PhaseCellInterface.generatedWindow s coreWidth p u localityTarget k).halo →
    (∀ F ∈ complexComponentFields Fs, SchurDominance.Solves (realMatrix s t p u) Finset.univ (Y F)
      (fun i => (value qRef ((2 : GaussianInt)^(qRef-p-1)*F i)).re)) →
    ∃ (J L : ReplicaHaloProblem s) (v' : HS T Q A U) (G : Stacks T A) (steps : ℕ) (word : List (Fin (A+4))),
      v'.user = v.user ∧ CyclicSecondInteriorProfile H K J L p solveTarget B.card ∧
      steps ≤ Cost.cyclicComplexCoreTimeCost H K p u l t a n target q W radius
        (coreLength s coreWidth k) Rs.length Fs.length ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+
        cyclicComplexCoreWorkspace (P := Empty) (A := A) (U := U) H K J L hR hQ
          p u l t a n solveTarget q (executionWidth p l stage 2) W B.card
          Rs.length Fs.length radius (coreLength s coreWidth k)) 0
        (placedCyclicComplexCore bank hR hQ) (mk v S) steps (mk v' G) ∧
      Exec body (placedCyclicComplexCore bank hR hQ) (mk v S) steps (mk v' G) ∧
      G.R (bank 850) = word ∧ G.R (bank 848) = [] ∧
      PackedNormalizedOutput p W target coreWidth k localityTarget Fs Y word ∧
      (G.inp = S.inp ∧ G.out = S.out) ∧
      (∀ i, (∀ j, bank j ≠ i) → G.L i = S.L i ∧ G.R i = S.R i) := by
  dsimp only
  intro Fs hF
  let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
  let solveTarget := boundaryRecoveryTarget p (target+1)
  let stage := initialSchurTarget p u (boundaryTableBits p solveTarget 2 B.card) 2
  let q := executionPrecision p l stage 2
  let hqp : p+1 ≤ q := by dsimp only [q,executionPrecision,executionExponent,inputExponent]; omega
  let Rs := (complexComponentFields Fs).map (fun F i => (2 : GaussianInt)^(q-p-1)*F i)
  let hRs := shiftedComplexComponents_bound p q hqp Fs hF
  let H := axis.cyclicLeftReplicaProblem stage 2 a n ha Rs hRs
  let K := axis.cyclicRightReplicaProblem stage 2 a n hn Rs hRs
  intro W hW buffersL buffersR v S I inputsL inputsR factory h226 h229 hview
    localityTarget qRef Y hqRef hwindow hY
  obtain ⟨J,L,X,R,fields,y,vf,m,savedL,savedR,hu,hprofile,hm,h247,h547,h125,h425,hlen,hstreams,hsol,hwithin,hex,hacc,hpacked⟩ :=
    executedCyclicComplexCore_spec (body := fun f : Empty => nomatch f) hR hQ hA axis ha hn
      hleftRoom hrightRoom coreWidth k radius hleft haCore hnCore hright Fs hF W hW
      (List.replicate W tick) (by simp) (List.replicate radius tick)
      (List.replicate (coreLength s coreWidth k) tick) (by simp) (by simp)
      buffersL buffersR (embDn bank v) I [] [] inputsL inputsR factory h226 h229
  rw [←cyclicComplexCoreInput_eq] at hex hwithin
  obtain ⟨v',G,hex',hv,hu',hbankView,hframe⟩ := exec_emb (ι := Empty.elim) (body' := body)
    hbank (fun f => nomatch f) hex v rfl S hview
  have hplacedWithin := exec_emb_within_stock_of_exec hbank (ι := Empty.elim)
    (body' := body) (fun f => nomatch f) hwithin v rfl S hview hex'
  have hwidth : executionWidth p l stage 2 = 2*q+8 := by
    dsimp only [q,executionWidth,executionPrecision]
    omega
  have hcost := Cost.cyclicComplexCoreTimeCost_eq_components H K p u l t a n target q W radius
    (coreLength s coreWidth k) Rs.length Fs.length hwidth hwidth hnCore
  have hwidth' := hwidth
  dsimp only [stage,B,solveTarget,q] at hwidth'
  simp only [hwidth'] at hm
  have hm' : m ≤ Cost.cyclicComplexCoreTimeCost H K p u l t a n target q W radius
      (coreLength s coreWidth k) Rs.length Fs.length := by
    rw [hcost]
    exact hm
  have hp := hpacked localityTarget qRef Y hqRef hwindow hY
  refine ⟨J,L,v',G,m,_,hu'.trans hu,hprofile,hm',hplacedWithin,hex',?_,?_,hp,?_,hframe⟩
  · have hh := congrArg (fun F : Stacks 909 A => F.R 850) hbankView
    simpa only [embStk_R,Function.update_self] using hh
  · have hh := congrArg (fun F : Stacks 909 A => F.R 848) hbankView
    simpa only [embStk_R,Function.update_of_ne (by decide : (848 : Fin 909) ≠ 850),
      Function.update_self] using hh

  · have hin := congrArg (fun F : Stacks 909 A => F.inp) hbankView
    have hout := congrArg (fun F : Stacks 909 A => F.out) hbankView
    have hin₀ := congrArg (fun F : Stacks 909 A => F.inp) hview
    have hout₀ := congrArg (fun F : Stacks 909 A => F.out) hview
    exact ⟨hin.trans (hstreams.1.trans hin₀.symm),hout.trans (hstreams.2.trans hout₀.symm)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
