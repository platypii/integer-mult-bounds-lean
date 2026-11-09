module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactoredCyclicComplexCore
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFittingCyclicCachedInputs

/-! A single routed complex batch executes through cached input production,
factor construction and certified numerical publication. Layout separation is
recorded once, independently of geometry, precision and tape contents. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
open CyclicReplicaPlacement

structure CyclicComplexCallerLayout (T : ℕ) where
  bank : Fin 909 → Fin T
  injective : Function.Injective bank
  seedL : Fin 392 → Fin T
  seedR : Fin 392 → Fin T
  controls : Fin 3 → Fin T
  count : Fin T
  archive : Fin T
  saved : Fin T
  span : Fin T
  tmp : Fin T
  move : [count,archive,bank (Fin.castLE (by decide : 834 ≤ 909) (leftInputReg 124)),saved,tmp].Nodup
  seedOff : ∀ i j, seedL i ≠ bank j ∧ seedR i ≠ bank j
  seedTmp : ∀ i, seedL i ≠ tmp ∧ seedR i ≠ tmp
  seedArchive : ∀ i, seedL i ≠ archive ∧ seedR i ≠ archive
  controlOff : ∀ i j, controls i ≠ bank j
  controlTmp : ∀ i, controls i ≠ tmp
  controlArchive : ∀ i, controls i ≠ archive
  spanOff : ∀ i, span ≠ bank i
  spanTmp : span ≠ tmp
  spanArchive : span ≠ archive
  tmpOff : ∀ i, bank i ≠ tmp
  archiveOff : ∀ i, archive ≠ bank i

namespace CyclicComplexCallerLayout
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def small (ports : CyclicComplexCallerLayout T) : Fin 834 → Fin T :=
  ports.bank ∘ Fin.castLE (by decide : 834 ≤ 909)

theorem small_injective (ports : CyclicComplexCallerLayout T) : Function.Injective ports.small :=
  ports.injective.comp (Fin.castLE_injective _)

noncomputable def program (ports : CyclicComplexCallerLayout T) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq (fittingCyclicCachedInputs ports.small ports.seedL ports.seedR ports.count ports.archive ports.saved ports.tmp)
    (factoredCyclicComplexCore ports.bank ports.controls ports.span ports.tmp hR hQ)

def inputTimeCost {s : ℕ} (ports : CyclicComplexCallerLayout T) (H K : ReplicaHaloProblem s)
    (W N : ℕ) (S : Stacks T A) : ℕ :=
  ((6*(N*H.span*W)+6)+
    (copyUnaryHeadersCost (fun k => (S.R k).length) (recoverySeedHeaderCopies ports.seedL (ports.small ∘ leftInputReg))+
      completeComplexRecoveryHeadersCost H N+prepareCachedComplexInputCost H W N))+
    (copyUnaryHeadersCost (fun k => (S.R k).length) (recoverySeedHeaderCopies ports.seedR (ports.small ∘ rightInputReg))+
      completeComplexRecoveryHeadersCost K N+prepareCachedComplexInputCost K W N)

def factorTimeCost (ports : CyclicComplexCallerLayout T) (s t p u a n : ℕ) [NeZero s]
    (C F : Stacks T A) : ℕ :=
  copyUnaryHeadersCost (fun k => (C.R k).length)
    (masterHeaderCopies ((ports.small ∘ factorReg) ∘ Fin.castLE (by decide : 224 ≤ 234))
      (cachedFactorSeedSource (ports.small ∘ left.plan.gather) ports.span))+
    prepareCyclicBoundaryPageCost
      (embStk (Fin.castLE (by decide : 154 ≤ 234)) (embStk (ports.small ∘ factorReg) F)).R
      s t (PhaseCellBand.width p u) a n

theorem program_exec (ports : CyclicComplexCallerLayout T)
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
    ∀ (W : ℕ), 2*p+13 ≤ W → executionWidth p l stage 2 ≤ W →
    ∀ (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4))),
    let small := ports.bank ∘ Fin.castLE (by decide : 834 ≤ 909)
    (∀ i, S.L (ports.bank i) = [] ∧ S.R (ports.bank i) = []) →
    (∀ i ∈ recoverySeedHeaderPorts, (S.R (ports.seedL i)).length = recoverySeedHeader H W Fs.length i) →
    (∀ i ∈ recoverySeedHeaderPorts, (S.R (ports.seedR i)).length = recoverySeedHeader K W Fs.length i) →
    S.R ports.archive = cstream A W (Fs.map (packedInterval a n)).flatten++tail →
    (S.R ports.count).length = Fs.length*n*W → (S.R ports.span).length = n →
    (∀ i, (S.R (ports.controls i)).length = ![W,radius,coreLength s coreWidth k] i) →
    S.R ports.saved = [] → S.R ports.tmp = [] →
    ∀ (localityTarget qRef : ℕ) (Y : (ZMod s → GaussianInt) → ZMod s → ℝ),
    p+1 ≤ qRef →
    cyclicPrincipalVertices s a n = (PhaseCellInterface.generatedWindow s coreWidth p u localityTarget k).halo →
    (∀ F ∈ complexComponentFields Fs, SchurDominance.Solves (realMatrix s t p u) Finset.univ (Y F)
      (fun i => (value qRef ((2 : GaussianInt)^(qRef-p-1)*F i)).re)) →
    ∃ (J L : ReplicaHaloProblem s) (v' : HS T Q A U) (C F G : Stacks T A) (steps : ℕ) (word : List (Fin (A+4))),
      v'.user = v.user ∧
      CyclicFactorSeedInput p l s t u solveTarget a n [] (embStk (small ∘ CyclicReplicaPlacement.factorReg) F) ∧
      CyclicSecondInteriorProfile H K J L p solveTarget B.card ∧
      steps ≤ ports.inputTimeCost H K W Fs.length S+
        (ports.factorTimeCost s t p u a n C F+((4*(W+radius+coreLength s coreWidth k)+13)+
          Cost.cyclicComplexCoreTimeCost H K p u l t a n target q W radius
            (coreLength s coreWidth k) Rs.length Fs.length)) ∧
      Exec body (ports.program hR hQ) (Host.mk v S) steps (Host.mk v' G) ∧
      G.R (ports.bank 850) = word ∧ G.R (ports.bank 848) = [] ∧ G.R ports.archive = tail ∧
      PackedNormalizedOutput p W target coreWidth k localityTarget Fs Y word ∧
      (∀ i, i ≠ ports.archive → (∀ j, ports.bank j ≠ i) → G.L i = S.L i ∧ G.R i = S.R i) := by
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
  intro W hW hWin v S tail hblank hvaluesL hvaluesR hsrc hcount hspan hcontrols hsaved htmp
  intro localityTarget qRef Y hqRef hwindow hY
  have hfit : a+n ≤ s := by omega
  have hspanL : H.span = n := by change min n (s-a) = n; omega
  have hspanR : K.span = 0 := by change n-min n (s-a) = 0; omega
  obtain ⟨v₁,C,n₁,hu₁,hn₁,he₁,inputsL,inputsR,harchive,hfactorFresh,hframe⟩ := fittingCyclicCachedInputs_exec
    (body := body) ports.small ports.small_injective (by omega : 4 ≤ A) H K W Fs rfl rfl
    hqp hqp hWin hWin hspanR ports.seedL ports.seedR ports.count ports.archive ports.saved ports.tmp
    ports.move (fun i j => ports.seedOff i _) ports.seedTmp (fun i => ports.tmpOff _)
    (fun i => ports.archiveOff _) ports.seedArchive v S tail hvaluesL hvaluesR
    (fun i => (hblank _).2) (fun i => (hblank _).1)
    (by change S.R ports.archive = cstream A W (Fs.map (packedInterval a H.span)).flatten++tail; rwa [hspanL]) (by simpa only [hspanL] using hcount) hsaved htmp
  have hspan' : (C.R ports.span).length = n := by
    rw [(hframe ports.span ports.spanArchive (fun i => (ports.spanOff _).symm)).2]
    exact hspan
  have hcontrols' (i : Fin 3) : (C.R (ports.controls i)).length = ![W,radius,coreLength s coreWidth k] i := by
    rw [(hframe _ (ports.controlArchive i) (fun j => (ports.controlOff i _).symm)).2]
    exact hcontrols i
  have hfresh' (i : Fin 909) (hi : 834 ≤ i.val) : C.L (ports.bank i) = [] ∧ C.R (ports.bank i) = [] := by
    have hoff : ∀ j, ports.small j ≠ ports.bank i := by
      intro j he
      have hv := congrArg Fin.val (ports.injective he)
      change j.val = i.val at hv
      have := j.isLt
      omega
    have hh := hframe _ (ports.archiveOff i).symm hoff
    exact ⟨hh.1.trans (hblank i).1,hh.2.trans (hblank i).2⟩
  have htmpArchive : ports.tmp ≠ ports.archive := by
    have hr := ports.move
    regs_ne hr
    exact Ne.symm (by assumption)
  have htmp' : C.R ports.tmp = [] :=
    (hframe _ htmpArchive (fun j => ports.tmpOff _)).2.trans htmp
  obtain ⟨J,L,v₂,F,G,n₂,word,hu₂,hseed,hprofile,hn₂,he₂,hword,h848,hcert,houtside⟩ :=
    factoredCyclicComplexCore_exec (body := body) ports.bank ports.injective hR hQ hA axis ha hn
      hleftRoom hrightRoom coreWidth k radius hleft haCore hnCore hright Fs hF W hW
      (generatedRecoveryBuffers H S.inp S.out) (generatedRecoveryBuffers K S.inp S.out)
      v₁ C ports.controls ports.span ports.tmp inputsL inputsR hspan'
      ports.spanOff ports.spanTmp hfactorFresh ports.controlOff ports.controlTmp ports.tmpOff
      hcontrols' hfresh' htmp' localityTarget qRef Y hqRef hwindow hY
  refine ⟨J,L,v₂,C,F,G,n₁+n₂,word,hu₂.trans hu₁,hseed,hprofile,Nat.add_le_add hn₁ hn₂,
    Exec.seq he₁ he₂,hword,h848,?_,hcert,?_⟩
  · exact (houtside ports.archive (fun j => (ports.archiveOff j).symm)).2.trans harchive
  · intro i hi hiBank
    have hh := hframe i hi (fun j => hiBank _)
    exact ⟨(houtside i hiBank).1.trans hh.1,(houtside i hiBank).2.trans hh.2⟩

end CyclicComplexCallerLayout
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
