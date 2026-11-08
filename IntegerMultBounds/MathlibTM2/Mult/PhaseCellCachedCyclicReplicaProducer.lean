module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedCyclicReplicaArchives
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaPlacement

/-! The canonical two-pass producer exposes the factor-bank frame needed by the
shared consumer. Its only factor-bank writes are the two generated masks. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open CyclicReplicaPlacement
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 834 Q A U}

theorem cachedCyclicReplicaProducer_exec {s t p u l : ℕ} [NeZero s] {α d : ℝ}
    (axis : RecoveryAxisBounds s t p u l α d) (cellTarget a n : ℕ)
    (ha : a < s) (hn : n ≤ s)
    (hleftRoom : min n (s-a)+PhaseCellBand.width p u ≤ s)
    (hrightRoom : n-min n (s-a)+PhaseCellBand.width p u ≤ s)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A) :
    let band := PhaseCellBand.width p u
    ∀ (Fs : List (ZMod s → GaussianInt))
      (hF : ∀ F ∈ Fs, ∀ i, ‖value (executionPrecision p l cellTarget 2) (F i)‖ ≤ (2 : ℝ)^2),
    let H := axis.cyclicLeftReplicaProblem cellTarget 2 a n ha Fs hF
    let K := axis.cyclicRightReplicaProblem cellTarget 2 a n hn Fs hF
    ∀ (leftBuffers rightBuffers : ReplicaLoopBuffers A) (v : HS 834 Q A U) (S : Stacks 834 A),
    CachedReplicaPassInput H left leftBuffers S → CachedReplicaPassInput K right rightBuffers S →
    S.R (factorReg 170) = [] → S.R (factorReg 173) = [] →
    ∃ (vf : HS 834 Q A U) (mid F : Stacks 834 A) (m : ℕ), ∃ Cs Ds : List (ZMod s → GaussianInt),
      vf.user = v.user ∧
      m ≤ (cachedReplicaPassCost H+cachedReplicaPassCost K)+
        (placedReplicaBoundaryMaskCost H+placedReplicaBoundaryMaskCost K) ∧
      Exec body (cachedReplicaPassMasks left right (factorReg 170) (factorReg 173) hR hQ)
        (mk v S) m (mk vf F) ∧
      CachedReplicaPassPost H left leftBuffers S F Cs ∧
      CachedReplicaPassPost K right rightBuffers mid F Ds ∧
      F.R (factorReg 170) = couplingSourceIntervalMaskSymbols true A s t band
        a (a+min n (s-a)) a (min n (s-a)) ∧
      F.R (factorReg 173) = couplingSourceIntervalMaskSymbols true A s t band
        0 (n-min n (s-a)) 0 (n-min n (s-a)) ∧
      F.inp = S.inp ∧ F.out = S.out ∧ (embStk factorReg F).L = (embStk factorReg S).L ∧
      ∀ k : Fin 234, k ≠ 170 → k ≠ 173 → F.R (factorReg k) = S.R (factorReg k) := by
  dsimp only
  intro Fs hF leftBuffers rightBuffers v S leftInputs rightInputs h170 h173
  let H := axis.cyclicLeftReplicaProblem cellTarget 2 a n ha Fs hF
  let K := axis.cyclicRightReplicaProblem cellTarget 2 a n hn Fs hF
  obtain ⟨vf,mid,G,m,Cs,Ds,hu,hm,he,hl,hr,hmaskL,hmaskR,hL,hframe⟩ :=
    cachedReplicaPassMasks_exec (body := body) H K left right disjoint
      (factorReg 170) (factorReg 173) (factorReg_injective.ne (by decide))
      (factor_disjoint 170) (factor_disjoint 173) hR hQ hA
      hleftRoom ha axis.hpad axis.hp axis.hpacket hrightRoom (NeZero.pos s)
      axis.hpad axis.hp axis.hpacket leftBuffers rightBuffers v S leftInputs rightInputs h170 h173
  refine ⟨vf,mid,_,m,Cs,Ds,hu,hm,he,hl,hr,hmaskL,?_,hl.input,hl.outputStream,?_,?_⟩
  · have hv : couplingSourceIntervalMaskSymbols true A s K.t K.band K.origin
        (K.origin+K.span) K.origin K.span = couplingSourceIntervalMaskSymbols true A s t
          (PhaseCellBand.width p u) 0 (n-min n (s-a)) 0 (n-min n (s-a)) := by
      change couplingSourceIntervalMaskSymbols true A s t (PhaseCellBand.width p u)
        0 (0+(n-min n (s-a))) 0 (n-min n (s-a)) = _
      rw [Nat.zero_add]
    exact hmaskR.trans hv
  · funext k; exact hL _ (factor_disjoint k).1 (factor_disjoint k).2
  · intro k hk170 hk173
    exact (hframe _ (factor_disjoint k).1 (factor_disjoint k).2
      (fun he => hk170 (factorReg_injective he))
      (fun he => hk173 (factorReg_injective he))).2

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
