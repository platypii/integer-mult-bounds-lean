module

public import IntegerMultBounds.MathlibTM2.Routing.DyadicFieldLayout
public import IntegerMultBounds.MathlibTM2.Routing.FieldMoveHeaders

/-! One fixed binary-pass program, including all runtime dimension changes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.DyadicFieldStep
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  DyadicFieldLayout FieldMoveHeaders FiberScan SmallFieldMove
variable {T Q A : ℕ} {P U β : Type} {body : P → Pr P T Q A U}

def fieldStep
    (prefixCount prefixClock count clock volume fiberVolume src archive zeroBank oneBank tmp : Fin T) :
    Pr P T Q A U :=
  .seq (halveHeader volume archive zeroBank)
    (.seq (retainedSplitFibers prefixCount prefixClock count clock volume fiberVolume
      src archive zeroBank oneBank tmp)
      (.seq (halveHeader fiberVolume archive zeroBank) (doubleHeader prefixCount archive tmp)))

theorem fieldStep_exec
    (prefixCount prefixClock count clock volume fiberVolume src archive zeroBank oneBank tmp : Fin T)
    (hreg : [prefixCount,prefixClock,count,clock,volume,fiberVolume,src,archive,zeroBank,oneBank,tmp].Nodup)
    (encode : β → List (Fin (A+4))) (W B k : ℕ) (hlen : ∀ x, (encode x).length = W)
    (fibers : List (List (Field β (k+1)))) (hrows : ∀ rows ∈ fibers, rows.length = B)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hprefix : (S.R prefixCount).length = fibers.length)
    (hcount : (S.R count).length = B) (hvolume : (S.R volume).length = 2*(2^k*W))
    (hfiber : (S.R fiberVolume).length = 2*(B*(2^k*W)))
    (hsrc : S.R src = stream encode fibers++tail)
    (hprefixClock : S.R prefixClock = []) (hclock : S.R clock = [])
    (harchive : S.R archive = []) (hzero : S.R zeroBank = [])
    (hone : S.R oneBank = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ fibers.length*(24*(B*(2^k*W))+15*B+27)+12*(2^k*W)+12*(B*(2^k*W))+30 ∧
      Exec body (fieldStep prefixCount prefixClock count clock volume fiberVolume
        src archive zeroBank oneBank tmp) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R
          volume (List.replicate (2^k*W) tick)) src (stream encode (refineFibers fibers)++tail))
          fiberVolume (List.replicate (B*(2^k*W)) tick)) prefixCount (S.R prefixCount++S.R prefixCount))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := halveHeader_exec (body := body) volume archive zeroBank
    (by regs_nodup) (2^k*W) v S hvolume harchive hzero
  let S₁ : Stacks T A := {S with R := Function.update S.R volume (List.replicate (2^k*W) tick)}
  have hoff₁ (i : Fin T) (hi : i ≠ volume) : S₁.R i = S.R i := by simp [S₁,hi]
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := splitFieldLevel_exec (body := body)
    prefixCount prefixClock count clock volume fiberVolume src archive zeroBank oneBank tmp hreg
    encode W B k hlen fibers hrows tail v₁ S₁
    (by rw [hoff₁ prefixCount ‹prefixCount ≠ volume›]; exact hprefix)
    (by rw [hoff₁ count ‹count ≠ volume›]; exact hcount)
    (by simp [S₁])
    (by rw [hoff₁ fiberVolume ‹volume ≠ fiberVolume›.symm]; exact hfiber)
    (by rw [hoff₁ src ‹volume ≠ src›.symm]; exact hsrc)
    (by rw [hoff₁ prefixClock ‹prefixClock ≠ volume›]; exact hprefixClock)
    (by rw [hoff₁ clock ‹clock ≠ volume›]; exact hclock)
    (by rw [hoff₁ archive ‹volume ≠ archive›.symm]; exact harchive)
    (by rw [hoff₁ zeroBank ‹volume ≠ zeroBank›.symm]; exact hzero)
    (by rw [hoff₁ oneBank ‹volume ≠ oneBank›.symm]; exact hone)
    (by rw [hoff₁ tmp ‹volume ≠ tmp›.symm]; exact htmp)
  let S₂ : Stacks T A := {S₁ with R := Function.update S₁.R src (stream encode (refineFibers fibers)++tail)}
  have hoff₂ (i : Fin T) (hiv : i ≠ volume) (his : i ≠ src) : S₂.R i = S.R i := by
    simp [S₂,S₁,hiv,his]
  obtain ⟨v₃,hu₃,he₃⟩ := halveHeader_exec (body := body) fiberVolume archive zeroBank
    (by regs_nodup) (B*(2^k*W)) v₂ S₂
    (by rw [hoff₂ fiberVolume ‹volume ≠ fiberVolume›.symm ‹fiberVolume ≠ src›]; exact hfiber)
    (by rw [hoff₂ archive ‹volume ≠ archive›.symm ‹src ≠ archive›.symm]; exact harchive)
    (by rw [hoff₂ zeroBank ‹volume ≠ zeroBank›.symm ‹src ≠ zeroBank›.symm]; exact hzero)
  let S₃ : Stacks T A := {S₂ with R := Function.update S₂.R fiberVolume (List.replicate (B*(2^k*W)) tick)}
  have hoff₃ (i : Fin T) (hiv : i ≠ volume) (his : i ≠ src) (hif : i ≠ fiberVolume) : S₃.R i = S.R i := by
    simp only [S₃,Function.update_of_ne hif]; exact hoff₂ i hiv his
  obtain ⟨v₄,hu₄,he₄⟩ := doubleHeader_exec (body := body) prefixCount archive tmp (by regs_nodup) v₃ S₃
    (by rw [hoff₃ archive ‹volume ≠ archive›.symm ‹src ≠ archive›.symm ‹fiberVolume ≠ archive›.symm]; exact harchive)
    (by rw [hoff₃ tmp ‹volume ≠ tmp›.symm ‹src ≠ tmp›.symm ‹fiberVolume ≠ tmp›.symm]; exact htmp)
  have hp : S₃.R prefixCount = S.R prefixCount :=
    hoff₃ prefixCount ‹prefixCount ≠ volume› ‹prefixCount ≠ src› ‹prefixCount ≠ fiberVolume›
  refine ⟨v₄,_,hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,
    (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄))).cast rfl ?_⟩
  · rw [hp,hprefix]; nlinarith only [hn₂]
  · simp [S₃,S₂,S₁,‹prefixCount ≠ volume›,‹prefixCount ≠ src›,‹prefixCount ≠ fiberVolume›]

/-- All per-fiber control work is absorbed by complete positive spectator and
block volumes. The same tensor-volume bound applies at every binary level. -/
theorem fieldStep_cost_le_volume {n P B R : ℕ} (hP : 0 < P) (hB : 0 < B) (hR : 0 < R)
    (hn : n ≤ P*(24*(B*R)+15*B+27)+12*R+12*(B*R)+30) :
    n ≤ 60*(2*(P*(B*R))) := by
  have hBRpos : 0 < B*R := Nat.mul_pos hB hR
  have hVpos : 0 < P*(B*R) := Nat.mul_pos hP hBRpos
  have hBR : B*R ≤ P*(B*R) := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (B*R) (show 1 ≤ P by omega)
  have hR' : R ≤ B*R := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right R (show 1 ≤ B by omega)
  have hB' : B ≤ B*R := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left B (show 1 ≤ R by omega)
  have hPB : P*B ≤ P*(B*R) := Nat.mul_le_mul_left P hB'
  have hP' : P ≤ P*(B*R) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left P (show 1 ≤ B*R by omega)
  nlinarith only [hn,hVpos,hBR,hR',hPB,hP']

theorem fieldStep_pushBound
    (prefixCount prefixClock count clock volume fiberVolume src archive zeroBank oneBank tmp : Fin T) :
    mnNativePushBound 3 (fieldStep (P := P) (Q := Q) (A := A) (U := U)
      prefixCount prefixClock count clock volume fiberVolume src archive zeroBank oneBank tmp) := by
  simp [fieldStep,halveHeader,doubleHeader,halfCount,halfPairAct,
    retainedSplitFibers,splitFibers,scanFibers,splitFiber,retainedSplitBlockPairs,
    splitBlockPairs,splitPair,countedLoop,countedLoopBody,transfer,copyR,copyStep,
    moveR,scanR,keepIn,transferAct,drainR,popDo,whileR,moveStep,peekR,uclear,
    mnNativePushBound,mnActPush]

end IntegerMultBounds.MathlibTM2.Routing.DyadicFieldStep
