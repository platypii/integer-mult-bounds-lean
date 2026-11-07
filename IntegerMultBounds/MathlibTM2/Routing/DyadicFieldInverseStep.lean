module

public import IntegerMultBounds.MathlibTM2.Routing.InverseFiberScan
public import IntegerMultBounds.MathlibTM2.Routing.DyadicFieldLayout
public import IntegerMultBounds.MathlibTM2.Routing.FieldMoveHeaders

/-! One inverse binary level: merge consecutive preceding-bit fibers and
restore the dimensions used before their forward split. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.DyadicFieldInverseStep
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  DyadicFieldLayout FieldMoveHeaders FiberScan InverseFiberScan SmallFieldMove
variable {T Q A : ℕ} {P U β : Type} {body : P → Pr P T Q A U}

theorem mergeFieldLevel_exec
    (prefixCount prefixClock count clock volume planeVolume src archive zeroBank oneBank tmp : Fin T)
    (hreg : [prefixCount,prefixClock,count,clock,volume,planeVolume,src,archive,zeroBank,oneBank,tmp].Nodup)
    (encode : β → List (Fin (A+4))) (W B k : ℕ) (hlen : ∀ x, (encode x).length = W)
    (fibers : List (List (Field β (k+1)))) (hrows : ∀ rows ∈ fibers, rows.length = B)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hprefix : (S.R prefixCount).length = fibers.length)
    (hcount : (S.R count).length = B) (hvolume : (S.R volume).length = 2^k*W)
    (hplane : (S.R planeVolume).length = B*(2^k*W))
    (hsrc : S.R src = stream encode (refineFibers fibers)++tail)
    (hprefixClock : S.R prefixClock = []) (hclock : S.R clock = [])
    (harchive : S.R archive = []) (hzero : S.R zeroBank = [])
    (hone : S.R oneBank = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ fibers.length*(30*(B*(2^k*W))+15*B+29)+8 ∧
      Exec body (retainedMergeFibers prefixCount prefixClock count clock volume planeVolume
        src archive zeroBank oneBank tmp) (mk v S) n
        (mk v' {S with R := Function.update S.R src (stream encode fibers++tail)}) := by
  have hpairs : ∀ rows ∈ fibers.map (blockPairs encode), rows.length = B ∧
      ∀ r ∈ rows, r.1.length = 2^k*W ∧ r.2.length = 2^k*W := by
    intro rows hm
    obtain ⟨xs,hxs,rfl⟩ := List.mem_map.mp hm
    refine ⟨by simpa [blockPairs] using hrows xs hxs,?_⟩
    intro r hr
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hr
    exact ⟨word_length encode W hlen x.1,word_length encode W hlen x.2⟩
  obtain ⟨v',n,hu,hn,he⟩ := retainedMergeFibers_exec (body := body)
    prefixCount prefixClock count clock volume planeVolume src archive zeroBank oneBank tmp hreg
    (fibers.map (blockPairs encode)) B (2^k*W) hpairs tail v S
    (by simpa only [List.length_map] using hprefix) hcount hvolume hplane
    (by rw [blockPairs_output encode fibers]; exact hsrc)
    hprefixClock hclock harchive hzero hone htmp
  refine ⟨v',n,hu,by simpa only [List.length_map] using hn,?_⟩
  simpa only [List.flatMap_map,Function.comp_def,blockPairs_input,stream] using he

def inverseFieldStep
    (prefixCount prefixClock count clock volume planeVolume src archive zeroBank oneBank tmp : Fin T) :
    Pr P T Q A U :=
  .seq (halveHeader prefixCount archive zeroBank)
    (.seq (retainedMergeFibers prefixCount prefixClock count clock volume planeVolume
      src archive zeroBank oneBank tmp)
      (.seq (doubleHeader volume archive tmp) (doubleHeader planeVolume archive tmp)))

theorem inverseFieldStep_exec
    (prefixCount prefixClock count clock volume planeVolume src archive zeroBank oneBank tmp : Fin T)
    (hreg : [prefixCount,prefixClock,count,clock,volume,planeVolume,src,archive,zeroBank,oneBank,tmp].Nodup)
    (encode : β → List (Fin (A+4))) (W B k : ℕ) (hlen : ∀ x, (encode x).length = W)
    (fibers : List (List (Field β (k+1)))) (hrows : ∀ rows ∈ fibers, rows.length = B)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hprefix : (S.R prefixCount).length = 2*fibers.length)
    (hcount : (S.R count).length = B) (hvolume : (S.R volume).length = 2^k*W)
    (hplane : (S.R planeVolume).length = B*(2^k*W))
    (hsrc : S.R src = stream encode (refineFibers fibers)++tail)
    (hprefixClock : S.R prefixClock = []) (hclock : S.R clock = [])
    (harchive : S.R archive = []) (hzero : S.R zeroBank = [])
    (hone : S.R oneBank = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ fibers.length*(30*(B*(2^k*W))+15*B+41)+6*(2^k*W)+6*(B*(2^k*W))+28 ∧
      Exec body (inverseFieldStep prefixCount prefixClock count clock volume planeVolume
        src archive zeroBank oneBank tmp) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R
          prefixCount (List.replicate fibers.length tick)) src (stream encode fibers++tail))
          volume (S.R volume++S.R volume)) planeVolume (S.R planeVolume++S.R planeVolume))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := halveHeader_exec (body := body) prefixCount archive zeroBank
    (by regs_nodup) fibers.length v S hprefix harchive hzero
  let S₁ : Stacks T A := {S with R := Function.update S.R prefixCount (List.replicate fibers.length tick)}
  have hoff₁ (i : Fin T) (hi : i ≠ prefixCount) : S₁.R i = S.R i := by simp [S₁,hi]
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := mergeFieldLevel_exec (body := body)
    prefixCount prefixClock count clock volume planeVolume src archive zeroBank oneBank tmp hreg
    encode W B k hlen fibers hrows tail v₁ S₁ (by simp [S₁])
    (by rw [hoff₁ count ‹prefixCount ≠ count›.symm]; exact hcount)
    (by rw [hoff₁ volume ‹prefixCount ≠ volume›.symm]; exact hvolume)
    (by rw [hoff₁ planeVolume ‹prefixCount ≠ planeVolume›.symm]; exact hplane)
    (by rw [hoff₁ src ‹prefixCount ≠ src›.symm]; exact hsrc)
    (by rw [hoff₁ prefixClock ‹prefixCount ≠ prefixClock›.symm]; exact hprefixClock)
    (by rw [hoff₁ clock ‹prefixCount ≠ clock›.symm]; exact hclock)
    (by rw [hoff₁ archive ‹prefixCount ≠ archive›.symm]; exact harchive)
    (by rw [hoff₁ zeroBank ‹prefixCount ≠ zeroBank›.symm]; exact hzero)
    (by rw [hoff₁ oneBank ‹prefixCount ≠ oneBank›.symm]; exact hone)
    (by rw [hoff₁ tmp ‹prefixCount ≠ tmp›.symm]; exact htmp)
  let S₂ : Stacks T A := {S₁ with R := Function.update S₁.R src (stream encode fibers++tail)}
  have hoff₂ (i : Fin T) (hip : i ≠ prefixCount) (his : i ≠ src) : S₂.R i = S.R i := by
    simp [S₂,S₁,hip,his]
  obtain ⟨v₃,hu₃,he₃⟩ := doubleHeader_exec (body := body) volume archive tmp (by regs_nodup) v₂ S₂
    (by rw [hoff₂ archive ‹prefixCount ≠ archive›.symm ‹src ≠ archive›.symm]; exact harchive)
    (by rw [hoff₂ tmp ‹prefixCount ≠ tmp›.symm ‹src ≠ tmp›.symm]; exact htmp)
  let S₃ : Stacks T A := {S₂ with R := Function.update S₂.R volume (S₂.R volume++S₂.R volume)}
  have hoff₃ (i : Fin T) (hip : i ≠ prefixCount) (his : i ≠ src) (hiv : i ≠ volume) : S₃.R i = S.R i := by
    simp only [S₃,Function.update_of_ne hiv]; exact hoff₂ i hip his
  obtain ⟨v₄,hu₄,he₄⟩ := doubleHeader_exec (body := body) planeVolume archive tmp (by regs_nodup) v₃ S₃
    (by rw [hoff₃ archive ‹prefixCount ≠ archive›.symm ‹src ≠ archive›.symm ‹volume ≠ archive›.symm]; exact harchive)
    (by rw [hoff₃ tmp ‹prefixCount ≠ tmp›.symm ‹src ≠ tmp›.symm ‹volume ≠ tmp›.symm]; exact htmp)
  have hv : S₂.R volume = S.R volume := hoff₂ volume ‹prefixCount ≠ volume›.symm ‹volume ≠ src›
  have hf : S₃.R planeVolume = S.R planeVolume :=
    hoff₃ planeVolume ‹prefixCount ≠ planeVolume›.symm ‹planeVolume ≠ src› ‹volume ≠ planeVolume›.symm
  refine ⟨v₄,_,hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,
    (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄))).cast rfl ?_⟩
  · rw [hv,hf,hvolume,hplane]; nlinarith only [hn₂]
  · simp [S₃,S₂,S₁,‹prefixCount ≠ volume›.symm,‹volume ≠ src›,
      ‹prefixCount ≠ planeVolume›.symm,‹planeVolume ≠ src›,‹volume ≠ planeVolume›.symm]

theorem inverseFieldStep_cost_le_volume {n P B R : ℕ} (hP : 0 < P) (hB : 0 < B) (hR : 0 < R)
    (hn : n ≤ P*(30*(B*R)+15*B+41)+6*R+6*(B*R)+28) :
    n ≤ 64*(2*(P*(B*R))) := by
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

theorem inverseFieldStep_pushBound
    (prefixCount prefixClock count clock volume planeVolume src archive zeroBank oneBank tmp : Fin T) :
    mnNativePushBound 3 (inverseFieldStep (P := P) (Q := Q) (A := A) (U := U)
      prefixCount prefixClock count clock volume planeVolume src archive zeroBank oneBank tmp) := by
  simp [inverseFieldStep,halveHeader,doubleHeader,halfCount,halfPairAct,
    retainedMergeFibers,mergeFibers,scanFibers,mergeFiber,mergeBlockPairs,
    joinBlockPairs,joinPair,transferTwice,countedLoop,countedLoopBody,transfer,copyR,copyStep,
    moveR,scanR,keepIn,transferAct,drainR,popDo,whileR,moveStep,peekR,uclear,
    mnNativePushBound,mnActPush]

end IntegerMultBounds.MathlibTM2.Routing.DyadicFieldInverseStep
