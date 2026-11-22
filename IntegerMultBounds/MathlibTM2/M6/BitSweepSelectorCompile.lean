module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepSelectorLoop
public import IntegerMultBounds.MathlibTM2.M6.BitSweepGatherLoop

/-! Consume the counted loop's reverse buffer to build the gather mask tape. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine Stack Host Node Routing

theorem compileSweepBuffer_exec {T Q A M : ℕ} {P U : Type} (body : P → Pr P T Q A U)
    (rg : BinaryMaskReg ↪ Fin T) (buf src out : Fin T) (ports : [src,buf,out].Nodup)
    (srcOff : ∀ i, src ≠ rg i) (bufOff : ∀ i, buf ≠ rg i) (outOff : ∀ i, out ≠ rg i)
    (H : ℕ) (fits : M < 2^H) (p : Equiv.Perm (Fin M)) (v : HS T Q A U) (S : Stacks T A)
    (ready : DescriptorCompileReady rg S.R H M) (empty : S.R src = [])
    (stream : S.R buf = (descriptorSelectorFrames H (List.ofFn p.symm)).reverse) :
    ∃ z n, z.user = v.user ∧ n ≤ M*(descriptorCompileCallCost H M+2)+6*(M*(H+1))+8 ∧
      Exec body (.seq (moveR buf src id) (.seq (descriptorCompileProgram rg src buf out) (bclear src)))
        (mk v S) n (mk z {S with
          R := Function.update (Function.update S.R buf []) out
            ((permutationMasks p).flatten.map bitSymbol ++ S.R out)}) := by
  regs_ne ports
  obtain ⟨u,hu,move⟩ := moveR_exec body buf src ‹src ≠ buf›.symm id v S
  simp only [stream,List.length_reverse,descriptorSelectorFrames_length,List.length_ofFn,movedR,
    List.map_id,List.reverse_reverse,empty,List.append_nil] at move
  let frames := descriptorSelectorFrames (A := A) H (List.ofFn p.symm)
  let B := {S with R := Function.update (Function.update S.R buf []) src frames}
  have keep (i) : B.R (rg i) = S.R (rg i) := by simp [B,(srcOff i).symm,(bufOff i).symm]
  obtain ⟨y,k,hy,hk,table⟩ := sweepPermutationMasks_exec body rg rg.injective src buf out
    ‹src ≠ buf› ‹src ≠ out› ‹buf ≠ out› srcOff bufOff outOff H fits p u B
    ⟨(keep _).trans ready.width, fun i hi => (keep i).trans (ready.blank i hi)⟩
    (Function.update_self ..) (by simp [B,Ne.symm ‹src ≠ buf›])
  let F := {B with R := Function.update B.R out ((permutationMasks p).flatten.map bitSymbol ++ B.R out)}
  obtain ⟨z,hz,_,clear⟩ := bclear_exec body src y F
  have size : (F.R src).length = M*(H+1) := by simp [F,B,frames,‹src ≠ out›,descriptorSelectorFrames_length]
  refine ⟨z,2*(M*(H+1))+2+(k+(2*(F.R src).length+2)),hz.trans (hy.trans hu),by rw [size]; omega,
    Exec.seq move (Exec.seq table ?_)⟩
  apply clear.cast rfl
  apply congrArg (mk z)
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hs : i = src <;> by_cases ho : i = out <;> simp_all [F,B,Ne.symm ‹buf ≠ out›]

/-- The complete selector stream, including rank evaluation, counter ticks,
both traversals of the binary frames and mask compilation, fits a cubic bill. -/
theorem sweepSelectorCompile_cost {M H L C cost : ℕ} (positive : 0 < M)
    (width : H ≤ M+1) (digits : L ≤ H) (evaluate : cost ≤ C*(H+1)^2) :
    M*(cost+(2*H+9*L+15)+3)+2 +
      (M*(descriptorCompileCallCost H M+2)+6*(M*(H+1))+8) ≤ (9*C+400)*M^3 := by
  have compile := sweepPermutationMasks_cost positive width
  have evalBound : cost ≤ C*((M+1)+1)^2 := evaluate.trans (by gcongr)
  have loop : M*(cost+(2*H+9*L+15)+3) ≤ M*(C*((M+1)+1)^2+(2*(M+1)+9*(M+1)+15)+3) := by
    gcongr; omega
  have linear : M*(H+1) ≤ M*((M+1)+1) := by gcongr
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero positive.ne'
  simp only [Nat.succ_eq_add_one] at *
  ring_nf at compile loop linear ⊢
  omega

theorem radixSweepSelectorCompile_cost {q w H C cost : ℕ} (base : 2 ≤ q)
    (fits : (q^w)^128 < 2^H) (width : H ≤ (q^w)^128+1) (evaluate : cost ≤ C*(H+1)^2) :
    let M := (q^w)^128
    M*(cost+(2*H+9*(w*128)+15)+3)+2 +
      (M*(descriptorCompileCallCost H M+2)+6*(M*(H+1))+8) ≤ (9*C+400)*M^3 := by
  apply sweepSelectorCompile_cost (pow_pos (pow_pos (by omega) _) _) width _ evaluate
  by_contra! h
  have bound := (Nat.pow_le_pow_right (by decide : 0 < 2) h.le).trans (Nat.pow_le_pow_left base (w*128))
  rw [pow_mul] at bound
  exact fits.not_ge bound

end IntegerMultBounds.MathlibTM2.M6.BitNode
