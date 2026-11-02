module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicGatherHeaders
public import IntegerMultBounds.MathlibTM2.Host.BinArith

/-! Decode the retained group length once, multiply by the retained coefficient
width and release the temporary length. Only the packet-width port changes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {Q K : ℕ} {P U : Type}

def gatherPacketWidthProgram : Pr P tapeCount Q (prime+K) U :=
  .seq (toUnary (headerReg 35) (headerReg 86) (headerReg 40) (headerReg 41) (headerReg 42))
    (.seq (unaryProduct (headerReg 86) (headerReg 87) packetWidth (headerReg 40) (headerReg 41))
      (uclear (headerReg 86)))

def gatherPacketWidthCost (V L w : ℕ) : ℕ := (6*L+11*V+6)+(L*(4*w+9)+4)+(2*L+2)

theorem gatherPacketWidth_exec_within (body : P → Pr P tapeCount Q (prime+K) U)
    (V L w : ℕ) (hfit : L < 2^V) (v : HS tapeCount Q (prime+K) U) (S : Stacks tapeCount (prime+K))
    (hlength : S.R (headerReg 35) = binSyms V L) (hword : (S.R (headerReg 87)).length = w)
    (hblank : ∀ i ∈ [(82 : Fin 117),86,40,41,42], S.R (headerReg i) = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ gatherPacketWidthCost V L w ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+3*gatherPacketWidthCost V L w)
        depth gatherPacketWidthProgram (mk v S) n
        (mk v' {S with R := Function.update S.R packetWidth (List.replicate (L*w) tick)}) := by
  have hi := headerReg_injective
  have hp : packetWidth = headerReg 82 := rfl
  have hz82 := hblank 82 (by simp)
  have hz86 := hblank 86 (by simp)
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := toUnary_exec_linear (body := body)
    (a := headerReg 35) (z := headerReg 86) (w := headerReg 40) (t := headerReg 41) (t₂ := headerReg 42)
    (by simp [List.nodup_cons,hi.eq_iff]) hfit v S hlength
    (hblank 40 (by simp)) (hblank 41 (by simp)) (hblank 42 (by simp))
  simp only [hz86,List.append_nil] at he₁
  let M : Stacks tapeCount (prime+K) := {S with R := Function.update S.R (headerReg 86) (List.replicate L tick)}
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := unaryProduct_exec (body := body)
    (a := headerReg 86) (b := headerReg 87) (dst := packetWidth) (t₁ := headerReg 40) (t₂ := headerReg 41)
    (by simp [hp,List.nodup_cons,hi.eq_iff]) v₁ M
    (by simpa [M,hi.eq_iff] using hblank 40 (by simp))
    (by simpa [M,hi.eq_iff] using hblank 41 (by simp))
  have he₂' : Exec body (unaryProduct (headerReg 86) (headerReg 87) packetWidth (headerReg 40) (headerReg 41))
      (mk v₁ M) n₂ (mk v₂ {M with R := Function.update M.R packetWidth (List.replicate (L*w) tick)}) := by
    simpa [M,hp,hi.eq_iff,hword,hz82] using he₂
  have hn₂' : n₂ ≤ L*(4*w+9)+4 := by simpa [M,hi.eq_iff,hword] using hn₂
  let F : Stacks tapeCount (prime+K) := {M with R := Function.update M.R packetWidth (List.replicate (L*w) tick)}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) (headerReg 86) v₂ F
  have hlen : (F.R (headerReg 86)).length = L := by simp [F,M,hp,hi.eq_iff]
  rw [hlen] at he₃
  have hend : {F with R := Function.update F.R (headerReg 86) []} =
      {S with R := Function.update S.R packetWidth (List.replicate (L*w) tick)} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk : k = headerReg 86
    · subst k; simp [hp,hi.eq_iff,hz86]
    · simp [F,M,hk,Function.update_apply]
  rw [hend] at he₃
  have he : Exec body gatherPacketWidthProgram (mk v S) (n₁+(n₂+(2*L+2)))
      (mk v₃ {S with R := Function.update S.R packetWidth (List.replicate (L*w) tick)}) :=
    Exec.seq he₁ (Exec.seq he₂' he₃)
  have hn : n₁+(n₂+(2*L+2)) ≤ gatherPacketWidthCost V L w := by
    unfold gatherPacketWidthCost
    omega
  have hnative : mnNativePushBound 3 (gatherPacketWidthProgram (P := P) (Q := Q) (K := K) (U := U)) := by
    simp [gatherPacketWidthProgram,toUnary,hornerIter,udbl,eachSym,unaryProduct,ucopy,umulSym,scanP,popPush,
      scanR,drainR,popDo,keepIn,pushN,moveR,moveStep,whileR,peekR,uclear,mnNativePushBound,mnActPush]
  exact ⟨v₃,_,hu₃.trans (hu₂.trans hu₁),hn,mn_native_exec_within he 3 hnative depth _ (by omega)⟩

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
