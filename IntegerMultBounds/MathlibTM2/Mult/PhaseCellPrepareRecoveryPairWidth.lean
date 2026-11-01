module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateWordWidth
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock
public import IntegerMultBounds.MathlibTM2.Host.EmbedStream

/-! Generate the complex pairing packet width from retained numerical masters.
The two intermediate unary dimensions are erased before returning. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 8 Q A U}

/-- Ports 0/1/2 retain precision/origin/end; port 5 receives the packet width. -/
def prepareRecoveryPairWidth : Pr P 8 Q A U :=
  .seq (generateWordWidth 0 3 6)
    (.seq (ucopy 2 4 6) (.seq (usub 1 4 6)
      (.seq (unaryProduct 4 3 5 6 7) (clearWords [3,4]))))

def prepareRecoveryPairWidthCost (q a b : ℕ) : ℕ :=
  (8*q+9)+(4*b+4)+(4*a+4)+((b-a)*(4*(2*q+8)+9)+4)+
    (2*((2*q+8)+(b-a))+5)

theorem prepareRecoveryPairWidth_exec (q a b : ℕ) (v : HS 8 Q A U) (S : Stacks 8 A)
    (hq : (S.R 0).length = q) (ha : (S.R 1).length = a) (hb : (S.R 2).length = b)
    (hblank : ∀ k ∈ ([(3 : Fin 8),4,5,6,7]), S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ prepareRecoveryPairWidthCost q a b ∧
      Exec body prepareRecoveryPairWidth (Host.mk v S) n
        (Host.mk v' {S with R := Function.update S.R 5 (List.replicate ((b-a)*(2*q+8)) tick)}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := generateWordWidth_exec (body := body)
    (show ([(0 : Fin 8),3,6]).Nodup by decide) q v S hq (hblank 3 (by simp)) (hblank 6 (by simp))
  let S₁ : Stacks 8 A := {S with R := Function.update S.R 3 (List.replicate (2*q+8) tick)}
  obtain ⟨v₂,hu₂,he₂⟩ := ucopy_exec (body := body) (a := 2) (b := 4) (t := 6)
    (by decide) (by decide) (by decide) v₁ S₁ (by simp [S₁,hblank 6 (by simp)])
  let S₂ : Stacks 8 A := {S₁ with R := Function.update S₁.R 4 (List.replicate b tick)}
  have he₂' : Exec body (ucopy 2 4 6) (Host.mk v₁ S₁) (4*b+4) (Host.mk v₂ S₂) := by
    simpa [S₂,S₁,hb,hblank 4 (by simp)] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := usub_exec (body := body) (a := 1) (b := 4) (t := 6)
    (by decide) (by decide) (by decide) v₂ S₂ (by simp [S₂,S₁,hblank 6 (by simp)])
  let S₃ : Stacks 8 A := {S₂ with R := Function.update S₂.R 4 (List.replicate (b-a) tick)}
  have he₃' : Exec body (usub 1 4 6) (Host.mk v₂ S₂) (4*a+4) (Host.mk v₃ S₃) := by
    simpa [S₃,S₂,S₁,ha] using he₃
  obtain ⟨v₄,n₄,hu₄,hn₄,he₄⟩ := unaryProduct_exec (body := body)
    (show ([(4 : Fin 8),3,5,6,7]).Nodup by decide) v₃ S₃
    (by simp [S₃,S₂,S₁,hblank 6 (by simp)]) (by simp [S₃,S₂,S₁,hblank 7 (by simp)])
  let S₄ : Stacks 8 A := {S₃ with R := Function.update S₃.R 5 (List.replicate ((b-a)*(2*q+8)) tick)}
  have he₄' : Exec body (unaryProduct 4 3 5 6 7) (Host.mk v₃ S₃) n₄ (Host.mk v₄ S₄) := by
    simpa [S₄,S₃,S₂,S₁,hblank 5 (by simp)] using he₄
  have hn₄' : n₄ ≤ (b-a)*(4*(2*q+8)+9)+4 := by simpa [S₃,S₂,S₁] using hn₄
  obtain ⟨v₅,hu₅,he₅⟩ := clearWords_exec (body := body) [3,4] (by decide) v₄ S₄
  have hfinal : {S₄ with R := fun k => if k ∈ ([(3 : Fin 8),4]) then [] else S₄.R k} =
      {S with R := Function.update S.R 5 (List.replicate ((b-a)*(2*q+8)) tick)} := by
    refine Stacks.ext ?_ ?_ ?_ ?_
    · rfl
    · rfl
    · rfl
    funext k
    fin_cases k <;> simp [S₄,S₃,S₂,S₁,hblank 3 (by simp),hblank 4 (by simp)]
  have he₅' : Exec body (clearWords [3,4]) (Host.mk v₄ S₄)
      (2*((2*q+8)+(b-a))+5)
      (Host.mk v₅ {S with R := Function.update S.R 5 (List.replicate ((b-a)*(2*q+8)) tick)}) := by
    rw [hfinal] at he₅
    simpa [S₄,S₃,S₂,S₁,Nat.add_assoc] using he₅
  refine ⟨v₅,_,hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))),?_,
    Exec.seq he₁ (Exec.seq he₂' (Exec.seq he₃' (Exec.seq he₄' he₅')))⟩
  unfold prepareRecoveryPairWidthCost
  omega

theorem prepareRecoveryPairWidth_native :
    mnNativePushBound 8 (prepareRecoveryPairWidth (P := P) (Q := Q) (A := A) (U := U)) := by
  simp [prepareRecoveryPairWidth,generateWordWidth,ucopy,usub,dropTop,unaryProduct,clearWords,uclear,
    scanP,popPush,umulSym,scanR,drainR,popDo,keepIn,pushN,moveR,whileR,moveStep,peekR,
    mnNativePushBound,mnActPush]

theorem prepareRecoveryPairWidth_within_stock
    {v v' : HS 8 Q A U} {S G : Stacks 8 A} {n q a b : ℕ}
    (hex : Exec body prepareRecoveryPairWidth (Host.mk v S) n (Host.mk v' G))
    (hn : n ≤ prepareRecoveryPairWidthCost q a b) (depth : ℕ) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
      8*prepareRecoveryPairWidthCost q a b) depth prepareRecoveryPairWidth
      (Host.mk v S) n (Host.mk v' G) :=
  mn_native_exec_within hex 8 prepareRecoveryPairWidth_native depth _ (by omega)

/-- Place the small setup bank in the supplier layout. Only the packet header
changes; masters, scratch, left stacks and all spectators restore. -/
theorem placedPrepareRecoveryPairWidth_exec {T : ℕ} {body' : P → Pr P T Q A U}
    (e : Fin 8 → Fin T) (he : Function.Injective e) (q a b : ℕ)
    (v : HS T Q A U) (S : Stacks T A)
    (hq : (S.R (e 0)).length = q) (ha : (S.R (e 1)).length = a) (hb : (S.R (e 2)).length = b)
    (hblank : ∀ k ∈ ([(3 : Fin 8),4,5,6,7]), S.R (e k) = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ prepareRecoveryPairWidthCost q a b ∧
      Exec body' (embProg e Empty.elim prepareRecoveryPairWidth) (Host.mk v S) n
        (Host.mk v' {S with R := Function.update S.R (e 5) (List.replicate ((b-a)*(2*q+8)) tick)}) ∧
      ∀ depth, ExecWithin body' (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        8*prepareRecoveryPairWidthCost q a b) depth (embProg e Empty.elim prepareRecoveryPairWidth)
        (Host.mk v S) n
        (Host.mk v' {S with R := Function.update S.R (e 5) (List.replicate ((b-a)*(2*q+8)) tick)}) := by
  obtain ⟨w,n,hu,hn,hex⟩ := prepareRecoveryPairWidth_exec (body := fun f : Empty => nomatch f)
    q a b (embDn e v) (embStk e S) hq ha hb hblank
  obtain ⟨v',_,hu',hex'⟩ := exec_emb_ovr (e := e) (ι := Empty.elim) (body' := body') he
    (fun f => nomatch f) hex v rfl S rfl
  rw [embOvr_stream e he] at hex'
  refine ⟨v',n,hu'.trans hu,hn,hex',fun depth => ?_⟩
  exact mn_native_exec_within hex' 8 (embProg_native e Empty.elim _ prepareRecoveryPairWidth_native)
    depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
