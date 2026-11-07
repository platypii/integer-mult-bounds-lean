module

public import IntegerMultBounds.MathlibTM2.Routing.PaddedFieldMove
public import IntegerMultBounds.MathlibTM2.Routing.FieldHeaderSetup

/-! The fixed destination continuation of a non-dyadic field move. Reuse the
retired block-width tape for the real crop volume and retire all evolved headers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.MixedRadixFinish
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  PaddedFieldLayout PaddedFieldMove FieldHeaderSetup GeneratedFiberPadding FieldBoundaryStock
variable {T Q A : ℕ} {P U β : Type} {body : P → Pr P T Q A U}

def finishMove
    (exponent realLength prefixCount prefixWork prefixClock clock volume fiberVolume src archive zeroBank oneBank tmp bits : Fin T) :
    Pr P T Q A U :=
  .seq (resetProduct realLength fiberVolume volume zeroBank prefixClock)
    (.seq (copyR prefixCount clock tmp (fun _ => tick))
      (.seq (generatedCropFibers exponent fiberVolume volume bits zeroBank prefixClock clock src archive oneBank tmp)
        (clearWords [volume,fiberVolume,prefixWork])))

theorem finishMove_exec
    (exponent realLength prefixCount prefixWork prefixClock clock volume fiberVolume src archive zeroBank oneBank tmp bits : Fin T)
    (hreg : [exponent,realLength,prefixCount,prefixWork,prefixClock,clock,volume,fiberVolume,src,archive,zeroBank,oneBank,tmp,bits].Nodup)
    (encode : β → List (Fin (A+4))) (R B M k : ℕ) (hR : 0 < R) (hB : 0 < B)
    (hencode : ∀ x, (encode x).length = R) (fill : β)
    (matrices : List (List (List β))) (hpositive : 0 < matrices.length)
    (hrows : ∀ rows ∈ matrices, rows.length = B) (hfit : M ≤ 2^k)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hk : (S.R exponent).length = k) (hm : (S.R realLength).length = M)
    (hp : (S.R prefixCount).length = matrices.length)
    (hpw : (S.R prefixWork).length = matrices.length*2^k)
    (hv : (S.R volume).length = R) (hf : (S.R fiberVolume).length = B*R)
    (hsrc : S.R src = SmallFieldMove.pairStream (matrices.map (destinationParts encode k M fill))++tail)
    (hfresh : ∀ i ∈ [prefixClock,clock,archive,zeroBank,oneBank,tmp,bits], S.R i = []) :
    let V := matrices.length*(B*(2^k*R))
    let output := matrices.flatMap (fun rows => (realColumns M fill rows).flatMap (fun col => col.flatMap encode))++tail
    ∃ vf n, vf.user = v.user ∧ n ≤ 128*V ∧
      Exec body (finishMove exponent realLength prefixCount prefixWork prefixClock clock volume fiberVolume
        src archive zeroBank oneBank tmp bits) (mk v S) n
        (mk vf {S with R := fun i => if i ∈ [volume,fiberVolume,prefixWork] then [] else Function.update S.R src output i}) := by
  dsimp only
  have hr := hreg
  regs_ne hr
  let V := matrices.length*(B*(2^k*R))
  let output := matrices.flatMap (fun rows => (realColumns M fill rows).flatMap (fun col => col.flatMap encode))++tail
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := resetProduct_exec (body := body) realLength fiberVolume volume zeroBank prefixClock
    (by regs_nodup) v S (hfresh _ (by simp)) (hfresh _ (by simp))
  let S₁ : Stacks T A := {S with R := Function.update S.R volume (List.replicate (M*(B*R)) tick)}
  have he₁' : Exec body (resetProduct realLength fiberVolume volume zeroBank prefixClock)
      (mk v S) n₁ (mk v₁ S₁) := by simpa only [hm,hf] using he₁
  have hoff₁ (i : Fin T) (hi : i ≠ volume) : S₁.R i = S.R i := by simp [S₁,hi]
  obtain ⟨v₂,hu₂,he₂⟩ := copyR_exec (body := body) prefixCount clock tmp
    ‹prefixCount ≠ clock› ‹prefixCount ≠ tmp› ‹clock ≠ tmp› (fun _ => tick) v₁ S₁
    (by rw [hoff₁ tmp ‹volume ≠ tmp›.symm]; exact hfresh _ (by simp))
  let S₂ : Stacks T A := {S₁ with R := (Function.update S₁.R clock
    (List.replicate matrices.length tick))}
  have he₂' : Exec body (copyR prefixCount clock tmp (fun _ => tick)) (mk v₁ S₁)
      (4*matrices.length+4) (mk v₂ S₂) := by
    simpa [S₂,hoff₁ prefixCount ‹prefixCount ≠ volume›,hoff₁ clock ‹clock ≠ volume›,
      hp,hfresh clock (by simp),List.map_const'] using he₂
  have hoff₂ (i : Fin T) (hi : i ≠ clock) : S₂.R i = S₁.R i := by simp [S₂,hi]
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃,hw₃⟩ := cropMovedRows_exec (body := body)
    exponent fiberVolume volume bits zeroBank prefixClock clock src archive oneBank tmp
    (by regs_nodup) encode R B M k hR hB hencode fill matrices hpositive hrows hfit tail v₂ S₂
    (by rw [hoff₂ exponent ‹exponent ≠ clock›,hoff₁ exponent ‹exponent ≠ volume›]; exact hk)
    (by rw [hoff₂ fiberVolume ‹clock ≠ fiberVolume›.symm,hoff₁ fiberVolume ‹volume ≠ fiberVolume›.symm]; exact hf)
    (by simp [S₂,S₁,‹clock ≠ volume›.symm]) (by simp [S₂])
    (by rw [hoff₂ src ‹clock ≠ src›.symm,hoff₁ src ‹volume ≠ src›.symm]; exact hsrc)
    (by rw [hoff₂ bits ‹clock ≠ bits›.symm,hoff₁ bits ‹volume ≠ bits›.symm]; exact hfresh _ (by simp))
    (by rw [hoff₂ zeroBank ‹clock ≠ zeroBank›.symm,hoff₁ zeroBank ‹volume ≠ zeroBank›.symm]; exact hfresh _ (by simp))
    (by rw [hoff₂ prefixClock ‹prefixClock ≠ clock›,hoff₁ prefixClock ‹prefixClock ≠ volume›]; exact hfresh _ (by simp))
    (by rw [hoff₂ archive ‹clock ≠ archive›.symm,hoff₁ archive ‹volume ≠ archive›.symm]; exact hfresh _ (by simp))
    (by rw [hoff₂ oneBank ‹clock ≠ oneBank›.symm,hoff₁ oneBank ‹volume ≠ oneBank›.symm]; exact hfresh _ (by simp))
    (by rw [hoff₂ tmp ‹clock ≠ tmp›.symm,hoff₁ tmp ‹volume ≠ tmp›.symm]; exact hfresh _ (by simp))
  let S₃ : Stacks T A := {S₂ with R := (Function.update (Function.update S₂.R src output) clock [])}
  obtain ⟨v₄,hu₄,he₄⟩ := clearWords_exec (body := body) [volume,fiberVolume,prefixWork] (by regs_nodup) v₃ S₃
  have h₃v : (S₃.R volume).length = M*(B*R) := by simp [S₃,S₂,S₁,‹clock ≠ volume›.symm,‹volume ≠ src›]
  have h₃f : (S₃.R fiberVolume).length = B*R := by
    simp [S₃,S₂,S₁,‹clock ≠ fiberVolume›.symm,‹fiberVolume ≠ src›,‹volume ≠ fiberVolume›.symm,hf]
  have h₃p : (S₃.R prefixWork).length = matrices.length*2^k := by
    simp [S₃,S₂,S₁,‹prefixWork ≠ clock›,‹prefixWork ≠ src›,‹prefixWork ≠ volume›,hpw]
  have h₄time : 2*([volume,fiberVolume,prefixWork].map fun i => (S₃.R i).length).sum+
      2*[volume,fiberVolume,prefixWork].length+1 = 2*(M*(B*R)+B*R+matrices.length*2^k)+7 := by
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil,h₃v,h₃f,h₃p]
    omega
  refine ⟨v₄,n₁+((4*matrices.length+4)+(n₃+_)),hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ he₄))).cast rfl ?_⟩
  · rw [hv,hm,hf] at hn₁
    rw [h₄time]
    have heq : (matrices.length*2^k)*(B*R) = V := by dsimp only [V]; ring
    have hd := dimensions_le_volume (Nat.mul_pos hpositive (Nat.two_pow_pos k)) hB hR
    rw [heq] at hd
    have hCBR : 2^k*(B*R) ≤ V := by
      have h := Nat.mul_le_mul_right (2^k*(B*R)) (show 1 ≤ matrices.length by omega)
      simpa only [V,Nat.one_mul,Nat.mul_assoc,Nat.mul_left_comm B (2^k)] using h
    have hMBR : M*(B*R) ≤ V := (Nat.mul_le_mul_right (B*R) hfit).trans hCBR
    have hM : M ≤ V := by
      have h := Nat.mul_le_mul_left M (show 1 ≤ B*R from Nat.mul_pos hB hR)
      simpa only [Nat.mul_one] using h.trans hMBR
    have hP : matrices.length ≤ V := by
      have h := Nat.mul_le_mul_left matrices.length (Nat.one_le_two_pow (n := k))
      simpa only [Nat.mul_one] using h.trans hd.1
    have hpos : 0 < V := by dsimp only [V]; positivity
    change n₃ ≤ 64*V at hn₃
    change n₁+((4*matrices.length+4)+(n₃+(2*(M*(B*R)+B*R+matrices.length*2^k)+7))) ≤ 128*V
    nlinarith only [hn₁,hn₃,hd.1,hd.2.1,hd.2.2,hMBR,hM,hP,hpos]
  · apply congrArg (mk v₄)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hm : i ∈ [volume,fiberVolume,prefixWork]
    · simp [hm]
    · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hm
      obtain ⟨hiv,hif,hip⟩ := hm
      by_cases hic : i = clock
      · subst i; simp [S₃,hiv,hif,hip,‹clock ≠ src›,hfresh clock (by simp)]
      · simp [S₃,S₂,S₁,Function.update_apply,hiv,hif,hip,hic,output]

theorem finishMove_pushBound
    (exponent realLength prefixCount prefixWork prefixClock clock volume fiberVolume src archive zeroBank oneBank tmp bits : Fin T) :
    mnNativePushBound 2 (finishMove (P := P) (Q := Q) (A := A) (U := U)
      exponent realLength prefixCount prefixWork prefixClock clock volume fiberVolume src archive zeroBank oneBank tmp bits) := by
  simp only [finishMove,mnNativePushBound]
  refine ⟨resetProduct_pushBound _ _ _ _ _,?_,generatedCropFibers_pushBound _ _ _ _ _ _ _ _ _ _ _,?_⟩
  · simp [copyR,copyStep,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]
  · simp [clearWords,uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]

theorem finishMove_within_stock
    {exponent realLength prefixCount prefixWork prefixClock clock volume fiberVolume src archive zeroBank oneBank tmp bits : Fin T}
    {v vf : HS T Q A U} {S F : Stacks T A} {n V : ℕ}
    (hex : Exec body (finishMove exponent realLength prefixCount prefixWork prefixClock clock volume fiberVolume
      src archive zeroBank oneBank tmp bits) (mk v S) n (mk vf F))
    (hn : n ≤ 128*V) (depth : ℕ) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+256*V)
      depth (finishMove exponent realLength prefixCount prefixWork prefixClock clock volume fiberVolume
        src archive zeroBank oneBank tmp bits) (mk v S) n (mk vf F) := by
  exact mn_native_exec_within hex 2 (finishMove_pushBound _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Routing.MixedRadixFinish
