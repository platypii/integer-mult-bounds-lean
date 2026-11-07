module

public import IntegerMultBounds.MathlibTM2.Routing.PaddedFieldInverseMove
public import IntegerMultBounds.MathlibTM2.Routing.FieldHeaderSetup

/-! Finish the non-dyadic return using the current real field length. Generate
both crop dimensions, remove row padding and retire the evolved headers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.MixedRadixReturnFinish
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  PaddedFieldLayout PaddedFieldInverseMove FieldHeaderSetup GeneratedFiberPadding FieldBoundaryStock
variable {T Q A : ℕ} {P U β : Type} {body : P → Pr P T Q A U}

def finishReturn
    (exponent prefixCount count realLength blockWidth bits prefixWork prefixClock clock volume fiberVolume src archive zeroBank oneBank tmp : Fin T) :
    Pr P T Q A U :=
  .seq (resetProduct realLength blockWidth volume zeroBank prefixClock)
    (.seq (resetProduct prefixCount count clock zeroBank prefixClock)
      (.seq (generatedCropFibers exponent blockWidth volume bits zeroBank prefixClock clock src archive oneBank tmp)
        (clearWords [volume,fiberVolume,prefixWork])))

theorem finishReturn_exec
    (exponent prefixCount count realLength blockWidth bits prefixWork prefixClock clock volume fiberVolume src archive zeroBank oneBank tmp : Fin T)
    (hreg : [exponent,prefixCount,count,realLength,blockWidth,bits,prefixWork,prefixClock,clock,volume,fiberVolume,src,archive,zeroBank,oneBank,tmp].Nodup)
    (encode : β → List (Fin (A+4))) (R B M k : ℕ) (hR : 0 < R) (hB : 0 < B)
    (hencode : ∀ x, (encode x).length = R) (zero : Fin (A+4))
    (matrices : List (List (List β))) (hpositive : 0 < matrices.length)
    (hrows : ∀ rows ∈ matrices, rows.length = B)
    (hlen : ∀ rows ∈ matrices, ∀ xs ∈ rows, xs.length = M) (hfit : M ≤ 2^k)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hk : (S.R exponent).length = k) (hm : (S.R realLength).length = M)
    (hp : (S.R prefixCount).length = matrices.length) (hb : (S.R count).length = B)
    (hw : (S.R blockWidth).length = R) (hpw : (S.R prefixWork).length = matrices.length)
    (hv : (S.R volume).length = 2^k*R) (hf : (S.R fiberVolume).length = B*(2^k*R))
    (hsrc : S.R src = (sourceRows encode matrices).flatMap
      (fun xs => xs++List.replicate (2^k*R-M*R) zero)++tail)
    (hfresh : ∀ i ∈ [prefixClock,clock,archive,zeroBank,oneBank,tmp,bits], S.R i = []) :
    let V := matrices.length*(B*(2^k*R))
    let output := (sourceRows encode matrices).flatten++tail
    ∃ vf n, vf.user = v.user ∧ n ≤ 128*V ∧
      Exec body (finishReturn exponent prefixCount count realLength blockWidth bits prefixWork prefixClock clock
        volume fiberVolume src archive zeroBank oneBank tmp) (mk v S) n
        (mk vf {S with R := fun i => if i ∈ [volume,fiberVolume,prefixWork] then [] else Function.update S.R src output i}) := by
  dsimp only
  have hr := hreg
  regs_ne hr
  let V := matrices.length*(B*(2^k*R))
  let output := (sourceRows encode matrices).flatten++tail
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := resetProduct_exec (body := body) realLength blockWidth volume zeroBank prefixClock
    (by regs_nodup) v S (hfresh _ (by simp)) (hfresh _ (by simp))
  let S₁ : Stacks T A := {S with R := Function.update S.R volume (List.replicate (M*R) tick)}
  have he₁' : Exec body (resetProduct realLength blockWidth volume zeroBank prefixClock) (mk v S) n₁ (mk v₁ S₁) := by
    simpa only [hm,hw] using he₁
  have off₁ (i : Fin T) (hi : i ≠ volume) : S₁.R i = S.R i := by simp [S₁,hi]
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := resetProduct_exec (body := body) prefixCount count clock zeroBank prefixClock
    (by regs_nodup) v₁ S₁
    (by rw [off₁ zeroBank ‹volume ≠ zeroBank›.symm]; exact hfresh _ (by simp))
    (by rw [off₁ prefixClock ‹prefixClock ≠ volume›]; exact hfresh _ (by simp))
  let S₂ : Stacks T A := {S₁ with R := Function.update S₁.R clock (List.replicate (matrices.length*B) tick)}
  have he₂' : Exec body (resetProduct prefixCount count clock zeroBank prefixClock) (mk v₁ S₁) n₂ (mk v₂ S₂) := by
    simpa only [off₁ prefixCount ‹prefixCount ≠ volume›,off₁ count ‹count ≠ volume›,hp,hb] using he₂
  have off₂ (i : Fin T) (hi : i ≠ clock) : S₂.R i = S₁.R i := by simp [S₂,hi]
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃,ht₃⟩ := cropReturnedRows_exec (body := body)
    exponent blockWidth volume bits zeroBank prefixClock clock src archive oneBank tmp
    (by regs_nodup) encode R B M k hR hB hencode zero matrices hpositive hrows hlen hfit tail v₂ S₂
    (by rw [off₂ exponent ‹exponent ≠ clock›,off₁ exponent ‹exponent ≠ volume›]; exact hk)
    (by rw [off₂ blockWidth ‹blockWidth ≠ clock›,off₁ blockWidth ‹blockWidth ≠ volume›]; exact hw)
    (by simp [S₂,S₁,‹clock ≠ volume›.symm]) (by simp [S₂])
    (by rw [off₂ src ‹clock ≠ src›.symm,off₁ src ‹volume ≠ src›.symm]; exact hsrc)
    (by rw [off₂ bits ‹bits ≠ clock›,off₁ bits ‹bits ≠ volume›]; exact hfresh _ (by simp))
    (by rw [off₂ zeroBank ‹clock ≠ zeroBank›.symm,off₁ zeroBank ‹volume ≠ zeroBank›.symm]; exact hfresh _ (by simp))
    (by rw [off₂ prefixClock ‹prefixClock ≠ clock›,off₁ prefixClock ‹prefixClock ≠ volume›]; exact hfresh _ (by simp))
    (by rw [off₂ archive ‹clock ≠ archive›.symm,off₁ archive ‹volume ≠ archive›.symm]; exact hfresh _ (by simp))
    (by rw [off₂ oneBank ‹clock ≠ oneBank›.symm,off₁ oneBank ‹volume ≠ oneBank›.symm]; exact hfresh _ (by simp))
    (by rw [off₂ tmp ‹clock ≠ tmp›.symm,off₁ tmp ‹volume ≠ tmp›.symm]; exact hfresh _ (by simp))
  let S₃ : Stacks T A := {S₂ with R := (Function.update (Function.update S₂.R src output) clock [])}
  obtain ⟨v₄,hu₄,he₄⟩ := clearWords_exec (body := body) [volume,fiberVolume,prefixWork] (by regs_nodup) v₃ S₃
  have h₃v : (S₃.R volume).length = M*R := by simp [S₃,S₂,S₁,‹clock ≠ volume›.symm,‹volume ≠ src›]
  have h₃f : (S₃.R fiberVolume).length = B*(2^k*R) := by
    simp [S₃,S₂,S₁,‹clock ≠ fiberVolume›.symm,‹fiberVolume ≠ src›,‹volume ≠ fiberVolume›.symm,hf]
  have h₃p : (S₃.R prefixWork).length = matrices.length := by
    simp [S₃,S₂,S₁,‹prefixWork ≠ clock›,‹prefixWork ≠ src›,‹prefixWork ≠ volume›,hpw]
  have h₄time : 2*([volume,fiberVolume,prefixWork].map fun i => (S₃.R i).length).sum+
      2*[volume,fiberVolume,prefixWork].length+1 = 2*(M*R+B*(2^k*R)+matrices.length)+7 := by
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,List.length_cons,List.length_nil,h₃v,h₃f,h₃p]
    omega
  refine ⟨v₄,n₁+(n₂+(n₃+_)),hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ he₄))).cast rfl ?_⟩
  · rw [hv,hm,hw] at hn₁
    have h₂cost : n₂ ≤ matrices.length*(4*B+9)+6 := by
      simp only [off₁ prefixCount ‹prefixCount ≠ volume›,off₁ count ‹count ≠ volume›,
        off₁ clock ‹clock ≠ volume›,hp,hb,hfresh clock (by simp),List.length_nil] at hn₂
      omega
    rw [h₄time]
    have hd := dimensions_le_volume hpositive hB (Nat.mul_pos (Nat.two_pow_pos k) hR)
    change matrices.length ≤ V ∧ 2^k*R ≤ V ∧ B*(2^k*R) ≤ V at hd
    have hMR : M*R ≤ V := (Nat.mul_le_mul_right R hfit).trans hd.2.1
    have hM : M ≤ V := by
      have hh := Nat.mul_le_mul_left M (show 1 ≤ R by omega)
      simpa only [Nat.mul_one] using hh.trans hMR
    have hPB : matrices.length*B ≤ V := by
      have hh := Nat.mul_le_mul_left (matrices.length*B) (show 1 ≤ 2^k*R from Nat.mul_pos (Nat.two_pow_pos k) hR)
      simpa only [V,Nat.mul_one,Nat.mul_assoc] using hh
    have hpos : 0 < V := by dsimp only [V]; positivity
    change n₃ ≤ 64*V at hn₃
    change n₁+(n₂+(n₃+(2*(M*R+B*(2^k*R)+matrices.length)+7))) ≤ 128*V
    nlinarith only [hn₁,h₂cost,hn₃,hd.1,hd.2.1,hd.2.2,hMR,hM,hPB,hpos]
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

theorem finishReturn_pushBound
    (exponent prefixCount count realLength blockWidth bits prefixWork prefixClock clock volume fiberVolume src archive zeroBank oneBank tmp : Fin T) :
    mnNativePushBound 2 (finishReturn (P := P) (Q := Q) (A := A) (U := U)
      exponent prefixCount count realLength blockWidth bits prefixWork prefixClock clock volume fiberVolume src archive zeroBank oneBank tmp) := by
  simp only [finishReturn,mnNativePushBound]
  refine ⟨resetProduct_pushBound _ _ _ _ _,resetProduct_pushBound _ _ _ _ _,
    generatedCropFibers_pushBound _ _ _ _ _ _ _ _ _ _ _,?_⟩
  simp [clearWords,uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]

theorem finishReturn_within_stock
    {exponent prefixCount count realLength blockWidth bits prefixWork prefixClock clock volume fiberVolume src archive zeroBank oneBank tmp : Fin T}
    {v vf : HS T Q A U} {S F : Stacks T A} {n V : ℕ}
    (hex : Exec body (finishReturn exponent prefixCount count realLength blockWidth bits prefixWork prefixClock clock
      volume fiberVolume src archive zeroBank oneBank tmp) (mk v S) n (mk vf F))
    (hn : n ≤ 128*V) (depth : ℕ) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+256*V)
      depth (finishReturn exponent prefixCount count realLength blockWidth bits prefixWork prefixClock clock
        volume fiberVolume src archive zeroBank oneBank tmp) (mk v S) n (mk vf F) := by
  exact mn_native_exec_within hex 2 (finishReturn_pushBound _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Routing.MixedRadixReturnFinish
