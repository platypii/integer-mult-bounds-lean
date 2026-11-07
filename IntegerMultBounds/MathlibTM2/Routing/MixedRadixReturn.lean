module

public import IntegerMultBounds.MathlibTM2.Routing.MixedRadixReturnFinish
public import IntegerMultBounds.MathlibTM2.Routing.FieldHeaderCopy

/-! Fixed sixteen-tape non-dyadic return controller. Pad current columns, undo
binary passes in reverse chronology, then crop the restored rows. Preparation
execution is proved here; complete composition is in MixedRadixReturnRun. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.MixedRadixReturn
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  FieldHeaderSetup FieldHeaderCopy GeneratedFiberPadding MixedRadixReturnFinish DyadicFieldInverse
  PaddedFieldLayout PaddedFieldInverseLayout FieldBoundaryStock
variable {T Q A : ℕ} {P U : Type}

def prepareReturn
    (exponent prefixCount count realLength blockWidth bits prefixWork prefixClock volume fiberVolume src archive zeroBank tmp : Fin T)
    (zero : Fin (A+4)) : Pr P T Q A U :=
  .seq (resetProduct count blockWidth fiberVolume zeroBank prefixClock)
    (.seq (resetProduct realLength fiberVolume volume zeroBank prefixClock)
      (.seq (copyR prefixCount bits tmp (fun _ => tick))
        (.seq (generatedPadFibers exponent fiberVolume volume prefixWork zeroBank prefixClock bits src archive tmp zero)
          (.seq (resetCopy blockWidth volume zeroBank)
            (.seq (resetDyadicWidth exponent prefixCount prefixWork zeroBank prefixClock)
              (copyR exponent bits tmp (fun _ => tick)))))))

/-- The field length is the current retained master, so a line map may change
its length before the return. The large spectator field is never moved bitwise. -/
def returnField
    (exponent prefixCount count realLength blockWidth bits prefixWork prefixClock clock volume fiberVolume src archive zeroBank oneBank tmp : Fin T)
    (zero : Fin (A+4)) : Pr P T Q A U :=
  .seq (prepareReturn exponent prefixCount count realLength blockWidth bits prefixWork prefixClock
    volume fiberVolume src archive zeroBank tmp zero)
    (.seq (inverseFieldMove bits prefixWork prefixClock count clock volume fiberVolume src archive zeroBank oneBank tmp)
      (finishReturn exponent prefixCount count realLength blockWidth bits prefixWork prefixClock clock
        volume fiberVolume src archive zeroBank oneBank tmp))

theorem prepareReturn_pushBound
    (exponent prefixCount count realLength blockWidth bits prefixWork prefixClock volume fiberVolume src archive zeroBank tmp : Fin T)
    (zero : Fin (A+4)) :
    mnNativePushBound 2 (prepareReturn (P := P) (Q := Q) (U := U)
      exponent prefixCount count realLength blockWidth bits prefixWork prefixClock volume fiberVolume src archive zeroBank tmp zero) := by
  simp only [prepareReturn,mnNativePushBound]
  refine ⟨resetProduct_pushBound _ _ _ _ _,resetProduct_pushBound _ _ _ _ _,?_,
    generatedPadFibers_pushBound _ _ _ _ _ _ _ _ _ _ _,resetCopy_pushBound _ _ _,
    resetDyadicWidth_pushBound _ _ _ _ _,?_⟩
  all_goals simp [copyR,copyStep,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

variable {β : Type} {body : P → Pr P T Q A U}

theorem prepareReturn_exec
    (exponent prefixCount count realLength blockWidth bits prefixWork prefixClock volume fiberVolume src archive zeroBank tmp : Fin T)
    (hreg : [exponent,prefixCount,count,realLength,blockWidth,bits,prefixWork,prefixClock,volume,fiberVolume,src,archive,zeroBank,tmp].Nodup)
    (encode : β → List (Fin (A+4))) (R B M k : ℕ) (hR : 0 < R) (hB : 0 < B)
    (hencode : ∀ x, (encode x).length = R) (fill : β) (zero : Fin (A+4))
    (matrices : List (List (List β))) (hpositive : 0 < matrices.length)
    (hrows : ∀ rows ∈ matrices, rows.length = B) (hfit : M ≤ 2^k)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hk : (S.R exponent).length = k) (hp : (S.R prefixCount).length = matrices.length)
    (hb : (S.R count).length = B) (hm : (S.R realLength).length = M) (hw : (S.R blockWidth).length = R)
    (hsrc : S.R src = (columnRows encode M fill matrices).flatten++tail)
    (hfresh : ∀ i ∈ [bits,prefixWork,prefixClock,volume,fiberVolume,archive,zeroBank,tmp], S.R i = []) :
    let V := matrices.length*(B*(2^k*R))
    let padded := (columnRows encode M fill matrices).flatMap
      (fun xs => xs++List.replicate (2^k*(B*R)-M*(B*R)) zero)++tail
    ∃ vf n, vf.user = v.user ∧ n ≤ 256*V ∧
      Exec body (prepareReturn exponent prefixCount count realLength blockWidth bits prefixWork prefixClock
        volume fiberVolume src archive zeroBank tmp zero) (mk v S) n
        (mk vf {S with R := (Function.update (Function.update (Function.update (Function.update (Function.update S.R
          bits (List.replicate k tick)) prefixWork (List.replicate (matrices.length*2^k) tick))
          volume (List.replicate R tick)) fiberVolume (List.replicate (B*R) tick)) src padded)}) := by
  dsimp only
  have hr := hreg
  regs_ne hr
  let V := matrices.length*(B*(2^k*R))
  let padded := (columnRows encode M fill matrices).flatMap
    (fun xs => xs++List.replicate (2^k*(B*R)-M*(B*R)) zero)++tail
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := resetProduct_exec (body := body) count blockWidth fiberVolume zeroBank prefixClock
    (by regs_nodup) v S (hfresh _ (by simp)) (hfresh _ (by simp))
  let S₁ : Stacks T A := {S with R := Function.update S.R fiberVolume (List.replicate (B*R) tick)}
  have he₁' : Exec body (resetProduct count blockWidth fiberVolume zeroBank prefixClock) (mk v S) n₁ (mk v₁ S₁) := by
    simpa only [hb,hw] using he₁
  have off₁ (i : Fin T) (hi : i ≠ fiberVolume) : S₁.R i = S.R i := by simp [S₁,hi]
  have h₁fiber : (S₁.R fiberVolume).length = B*R := by simp [S₁]
  have h₁real : (S₁.R realLength).length = M := by rw [off₁ realLength ‹realLength ≠ fiberVolume›]; exact hm
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := resetProduct_exec (body := body) realLength fiberVolume volume zeroBank prefixClock
    (by regs_nodup) v₁ S₁
    (by rw [off₁ zeroBank ‹fiberVolume ≠ zeroBank›.symm]; exact hfresh _ (by simp))
    (by rw [off₁ prefixClock ‹prefixClock ≠ fiberVolume›]; exact hfresh _ (by simp))
  let S₂ : Stacks T A := {S₁ with R := Function.update S₁.R volume (List.replicate (M*(B*R)) tick)}
  have he₂' : Exec body (resetProduct realLength fiberVolume volume zeroBank prefixClock) (mk v₁ S₁) n₂ (mk v₂ S₂) := by
    simpa only [h₁real,h₁fiber] using he₂
  have off₂ (i : Fin T) (hif : i ≠ fiberVolume) (hiv : i ≠ volume) : S₂.R i = S.R i := by
    simp only [S₂,Function.update_of_ne hiv]; exact off₁ i hif
  have h₂p : S₂.R prefixCount = S.R prefixCount := off₂ prefixCount ‹prefixCount ≠ fiberVolume› ‹prefixCount ≠ volume›
  have h₂bits : S₂.R bits = [] := by rw [off₂ bits ‹bits ≠ fiberVolume› ‹bits ≠ volume›]; exact hfresh _ (by simp)
  obtain ⟨v₃,hu₃,he₃⟩ := copyR_exec (body := body) prefixCount bits tmp
    ‹prefixCount ≠ bits› ‹prefixCount ≠ tmp› ‹bits ≠ tmp› (fun _ => tick) v₂ S₂
    (by rw [off₂ tmp ‹fiberVolume ≠ tmp›.symm ‹volume ≠ tmp›.symm]; exact hfresh _ (by simp))
  let S₃ : Stacks T A := {S₂ with R := Function.update S₂.R bits (List.replicate matrices.length tick)}
  have he₃' : Exec body (copyR prefixCount bits tmp (fun _ => tick)) (mk v₂ S₂) (4*matrices.length+4) (mk v₃ S₃) := by
    simpa [S₃,h₂p,h₂bits,hp,List.map_const'] using he₃
  have off₃ (i : Fin T) (hif : i ≠ fiberVolume) (hiv : i ≠ volume) (hib : i ≠ bits) : S₃.R i = S.R i := by
    simp only [S₃,Function.update_of_ne hib]; exact off₂ i hif hiv
  have hfitBytes := Nat.mul_le_mul_right (B*R) hfit
  obtain ⟨v₄,n₄,hu₄,hn₄,he₄⟩ := generatedPadFibers_exec (body := body)
    exponent fiberVolume volume prefixWork zeroBank prefixClock bits src archive tmp (by regs_nodup)
    zero (columnRows encode M fill matrices) k (B*R) (M*(B*R))
    (columnRows_row_length encode M B R fill matrices hencode hrows) hfitBytes tail v₃ S₃
    (by rw [off₃ exponent ‹exponent ≠ fiberVolume› ‹exponent ≠ volume› ‹exponent ≠ bits›]; exact hk)
    (by simp [S₃,S₂,S₁,‹bits ≠ fiberVolume›.symm,‹volume ≠ fiberVolume›.symm])
    (by simp [S₃,S₂,‹bits ≠ volume›.symm])
    (by simp [S₃,columnRows_length])
    (by rw [off₃ src ‹fiberVolume ≠ src›.symm ‹volume ≠ src›.symm ‹bits ≠ src›.symm]; exact hsrc)
    (by rw [off₃ prefixWork ‹prefixWork ≠ fiberVolume› ‹prefixWork ≠ volume› ‹bits ≠ prefixWork›.symm]; exact hfresh _ (by simp))
    (by rw [off₃ zeroBank ‹fiberVolume ≠ zeroBank›.symm ‹volume ≠ zeroBank›.symm ‹bits ≠ zeroBank›.symm]; exact hfresh _ (by simp))
    (by rw [off₃ prefixClock ‹prefixClock ≠ fiberVolume› ‹prefixClock ≠ volume› ‹bits ≠ prefixClock›.symm]; exact hfresh _ (by simp))
    (by rw [off₃ archive ‹fiberVolume ≠ archive›.symm ‹volume ≠ archive›.symm ‹bits ≠ archive›.symm]; exact hfresh _ (by simp))
    (by rw [off₃ tmp ‹fiberVolume ≠ tmp›.symm ‹volume ≠ tmp›.symm ‹bits ≠ tmp›.symm]; exact hfresh _ (by simp))
  let S₄ : Stacks T A := {S₃ with R := (Function.update (Function.update S₃.R src padded) bits [])}
  have off₄ (i : Fin T) (hif : i ≠ fiberVolume) (hiv : i ≠ volume) (hib : i ≠ bits) (his : i ≠ src) : S₄.R i = S.R i := by
    simp only [S₄,Function.update_of_ne hib,Function.update_of_ne his]; exact off₃ i hif hiv hib
  have h₄width : (S₄.R blockWidth).length = R := by
    rw [off₄ blockWidth ‹blockWidth ≠ fiberVolume› ‹blockWidth ≠ volume› ‹blockWidth ≠ bits› ‹blockWidth ≠ src›]; exact hw
  have h₄volume : (S₄.R volume).length = M*(B*R) := by
    simp [S₄,S₃,S₂,‹bits ≠ volume›.symm,‹volume ≠ src›]
  obtain ⟨v₅,hu₅,he₅⟩ := resetCopy_exec (body := body) blockWidth volume zeroBank (by regs_nodup) v₄ S₄
    (by rw [off₄ zeroBank ‹fiberVolume ≠ zeroBank›.symm ‹volume ≠ zeroBank›.symm ‹bits ≠ zeroBank›.symm ‹src ≠ zeroBank›.symm]; exact hfresh _ (by simp))
  let S₅ : Stacks T A := {S₄ with R := Function.update S₄.R volume (List.replicate R tick)}
  have he₅' : Exec body (resetCopy blockWidth volume zeroBank) (mk v₄ S₄) (2*(M*(B*R))+4*R+6) (mk v₅ S₅) := by
    simpa only [h₄width,h₄volume] using he₅
  have off₅ (i : Fin T) (hif : i ≠ fiberVolume) (hiv : i ≠ volume) (hib : i ≠ bits) (his : i ≠ src) : S₅.R i = S.R i := by
    simp only [S₅,Function.update_of_ne hiv]; exact off₄ i hif hiv hib his
  have h₅e : (S₅.R exponent).length = k := by
    rw [off₅ exponent ‹exponent ≠ fiberVolume› ‹exponent ≠ volume› ‹exponent ≠ bits› ‹exponent ≠ src›]; exact hk
  have h₅p : (S₅.R prefixCount).length = matrices.length := by
    rw [off₅ prefixCount ‹prefixCount ≠ fiberVolume› ‹prefixCount ≠ volume› ‹prefixCount ≠ bits› ‹prefixCount ≠ src›]; exact hp
  have h₅pw : S₅.R prefixWork = [] := by
    rw [off₅ prefixWork ‹prefixWork ≠ fiberVolume› ‹prefixWork ≠ volume› ‹bits ≠ prefixWork›.symm ‹prefixWork ≠ src›]
    exact hfresh _ (by simp)
  obtain ⟨v₆,n₆,hu₆,hn₆,he₆⟩ := resetDyadicWidth_exec (body := body) exponent prefixCount prefixWork zeroBank prefixClock
    (by regs_nodup) v₅ S₅
    (by rw [off₅ zeroBank ‹fiberVolume ≠ zeroBank›.symm ‹volume ≠ zeroBank›.symm ‹bits ≠ zeroBank›.symm ‹src ≠ zeroBank›.symm]; exact hfresh _ (by simp))
    (by rw [off₅ prefixClock ‹prefixClock ≠ fiberVolume› ‹prefixClock ≠ volume› ‹bits ≠ prefixClock›.symm ‹prefixClock ≠ src›]; exact hfresh _ (by simp))
  let S₆ : Stacks T A := {S₅ with R := Function.update S₅.R prefixWork (List.replicate (matrices.length*2^k) tick)}
  have he₆' : Exec body (resetDyadicWidth exponent prefixCount prefixWork zeroBank prefixClock) (mk v₅ S₅) n₆ (mk v₆ S₆) := by
    simpa only [h₅e,h₅p,Nat.mul_comm (2^k) matrices.length] using he₆
  have off₆ (i : Fin T) (hif : i ≠ fiberVolume) (hiv : i ≠ volume) (hib : i ≠ bits) (his : i ≠ src) (hip : i ≠ prefixWork) : S₆.R i = S.R i := by
    simp only [S₆,Function.update_of_ne hip]; exact off₅ i hif hiv hib his
  have h₆bits : S₆.R bits = [] := by simp [S₆,S₅,S₄,‹bits ≠ prefixWork›,‹bits ≠ volume›]
  have h₆e : S₆.R exponent = S.R exponent := off₆ exponent ‹exponent ≠ fiberVolume› ‹exponent ≠ volume› ‹exponent ≠ bits› ‹exponent ≠ src› ‹exponent ≠ prefixWork›
  obtain ⟨v₇,hu₇,he₇⟩ := copyR_exec (body := body) exponent bits tmp ‹exponent ≠ bits› ‹exponent ≠ tmp› ‹bits ≠ tmp›
    (fun _ => tick) v₆ S₆
    (by rw [off₆ tmp ‹fiberVolume ≠ tmp›.symm ‹volume ≠ tmp›.symm ‹bits ≠ tmp›.symm ‹src ≠ tmp›.symm ‹prefixWork ≠ tmp›.symm]; exact hfresh _ (by simp))
  let S₇ : Stacks T A := {S₆ with R := Function.update S₆.R bits (List.replicate k tick)}
  have he₇' : Exec body (copyR exponent bits tmp (fun _ => tick)) (mk v₆ S₆) (4*k+4) (mk v₇ S₇) := by
    simpa [S₇,h₆e,h₆bits,hk,List.map_const'] using he₇
  refine ⟨v₇,n₁+(n₂+((4*matrices.length+4)+(n₄+((2*(M*(B*R))+4*R+6)+(n₆+(4*k+4)))))),
    hu₇.trans (hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))))),?_,
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃' (Exec.seq he₄ (Exec.seq he₅' (Exec.seq he₆' he₇')))))).cast rfl ?_⟩
  · have h₁cost : n₁ ≤ B*(4*R+9)+6 := by
      simp only [hb,hw,hfresh fiberVolume (by simp),List.length_nil] at hn₁; omega
    have h₂cost : n₂ ≤ M*(4*(B*R)+9)+6 := by
      simp only [h₁real,h₁fiber,off₁ volume ‹volume ≠ fiberVolume›,hfresh volume (by simp),List.length_nil] at hn₂; omega
    have h₄cost : n₄ ≤ 64*V := by
      have hc := generatedPaddingCost_le (Nat.mul_pos hB hR)
        (show 0 < (columnRows encode M fill matrices).length by simpa only [columnRows_length] using hpositive) hfitBytes
        (n := n₄) (by nlinarith only [hn₄])
      have heq : (columnRows encode M fill matrices).length*(2^k*(B*R)) = V := by
        rw [columnRows_length]; dsimp only [V]; ring
      simpa only [heq] using hc
    have h₆cost : n₆ ≤ 4*matrices.length+4*(2^k*matrices.length)+9*k+10 := by
      simp only [h₅pw,List.length_nil,h₅e,h₅p] at hn₆
      omega
    have heq : (matrices.length*2^k)*(B*R) = V := by dsimp only [V]; ring
    have hd := dimensions_le_volume (Nat.mul_pos hpositive (Nat.two_pow_pos k)) hB hR
    rw [heq] at hd
    have hCBR : 2^k*(B*R) ≤ V := by
      have hh := Nat.mul_le_mul_right (2^k*(B*R)) (show 1 ≤ matrices.length by omega)
      simpa only [V,Nat.one_mul,Nat.mul_assoc,Nat.mul_left_comm B (2^k)] using hh
    have hMBR : M*(B*R) ≤ V := (Nat.mul_le_mul_right (B*R) hfit).trans hCBR
    have hM : M ≤ V := by
      have hh := Nat.mul_le_mul_left M (show 1 ≤ B*R from Nat.mul_pos hB hR)
      simpa only [Nat.mul_one] using hh.trans hMBR
    have hB' : B ≤ V := by
      have hh := Nat.mul_le_mul_left B (show 1 ≤ R by omega)
      have hh' : B ≤ B*R := by simpa only [Nat.mul_one] using hh
      exact hh'.trans hd.2.2
    have hP : matrices.length ≤ V := by
      have hh := Nat.mul_le_mul_left matrices.length (Nat.one_le_two_pow (n := k))
      simpa only [Nat.mul_one] using hh.trans hd.1
    have hkV : k ≤ V := bits_le_volume k matrices.length B R hpositive hB hR
    have hpos : 0 < V := by dsimp only [V]; positivity
    change n₁+(n₂+((4*matrices.length+4)+(n₄+((2*(M*(B*R))+4*R+6)+(n₆+(4*k+4)))))) ≤ 256*V
    nlinarith only [h₁cost,h₂cost,h₄cost,h₆cost,hd.1,hd.2.1,hd.2.2,hMBR,hM,hB',hP,hkV,hpos]
  · apply congrArg (mk v₇)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hib : i = bits
    · subst i
      simp [S₇,‹bits ≠ src›,‹bits ≠ fiberVolume›,‹bits ≠ volume›,‹bits ≠ prefixWork›]
    by_cases hip : i = prefixWork
    · subst i
      simp [S₇,S₆,‹bits ≠ prefixWork›.symm,‹prefixWork ≠ src›,‹prefixWork ≠ fiberVolume›,‹prefixWork ≠ volume›]
    by_cases his : i = src
    · subst i
      have hs₆ : S₆.R src = padded := by
        simp [S₆,S₅,S₄,‹prefixWork ≠ src›.symm,‹volume ≠ src›.symm,‹bits ≠ src›.symm]
      simp only [S₇,Function.update_of_ne ‹bits ≠ src›.symm,Function.update_self,hs₆,padded]
    by_cases hiv : i = volume
    · subst i
      simp [S₇,S₆,S₅,‹bits ≠ volume›.symm,‹prefixWork ≠ volume›.symm,‹volume ≠ src›,‹volume ≠ fiberVolume›]
    by_cases hif : i = fiberVolume
    · subst i
      simp [S₇,S₆,S₅,S₄,S₃,S₂,S₁,‹bits ≠ fiberVolume›.symm,‹prefixWork ≠ fiberVolume›.symm,
        ‹volume ≠ fiberVolume›.symm,‹fiberVolume ≠ src›]
    · simp only [S₇,off₆ i hif hiv hib his hip,
        Function.update_of_ne his,Function.update_of_ne hif,Function.update_of_ne hiv,
        Function.update_of_ne hip,Function.update_of_ne hib]

end IntegerMultBounds.MathlibTM2.Routing.MixedRadixReturn
