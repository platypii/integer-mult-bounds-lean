module

public import IntegerMultBounds.MathlibTM2.Routing.MixedRadixFinish

/-! A fixed non-dyadic field controller: prepare and pad only the current field,
execute its dyadic bit passes, then crop real columns and retire all work headers.
Preparation execution is proved here; complete composition is in MixedRadixRun. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.MixedRadixMove
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  FieldHeaderSetup GeneratedFiberPadding MixedRadixFinish DyadicFieldMove PaddedFieldLayout FieldBoundaryStock
variable {T Q A : ℕ} {P U : Type}

/-- Original prefix and spectator counts generate the row clock. Padding's
counter is retired before that tape becomes the full dyadic fiber-volume header. -/
def prepareMove
    (exponent prefixCount count realLength blockWidth bits prefixWork prefixClock volume fiberVolume src archive zeroBank tmp : Fin T)
    (zero : Fin (A+4)) : Pr P T Q A U :=
  .seq (resetProduct prefixCount count bits zeroBank prefixClock)
    (.seq (resetProduct realLength blockWidth volume zeroBank prefixClock)
      (.seq (generatedPadFibers exponent blockWidth volume fiberVolume zeroBank prefixClock bits src archive tmp zero)
        (.seq (resetDyadicWidth exponent blockWidth volume zeroBank prefixClock)
          (.seq (resetProduct count volume fiberVolume zeroBank prefixClock)
            (.seq (copyR exponent bits tmp (fun _ => tick))
              (copyR prefixCount prefixWork tmp (fun _ => tick)))))))

/-- Sixteen tapes suffice, including five retained dimension masters and the
source. Program size is independent of all field lengths and the bit count. -/
def moveField
    (exponent prefixCount count realLength blockWidth bits prefixWork prefixClock clock volume fiberVolume src archive zeroBank oneBank tmp : Fin T)
    (zero : Fin (A+4)) : Pr P T Q A U :=
  .seq (prepareMove exponent prefixCount count realLength blockWidth bits prefixWork prefixClock
    volume fiberVolume src archive zeroBank tmp zero)
    (.seq (fieldMove bits prefixWork prefixClock count clock volume fiberVolume src archive zeroBank oneBank tmp)
      (finishMove exponent realLength prefixCount prefixWork prefixClock clock volume fiberVolume
        src archive zeroBank oneBank tmp bits))

theorem prepareMove_pushBound
    (exponent prefixCount count realLength blockWidth bits prefixWork prefixClock volume fiberVolume src archive zeroBank tmp : Fin T)
    (zero : Fin (A+4)) :
    mnNativePushBound 2 (prepareMove (P := P) (Q := Q) (U := U)
      exponent prefixCount count realLength blockWidth bits prefixWork prefixClock volume fiberVolume src archive zeroBank tmp zero) := by
  simp only [prepareMove,mnNativePushBound]
  refine ⟨resetProduct_pushBound _ _ _ _ _,resetProduct_pushBound _ _ _ _ _,
    generatedPadFibers_pushBound _ _ _ _ _ _ _ _ _ _ _,resetDyadicWidth_pushBound _ _ _ _ _,
    resetProduct_pushBound _ _ _ _ _,?_,?_⟩
  all_goals simp [copyR,copyStep,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

variable {β : Type} {body : P → Pr P T Q A U}

theorem prepareMove_exec
    (exponent prefixCount count realLength blockWidth bits prefixWork prefixClock volume fiberVolume src archive zeroBank tmp : Fin T)
    (hreg : [exponent,prefixCount,count,realLength,blockWidth,bits,prefixWork,prefixClock,volume,fiberVolume,src,archive,zeroBank,tmp].Nodup)
    (encode : β → List (Fin (A+4))) (R B M k : ℕ) (hR : 0 < R) (hB : 0 < B)
    (hencode : ∀ x, (encode x).length = R) (zero : Fin (A+4))
    (matrices : List (List (List β))) (hpositive : 0 < matrices.length)
    (hrows : ∀ rows ∈ matrices, rows.length = B)
    (hlen : ∀ rows ∈ matrices, ∀ xs ∈ rows, xs.length = M) (hfit : M ≤ 2^k)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hk : (S.R exponent).length = k) (hp : (S.R prefixCount).length = matrices.length)
    (hb : (S.R count).length = B) (hm : (S.R realLength).length = M) (hw : (S.R blockWidth).length = R)
    (hsrc : S.R src = (sourceRows encode matrices).flatten++tail)
    (hfresh : ∀ i ∈ [bits,prefixWork,prefixClock,volume,fiberVolume,archive,zeroBank,tmp], S.R i = []) :
    let V := matrices.length*(B*(2^k*R))
    let padded := (sourceRows encode matrices).flatMap (fun xs => xs++List.replicate (2^k*R-M*R) zero)++tail
    ∃ vf n, vf.user = v.user ∧ n ≤ 256*V ∧
      Exec body (prepareMove exponent prefixCount count realLength blockWidth bits prefixWork prefixClock
        volume fiberVolume src archive zeroBank tmp zero) (mk v S) n
        (mk vf {S with R := (Function.update (Function.update (Function.update (Function.update (Function.update S.R
          bits (List.replicate k tick)) prefixWork (List.replicate matrices.length tick))
          volume (List.replicate (2^k*R) tick)) fiberVolume (List.replicate (B*(2^k*R)) tick)) src padded)}) := by
  dsimp only
  have hr := hreg
  regs_ne hr
  let V := matrices.length*(B*(2^k*R))
  let padded := (sourceRows encode matrices).flatMap (fun xs => xs++List.replicate (2^k*R-M*R) zero)++tail
  have hrowCount : (sourceRows encode matrices).length = matrices.length*B := by
    rw [sourceRows,List.length_flatMap,List.map_eq_replicate_iff.mpr ?_,List.sum_replicate,smul_eq_mul]
    intro rows hm
    simpa only [List.length_map] using hrows rows hm
  have hrowBytes : ∀ xs ∈ sourceRows encode matrices, xs.length = M*R := by
    intro xs hx
    obtain ⟨rows,hr,hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨ys,hy,rfl⟩ := List.mem_map.mp hx
    rw [List.length_flatMap,List.map_eq_replicate_iff.mpr (by intro x _; exact hencode x),
      List.sum_replicate,smul_eq_mul,hlen rows hr ys hy]
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := resetProduct_exec (body := body) prefixCount count bits zeroBank prefixClock
    (by regs_nodup) v S (hfresh _ (by simp)) (hfresh _ (by simp))
  let S₁ : Stacks T A := {S with R := Function.update S.R bits (List.replicate (matrices.length*B) tick)}
  have he₁' : Exec body (resetProduct prefixCount count bits zeroBank prefixClock) (mk v S) n₁ (mk v₁ S₁) := by
    simpa only [hp,hb] using he₁
  have off₁ (i : Fin T) (hi : i ≠ bits) : S₁.R i = S.R i := by simp [S₁,hi]
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := resetProduct_exec (body := body) realLength blockWidth volume zeroBank prefixClock
    (by regs_nodup) v₁ S₁
    (by rw [off₁ zeroBank ‹bits ≠ zeroBank›.symm]; exact hfresh _ (by simp))
    (by rw [off₁ prefixClock ‹bits ≠ prefixClock›.symm]; exact hfresh _ (by simp))
  let S₂ : Stacks T A := {S₁ with R := Function.update S₁.R volume (List.replicate (M*R) tick)}
  have he₂' : Exec body (resetProduct realLength blockWidth volume zeroBank prefixClock) (mk v₁ S₁) n₂ (mk v₂ S₂) := by
    simpa only [off₁ realLength ‹realLength ≠ bits›,off₁ blockWidth ‹blockWidth ≠ bits›,hm,hw] using he₂
  have off₂ (i : Fin T) (hib : i ≠ bits) (hiv : i ≠ volume) : S₂.R i = S.R i := by
    simp only [S₂,Function.update_of_ne hiv]; exact off₁ i hib
  have hfitBytes := Nat.mul_le_mul_right R hfit
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := generatedPadFibers_exec (body := body)
    exponent blockWidth volume fiberVolume zeroBank prefixClock bits src archive tmp
    (by regs_nodup) zero (sourceRows encode matrices) k R (M*R) hrowBytes hfitBytes tail v₂ S₂
    (by rw [off₂ exponent ‹exponent ≠ bits› ‹exponent ≠ volume›]; exact hk)
    (by rw [off₂ blockWidth ‹blockWidth ≠ bits› ‹blockWidth ≠ volume›]; exact hw)
    (by simp [S₂]) (by rw [hrowCount]; simp [S₂,S₁,‹bits ≠ volume›])
    (by rw [off₂ src ‹bits ≠ src›.symm ‹volume ≠ src›.symm]; exact hsrc)
    (by rw [off₂ fiberVolume ‹bits ≠ fiberVolume›.symm ‹volume ≠ fiberVolume›.symm]; exact hfresh _ (by simp))
    (by rw [off₂ zeroBank ‹bits ≠ zeroBank›.symm ‹volume ≠ zeroBank›.symm]; exact hfresh _ (by simp))
    (by rw [off₂ prefixClock ‹bits ≠ prefixClock›.symm ‹prefixClock ≠ volume›]; exact hfresh _ (by simp))
    (by rw [off₂ archive ‹bits ≠ archive›.symm ‹volume ≠ archive›.symm]; exact hfresh _ (by simp))
    (by rw [off₂ tmp ‹bits ≠ tmp›.symm ‹volume ≠ tmp›.symm]; exact hfresh _ (by simp))
  let S₃ : Stacks T A := {S₂ with R := (Function.update (Function.update S₂.R src padded) bits [])}
  have off₃ (i : Fin T) (hib : i ≠ bits) (hiv : i ≠ volume) (his : i ≠ src) : S₃.R i = S.R i := by
    simp only [S₃,Function.update_of_ne hib,Function.update_of_ne his]; exact off₂ i hib hiv
  obtain ⟨v₄,n₄,hu₄,hn₄,he₄⟩ := resetDyadicWidth_exec (body := body) exponent blockWidth volume zeroBank prefixClock
    (by regs_nodup) v₃ S₃
    (by rw [off₃ zeroBank ‹bits ≠ zeroBank›.symm ‹volume ≠ zeroBank›.symm ‹src ≠ zeroBank›.symm]; exact hfresh _ (by simp))
    (by rw [off₃ prefixClock ‹bits ≠ prefixClock›.symm ‹prefixClock ≠ volume› ‹prefixClock ≠ src›]; exact hfresh _ (by simp))
  let S₄ : Stacks T A := {S₃ with R := Function.update S₃.R volume (List.replicate (2^k*R) tick)}
  have he₄' : Exec body (resetDyadicWidth exponent blockWidth volume zeroBank prefixClock) (mk v₃ S₃) n₄ (mk v₄ S₄) := by
    simpa only [off₃ exponent ‹exponent ≠ bits› ‹exponent ≠ volume› ‹exponent ≠ src›,
      off₃ blockWidth ‹blockWidth ≠ bits› ‹blockWidth ≠ volume› ‹blockWidth ≠ src›,hk,hw] using he₄
  have off₄ (i : Fin T) (hib : i ≠ bits) (hiv : i ≠ volume) (his : i ≠ src) : S₄.R i = S.R i := by
    simp only [S₄,Function.update_of_ne hiv]; exact off₃ i hib hiv his
  obtain ⟨v₅,n₅,hu₅,hn₅,he₅⟩ := resetProduct_exec (body := body) count volume fiberVolume zeroBank prefixClock
    (by regs_nodup) v₄ S₄
    (by rw [off₄ zeroBank ‹bits ≠ zeroBank›.symm ‹volume ≠ zeroBank›.symm ‹src ≠ zeroBank›.symm]; exact hfresh _ (by simp))
    (by rw [off₄ prefixClock ‹bits ≠ prefixClock›.symm ‹prefixClock ≠ volume› ‹prefixClock ≠ src›]; exact hfresh _ (by simp))
  let S₅ : Stacks T A := {S₄ with R := Function.update S₄.R fiberVolume (List.replicate (B*(2^k*R)) tick)}
  have h₄count : (S₄.R count).length = B := by
    rw [off₄ count ‹count ≠ bits› ‹count ≠ volume› ‹count ≠ src›]; exact hb
  have h₄width : (S₄.R volume).length = 2^k*R := by simp [S₄]
  have h₄fiber : S₄.R fiberVolume = [] := by
    rw [off₄ fiberVolume ‹bits ≠ fiberVolume›.symm ‹volume ≠ fiberVolume›.symm ‹fiberVolume ≠ src›]
    exact hfresh _ (by simp)
  have he₅' : Exec body (resetProduct count volume fiberVolume zeroBank prefixClock) (mk v₄ S₄) n₅ (mk v₅ S₅) := by
    simpa only [h₄count,h₄width] using he₅
  have off₅ (i : Fin T) (hib : i ≠ bits) (hiv : i ≠ volume) (his : i ≠ src) (hif : i ≠ fiberVolume) : S₅.R i = S.R i := by
    simp only [S₅,Function.update_of_ne hif]; exact off₄ i hib hiv his
  have h₅bits : S₅.R bits = [] := by simp [S₅,S₄,S₃,‹bits ≠ fiberVolume›,‹bits ≠ volume›]
  have h₅e : S₅.R exponent = S.R exponent := off₅ exponent ‹exponent ≠ bits› ‹exponent ≠ volume› ‹exponent ≠ src› ‹exponent ≠ fiberVolume›
  obtain ⟨v₆,hu₆,he₆⟩ := copyR_exec (body := body) exponent bits tmp
    ‹exponent ≠ bits› ‹exponent ≠ tmp› ‹bits ≠ tmp› (fun _ => tick) v₅ S₅
    (by rw [off₅ tmp ‹bits ≠ tmp›.symm ‹volume ≠ tmp›.symm ‹src ≠ tmp›.symm ‹fiberVolume ≠ tmp›.symm]; exact hfresh _ (by simp))
  let S₆ : Stacks T A := {S₅ with R := Function.update S₅.R bits (List.replicate k tick)}
  have he₆' : Exec body (copyR exponent bits tmp (fun _ => tick)) (mk v₅ S₅) (4*k+4) (mk v₆ S₆) := by
    simpa [S₆,h₅e,h₅bits,hk,List.map_const'] using he₆
  have off₆ (i : Fin T) (hib : i ≠ bits) (hiv : i ≠ volume) (his : i ≠ src) (hif : i ≠ fiberVolume) : S₆.R i = S.R i := by
    simp only [S₆,Function.update_of_ne hib]; exact off₅ i hib hiv his hif
  have h₆p : S₆.R prefixCount = S.R prefixCount := off₆ prefixCount ‹prefixCount ≠ bits› ‹prefixCount ≠ volume› ‹prefixCount ≠ src› ‹prefixCount ≠ fiberVolume›
  have h₆pw : S₆.R prefixWork = [] := by
    rw [off₆ prefixWork ‹bits ≠ prefixWork›.symm ‹prefixWork ≠ volume› ‹prefixWork ≠ src› ‹prefixWork ≠ fiberVolume›]
    exact hfresh _ (by simp)
  obtain ⟨v₇,hu₇,he₇⟩ := copyR_exec (body := body) prefixCount prefixWork tmp
    ‹prefixCount ≠ prefixWork› ‹prefixCount ≠ tmp› ‹prefixWork ≠ tmp› (fun _ => tick) v₆ S₆
    (by rw [off₆ tmp ‹bits ≠ tmp›.symm ‹volume ≠ tmp›.symm ‹src ≠ tmp›.symm ‹fiberVolume ≠ tmp›.symm]; exact hfresh _ (by simp))
  let S₇ : Stacks T A := {S₆ with R := Function.update S₆.R prefixWork (List.replicate matrices.length tick)}
  have he₇' : Exec body (copyR prefixCount prefixWork tmp (fun _ => tick)) (mk v₆ S₆) (4*matrices.length+4) (mk v₇ S₇) := by
    simpa [S₇,h₆p,h₆pw,hp,List.map_const'] using he₇
  refine ⟨v₇,n₁+(n₂+(n₃+(n₄+(n₅+((4*k+4)+(4*matrices.length+4)))))),
    hu₇.trans (hu₆.trans (hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))))),?_,
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ (Exec.seq he₄' (Exec.seq he₅' (Exec.seq he₆' he₇')))))).cast rfl ?_⟩
  · have h₃cost : n₃ ≤ 64*V := by
      have hc := generatedPaddingCost_le hR (show 0 < (sourceRows encode matrices).length by rw [hrowCount]; exact Nat.mul_pos hpositive hB)
        hfitBytes (n := n₃) (by nlinarith only [hn₃])
      simpa only [hrowCount,V,Nat.mul_assoc] using hc
    have h₁cost : n₁ ≤ matrices.length*(4*B+9)+6 := by
      simp only [hp,hb,hfresh bits (by simp),List.length_nil] at hn₁
      omega
    have h₂cost : n₂ ≤ M*(4*R+9)+6 := by
      simp only [off₁ realLength ‹realLength ≠ bits›,off₁ blockWidth ‹blockWidth ≠ bits›,
        off₁ volume ‹bits ≠ volume›.symm,hm,hw,hfresh volume (by simp),List.length_nil] at hn₂
      omega
    have h₄v : (S₃.R volume).length = M*R := by simp [S₃,S₂,‹bits ≠ volume›.symm,‹volume ≠ src›]
    have h₄cost : n₄ ≤ 2*(M*R)+4*R+4*(2^k*R)+9*k+10 := by
      simpa only [h₄v,off₃ exponent ‹exponent ≠ bits› ‹exponent ≠ volume› ‹exponent ≠ src›,
        off₃ blockWidth ‹blockWidth ≠ bits› ‹blockWidth ≠ volume› ‹blockWidth ≠ src›,hk,hw] using hn₄
    have h₅cost : n₅ ≤ B*(4*(2^k*R)+9)+6 := by
      simp only [h₄count,h₄width,h₄fiber,List.length_nil] at hn₅
      omega
    have hd := dimensions_le_volume hpositive hB (Nat.mul_pos (Nat.two_pow_pos k) hR)
    change matrices.length ≤ V ∧ 2^k*R ≤ V ∧ B*(2^k*R) ≤ V at hd
    have hkV : k ≤ V := bits_le_volume k matrices.length B R hpositive hB hR
    have hPB : matrices.length*B ≤ V := by
      have hh := Nat.mul_le_mul_left (matrices.length*B) (show 1 ≤ 2^k*R from Nat.mul_pos (Nat.two_pow_pos k) hR)
      simpa only [Nat.mul_one,V,Nat.mul_assoc] using hh
    have hMR : M*R ≤ V := hfitBytes.trans hd.2.1
    have hM : M ≤ V := by
      have hh := Nat.mul_le_mul_left M (show 1 ≤ R by omega)
      simpa only [Nat.mul_one] using hh.trans hMR
    have hRV : R ≤ V := by
      have hh := Nat.mul_le_mul_right R (Nat.one_le_two_pow (n := k))
      have hh' : R ≤ 2^k*R := by simpa only [Nat.one_mul] using hh
      exact hh'.trans hd.2.1
    have hBV : B ≤ V := by
      have hh := Nat.mul_le_mul_left B (show 1 ≤ 2^k*R from Nat.mul_pos (Nat.two_pow_pos k) hR)
      have hh' : B ≤ B*(2^k*R) := by simpa only [Nat.mul_one] using hh
      exact hh'.trans hd.2.2
    have hpos : 0 < V := by dsimp only [V]; positivity
    change n₁+(n₂+(n₃+(n₄+(n₅+((4*k+4)+(4*matrices.length+4)))))) ≤ 256*V
    nlinarith only [h₁cost,h₂cost,h₃cost,h₄cost,h₅cost,hd.1,hd.2.1,hd.2.2,hkV,hPB,hMR,hM,hRV,hBV,hpos]
  · apply congrArg (mk v₇)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hip : i = prefixWork
    · subst i
      simp [S₇,‹prefixWork ≠ src›,‹prefixWork ≠ fiberVolume›,‹prefixWork ≠ volume›]
    by_cases his : i = src
    · subst i
      have hs₆ : S₆.R src = padded := by
        simp [S₆,S₅,S₄,S₃,‹bits ≠ src›.symm,‹fiberVolume ≠ src›.symm,‹volume ≠ src›.symm]
      simp only [S₇,Function.update_of_ne ‹prefixWork ≠ src›.symm,Function.update_self,hs₆,padded]
    by_cases hif : i = fiberVolume
    · subst i
      simp [S₇,S₆,S₅,‹prefixWork ≠ fiberVolume›.symm,‹bits ≠ fiberVolume›.symm,‹fiberVolume ≠ src›]
    by_cases hiv : i = volume
    · subst i
      simp [S₇,S₆,S₅,S₄,‹prefixWork ≠ volume›.symm,‹bits ≠ volume›.symm,‹volume ≠ fiberVolume›,‹volume ≠ src›]
    by_cases hib : i = bits
    · subst i
      simp [S₇,S₆,‹bits ≠ prefixWork›,‹bits ≠ src›,‹bits ≠ volume›,‹bits ≠ fiberVolume›]
    · simp only [S₇,off₆ i hib hiv his hif,
        Function.update_of_ne his,Function.update_of_ne hif,Function.update_of_ne hiv,
        Function.update_of_ne hip,Function.update_of_ne hib]

end IntegerMultBounds.MathlibTM2.Routing.MixedRadixMove
