module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWidenEncodedPrefix
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedPublicationPlan
public import IntegerMultBounds.MathlibTM2.Host.NativePushBoundMono

/-! Compose actual signed widening with prepared scatter. No intermediate
readiness or execution premise is supplied by the caller. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.LayerMachine
variable {T Q A s L : ℕ} {P U : Type} {src dst : Fin T}

theorem widenedPublication_exec (body : P → Pr P T Q A U)
    (plan : PreparedPublicationPlan T src dst) (windows : PublicationWindows s L)
    (wide width count work saved tmp extra : Fin T)
    (hreg : [wide,width,count,src,work,saved,tmp,extra].Nodup)
    (w W : ℕ) (hw : 1 ≤ w) (hwidth : w ≤ W)
    (rows : List (List GaussianInt)) (hlen : rows.length = windows.origins.length)
    (hrows : ∀ row ∈ rows, row.length = L)
    (E sourceTail outputTail borrowed : List (Fin (A+4))) (hE : E.length = s*W)
    (v : HS T Q A U) (S : Stacks T A) (hready : plan.Ready windows W 0 borrowed S)
    (hwide : (S.R wide).length = W) (hword : (S.R width).length = w)
    (hcount : (S.R count).length = rows.flatten.length*w)
    (hsrc : S.R src = cstream A w rows.flatten++sourceTail)
    (hdst : S.R dst = E++outputTail)
    (hblank : ∀ r ∈ [work,saved,tmp,extra], S.R r = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ widenPackedPrefixCost w W rows.flatten.length+retireCountedLineCost 0 W+72*s*W+31 ∧
      Exec body (.seq (widenPackedPrefix wide width count src work saved tmp extra) plan.program)
        (mk v S) n (mk v' {S with R := (Function.update (Function.update S.R src sourceTail) dst
          (scatterRows (L*W) E (cstream A W (rows.flatten.map (symZ w))) (windows.gaps W)++outputTail))}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := widenEncodedPrefix_exec (body := body) hreg w W hw hwidth
    rows.flatten sourceTail v S hwide hword hcount hsrc hblank
  let rs := rows.map (List.map (symZ w))
  have hflat : rs.flatten = rows.flatten.map (symZ w) := by simp [rs,List.map_flatten]
  let M : Stacks T A := {S with R := Function.update S.R src (cstream A W rs.flatten++sourceTail)}
  have hr : plan.Ready windows W 0 borrowed M := hready.of_frame (by
    intro i hi
    exact Function.update_of_ne (plan.support_off hi).1 _ _)
  have hl : ∀ row ∈ rs, row.length = L := by
    intro row hrow
    change row ∈ rows.map (List.map (symZ w)) at hrow
    obtain ⟨xs,hxs,rfl⟩ := List.mem_map.mp hrow
    simpa only [List.length_map] using hrows xs hxs
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := plan.exec body windows W 0 (hw.trans hwidth) rs rs
    (by simpa [rs] using hlen) hl hl (by simp) (by simp)
    E sourceTail outputTail borrowed hE v₁ M hr (by simp [M])
    (by simpa [M,plan.src_ne_dst.symm] using hdst)
  have he₁' : Exec body (widenPackedPrefix wide width count src work saved tmp extra)
      (mk v S) n₁ (mk v₁ M) := by simpa only [M,hflat] using he₁
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,?_,?_⟩
  · simp only [Nat.zero_mul] at hn₂
    omega
  · simpa only [M,Function.update_idem,hflat] using Exec.seq he₁' he₂


open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main

theorem widenPackedPrefix_native (wide width count src work saved tmp extra : Fin T) :
    mnNativePushBound 13 (widenPackedPrefix (P := P) (Q := Q) (A := A) (U := U)
      wide width count src work saved tmp extra) := by
  simp [widenPackedPrefix,generatedWidenPackets,withWidthDifference,transformPrefix,
    topPass,topWords,topWidenWord,topDupF,Shift.counted,Shift.copyStep,ucopy,usub,dropTop,umulSym,transfer,transferAct,
    moveR,moveStep,uclear,scanR,drainR,popDo,keepIn,whileR,peekR,pushN,
    mnNativePushBound,mnActPush]

/-- Widening and scatter share one bound on every intermediate configuration. -/
theorem widenedPublication_within (body : P → Pr P T Q A U)
    (plan : PreparedPublicationPlan T src dst) (wide width count work saved tmp extra : Fin T)
    (v v' : HS T Q A U) (S F : Stacks T A) (n bill depth : ℕ)
    (he : Exec body (.seq (widenPackedPrefix wide width count src work saved tmp extra) plan.program)
      (mk v S) n (mk v' F)) (hn : n ≤ bill) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+13*bill) depth
      (.seq (widenPackedPrefix wide width count src work saved tmp extra) plan.program)
      (mk v S) n (mk v' F) := by
  have hp : mnNativePushBound 2 (plan.program (P := P) (Q := Q) (A := A) (U := U)) :=
    preparedWindowPublication_native _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  exact mn_native_exec_within he 13
    ⟨widenPackedPrefix_native _ _ _ _ _ _ _ _,mnNativePushBound_mono (by decide) hp⟩
    depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
