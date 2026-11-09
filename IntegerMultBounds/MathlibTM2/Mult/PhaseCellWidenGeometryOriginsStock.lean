module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWidenGeometryOrigins
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedWeightWidth

/-! Geometry packet widening has linear native traffic, with no arithmetic
reserve multiplied by the number of origins. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Host.SS IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem widenGeometryOrigins_native :
    mnNativePushBound 18 (widenGeometryOrigins (P₀ := P₀) (Q := Q) (A := A) (U := U)) := by
  simp [widenGeometryOrigins,prepareOriginWidening,generateWeightWidth_native,
    widenOriginPackets,widenOriginPacket,takePrefix,padCopy,padStep,eachSym,
    transfer,transferAct,scanR,drainR,popDo,keepIn,popPush,uclear,
    moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

theorem widenGeometryOrigins_exec_within (P q w t u : ℕ)
    (xs : List ℕ) (hfit : ∀ x ∈ xs, x < 2^haloGeometryWidth t w)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tail : List (Fin (A+4)))
    (hP : (S.R 114).length = P) (hq : (S.R 112).length = q)
    (hw : (S.R 94).length = w) (ht : (S.R 98).length = t) (hu : (S.R 99).length = u)
    (hV : (S.R 115).length = haloGeometryWidth t w)
    (hcount : (S.R 116).length = xs.length)
    (hsrc : S.R 109 = xs.flatMap (binSyms (haloGeometryWidth t w))++tail)
    (hfresh : ∀ k ∈ [(0 : Fin 117),1,2,3,4,19,20,21,22,23,24,104,25,26,27], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ widenGeometryOriginsCost P q w t u xs.length ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          18*widenGeometryOriginsCost P q w t u xs.length)
        depth widenGeometryOrigins (mk v S) n
        (mk v' {S with R := (Function.update S.R 109
          (xs.flatMap (binSyms (weightWorkspaceWidth P q w t u))++tail))})) := by
  obtain ⟨v',n,hu',hn,he⟩ := widenGeometryOrigins_exec (body := body) P q w t u xs hfit
    v S tail hP hq hw ht hu hV hcount hsrc hfresh
  refine ⟨v',n,hu',hn,?_⟩
  intro depth
  exact mn_native_exec_within he 18 widenGeometryOrigins_native depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
