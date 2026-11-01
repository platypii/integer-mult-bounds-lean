module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedHaloLengthKeys
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOriginLoadStock
public import IntegerMultBounds.MathlibTM2.Fast.TableNativePush

/-! Retained-width key discovery is native control work with a fixed push bound. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

theorem retainedHaloLengthKeys_native :
    mnNativePushBound 3 (retainedHaloLengthKeys (P₀ := P) (Q := Q) (A := A) (U := U)) := by
  unfold retainedHaloLengthKeys preparedHaloLengthCandidates selectSixPositiveLengths
  refine ⟨⟨chirpBankLoad_native _ _ _ _,loadOriginList_native _,?_,clearWords_native_three _⟩,
    chirpBankLoad_native _ _ _ _,?_,tblCompile_native _ _,?_,?_,clearWords_native_three _⟩
  · simp [haloLengthCandidatesController,mnNativePushBound,tblCompile_native,
      moveR,moveStep,whileR,peekR,mnActPush]
  · simp [loadBinaryHeaders,loadBinaryHeader,takePrefix,transfer,scanR,transferAct,
      uclear,drainR,popDo,keepIn,moveR,moveStep,whileR,peekR,
      mnNativePushBound,mnActPush]
  · simp [countWords,countWordsBody,transfer,scanR,transferAct,keepIn,drainR,popDo,
      moveR,moveStep,whileR,peekR,pushN,mnNativePushBound,mnActPush]
  · simp [moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

theorem retainedHaloLengthKeys_exec_within (P q w s t u band a b : ℕ)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u) (hband : band ≤ s)
    (has : a ≤ s) (hbs : b ≤ s) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hsSrc : (S.R 97).length = s) (htSrc : (S.R 98).length = t) (hbSrc : (S.R 100).length = band)
    (haSrc : (S.R 111).length = a) (hbEndSrc : (S.R 113).length = b)
    (hV : (S.R 115).length = weightWorkspaceWidth P q w t u)
    (hfresh : ∀ k ∈ [(104 : Fin 117),106,86], S.R k = [])
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R k = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ retainedHaloLengthKeysCost s t band a b (weightWorkspaceWidth P q w t u) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        3*retainedHaloLengthKeysCost s t band a b (weightWorkspaceWidth P q w t u)) depth
        retainedHaloLengthKeys (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 87
          (haloPositiveLengthPackets A (weightWorkspaceWidth P q w t u) s t band a b++S.R 87))
          86 (List.replicate (IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry.haloLengthKeys s t band a b).length tick))}) := by
  obtain ⟨v',n,hu',hn,he⟩ := retainedHaloLengthKeys_exec (body := body)
    P q w s t u band a b hP hs hst hu hband has hbs hA v S hsSrc htSrc hbSrc haSrc hbEndSrc hV hfresh hblank
  exact ⟨v',n,hu',hn,mn_native_exec_within he 3 retainedHaloLengthKeys_native depth _
    (Nat.add_le_add_left (Nat.mul_le_mul_left 3 hn) _)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
