module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializeHaloLengthKeys
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseKeyRuntime
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellConditionalHaloPreparationStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedHaloLengthKeysStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedWeightWidth
public import IntegerMultBounds.MathlibTM2.Host.NativePushBoundMono

/-! The six-candidate key controller and ordinary header routing are native setup.
The selected classes retain their separate shared numerical reserves. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem prepareHaloLengthKeys_native :
    mnNativePushBound 18 (prepareHaloLengthKeys (P₀ := P₀) (Q := Q) (A := A) (U := U)) := by
  refine ⟨?_,generateWeightWidth_native,mnNativePushBound_mono (by decide) retainedHaloLengthKeys_native⟩
  simp [generateRuntimeWidth,umul,umulSym,scanR,drainR,popDo,keepIn,pushN,
    moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

theorem initializeHaloLengthKeys_native :
    mnNativePushBound 18 (initializeHaloLengthKeys (P₀ := P₀) (Q := Q) (A := A) (U := U)) := by
  refine ⟨mnNativePushBound_mono (by decide) installHaloGroupHeaders_native,
    embProg_native groupReg id _ prepareHaloLengthKeys_native,?_,?_⟩
  · simp [installKeyRuntime,ucopy,umulSym,scanR,drainR,popDo,keepIn,pushN,
      moveR,moveStep,whileR,peekR,clearWords,uclear,mnNativePushBound,mnActPush]
  · exact mnNativePushBound_mono (by decide : 0 ≤ 18)
      (show mnNativePushBound 0 (releaseHaloGroupHeaders (P := P₀)) from
        ⟨clearWords_native_zero _,clearWords_native_zero _⟩)

theorem releaseKeyRuntime_native :
    mnNativePushBound 0 (releaseKeyRuntime (P₀ := P₀) (Q := Q) (A := A) (U := U)) :=
  clearWords_native_zero _

theorem initializeHaloLengthKeys_exec_within (P N q l s t u band a b : ℕ)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hband : band ≤ s) (has : a ≤ s) (hbs : b ≤ s) (hA : 4 ≤ A) (v : HS 144 Q A U) (S : Stacks 144 A)
    (hmasters : ∀ r ∈ groupHeaderCopies,
      (S.R r.1).length = groupHeaderValue P N q l s t u band 0 r.1)
    (haMaster : (S.R 141).length = a) (hbMaster : (S.R 142).length = b)
    (hleft : ∀ k : Fin 144, k.val < 117 → S.L k = [])
    (hblank : ∀ k : Fin 144, k.val < 117 → k ≠ 93 → k ≠ 110 → S.R k = [])
    (hfresh : ∀ k ∈ [(125 : Fin 144),127,130,133,138], S.R k = []) :
    let w := 2*q+8
    let V := weightWorkspaceWidth P q w t u
    ∃ v' n, v'.user = v.user ∧ n ≤ initializeHaloLengthKeysCost P N q l s t u band a b ∧
      (∀ depth, ExecWithin (embTab groupReg body)
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          18*initializeHaloLengthKeysCost P N q l s t u band a b)
        depth initializeHaloLengthKeys (mk v S) n
        (mk v' { S with R := (initializedKeyRuntimeR S.R V w
          (haloLengthKeys s t band a b).length (haloPositiveLengthPackets A V s t band a b)) })) := by
  obtain ⟨v',n,hu',hn,he⟩ := initializeHaloLengthKeys_exec (body := body)
    P N q l s t u band a b hP hs hst hu hband has hbs hA v S
    hmasters haMaster hbMaster hleft hblank hfresh
  exact ⟨v',n,hu',hn,fun depth =>
    mn_native_exec_within he 18 initializeHaloLengthKeys_native depth _ (by omega)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
