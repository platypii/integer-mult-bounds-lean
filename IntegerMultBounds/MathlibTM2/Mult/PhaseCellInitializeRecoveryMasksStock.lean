module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBinaryRibbonMask
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingIntervalMetadata
public import IntegerMultBounds.MathlibTM2.Host.ClosedProgramStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializeRecoveryMasks

/-! Generate both recovery masks once, retaining natural-order streams in the cache ports. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {U : Type} {body : Empty → Pr Empty 168 Q A U}

theorem initializeCouplingMasks_exec_within (boundary : Bool) {s t band a b origin N V : ℕ} [NeZero s]
    (hst : s < t) (ha : a ≤ s) (hb : b ≤ s) (hband : band ≤ s) (hfit : origin+N ≤ s)
    (hwide : 8*(t+1)^2+4*band+8 < 2^V) (hfitV : origin+(N+2*band)+s < 2^V)
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (hgeometry : CouplingIntervalMetadata V s t band a b origin N S)
    (hclean : ∀ k : Fin 168, k.val < 63 → S.R k = [])
    (h136 : S.R 136 = []) (h158 : S.R 158 = []) (h159 : S.R 159 = []) (h161 : S.R 161 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ initializeRecoveryMasksCost V N band ∧
      ∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          mnProgPush (initializeCouplingMasks boundary (P := Empty) (Q := Q) (A := A) (U := U))*initializeRecoveryMasksCost V N band)
        depth (initializeCouplingMasks boundary) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 159
          ((couplingRibbonFlags (s := s) boundary t band a b origin N).map (fun flag => pairSym A flag flag)))
          161 (recoveryGuardIntervalSymbols true A s t (2*band) a b origin N))}) := by
  obtain ⟨v',m,hu,hm,he⟩ := initializeCouplingMasks_exec (body := body) boundary
    hst ha hb hband hfit hwide hfitV v S hgeometry hclean h136 h158 h159 h161
  refine ⟨v',m,hu,hm,?_⟩
  intro depth
  exact mn_native_exec_within he _ (WordCmd.empty_native (initializeCouplingMasks boundary)) depth _
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ hm) _)

theorem initializeRecoveryMasks_exec_within {s t band a b origin N V : ℕ} [NeZero s]
    (hst : s < t) (ha : a ≤ s) (hb : b ≤ s) (hband : band ≤ s) (hfit : origin+N ≤ s)
    (hwide : 8*(t+1)^2+4*band+8 < 2^V) (hfitV : origin+(N+2*band)+s < 2^V)
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (hgeometry : CouplingIntervalMetadata V s t band a b origin N S)
    (hclean : ∀ k : Fin 168, k.val < 63 → S.R k = [])
    (h136 : S.R 136 = []) (h158 : S.R 158 = []) (h159 : S.R 159 = []) (h161 : S.R 161 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ initializeRecoveryMasksCost V N band ∧
      ∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          mnProgPush (initializeRecoveryMasks (P := Empty) (Q := Q) (A := A) (U := U))*initializeRecoveryMasksCost V N band)
        depth initializeRecoveryMasks (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 159
          ((couplingRibbonFlags (s := s) true t band a b origin N).map (fun flag => pairSym A flag flag)))
          161 (recoveryGuardIntervalSymbols true A s t (2*band) a b origin N))}) := by
  exact initializeCouplingMasks_exec_within (body := body) true hst ha hb hband hfit hwide hfitV
    v S hgeometry hclean h136 h158 h159 h161

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
