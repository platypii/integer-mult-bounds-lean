module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBinaryRibbonMask
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingIntervalMetadata
public import IntegerMultBounds.MathlibTM2.Host.OrderedMove

/-! Generate coupling masks once for either source mode. Recovery retains its
existing true-source wrapper; both modes use the same target guard and cost. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def initializeCouplingMasks (boundary : Bool) : Pr P 168 Q A U :=
  .seq (.seq loadRibbonMaskBank (ribbonMaskHost boundary))
    (.seq (moveRightOrdered 158 0 159)
      (.seq (placedBinaryRecoveryGuardInterval true) (moveRightOrdered 136 0 161)))

def initializeRecoveryMasks : Pr P 168 Q A U :=
  .seq (.seq loadRibbonMaskBank (ribbonMaskHost true))
    (.seq (moveRightOrdered 158 0 159)
      (.seq (placedBinaryRecoveryGuardInterval true) (moveRightOrdered 136 0 161)))

def initializeRecoveryMasksCost (V N band : ℕ) :=
  (152*V+153+((32*(N+2*band)+2)*tblC V 1+68*V+2*(N+2*band)+72))+
    (4*(N+2*band)+4)+(144*V+145+((46*N+2)*tblC V 1+66*V+2*N+70))+(4*N+4)

theorem initializeCouplingMasks_exec (boundary : Bool) {s t band a b origin N V : ℕ} [NeZero s]
    (hst : s < t) (ha : a ≤ s) (hb : b ≤ s) (hband : band ≤ s) (hfit : origin+N ≤ s)
    (hwide : 8*(t+1)^2+4*band+8 < 2^V) (hfitV : origin+(N+2*band)+s < 2^V)
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (hgeometry : CouplingIntervalMetadata V s t band a b origin N S)
    (hclean : ∀ k : Fin 168, k.val < 63 → S.R k = [])
    (h136 : S.R 136 = []) (h158 : S.R 158 = []) (h159 : S.R 159 = []) (h161 : S.R 161 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ initializeRecoveryMasksCost V N band ∧
      Exec body (initializeCouplingMasks boundary) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 159
          ((couplingRibbonFlags (s := s) boundary t band a b origin N).map (fun flag => pairSym A flag flag)))
          161 (recoveryGuardIntervalSymbols true A s t (2*band) a b origin N))}) := by
  let rv := couplingIntervalValue s t band a b origin N
  let gv := fun k : Fin 117 => rv (intervalGuardPlacement k)
  have htV : t < 2^V := by nlinarith [Nat.zero_le (t*t)]
  have hbound (k : Fin 168) : rv k < 2^V := couplingIntervalValue_bound hfit ha hb hst hfitV htV k
  have hblank : ∀ r, S.R (ribbonTableReg r) = [] := by
    intro r
    exact hclean _ ((ribbonTableReg_range r).trans (by decide))
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := binaryRibbonMask_exec (body := body) boundary rv
    (by simp [rv,couplingIntervalValue]) (by simp [rv,couplingIntervalValue])
    (by simp [rv,couplingIntervalValue]) (by simp [rv,couplingIntervalValue])
    (by simp [rv,couplingIntervalValue]) (by simp [rv,couplingIntervalValue])
    (by simp [rv,couplingIntervalValue]) hst ha hb hband hfit hfitV (by omega)
    (fun i => hbound _) v S hgeometry.width hgeometry.ribbon hblank
  let xs := (couplingRibbonFlags (s := s) boundary t band a b origin N).map (fun flag => pairSym A flag flag)
  have hxs : xs.length = N+2*band := by
    dsimp only [xs,List.length_map]
    rw [couplingRibbonFlags_eq_map boundary hst band a b origin N hb hband hfit]
    simp
  let B : Stacks 168 A := {S with R := Function.update S.R 158 xs}
  have he₁' : Exec body (.seq loadRibbonMaskBank (ribbonMaskHost boundary)) (mk v S) m₁ (mk v₁ B) := by
    simpa only [h158,List.append_nil] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := moveRightOrdered_exec (body := body) 158 0 159 (by decide) (by decide) (by decide)
    v₁ B (by simpa [B] using hclean 0 (by decide))
  let J : Stacks 168 A := {S with R := Function.update S.R 159 xs}
  have he₂' : Exec body (moveRightOrdered 158 0 159) (mk v₁ B) (4*(N+2*band)+4) (mk v₂ J) := by
    refine he₂.cast (by simp [B,hxs]) ?_
    apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk158 : k = 158 <;> by_cases hk159 : k = 159 <;> simp [B,J,h158,h159,hk158,hk159]
  have hgeometryJ : CouplingIntervalMetadata V s t band a b origin N J := by
    apply hgeometry.of_frame (by simp [J])
    intro k hk
    have hn : k ≠ 159 := by
      simp only [couplingIntervalPorts,List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simp [J,hn]
  have hguardBlank : ∀ r, (embStk intervalGuardPlacement J).R (intervalGuardReg r) = [] := by
    intro r
    have hr := intervalGuardReg_range r
    have hn : intervalGuardReg r ≠ (109 : Fin 117) := by
      intro he; have hv := congrArg Fin.val he; omega
    change J.R (intervalGuardPlacement (intervalGuardReg r)) = []
    have hk : (intervalGuardPlacement (intervalGuardReg r)).val < 63 := by
      simp [intervalGuardPlacement,hn,show (intervalGuardReg r).val < 96 by omega]
      omega
    simp only [J,Function.update_of_ne (show intervalGuardPlacement (intervalGuardReg r) ≠ 159 by intro he; have := congrArg Fin.val he; omega)]
    exact hclean _ hk
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃⟩ := placedBinaryRecoveryGuardInterval_exec (body := body) (s := s) (t := t) (band := 2*band)
    (a := a) (b := b) (origin := origin) (N := N) (V := V) true gv
    (by simp [gv,rv,intervalGuardPlacement,couplingIntervalValue])
    (by simp [gv,rv,intervalGuardPlacement,couplingIntervalValue])
    (by simp [gv,rv,intervalGuardPlacement,couplingIntervalValue])
    (by simp [gv,rv,intervalGuardPlacement,couplingIntervalValue])
    (by simp [gv,rv,intervalGuardPlacement,couplingIntervalValue])
    (by simp [gv,rv,intervalGuardPlacement,couplingIntervalValue])
    (by simp [gv,rv,intervalGuardPlacement,couplingIntervalValue])
    hfit (NeZero.pos s) hst ha hb (by omega) (fun i => hbound _)
    v₂ J hgeometryJ.width hgeometryJ.guard hguardBlank
  let ys := recoveryGuardIntervalSymbols true A s t (2*band) a b origin N
  let K : Stacks 168 A := {J with R := Function.update J.R 136 ys}
  have he₃' : Exec body (placedBinaryRecoveryGuardInterval true) (mk v₂ J) m₃ (mk v₃ K) := by
    simpa [K,J,h136,ys] using he₃
  obtain ⟨v₄,hu₄,he₄⟩ := moveRightOrdered_exec (body := body) 136 0 161 (by decide) (by decide) (by decide)
    v₃ K (by simpa [K,J] using hclean 0 (by decide))
  refine ⟨v₄,m₁+((4*(N+2*band)+4)+(m₃+(4*N+4))),hu₄.trans (hu₃.trans (hu₂.trans hu₁)),
    (by unfold initializeRecoveryMasksCost; omega),?_⟩
  refine (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃' he₄))).cast (by simp [K,ys]) ?_
  apply congrArg (mk v₄)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hk136 : k = 136 <;> by_cases hk159 : k = 159 <;> by_cases hk161 : k = 161 <;>
    simp [K,J,h136,h161,ys,xs,hk136,hk159,hk161]


theorem initializeRecoveryMasks_exec {s t band a b origin N V : ℕ} [NeZero s]
    (hst : s < t) (ha : a ≤ s) (hb : b ≤ s) (hband : band ≤ s) (hfit : origin+N ≤ s)
    (hwide : 8*(t+1)^2+4*band+8 < 2^V) (hfitV : origin+(N+2*band)+s < 2^V)
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (hgeometry : CouplingIntervalMetadata V s t band a b origin N S)
    (hclean : ∀ k : Fin 168, k.val < 63 → S.R k = [])
    (h136 : S.R 136 = []) (h158 : S.R 158 = []) (h159 : S.R 159 = []) (h161 : S.R 161 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ initializeRecoveryMasksCost V N band ∧
      Exec body initializeRecoveryMasks (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 159
          ((couplingRibbonFlags (s := s) true t band a b origin N).map (fun flag => pairSym A flag flag)))
          161 (recoveryGuardIntervalSymbols true A s t (2*band) a b origin N))}) := by
  exact initializeCouplingMasks_exec (body := body) true hst ha hb hband hfit hwide hfitV v S
    hgeometry hclean h136 h158 h159 h161

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
