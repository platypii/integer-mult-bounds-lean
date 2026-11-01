module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedRecoveryCrop
public import IntegerMultBounds.MathlibTM2.Host.NativePushBoundMono

/-! Crop and retire complex packets while retaining the generated row-symbol
header for normalization. All other generated controls and scratch restore. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 19 Q A U}

def recoveryCropWithWidth : Pr P 19 Q A U :=
  .seq recoveryCropArchive (clearWords [6,7,8])

def recoveryCropWithWidthCost (q a b offset rows N : ℕ) : ℕ :=
  prepareRecoveryCropHeadersCost q a b offset rows N+
    (N*(packedCoreArchiveStepCost offset rows (b-a) (2*q+8)+3)+2)+
    (2*((2*q+8)+(b-a)+offset*(2*q+8))+7)

/-- Retaining this header merely moves its existing cleanup bill to the next
stage; it introduces no extra setup or erasure work. -/
theorem recoveryCropWithWidthCost_retire (q a b offset rows N : ℕ) :
    recoveryCropWithWidthCost q a b offset rows N+(2*(rows*(2*q+8))+2) =
      generatedRecoveryCropCost q a b offset rows N := by
  unfold recoveryCropWithWidthCost generatedRecoveryCropCost
  omega

theorem recoveryCropWithWidth_exec (q a b offset rows : ℕ)
    (hfit : a+(b-a) ≤ s) (hpart : offset+rows ≤ b-a)
    (Zs : List (ZMod s → ℂ)) (Ds : List (ZMod s → GaussianInt)) (ε : ℝ)
    (tail : List (Fin (A+4))) (v : HS 19 Q A U) (S : Stacks 19 A)
    (hq : (S.R 0).length = q) (ha : (S.R 1).length = a) (hb : (S.R 2).length = b)
    (hoffset : (S.R 3).length = offset) (hrows : (S.R 4).length = rows)
    (hN : (S.R 5).length = Ds.length)
    (hblank : ∀ k ∈ ([(6 : Fin 19),7,8,9,10,13,14,15,16,17,18]), S.R k = [])
    (hsrc : S.R 11 = (Ds.map (fun D => cstream A (2*q+8) (packedInterval a (b-a) D))).flatten++tail)
    (hgood : List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn (haloVertices s a (a+(b-a)))
      (packedIntervalRead q (2*q+8) a (cstream A (2*q+8) (packedInterval a (b-a) D)++tail)) z ε) Zs Ds) :
    ∃ v' n, v'.user = v.user ∧ n ≤ recoveryCropWithWidthCost q a b offset rows Ds.length ∧
      Exec body recoveryCropWithWidth (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update (Function.update S.R 9 (List.replicate (rows*(2*q+8)) tick)) 11 tail) 12
          ((Ds.reverse.map (fun D => cstream A (2*q+8)
            (packedInterval (a+offset) rows D))).flatten++S.R 12))}) ∧
      List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn (haloVertices s (a+offset) (a+offset+rows))
        (packedIntervalRead q (2*q+8) (a+offset)
          (cstream A (2*q+8) (packedInterval (a+offset) rows D)++S.R 12)) z ε) Zs.reverse Ds.reverse := by
  obtain ⟨v₂,G,n₂,hu₂,hn₂,he₂,hs,hd,hc,hI,hO,hL,hframe,haccuracy⟩ := recoveryCropArchive_exec
    (body := body) q a b offset rows hfit hpart Zs Ds ε tail v S hq ha hb hoffset hrows hN hblank hsrc hgood
  let F := recoveryCropHeaderState q a b offset rows Ds.length S
  have hG (k : Fin 19) (hk : k ∈ ([(6 : Fin 19),7,8])) : G.R k = F.R k := by
    apply hframe
    all_goals
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl <;> decide
  obtain ⟨v₃,hu₃,he₃⟩ := clearWords_exec (body := body) [6,7,8] (by decide) v₂ G
  have hcost : 2*(([(6 : Fin 19),7,8]).map (fun k => (G.R k).length)).sum+
      2*([(6 : Fin 19),7,8]).length+1 =
      2*((2*q+8)+(b-a)+offset*(2*q+8))+7 := by
    simp [hG 6 (by simp),hG 7 (by simp),hG 8 (by simp),F,recoveryCropHeaderState]
    omega
  rw [hcost] at he₃
  let output := (Ds.reverse.map (fun D => cstream A (2*q+8) (packedInterval (a+offset) rows D))).flatten++S.R 12
  have hdst : G.R 12 = output := by simpa [F,recoveryCropHeaderState,output] using hd
  have h9 : G.R 9 = List.replicate (rows*(2*q+8)) tick := by
    rw [hframe 9 (by decide) (by decide) (by decide)]
    simp [recoveryCropHeaderState]
  have hfinal : {G with R := fun k => if k ∈ ([(6 : Fin 19),7,8]) then [] else G.R k} =
      {S with R := Function.update (Function.update (Function.update S.R 9 (List.replicate (rows*(2*q+8)) tick)) 11 tail) 12 output} := by
    refine Stacks.ext ?_ ?_ ?_ ?_
    · exact hI
    · exact hO
    · exact hL
    funext k
    change (if k ∈ ([(6 : Fin 19),7,8]) then [] else G.R k) =
      Function.update (Function.update (Function.update S.R 9 (List.replicate (rows*(2*q+8)) tick)) 11 tail) 12 output k
    by_cases hk : k ∈ ([(6 : Fin 19),7,8])
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl <;> simp [hblank 6 (by simp),hblank 7 (by simp),hblank 8 (by simp)]
    · rw [ite_eq_right hk]
      by_cases hp' : k = 9
      · subst k; simpa using h9
      ·
        by_cases hs' : k = 11
        · subst k; simpa using hs
        · by_cases hd' : k = 12
          · subst k; simpa using hdst
          · rw [Function.update_of_ne hd',Function.update_of_ne hs',Function.update_of_ne hp']
            by_cases hc' : k = 10
            · subst k; simpa [hblank 10 (by simp)] using hc
            · rw [hframe k hs' hd' hc']
              simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hk
              simp [recoveryCropHeaderState,Function.update_of_ne hk.1,Function.update_of_ne hk.2.1,
                Function.update_of_ne hk.2.2,Function.update_of_ne hp',Function.update_of_ne hc']
  rw [hfinal] at he₃
  refine ⟨v₃,n₂+(2*((2*q+8)+(b-a)+offset*(2*q+8))+7),
    hu₃.trans hu₂,?_,Exec.seq he₂ he₃,?_⟩
  · unfold recoveryCropWithWidthCost
    unfold recoveryCropArchiveCost at hn₂
    omega
  · simpa [F,recoveryCropHeaderState] using haccuracy

omit [NeZero s] in
theorem recoveryCropWithWidth_native :
    mnNativePushBound 8 (recoveryCropWithWidth (P := P) (Q := Q) (A := A) (U := U)) := by
  change mnNativePushBound 8 (.seq (.seq prepareRecoveryCropHeaders
    (packedCoreArchiveLoop 10 8 9 11 12 13 14 15 7 6 16 17 18)) (clearWords [6,7,8]))
  refine ⟨⟨prepareRecoveryCropHeaders_native,?_⟩,?_⟩
  · exact mnNativePushBound_mono (by decide : 2 ≤ 8)
      (packedCoreArchiveLoop_interval_native 10 8 9 11 12 13 14 15 7 6 16 17 18)
  · simp [clearWords,uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]

omit [NeZero s] in
theorem recoveryCropWithWidth_within_stock
    {v v' : HS 19 Q A U} {S F : Stacks 19 A} {n q a b offset rows N : ℕ}
    (hex : Exec body recoveryCropWithWidth (Host.mk v S) n (Host.mk v' F))
    (hn : n ≤ recoveryCropWithWidthCost q a b offset rows N) (depth : ℕ) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
      8*recoveryCropWithWidthCost q a b offset rows N) depth recoveryCropWithWidth
      (Host.mk v S) n (Host.mk v' F) :=
  mn_native_exec_within hex 8 recoveryCropWithWidth_native depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
