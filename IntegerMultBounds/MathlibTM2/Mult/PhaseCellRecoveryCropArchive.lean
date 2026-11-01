module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareRecoveryCropHeaders
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellIntervalArchiveAccuracy
public import IntegerMultBounds.MathlibTM2.Host.NativePushBoundMono

/-! A generated crop/archive lifecycle from numerical masters and ordinary
geometric dimensions. All generated controls and scratch restore. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 19 Q A U}

def recoveryCropArchive : Pr P 19 Q A U :=
  .seq prepareRecoveryCropHeaders (packedCoreArchiveLoop 10 8 9 11 12 13 14 15 7 6 16 17 18)

def recoveryCropArchiveCost (q a b offset rows N : ℕ) : ℕ :=
  prepareRecoveryCropHeadersCost q a b offset rows N+
    (N*(packedCoreArchiveStepCost offset rows (b-a) (2*q+8)+3)+2)

theorem recoveryCropArchive_exec (q a b offset rows : ℕ)
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
    ∃ v', ∃ G : Stacks 19 A, ∃ n, v'.user = v.user ∧ n ≤ recoveryCropArchiveCost q a b offset rows Ds.length ∧
      Exec body recoveryCropArchive (Host.mk v S) n (Host.mk v' G) ∧
      G.R 11 = tail ∧ G.R 12 = (Ds.reverse.map (fun D => cstream A (2*q+8)
        (packedInterval (a+offset) rows D))).flatten++S.R 12 ∧
      G.R 10 = [] ∧ G.inp = S.inp ∧ G.out = S.out ∧ G.L = S.L ∧
      (∀ k, k ≠ 11 → k ≠ 12 → k ≠ 10 → G.R k = (recoveryCropHeaderState q a b offset rows Ds.length S).R k) ∧
      List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn (haloVertices s (a+offset) (a+offset+rows))
        (packedIntervalRead q (2*q+8) (a+offset)
          (cstream A (2*q+8) (packedInterval (a+offset) rows D)++S.R 12)) z ε) Zs.reverse Ds.reverse := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := prepareRecoveryCropHeaders_exec (body := body)
    q a b offset rows Ds.length v S hq ha hb hoffset hrows hN
    (by intro k hk; apply hblank; simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢; tauto)
  let F := recoveryCropHeaderState q a b offset rows Ds.length S
  obtain ⟨v₂,G,n₂,hu₂,hn₂,he₂,hs,hd,hc,hI,hO,hL,hframe,haccuracy⟩ :=
    packedCoreArchiveLoop_interval_accurate_exec (body := body) 10 8 9 11 12 13 14 15 7 6 16 17 18
      (by decide) v₁ F q (2*q+8) a (b-a) offset rows hfit hpart Zs Ds ε tail hgood
      (by simpa [F,recoveryCropHeaderState] using hsrc)
      (by simp [F,recoveryCropHeaderState]) (by simp [F,recoveryCropHeaderState])
      (by simp [F,recoveryCropHeaderState]) (by simp [F,recoveryCropHeaderState])
      (by simp [F,recoveryCropHeaderState])
      (by
        intro k hk
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
        all_goals simp [F,recoveryCropHeaderState,hblank 13 (by simp),hblank 14 (by simp),
          hblank 15 (by simp),hblank 16 (by simp),hblank 17 (by simp),hblank 18 (by simp)])
  refine ⟨v₂,G,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,Exec.seq he₁ he₂,
    hs,?_,hc,hI,hO,hL,hframe,?_⟩
  · simpa [F,recoveryCropHeaderState] using hd
  · simpa [F,recoveryCropHeaderState] using haccuracy

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
