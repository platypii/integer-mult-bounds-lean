module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPeriodicCouplingWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPeriodicCouplingPage

/-! Execute width and coefficient-page preparation from the factor supplier's
restored bank. Every physical premise is derived from its between-call invariant. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv ScalarPlacement

theorem periodicPreparedPage_exec {Q A V precision stage q l s t u band W N : ℕ} [NeZero s]
    {P U : Type} {body : P → Pr P 242 Q A U}
    (hA : 4 ≤ A) (hprecision : 13 ≤ precision) (hst : s < t)
    (hwide : 8*(t+1)^2+4*band+8 < 2^V) (hfitV : (s+2*band)+s < 2^V)
    (v : HS 242 Q A U) (S : Stacks 242 A)
    (h : PackedHaloBetweenInputs precision stage q l s t u band 0 s V (2*q+8) W N
      (extendStacks (by decide) S)) :
    let e : Fin 168 → Fin 242 := Fin.castLE (by decide)
    let xs := couplingCoefficientPageInterval precision q s t u band 0 s 0 s
    let F := periodicCouplingPageBank band (2*q+8) xs (periodicCouplingWidthBank q S)
    ∃ v' n, v'.user = v.user ∧
      n ≤ (8*q+9)+sharedCouplingCoefficientIntervalCost precision q (2*q+8) s t u band 0 s V ∧
      Exec body (.seq (generateWordWidth 119 130 135)
        (embProg e Empty.elim sharedCouplingCoefficientInterval)) (mk v S) n (mk v' F) ∧
      PackedPreparedBank q (2*q+8) W N F ∧
      ∀ bo hf df, PackedBoundaryFactorPages bo hf df S → PackedBoundaryFactorPages bo hf df F := by
  dsimp only
  obtain ⟨v₁,hu₁,he₁,hready⟩ := periodicCouplingWidth_exec (body := body) v S h
  let e : Fin 168 → Fin 242 := Fin.castLE (by decide)
  let B := periodicCouplingWidthBank q S
  have hview : embStk packedRecoveryRuntimeReg (extendStacks (by decide : 242 ≤ 248) S) =
      embStk e S := by
    refine Stacks.ext rfl rfl ?_ ?_
    all_goals
      funext i
      have hi := i.isLt
      simp [e,embStk,packedRecoveryRuntimeReg,extendStacks,show i.val < 242 by omega]; rfl
  have hmeta := h.headers.geometry
  rw [hview] at hmeta
  simp only [Nat.sub_zero] at hmeta
  have hmetaB : CouplingIntervalMetadata V s t band 0 s 0 s (embStk e B) := by
    constructor
    · simpa [B,e,embStk,periodicCouplingWidthBank] using hmeta.width
    · intro k hk
      have hn : e k ≠ 130 := by
        simp only [couplingIntervalPorts,List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      simpa [B,embStk,periodicCouplingWidthBank,hn] using hmeta.encoded k hk
  have h107 : B.R 107 = [] := by
    have hh : S.R 107 = [] := h.native 107 (by decide) (by decide)
    simpa [B,periodicCouplingWidthBank] using hh
  have hfresh : ∀ k ∈ ([135,139,140,143,166] : List (Fin 242)), B.R k = [] := by
    have hc : ([135,139,140,143,166] : List (Fin 242)).all (fun k => decide
        (Fin.castLE (by decide : 242 ≤ 248) k ∈
          ([125,127,128,129,130,131,133,134,135,136,138,139,140,143,153,158,166,167] : List (Fin 248)) ∧
          k ≠ 130)) = true := by decide +kernel
    intro k hk
    obtain ⟨hport,hne⟩ := of_decide_eq_true (List.all_eq_true.mp hc k hk)
    have hh := h.scratch (Fin.castLE (by decide : 242 ≤ 248) k) hport
    simpa [B,periodicCouplingWidthBank,hne,extendStacks,k.isLt] using hh
  obtain ⟨v₂,n,hu₂,hn,he₂⟩ := periodicCouplingPage_exec (body := body) hA hprecision hst hwide hfitV
    (S.R 110) v₁ B hready hmetaB h107 hfresh
  have hbank := h.bank
  simp only [packedBoundaryRecoveryBase,embStk_extendStacks] at hbank
  refine ⟨v₂,(8*q+9)+n,hu₂.trans hu₁,Nat.add_le_add_left hn _,Exec.seq he₁ he₂,
    periodicCouplingPageBank_bank (periodicCouplingWidth_bank hbank),?_⟩
  intro bo hf df hpages
  exact periodicCouplingPageBank_factorPages (periodicCouplingWidth_factorPages hpages)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
