module

public import IntegerMultBounds.MathlibTM2.Host.RightWrites
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedCouplingCoefficientInterval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundarySolveWorkspace

/-! Generate the full periodic coefficient page beside the retained factors.
The existing shared-header generator works without interval separation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv ScalarPlacement

def periodicCouplingPageBank {A : ℕ} (band w : ℕ) (xs : List GaussianInt)
    (S : Stacks 242 A) : Stacks 242 A :=
  {S with R := Function.update (Function.update (Function.update (Function.update (Function.update S.R
    140 (List.replicate (2*band+1) tick)) 135 []) 138 (cstream A w xs++S.R 138))
    139 (List.replicate xs.length tick)) 143 []}

private theorem periodicCouplingPageBank_frame {A band w : ℕ} (xs : List GaussianInt)
    (S : Stacks 242 A) (k : Fin 242) (hk : k ∉ ([135,138,139,140,143] : List (Fin 242))) :
    (periodicCouplingPageBank band w xs S).R k = S.R k := by
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hk
  simp [periodicCouplingPageBank,hk.1,hk.2.1,hk.2.2.1,hk.2.2.2.1,hk.2.2.2.2]

theorem periodicCouplingPageBank_bank {A band q w W N : ℕ} {xs : List GaussianInt}
    {S : Stacks 242 A} (h : PackedPreparedBank q w W N S) :
    PackedPreparedBank q w W N (periodicCouplingPageBank band w xs S) := by
  apply h.of_runtime_frame (F := periodicCouplingPageBank band w xs S) rfl
  · intro k hk
    apply periodicCouplingPageBank_frame
    simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff]
    omega
  · exact periodicCouplingPageBank_frame xs S 119 (by decide)
  · intro k hk _
    apply periodicCouplingPageBank_frame
    simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff]
    omega

theorem periodicCouplingPageBank_factorPages {A band w : ℕ} {xs : List GaussianInt}
    {S : Stacks 242 A} {bo hf df : List (Fin (A+4))} (h : PackedBoundaryFactorPages bo hf df S) :
    PackedBoundaryFactorPages bo hf df (periodicCouplingPageBank band w xs S) := by
  apply h.of_solution_frame
  intro k hk _
  apply periodicCouplingPageBank_frame
  simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff]
  omega

theorem periodicCouplingPage_exec {Q A V precision q w s t u band : ℕ} [NeZero s]
    {P U : Type} {body : P → Pr P 242 Q A U}
    (hA : 4 ≤ A) (hprecision : 13 ≤ precision) (hst : s < t)
    (hwide : 8*(t+1)^2+4*band+8 < 2^V) (hfitV : (s+2*band)+s < 2^V)
    (raw : List (Fin (A+4))) (v : HS 242 Q A U) (S : Stacks 242 A)
    (hready : CouplingReady precision q w s t u band 0 s raw
      (embStk sharedCouplingCoreReg (embStk (Fin.castLE (by decide : 168 ≤ 242)) S)))
    (hmeta : CouplingIntervalMetadata V s t band 0 s 0 s
      (embStk (Fin.castLE (by decide : 168 ≤ 242)) S))
    (h107 : S.R 107 = [])
    (hfresh : ∀ k ∈ ([135,139,140,143,166] : List (Fin 242)), S.R k = []) :
    let e : Fin 168 → Fin 242 := Fin.castLE (by decide)
    let xs := couplingCoefficientPageInterval precision q s t u band 0 s 0 s
    ∃ v' n, v'.user = v.user ∧
      n ≤ sharedCouplingCoefficientIntervalCost precision q w s t u band 0 s V ∧
      Exec body (embProg e Empty.elim sharedCouplingCoefficientInterval) (mk v S) n
        (mk v' (periodicCouplingPageBank band w xs S)) := by
  dsimp only
  let e : Fin 168 → Fin 242 := Fin.castLE (by decide)
  have hinj : Function.Injective e := by
    intro i j he
    exact Fin.ext (congrArg (fun k : Fin 242 => k.val) he)
  have h141 : S.R 141 = [] := List.eq_nil_of_length_eq_zero (by
    simpa [embStk,sharedCouplingCoreReg,sharedCouplingReg,packedCellCoreReg] using hready.lower)
  obtain ⟨v₁,n,hu₁,hn,he₁⟩ := sharedCouplingCoefficientInterval_exec
    (body := fun f : Empty => nomatch f) hA hprecision hst (by omega) (by omega) (NeZero.pos s)
    hwide (by simpa only [Nat.sub_zero,Nat.zero_add] using hfitV) raw (embDn e v) (embStk e S)
    hready (by simpa only [Nat.sub_zero] using hmeta)
    (by change (S.R 141).length = 0; rw [h141]; rfl) h107
    (by intro k hk
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl
        all_goals exact hfresh _ (by decide))
  obtain ⟨v₂,hv₂,hu₂,he₂⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim) hinj
    (fun f => nomatch f) he₁ v rfl S rfl
  refine ⟨v₂,n,hu₂.trans hu₁,hn,he₂.cast rfl ?_⟩
  apply congrArg (mk v₂)
  let xs := couplingCoefficientPageInterval precision q s t u band 0 s 0 s
  change embOvr e (writeRight
    [(140,List.replicate (2*band+1) tick),(135,[]),
      (138,cstream A w xs++(embStk e S).R 138),(139,List.replicate xs.length tick),(143,[])]
    (embStk e S)).get S = periodicCouplingPageBank band w xs S
  rw [embOvr_writeRight_view hinj]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
