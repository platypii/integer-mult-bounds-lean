module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOrdinaryCouplingCoefficientInterval

/-! Generate one coefficient page in the disjoint extended replica bank. The
native headers, binary geometry, retained masters and row queues survive. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def prepareReplicaCouplingPage {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) : Pr P T Q A U :=
  embProg placement.bank Empty.elim (ordinaryCouplingCoefficientInterval (P := Empty))

theorem prepareReplicaCouplingPage_exec {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) {V precision q w s t u band a b : ℕ} [NeZero s]
    (hA : 4 ≤ A) (hprecision : 13 ≤ precision) (hst : s < t) (hab : a ≤ b) (hb : b ≤ s) (ha : a < s)
    (hwide : 8*(t+1)^2+4*band+8 < 2^V) (hfitV : a+((b-a)+2*band)+s < 2^V)
    (raw : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hready : CouplingReady precision q w s t u band a b raw (embStk weightCacheCoreReg (embStk plan.solver S)))
    (hmeta : CouplingIntervalMetadata V s t band a b a (b-a) (embStk placement.bank S))
    (h107 : S.R (placement.bank 107) = [])
    (hfresh : ∀ k ∈ [(135 : Fin 168),139,140,143,166], S.R (placement.bank k) = []) :
    let xs := couplingCoefficientPageInterval precision q s t u band a b a (b-a)
    ∃ v' F n, v'.user = v.user ∧ n ≤ sharedCouplingCoefficientIntervalCost precision q w s t u band a b V ∧
      Exec body (prepareReplicaCouplingPage placement) (mk v S) n (mk v' F) ∧
      embStk placement.bank F = sharedCouplingPageState band w xs (embStk placement.bank S) ∧
      embStk plan.gather F = embStk plan.gather S ∧
      embStk weightCacheCoreReg (embStk plan.solver F) = embStk weightCacheCoreReg (embStk plan.solver S) ∧
      CouplingIntervalMetadata V s t band a b a (b-a) (embStk placement.bank F) ∧
      F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      (∀ k, (∀ i : Fin 168, placement.bank i ≠ k) → F.R k = S.R k) := by
  dsimp only
  let B := embStk placement.bank S
  have hreadyB : CouplingReady precision q w s t u band a b raw (embStk packedCellCoreReg B) := by
    exact (placement.native_view S).symm ▸ hready
  obtain ⟨vi,n,hu,hn,he⟩ := ordinaryCouplingCoefficientInterval_exec
    (body := fun p : Empty => nomatch p) hA hprecision hst hab hb ha hwide hfitV raw
    (embDn placement.bank v) B hreadyB hmeta h107 hfresh
  obtain ⟨v',_,hu',he'⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    placement.bank_injective (fun p : Empty => nomatch p) he v rfl S rfl
  let xs := couplingCoefficientPageInterval precision q s t u band a b a (b-a)
  let F := embOvr placement.bank (sharedCouplingPageState band w xs B).get S
  have hview : embStk placement.bank F = sharedCouplingPageState band w xs B :=
    embStk_ovr placement.bank_injective _ S
  have hleft : F.L = S.L := embOvr_right_left S _
  have hframe (k : Fin 168) (hk : k ∉ ([(135 : Fin 168),138,139,140,143])) :
      (sharedCouplingPageState band w xs B).R k = B.R k := by
    have hn : k ≠ 140 ∧ k ≠ 135 ∧ k ≠ 138 ∧ k ≠ 139 ∧ k ≠ 143 := by
      exact ⟨(fun he => hk (by simp [he])),(fun he => hk (by simp [he])),
        (fun he => hk (by simp [he])),(fun he => hk (by simp [he])),(fun he => hk (by simp [he]))⟩
    simp only [sharedCouplingPageState,Function.update_of_ne hn.1,Function.update_of_ne hn.2.1,
      Function.update_of_ne hn.2.2.1,Function.update_of_ne hn.2.2.2.1,Function.update_of_ne hn.2.2.2.2]
  refine ⟨v',F,n,hu'.trans hu,hn,he',hview,?_,?_,?_,hleft,rfl,rfl,?_⟩
  · refine Stacks.ext rfl rfl ?_ ?_ <;> funext k
    · exact (placement.gather_frame _ S k).1
    · exact (placement.gather_frame _ S k).2
  · rw [← placement.native_view F,hview]
    change embStk packedCellCoreReg (sharedCouplingPageState band w xs B) = _
    rw [sharedCouplingPage_native]
    exact placement.native_view S
  · rw [hview]
    apply hmeta.of_frame (hframe 163 (by decide))
    intro k hk
    apply hframe
    simp only [couplingIntervalPorts,List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro k hk
    exact (embOvr_off _ S hk).2

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
