module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedCouplingCoefficientInterval

/-! Reuse shared coefficient generation through its involutive header view.
Ordinary headers and all scratch are restored; only the shared page is retained. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def ordinaryCouplingCoefficientInterval : Pr P 168 Q A U :=
  embProg sharedCouplingReg Empty.elim (sharedCouplingCoefficientInterval (P := Empty))

theorem sharedCouplingCore_involutive_view (S : Stacks 168 A) :
    embStk sharedCouplingCoreReg (embStk sharedCouplingReg S) = embStk packedCellCoreReg S := by
  refine Stacks.ext rfl rfl ?_ ?_
  · funext i
    exact congrArg S.L (sharedCouplingReg_involutive (packedCellCoreReg i))
  · funext i
    exact congrArg S.R (sharedCouplingReg_involutive (packedCellCoreReg i))

theorem ordinaryCouplingCoefficientInterval_exec {V precision q w s t u band a b : ℕ} [NeZero s]
    (hA : 4 ≤ A) (hprecision : 13 ≤ precision) (hst : s < t) (hab : a ≤ b) (hb : b ≤ s) (ha : a < s)
    (hwide : 8*(t+1)^2+4*band+8 < 2^V) (hfitV : a+((b-a)+2*band)+s < 2^V)
    (raw : List (Fin (A+4))) (v : HS 168 Q A U) (S : Stacks 168 A)
    (hready : CouplingReady precision q w s t u band a b raw (embStk packedCellCoreReg S))
    (hmeta : CouplingIntervalMetadata V s t band a b a (b-a) S)
    (h107 : S.R 107 = [])
    (hfresh : ∀ k ∈ [(135 : Fin 168),139,140,143,166], S.R k = []) :
    let xs := couplingCoefficientPageInterval precision q s t u band a b a (b-a)
    ∃ v' m, v'.user = v.user ∧ m ≤ sharedCouplingCoefficientIntervalCost precision q w s t u band a b V ∧
      Exec body ordinaryCouplingCoefficientInterval (mk v S) m
        (mk v' (sharedCouplingPageState band w xs S)) := by
  dsimp only
  let T := embStk sharedCouplingReg S
  have hreadyT : CouplingReady precision q w s t u band a b raw (embStk sharedCouplingCoreReg T) := by
    rw [sharedCouplingCore_involutive_view]
    exact hready
  obtain ⟨vi,m,hu,hm,he⟩ := sharedCouplingCoefficientInterval_exec
    (body := fun p : Empty => nomatch p) hA hprecision hst hab hb ha hwide hfitV raw
    (embDn sharedCouplingReg v) T hreadyT (couplingIntervalMetadata_shared hmeta)
    (by simpa [T,embStk,sharedCouplingReg,packedCellCoreReg] using hready.lower)
    (by simpa [T,embStk,sharedCouplingReg] using h107)
    (by intro k hk
        have hfix : sharedCouplingReg k = k := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide
        simpa only [T,embStk_R,hfix] using hfresh k hk)
  obtain ⟨v',_,hu',he'⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    sharedCouplingReg_injective (fun p : Empty => nomatch p) he v rfl S rfl
  refine ⟨v',m,hu'.trans hu,hm,he'.cast rfl ?_⟩
  apply congrArg (mk v')
  let xs := couplingCoefficientPageInterval precision q s t u band a b a (b-a)
  let T₁ : Stacks 168 A := {T with R := Function.update T.R 140 (List.replicate (2*band+1) tick)}
  let T₂ : Stacks 168 A := {T₁ with R := Function.update T₁.R 135 []}
  let T₃ : Stacks 168 A := {T₂ with R := Function.update T₂.R 138 (cstream A w xs++T.R 138)}
  let T₄ : Stacks 168 A := {T₃ with R := Function.update T₃.R 139 (List.replicate xs.length tick)}
  change embOvr sharedCouplingReg ({T₄ with R := Function.update T₄.R 143 []} : Stacks 168 A).get S = _
  rw [embOvr_updR sharedCouplingReg_injective T₄ S 143,
    embOvr_updR sharedCouplingReg_injective T₃ S 139,
    embOvr_updR sharedCouplingReg_injective T₂ S 138,
    embOvr_updR sharedCouplingReg_injective T₁ S 135,
    embOvr_updR sharedCouplingReg_injective T S 140,embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
