module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputTableLoad
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterchangeHeaderStock

/-! Retire the live variable words and width header of a restored input table,
preserving the numerical output and all retained caller words. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A n : ℕ} {P U : Type}

def inputTableWords (rg : TblR n → Fin T) : List (Fin T) := rg .wr :: List.ofFn (fun i => rg (.v i))

theorem retireInputTable_exec_within (body : P → Pr P T Q A U)
    (rg : TblR n → Fin T) (hrg : Function.Injective rg) (input : Fin n → Fin T)
    (D : ℕ) (value : Fin T → ℕ) (k : Fin T) (hoff : ∀ r, rg r ≠ k) (ys : List (Fin (A+4)))
    (v : HS T Q A U) (S : Stacks T A) (hblank : ∀ r, S.R (rg r) = []) (depth : ℕ) :
    let M := loadedInputTable rg input D value S
    let F : Stacks T A := {M with R := Function.update M.R k ys}
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v F)+depth+0) depth
        (clearWords (inputTableWords rg)) (Host.mk v F) ((2*n+2)*D+2*n+3)
        (Host.mk v' {S with R := Function.update S.R k ys}) := by
  dsimp only
  let M := loadedInputTable rg input D value S
  let F : Stacks T A := {M with R := Function.update M.R k ys}
  let regs := inputTableWords rg
  have hnd : regs.Nodup := by
    simp [regs,inputTableWords,List.nodup_cons,List.nodup_ofFn,hrg.eq_iff]
    intro i j he
    exact TblR.v.inj (hrg he)
  have hh : tblHolds rg M (tblRho D (List.replicate D tick) [] ⟨fun i => value (input i),[]⟩) := by
    simpa only [M,loadedInputTable,List.replicate_zero] using chirpBankLoad_holds rg hrg input D 0 value S hblank
  have hwr : (F.R (rg .wr)).length = D := by
    rw [show F.R (rg .wr) = M.R (rg .wr) from Function.update_of_ne (hoff .wr) _ _,hh .wr]
    simp [tblRho]
  have hvar (i : Fin n) : (F.R (rg (.v i))).length = D := by
    rw [show F.R (rg (.v i)) = M.R (rg (.v i)) from Function.update_of_ne (hoff (.v i)) _ _,hh (.v i)]
    simp [tblRho,length_binSyms]
  have hvolume : (regs.map (fun j => (F.R j).length)).sum = (n+1)*D := by
    simp [regs,inputTableWords,List.map_ofFn,Function.comp_def,hwr,hvar]
    ring
  have hlen : regs.length = n+1 := by simp [regs,inputTableWords]
  obtain ⟨v',hu,he⟩ := clearWords_exec (body := body) regs hnd v F
  rw [hvolume,hlen] at he
  have htime : 2*((n+1)*D)+2*(n+1)+1 = (2*n+2)*D+2*n+3 := by ring
  rw [htime] at he
  have hM (j : Fin T) (hj : j ∉ regs) : M.R j = S.R j := by
    by_cases hr : ∃ r, rg r = j
    · obtain ⟨r,rfl⟩ := hr
      cases r with
      | v i => exact False.elim (hj (by simp [regs,inputTableWords,List.mem_ofFn]))
      | wr => exact False.elim (hj (by simp [regs,inputTableWords]))
      | wn => simpa only [tblRho,List.replicate_zero,hblank] using hh .wn
      | acc => simpa only [tblRho,List.replicate_zero,hblank] using hh .acc
      | z i => simpa only [tblRho,List.replicate_zero,hblank] using hh (.z i)
    · apply loadedInputTable_off
      intro r he
      exact hr ⟨r,he.symm⟩
  have hend : {F with R := fun j => if j ∈ regs then [] else F.R j} = {S with R := Function.update S.R k ys} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext j
    by_cases hj : j ∈ regs
    · have hjr : ∃ r, rg r = j := by
        simp only [regs,inputTableWords,List.mem_cons,List.mem_ofFn] at hj
        rcases hj with he | ⟨i,he⟩
        · exact ⟨.wr,he.symm⟩
        · exact ⟨.v i,he⟩
      obtain ⟨r,rfl⟩ := hjr
      simp only [if_pos hj,Function.update_of_ne (hoff r),hblank]
    · simp [hj,F,hM j hj,Function.update_apply]
  rw [hend] at he
  exact ⟨v',hu,mn_native_exec_within he 0 (clearWords_native _) depth _
    (by simp only [F,M,Nat.zero_mul,Nat.add_zero]; exact le_rfl)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
