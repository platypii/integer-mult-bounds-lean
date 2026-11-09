module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupStock

/-! Restore any injectively placed generated unary header bank. The caller's
retained streams and outputs are part of the restored base state. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {N T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem retireGeneratedHeaders_exec (ports : Fin N → Fin T) (hports : Function.Injective ports)
    (values : Fin N → ℕ) (v : HS T Q A U) (S F : Stacks T A)
    (hblank : ∀ i, S.R (ports i) = [])
    (hvalues : ∀ i, (F.R (ports i)).length = values i)
    (hin : F.inp = S.inp) (hout : F.out = S.out) (hleft : F.L = S.L)
    (hframe : ∀ k, (∀ i, ports i ≠ k) → F.R k = S.R k) (depth : ℕ) :
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v F)+depth) depth
        (clearWords (List.ofFn ports)) (Host.mk v F)
        (2*(List.ofFn values).sum+2*N+1) (Host.mk v' S) := by
  obtain ⟨v',hu,he⟩ := clearWords_exec (body := body) (List.ofFn ports) (List.nodup_ofFn.mpr hports) v F
  have hcost : 2*((List.ofFn ports).map fun r => (F.R r).length).sum+
      2*(List.ofFn ports).length+1 = 2*(List.ofFn values).sum+2*N+1 := by
    simp only [List.map_ofFn,Function.comp_def,hvalues,List.length_ofFn]
  have hfinal : {F with R := fun k => if k ∈ List.ofFn ports then [] else F.R k} = S := by
    refine Stacks.ext hin hout hleft ?_
    funext k
    by_cases hk : ∃ i, ports i = k
    · obtain ⟨i,rfl⟩ := hk
      simp only [List.mem_ofFn,exists_apply_eq_apply,ite_true]
      exact (hblank i).symm
    · have hoff : ∀ i, ports i ≠ k := by simpa only [not_exists] using hk
      simp only [List.mem_ofFn,hk,ite_false]
      exact hframe k hoff
  rw [hcost,hfinal] at he
  exact ⟨v',hu,mn_native_exec_within he 0 (clearWords_native _) depth _
    (by simp only [Nat.zero_mul,Nat.add_zero]; exact le_rfl)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
