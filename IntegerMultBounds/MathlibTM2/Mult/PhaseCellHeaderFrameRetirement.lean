module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupStock

/-! Release a generated header bank while retaining two consumer data updates.
Only its frame and initially blank destinations matter, not its construction. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type}

theorem retireHeaderFrame_pair_exec (body : P → Pr P T Q A U)
    (headers : List (Fin T)) (hnd : headers.Nodup) (S M : Stacks T A)
    (hinput : M.inp = S.inp) (houtput : M.out = S.out) (hleft : M.L = S.L)
    (hframe : ∀ i, i ∉ headers → M.R i = S.R i)
    (hblank : ∀ i ∈ headers, S.R i = [])
    (src dst : Fin T) (hsrc : src ∉ headers) (hdst : dst ∉ headers)
    (xs ys : List (Fin (A+4))) (v : HS T Q A U) (depth : ℕ) :
    let F : Stacks T A := {M with R := (Function.update (Function.update M.R src xs) dst ys)}
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v F)+depth) depth
        (clearWords headers) (mk v F)
        (2*(headers.map (fun i => (M.R i).length)).sum+2*headers.length+1)
        (mk v' {S with R := (Function.update (Function.update S.R src xs) dst ys)}) := by
  dsimp only
  let F : Stacks T A := {M with R := (Function.update (Function.update M.R src xs) dst ys)}
  have hread (i : Fin T) (hi : i ∈ headers) : F.R i = M.R i := by
    have hs : i ≠ src := by intro h; subst i; exact hsrc hi
    have hd : i ≠ dst := by intro h; subst i; exact hdst hi
    simp only [F,Function.update_of_ne hd,Function.update_of_ne hs]
  obtain ⟨v',hu,he⟩ := clearWords_exec (body := body) headers hnd v F
  have hcost : (headers.map (fun i => (F.R i).length)).sum =
      (headers.map (fun i => (M.R i).length)).sum := by
    congr 1
    exact List.map_congr_left (fun i hi => congrArg List.length (hread i hi))
  rw [hcost] at he
  have hend : ({F with R := fun i => if i ∈ headers then [] else F.R i} : Stacks T A) =
      {S with R := (Function.update (Function.update S.R src xs) dst ys)} := by
    refine Stacks.ext hinput houtput hleft ?_
    funext i
    by_cases hi : i ∈ headers
    · have hs : i ≠ src := by intro h; subst i; exact hsrc hi
      have hd : i ≠ dst := by intro h; subst i; exact hdst hi
      simp only [ite_eq_left hi,Function.update_of_ne hd,Function.update_of_ne hs,hblank i hi]
    · simp only [ite_eq_right hi,F,Function.update_apply,hframe i hi]
  rw [hend] at he
  refine ⟨v',hu,?_⟩
  exact mn_native_exec_within he 0 (clearWords_native _) depth _
    (by simp only [F,Nat.zero_mul,Nat.add_zero]; exact le_rfl)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
