module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCopyWordHeaders
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupStock

/-! Retire a copied header bank after a restoring consumer changes two ports.
The proof is structural in the header list and independent of its size. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type}

theorem retireCopiedHeaders_pair_exec (body : P → Pr P T Q A U)
    (pairs : List (Fin T × Fin T)) (hnd : (pairs.map Prod.snd).Nodup)
    (src dst : Fin T) (hsrc : ∀ p ∈ pairs, p.2 ≠ src) (hdst : ∀ p ∈ pairs, p.2 ≠ dst)
    (xs ys : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hblank : ∀ p ∈ pairs, S.R p.2 = []) (depth : ℕ) :
    let loaded : Stacks T A := {S with R := copyWordHeadersR S.R pairs S.R}
    let M : Stacks T A := {loaded with R := (Function.update (Function.update loaded.R src xs) dst ys)}
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v M)+depth) depth
        (clearWords (pairs.map Prod.snd)) (mk v M)
        (2*(pairs.map (fun p => (S.R p.1).length)).sum+2*pairs.length+1)
        (mk v' {S with R := (Function.update (Function.update S.R src xs) dst ys)}) := by
  dsimp only
  let loaded : Stacks T A := {S with R := copyWordHeadersR S.R pairs S.R}
  let M : Stacks T A := {loaded with R := (Function.update (Function.update loaded.R src xs) dst ys)}
  have hget (p : Fin T × Fin T) (hp : p ∈ pairs) : M.R p.2 = S.R p.1 := by
    dsimp only [M,loaded]
    rw [Function.update_of_ne (hdst p hp),Function.update_of_ne (hsrc p hp),
      copyWordHeadersR_get S.R pairs hnd S.R p hp,hblank p hp,List.append_nil]
  obtain ⟨v',hu,he⟩ := clearWords_exec (body := body) (pairs.map Prod.snd) hnd v M
  have hcost : ((pairs.map Prod.snd).map (fun i => (M.R i).length)).sum =
      (pairs.map (fun p => (S.R p.1).length)).sum := by
    rw [List.map_map]
    congr 1
    exact List.map_congr_left (fun p hp => congrArg List.length (hget p hp))
  rw [hcost,List.length_map] at he
  have hend : ({M with R := fun i => if i ∈ pairs.map Prod.snd then [] else M.R i} : Stacks T A) =
      {S with R := (Function.update (Function.update S.R src xs) dst ys)} := by
    refine Stacks.ext (by rfl) (by rfl) (by rfl) ?_
    funext i
    by_cases hi : i ∈ pairs.map Prod.snd
    · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hi
      simp only [ite_eq_left (List.mem_map.mpr ⟨p,hp,rfl⟩),Function.update_of_ne (hdst p hp),
        Function.update_of_ne (hsrc p hp),hblank p hp]
    · have hoff : ∀ p ∈ pairs, p.2 ≠ i := by
        intro p hp he
        exact hi (List.mem_map.mpr ⟨p,hp,he⟩)
      simp only [ite_eq_right hi,M,loaded,Function.update_apply]
      rw [copyWordHeadersR_off S.R pairs S.R i hoff]
  rw [hend] at he
  refine ⟨v',hu,?_⟩
  exact mn_native_exec_within he 0 (clearWords_native _) depth _ (by simp only [M,loaded,Nat.zero_mul,Nat.add_zero]; exact le_rfl)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
