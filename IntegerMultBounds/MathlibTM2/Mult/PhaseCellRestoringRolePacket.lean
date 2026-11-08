module

public import IntegerMultBounds.MathlibTM2.Fast.ResampBRunStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetiringPacketWorker

/-! Exact physical endpoints for restoring role-bank operations. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U R : Type} [DecidableEq R]
  {body : P → Pr P T Q A U} {rg : R → Fin T} {ι : Fin 64 → Fin T}

theorem RsbFr.eq_update_of_holds (hrg : Function.Injective rg) {S F : Stacks T A}
    {ρ : R → List (Fin (A+4))} (o : R) (packet : List (Fin (A+4)))
    (hS : RsbHolds rg S ρ) (hF : RsbHolds rg F (Function.update ρ o (packet++ρ o)))
    (hframe : RsbFr rg S F) :
    F = {S with R := Function.update S.R (rg o) (packet++S.R (rg o))} := by
  classical
  refine Stacks.ext hframe.1 hframe.2.1 hframe.2.2.1 ?_
  funext k
  change F.R k = Function.update S.R (rg o) (packet++S.R (rg o)) k
  by_cases hk : ∃ r, rg r = k
  · obtain ⟨r,rfl⟩ := hk
    by_cases hr : r = o
    · subst r; simpa only [Function.update_self,hS o] using hF o
    · rw [Function.update_of_ne (fun he => hr (hrg he))]
      have hh : F.R (rg r) = ρ r := by simpa only [Function.update_of_ne hr] using hF r
      exact hh.trans (hS r).symm
  · have hoff : ∀ r, rg r ≠ k := by simpa only [not_exists] using hk
    rw [Function.update_of_ne (hoff o).symm]
    exact hframe.2.2.2 k hoff

theorem RsbRunsWithin.exec_update {run : Pr P T Q A U} {ρ : R → List (Fin (A+4))}
    (hrg : Function.Injective rg) (o : R) (packet : List (Fin (A+4))) (cost reserve : ℕ)
    (h : RsbRunsWithin (body := body) (rg := rg) (ι := ι) run ρ
      (Function.update ρ o (packet++ρ o)) cost reserve)
    (v : HS T Q A U) (S : Stacks T A) (hclean : RsbClean ι S) (hS : RsbHolds rg S ρ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ cost ∧
      Exec body run (Host.mk v S) n
        (Host.mk v' {S with R := Function.update S.R (rg o) (packet++S.R (rg o))}) ∧
      ∀ depth, ExecWithin body (fun j z => mnSize z+j ≤ mnSize (Host.mk v S)+depth+reserve)
        depth run (Host.mk v S) n
        (Host.mk v' {S with R := Function.update S.R (rg o) (packet++S.R (rg o))}) := by
  obtain ⟨v',F,n,hu,hn,hF,hframe,htrace⟩ := h v S hclean hS
  rw [hframe.eq_update_of_holds hrg o packet hS hF] at htrace
  exact ⟨v',n,hu,hn,(htrace 0).toExec,htrace⟩

end IntegerMultBounds.MathlibTM2.Fast

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U R : Type} [DecidableEq R]
  {body : P → Pr P T Q A U} {rg : R → Fin T} {ι : Fin 64 → Fin T}

theorem retiringRolePacket_exec (hrg : Function.Injective rg)
    (hdisj : ∀ r j, rg r ≠ ι j) (count queue saved tmp : Fin T) (x o : R)
    (hreg : [count,queue,rg x,rg o,saved,tmp].Nodup)
    (hoff : ∀ r, rg r ≠ queue) (hqueueWork : ∀ j, queue ≠ ι j)
    (run : Pr P T Q A U) (payload result tail : List (Fin (A+4)))
    (hlen : result.length = payload.length) (cost reserve : ℕ)
    (ρ : R → List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hqueue : S.R queue = payload++tail) (hcount : (S.R count).length = payload.length)
    (hinput : S.R (rg x) = []) (hsaved : S.R saved = []) (htmp : S.R tmp = [])
    (hclean : RsbClean ι S) (hS : RsbHolds rg S ρ)
    (hrun : RsbRunsWithin (body := body) (rg := rg) (ι := ι) run (Function.update ρ x payload)
      (Function.update (Function.update ρ x payload) o (result++(Function.update ρ x payload) o)) cost reserve) :
    ∃ v' n, v'.user = v.user ∧ n ≤ (6*payload.length+6)+cost+(2*payload.length+2) ∧
      Exec body (retiringPacketWorker count queue (rg x) saved tmp run) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R queue tail) (rg o) (result++S.R (rg o)))}) ∧
      (∀ depth, ExecWithin body (fun j z => mnSize z+j ≤ mnSize (Host.mk v S)+depth+
        (2*(6*payload.length+6)+reserve)) depth
        (retiringPacketWorker count queue (rg x) saved tmp run) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R queue tail) (rg o) (result++S.R (rg o)))})) ∧
      mnSize (Host.mk v' {S with R := (Function.update (Function.update S.R queue tail) (rg o) (result++S.R (rg o)))}) =
        mnSize (Host.mk v S) := by
  have hr := hreg
  regs_ne hr
  apply retiringPacketWorker_exec count queue (rg x) (rg o) saved tmp hreg run payload result tail hlen
    cost reserve v S hqueue hcount hinput hsaved htmp
  intro v₁
  let F : Stacks T A := {S with R := Function.update (Function.update S.R queue tail) (rg x) payload}
  have hc : RsbClean ι F := by
    refine ⟨hclean.1,?_⟩
    intro j
    simpa only [F,Function.update_of_ne (hdisj x j).symm,Function.update_of_ne (hqueueWork j).symm]
      using hclean.2 j
  have hh : RsbHolds rg F (Function.update ρ x payload) := by
    intro r
    by_cases hr : r = x
    · subst r; simp [F]
    · have hne : rg r ≠ rg x := fun he => hr (hrg he)
      simpa only [F,Function.update_of_ne hne,Function.update_of_ne (hoff r),Function.update_of_ne hr] using hS r
  obtain ⟨v₂,n,hu,hn,he,ht⟩ := hrun.exec_update hrg o result cost reserve v₁ F hc hh
  have ho : F.R (rg o) = S.R (rg o) := by
    simp only [F,Function.update_of_ne ‹rg x ≠ rg o›.symm,Function.update_of_ne (hoff o)]
  rw [ho] at he ht
  exact ⟨v₂,n,hu,hn,he,ht⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
