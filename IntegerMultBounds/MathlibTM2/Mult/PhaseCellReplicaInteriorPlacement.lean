module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedPrefixHandoff
public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchInputBankUpdate

/-! Disjoint gather/numerical banks exchange one generated counted prefix.
Their coordinate/header languages stay separate and both suffixes survive. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

structure ReplicaInteriorPlacement (T : ℕ) where
  gather : Fin 126 → Fin T
  solver : Fin 121 → Fin T
  gather_injective : Function.Injective gather
  solver_injective : Function.Injective solver
  disjoint : ∀ i j, gather i ≠ solver j

namespace ReplicaInteriorPlacement
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def standard : ReplicaInteriorPlacement 247 where
  gather := Fin.castLE (by decide)
  solver i := ⟨126+i.val,by omega⟩
  gather_injective := Fin.castLE_injective (by decide)
  solver_injective := by
    intro i j h
    apply Fin.ext
    have hv := congrArg Fin.val h
    dsimp only at hv
    omega
  disjoint := by
    intro i j h
    have hv := congrArg Fin.val h
    dsimp only [Fin.castLE] at hv
    omega

def bank (plan : ReplicaInteriorPlacement T) : Fin 126 ⊕ Fin 121 → Fin T :=
  Sum.elim plan.gather plan.solver

theorem bank_injective (plan : ReplicaInteriorPlacement T) : Function.Injective plan.bank := by
  intro i j h
  cases i with
  | inl i =>
    cases j with
    | inl j => exact congrArg Sum.inl (plan.gather_injective h)
    | inr j => exact (plan.disjoint i j h).elim
  | inr i =>
    cases j with
    | inl j => exact (plan.disjoint j i h.symm).elim
    | inr j => exact congrArg Sum.inr (plan.solver_injective h)

theorem gather_update_solver (plan : ReplicaInteriorPlacement T) (S : Stacks T A)
    (j : Fin 121) (xs : List (Fin (A+4))) :
    embStk plan.gather {S with R := Function.update S.R (plan.solver j) xs} = embStk plan.gather S :=
  embStk_updateR_off S _ xs (fun i => plan.disjoint i j)

theorem solver_update_gather (plan : ReplicaInteriorPlacement T) (S : Stacks T A)
    (i : Fin 126) (xs : List (Fin (A+4))) :
    embStk plan.solver {S with R := Function.update S.R (plan.gather i) xs} = embStk plan.solver S :=
  embStk_updateR_off S _ xs (fun j => (plan.disjoint i j).symm)

def handoff (plan : ReplicaInteriorPlacement T) : Pr P T Q A U :=
  generatedPrefixHandoff (plan.solver 116) (plan.solver 103) (plan.gather 94)
    (plan.gather 88) (plan.gather 89) (plan.gather 110) (plan.solver 110) (plan.gather 6) (plan.gather 7)

theorem handoff_exec (plan : ReplicaInteriorPlacement T) (N B L w : ℕ)
    (xs tail : List (Fin (A+4))) (hlen : xs.length = (N*B)*L*w)
    (v : HS T Q A U) (S : Stacks T A)
    (hN : (S.R (plan.solver 116)).length = N*B) (hL : (S.R (plan.solver 103)).length = L)
    (hw : (S.R (plan.gather 94)).length = w) (hsource : S.R (plan.gather 110) = xs++tail)
    (hfresh : ∀ k ∈ [(88 : Fin 126),89,6,7], S.R (plan.gather k) = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ generatedPrefixHandoffCost (N*B) L w ∧
      let F : Stacks T A := {S with R := (Function.update (Function.update S.R (plan.gather 110) tail)
        (plan.solver 110) (xs++S.R (plan.solver 110)))}
      Exec body plan.handoff (Host.mk v S) n (Host.mk v' F) ∧
      embStk plan.gather F = {embStk plan.gather S with R := Function.update (embStk plan.gather S).R 110 tail} ∧
      embStk plan.solver F = {embStk plan.solver S with R := (Function.update (embStk plan.solver S).R 110
        (xs++(embStk plan.solver S).R 110))} := by
  let regs : List (Fin 126 ⊕ Fin 121) :=
    [.inr 116,.inr 103,.inl 94,.inl 88,.inl 89,.inl 110,.inr 110,.inl 6,.inl 7]
  have hregs := List.Nodup.map plan.bank_injective (show regs.Nodup by decide)
  have hreg : [plan.solver 116,plan.solver 103,plan.gather 94,plan.gather 88,plan.gather 89,
      plan.gather 110,plan.solver 110,plan.gather 6,plan.gather 7].Nodup := by
    simpa only [regs,List.map_cons,List.map_nil,bank,Sum.elim_inl,Sum.elim_inr] using hregs
  obtain ⟨v',n,huser,hcost,he⟩ := generatedPrefixHandoff_exec (body := body) hreg
    (N*B) L w xs tail hlen v S hN hL hw hsource (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl
      · exact hfresh 88 (by simp)
      · exact hfresh 89 (by simp)
      · exact hfresh 6 (by simp)
      · exact hfresh 7 (by simp))
  refine ⟨v',n,huser,hcost,he,?_,?_⟩
  · let H : Stacks T A := {S with R := Function.update S.R (plan.gather 110) tail}
    change embStk plan.gather {H with R := Function.update H.R (plan.solver 110) (xs++S.R (plan.solver 110))} = _
    rw [plan.gather_update_solver]
    exact embStk_updateR plan.gather_injective S 110 tail
  · let H : Stacks T A := {S with R := Function.update S.R (plan.gather 110) tail}
    change embStk plan.solver {H with R := Function.update H.R (plan.solver 110) (xs++S.R (plan.solver 110))} = _
    rw [embStk_updateR plan.solver_injective]
    have hh := plan.solver_update_gather S 110 tail
    change embStk plan.solver H = embStk plan.solver S at hh
    rw [hh]
    rfl

end ReplicaInteriorPlacement

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
