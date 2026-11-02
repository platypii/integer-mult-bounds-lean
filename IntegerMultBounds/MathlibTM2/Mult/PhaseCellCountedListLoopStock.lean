module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoopSharedStock

/-! A list-indexed interface to the existing chronological shared-reserve loop.
The physical body is fixed; the list describes data consumed by each iteration. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main

private theorem sum_range_list_cost {E : Type*} (rs : List E) (cost : E → ℕ) :
    (Finset.range rs.length).sum (fun j => (rs[j]?).elim 0 cost+3) =
      (rs.map (fun r => cost r+3)).sum := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    simpa only [List.length_cons,Finset.sum_range_succ',List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.elim_some,List.map_cons,List.sum_cons,Nat.add_comm] using
      congrArg (fun n => cost r+3+n) ih

theorem countedListLoop_exec_within {T Q A : ℕ} {P U E : Type}
    {body : P → Pr P T Q A U}
    (count : Fin T) (run : Pr P T Q A U) (rs : List E) (cost : E → ℕ)
    (Ready : List E → Stacks T A → Prop) (reserve : ℕ)
    (hstable : ∀ xs S word, Ready xs S → Ready xs {S with R := Function.update S.R count word})
    (hstep : ∀ r ∈ rs, ∀ xs (v : HS T Q A U) S, Ready (r::xs) S →
      ∃ v' F n, v'.user = v.user ∧ n ≤ cost r ∧
        (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+reserve)
          depth run (Host.mk v S) n (Host.mk v' F)) ∧
        F.R count = S.R count ∧ Ready xs F ∧ mnSize (Host.mk v' F) ≤ mnSize (Host.mk v S))
    (v : HS T Q A U) (S : Stacks T A) (hcount : (S.R count).length = rs.length)
    (hReady : Ready rs S) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ (rs.map (fun r => cost r+3)).sum+2 ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+reserve)
        depth (countedLoop count run) (Host.mk v S) n (Host.mk v' F)) ∧
      F.R count = [] ∧ Ready [] F := by
  let c := fun j : ℕ => (rs[j]?).elim 0 cost
  let Inv := fun j S => Ready (rs.drop j) S
  have hsteps : ∀ j < rs.length, ∀ (vi : HS T Q A U) F, Inv j F →
      ∃ vf G n, vf.user = vi.user ∧ n ≤ c j ∧
        (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk vi F)+depth+reserve)
          depth run (Host.mk vi F) n (Host.mk vf G)) ∧
        G.R count = F.R count ∧ Inv (j+1) G ∧ mnSize (Host.mk vf G) ≤ mnSize (Host.mk vi F) := by
    intro j hj vi F hI
    have hdrop : rs.drop j = rs[j]::rs.drop (j+1) := List.drop_eq_getElem_cons hj
    have hR : Ready (rs[j]::rs.drop (j+1)) F := by simpa only [Inv,hdrop] using hI
    obtain ⟨vf,G,n,hu,hn,he,hc,hG,hs⟩ := hstep rs[j] (List.getElem_mem hj) (rs.drop (j+1)) vi F hR
    refine ⟨vf,G,n,hu,?_,he,hc,hG,hs⟩
    simpa only [c,List.getElem?_eq_getElem hj,Option.elim_some] using hn
  obtain ⟨v',F,n,hu,hn,he,hc,hF⟩ := countedLoop_exec_costs_within count run rs.length c Inv reserve
    (by intro j F word hF; exact hstable _ F word hF) hsteps v S hcount (by simpa [Inv] using hReady)
  refine ⟨v',F,n,hu,?_,he,hc,?_⟩
  · simpa only [c,sum_range_list_cost] using hn
  · simpa only [Inv,List.drop_length] using hF

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
