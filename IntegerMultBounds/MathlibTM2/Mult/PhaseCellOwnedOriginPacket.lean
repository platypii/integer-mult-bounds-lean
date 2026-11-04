module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterchangeHeaderStock

/-! An owned origin packet and count commute with external data writes and
can be retired after publication without disturbing the ambient destination. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type}

def originPacketState (packet count : Fin T) (V : ℕ) (origins : List ℕ) (S : Stacks T A) :=
  {S with R := (Function.update (Function.update S.R packet (origins.flatMap (binSyms V)))
    count (List.replicate origins.length tick))}

theorem originPacketState_off (packet count : Fin T) (V : ℕ) (origins : List ℕ)
    (S : Stacks T A) (k : Fin T) (hp : k ≠ packet) (hc : k ≠ count) :
    (originPacketState packet count V origins S).R k = S.R k := by
  simp only [originPacketState,Function.update_of_ne hp,Function.update_of_ne hc]

theorem originPacketState_update_off (packet count : Fin T) (V : ℕ) (origins : List ℕ)
    (S : Stacks T A) (k : Fin T) (xs : List (Fin (A+4))) (hp : packet ≠ k) (hc : count ≠ k) :
    originPacketState packet count V origins {S with R := Function.update S.R k xs} =
      {originPacketState packet count V origins S with R :=
        (Function.update (originPacketState packet count V origins S).R k xs)} := by
  refine Stacks.ext rfl rfl rfl ?_
  simp only [originPacketState]
  rw [Function.update_comm hp.symm,Function.update_comm hc.symm]

theorem retireOriginPacket_exec_within (body : P → Pr P T Q A U)
    (packet count : Fin T) (hports : packet ≠ count) (V : ℕ) (origins : List ℕ)
    (output : Fin T) (houtPacket : output ≠ packet) (houtCount : output ≠ count)
    (ys : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hpacket : S.R packet = []) (hcount : S.R count = []) (depth : ℕ) :
    let M := originPacketState packet count V origins S
    let F : Stacks T A := {M with R := Function.update M.R output ys}
    ∃ v', v'.user = v.user ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v F)+depth+0) depth
        (clearWords [packet,count]) (mk v F) (2*(origins.length*V+origins.length)+5)
        (mk v' {S with R := Function.update S.R output ys}) := by
  dsimp only
  let M := originPacketState packet count V origins S
  let F : Stacks T A := {M with R := Function.update M.R output ys}
  obtain ⟨v',hu,he⟩ := clearWords_exec (body := body) [packet,count] (by simp [hports]) v F
  have hcost : 2*(([packet,count].map fun r => (F.R r).length).sum)+2*[packet,count].length+1 =
      2*(origins.length*V+origins.length)+5 := by
    simp [F,M,originPacketState,houtPacket.symm,houtCount.symm,hports,List.length_flatMap,binSyms]
  rw [hcost] at he
  have hend : {F with R := fun k => if k ∈ [packet,count] then [] else F.R k} =
      {S with R := Function.update S.R output ys} := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hp : k = packet
    · subst k; simp [houtPacket.symm,hpacket]
    by_cases hc : k = count
    · subst k; simp [houtCount.symm,hcount]
    simp [F,M,originPacketState,Function.update_apply,hp,hc]
  rw [hend] at he
  exact ⟨v',hu,mn_native_exec_within he 0 (clearWords_native _) depth _ (by simp only [F,M,Nat.zero_mul,Nat.add_zero]; exact le_rfl)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
