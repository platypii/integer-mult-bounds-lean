module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRemoveDummyPrefix
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaKeyLayout

/-! Publish the real suffix of an arbitrary computed padded replica tile. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

/-- Erase whole dummy rows from a computed replica-major tile. The remaining
array is derived from the actual suffix, without assumptions on dummy values. -/
theorem removeDummyReplicas_exec {src keep count tmp : Fin T}
    (hreg : [src,keep,count,tmp].Nodup) {C N K W : ℕ} (hN : N ≤ C)
    (f : Fin C → Fin K → Fin W → Fin (A+4))
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = replicaKeyWords f) (hkeep : (S.R keep).length = N*(K*W))
    (hcount : S.R count = []) (htmp : S.R tmp = []) :
    ∃ g : Fin N → Fin K → Fin W → Fin (A+4),
      replicaKeyWords g = (replicaKeyWords f).drop ((C-N)*(K*W)) ∧
      ∃ v' n, v'.user = v.user ∧ n ≤ 10*(C*(K*W))+14 ∧
        Exec body (removeDummyPrefix src keep count tmp) (mk v S) n
          (mk v' {S with R := Function.update S.R src (replicaKeyWords g)}) := by
  let cut := (C-N)*(K*W)
  let xs := replicaKeyWords f
  have hlen : xs.length = C*(K*W) := by simp [xs,replicaKeyWords]
  have hfit := Nat.mul_le_mul_right (K*W) hN
  have hcut : cut = C*(K*W)-N*(K*W) := Nat.sub_mul C N (K*W)
  have hreal : (xs.drop cut).length = N*(K*W) := by
    rw [List.length_drop,hlen,hcut]
    omega
  obtain ⟨g,hg⟩ := replicaKeyWords_of_length (xs.drop cut) hreal
  obtain ⟨v',hu,he⟩ := removeDummyPrefix_exec (body := body) hreg (xs.take cut) (xs.drop cut)
    v S (by rw [List.take_append_drop]; exact hsrc) (hkeep.trans hreal.symm) hcount htmp
  refine ⟨g,hg,v',10*(xs.take cut).length+8*(xs.drop cut).length+14,hu,?_,?_⟩
  · have hc := removeDummyPrefix_cost_le (xs.take cut).length (xs.drop cut).length
    have hs : (xs.take cut).length+(xs.drop cut).length = C*(K*W) := by
      rw [←List.length_append,List.take_append_drop,hlen]
    simpa only [hs] using hc
  · simpa only [hg] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
