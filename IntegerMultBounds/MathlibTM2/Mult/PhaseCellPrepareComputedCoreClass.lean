module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedCoreOrigins
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryPayloadCount
public import IntegerMultBounds.MathlibTM2.StackStockComposition

/-! Prepare origins, loop count and payload count from ordinary class geometry
and dimensions. No older supplier setup bank is required. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def prepareComputedCoreClass (e : Fin 117 → Fin T)
    (replicas halo wide symbols count saved tmp : Fin T) : Pr P T Q A U :=
  .seq (placedCoreOrigins e) (recoveryPayloadCount replicas halo wide symbols count saved tmp)

theorem prepareComputedCoreClass_exec (e : Fin 117 → Fin T) (he : Function.Injective e)
    (replicas halo wide symbols count saved tmp : Fin T)
    (hreg : [replicas,halo,wide,symbols,count,saved,tmp].Nodup)
    (hoff : ∀ k ∈ [replicas,halo,wide,symbols,count,saved,tmp], k ≠ e 109 ∧ k ≠ e 116)
    (V s width radius H N W : ℕ) (hwidth : 0 < width) (hwide : s+width+2*radius < 2^V)
    (hHfit : H < 2^V) (hA : 4 ≤ A) (hV : 0 < V)
    (v : HS T Q A U) (S : Stacks T A)
    (h37 : (S.R (e 37)).length = V)
    (hs : S.R (e 32) = binSyms V s) (hw : S.R (e 33) = binSyms V width)
    (hr : S.R (e 34) = binSyms V radius) (hH : S.R (e 35) = binSyms V H) (hz : S.R (e 36) = [])
    (htable : ∀ k : Fin 117, k.val < 31 → S.R (e k) = [])
    (h104 : S.R (e 104) = []) (h106 : S.R (e 106) = []) (h116 : S.R (e 116) = [])
    (hN : (S.R replicas).length = N) (hhalo : (S.R halo).length = H) (hW : (S.R wide).length = W)
    (hblank : ∀ k ∈ [symbols,count,saved,tmp], S.R k = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ preparedCoreOriginsCost V s width radius H+recoveryPayloadCountCost N H W ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        (3*preparedCoreOriginsCost V s width radius H+2*recoveryPayloadCountCost N H W)) depth
        (prepareComputedCoreClass e replicas halo wide symbols count saved tmp) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update (Function.update S.R (e 109)
          ((coreGatherIndices s width radius H).flatMap (fun k => binSyms V (coreStart width k-radius))++S.R (e 109)))
          (e 116) (List.replicate (coreGatherIndices s width radius H).length tick))
          count (List.replicate (N*(H*W)) tick))}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := placedCoreOrigins_exec_within (body := body) e he
    hwidth hwide hHfit hA hV v S h37 hs hw hr hH hz htable h104 h106 h116 depth
  let F : Stacks T A := {S with R := (Function.update (Function.update S.R (e 109)
    ((coreGatherIndices s width radius H).flatMap (fun k => binSyms V (coreStart width k-radius))++S.R (e 109)))
    (e 116) (List.replicate (coreGatherIndices s width radius H).length tick))}
  have hframe (k : Fin T) (hk : k ∈ [replicas,halo,wide,symbols,count,saved,tmp]) : F.R k = S.R k := by
    simp only [F,Function.update_of_ne (hoff k hk).2,Function.update_of_ne (hoff k hk).1]
  obtain ⟨v₂,n₂,hu₂,hn₂,hex₂,htrace₂⟩ := recoveryPayloadCount_exec (body := body)
    replicas halo wide symbols count saved tmp hreg N H W v₁ F
    (by rw [hframe replicas (by simp)]; exact hN)
    (by rw [hframe halo (by simp)]; exact hhalo)
    (by rw [hframe wide (by simp)]; exact hW)
    (by
      intro k hk
      have hmem : k ∈ [replicas,halo,wide,symbols,count,saved,tmp] := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl <;> simp
      rw [hframe k hmem]
      exact hblank k hk)
  have ht := mn_seq_within_add he₁ (htrace₂ depth)
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,?_⟩
  simpa only [prepareComputedCoreClass,F] using ht

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
