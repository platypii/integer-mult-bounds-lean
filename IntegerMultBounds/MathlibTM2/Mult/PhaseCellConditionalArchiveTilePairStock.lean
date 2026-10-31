module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellConditionalArchiveTilePair
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellConditionalArchiveTileStock

/-! Paired archive transposes share workspace; only the first retained padded
output increases the boundary stock seen by the second execution. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ArchiveTilePlan
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

private theorem shared_first (s d V a b x : ℕ) (h : x ≤ s+d+a) : x ≤ s+d+V+max a b := by omega

private theorem shared_second (s t d V a b x : ℕ) (ht : t ≤ s+V) (h : x ≤ t+d+b) :
    x ≤ s+d+V+max a b := by omega

theorem conditional_pair_exec_within {t₁ t₂ T Q c₁ c₂ d W₁ W₂ K N₁ N₂ : ℕ} {P U : Type}
    (plan₁ : ArchiveTilePlan t₁ T Q c₁ d W₁) (plan₂ : ArchiveTilePlan t₂ T Q c₂ d W₂)
    (active₁ active₂ : Fin T) (hsep : plan₁.src ∉ plan₂.support) (hactiveOff : active₂ ≠ plan₁.src)
    (body : P → Pr P T Q (prime+K) U) (hA : 4 ≤ prime+K)
    (hW₁ : 0 < N₁ → 0 < W₁) (hW₂ : 0 < N₂ → 0 < W₂) (L₁ L₂ w : ℕ)
    (hpacket₁ : W₁ = L₁*w) (hpacket₂ : W₂ = L₂*w)
    (hN₁ : N₁ ≤ (2^d)^c₁) (hN₂ : N₂ ≤ (2^d)^c₂)
    (rows₁ : Fin N₁ → Fin (2^d) → List GaussianInt)
    (rows₂ : Fin N₂ → Fin (2^d) → List GaussianInt)
    (hlen₁ : ∀ i j, (rows₁ i j).length = L₁) (hlen₂ : ∀ i j, (rows₂ i j).length = L₂)
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (hready₁ : plan₁.Ready w rows₁ S) (hready₂ : plan₂.Ready w rows₂ S)
    (hactive₁ : (S.R active₁).head?.isSome = decide (0 < N₁))
    (hactive₂ : (S.R active₂).head?.isSome = decide (0 < N₂)) (depth : ℕ) :
    ∃ result₁ : Result L₁ rows₁, ∃ result₂ : Result L₂ rows₂,
      result₁.capacity = capacity N₁ ((2^d)^c₁) ∧ result₂.capacity = capacity N₂ ((2^d)^c₂) ∧
      ∃ v' n, v'.user = v.user ∧ n ≤ plan₁.conditionalCost N₁ S+plan₂.conditionalCost N₂ S ∧
        ExecWithin body (fun z state => mnSize state+z ≤ mnSize (Host.mk v S)+depth+
          capacity N₁ ((2^d)^c₁)*(2^d*W₁)+
          max (plan₁.conditionalStockAllowance N₁) (plan₂.conditionalStockAllowance N₂)) depth (.seq (plan₁.conditionalProgram active₁) (plan₂.conditionalProgram active₂)) (Host.mk v S) n
          (Host.mk v' {S with L := fun _ => [], R := (Function.update
            (Function.update S.R plan₁.src
              ((List.ofFn fun j => cstream (prime+K) w (List.ofFn fun i => result₁.padded i j).flatten).flatten))
            plan₂.src ((List.ofFn fun j => cstream (prime+K) w (List.ofFn fun i => result₂.padded i j).flatten).flatten))}) := by
  obtain ⟨result₁,hcap₁,v₁,n₁,hu₁,hn₁,he₁⟩ := plan₁.conditional_exec_within active₁ body hA hW₁ L₁ w hpacket₁ hN₁ rows₁ hlen₁ v S hready₁ hactive₁ depth
  let M : Stacks T (prime+K) := {S with L := fun _ => [], R := (Function.update S.R plan₁.src
    ((List.ofFn fun j => cstream (prime+K) w (List.ofFn fun i => result₁.padded i j).flatten).flatten))}
  have hR (i : Fin T) (hi : i ∈ plan₂.support) : M.R i = S.R i := by
    have hne : i ≠ plan₁.src := by intro he; subst i; exact hsep hi
    simp [M,hne]
  have hL : M.L = S.L := by funext i; exact (hready₁.hL i).symm
  have hnext := hready₂.of_frame hR hL
  obtain ⟨result₂,hcap₂,v₂,n₂,hu₂,hn₂,he₂⟩ := plan₂.conditional_exec_within active₂ body hA hW₂ L₂ w hpacket₂ hN₂ rows₂ hlen₂ v₁ M hnext
    (by simpa only [M,Function.update_of_ne hactiveOff] using hactive₂) depth
  have hsum : (∑ j, (M.R (plan₂.ι j)).length) = ∑ j, (S.R (plan₂.ι j)).length := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hR _ (embedded_mem_support plan₂ j)]
  have hcost : plan₂.conditionalCost N₂ M = plan₂.conditionalCost N₂ S := by simp only [conditionalCost,cost,hsum]
  rw [hcost] at hn₂
  refine ⟨result₁,result₂,hcap₁,hcap₂,v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,?_⟩
  let V := capacity N₁ ((2^d)^c₁)*(2^d*W₁)
  let bound := mnSize (Host.mk v S)+depth+V+
    max (plan₁.conditionalStockAllowance N₁) (plan₂.conditionalStockAllowance N₂)
  have hlength : ((List.ofFn fun j => cstream (prime+K) w
      (List.ofFn fun i => result₁.padded i j).flatten).flatten).length = V := by
    simp [List.length_flatten,List.map_ofFn,List.sum_ofFn,result₁.rowLength,V,←hcap₁,hpacket₁,
      Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
  have hleft : (fun _ : Fin T => ([] : List (Fin (prime+K+4)))) = S.L := by
    funext i
    exact (hready₁.hL i).symm
  have hbalance : mnSize (Host.mk v₁ M)+(S.R plan₁.src).length = mnSize (Host.mk v S)+V := by
    simp only [M,hleft]
    rw [←hlength]
    simpa only [Host.mk,update_rt,get_rt] using mn_size_update (Host.mk v S) v₁ (.rt plan₁.src)
      ((List.ofFn fun j => cstream (prime+K) w (List.ofFn fun i => result₁.padded i j).flatten).flatten)
  have hboundary : mnSize (Host.mk v₁ M) ≤ mnSize (Host.mk v S)+V := by omega
  have hw₁ := he₁.mono (J := fun z state => mnSize state+z ≤ bound) (by
    intro z state hc
    exact shared_first _ _ _ _ _ _ hc)
  have hw₂ := he₂.mono (J := fun z state => mnSize state+z ≤ bound) (by
    intro z state hc
    change mnSize state+z ≤ mnSize (Host.mk v₁ M)+depth+plan₂.conditionalStockAllowance N₂ at hc
    exact shared_second _ _ _ _ _ _ _ hboundary hc)
  exact ExecWithin.seq hw₁ hw₂

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ArchiveTilePlan
