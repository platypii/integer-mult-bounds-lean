module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellConditionalArchiveTileStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellChunkInterchangeStockBound

/-! The physical tile allowance is linear in volume with a coefficient depending
only on the fixed host bank, not on the number of address chunks. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

private theorem chain_cost_le (T K n m V : ℕ) (hK : 1 ≤ K) (hm : m ≤ T)
    (hn : n*K^m ≤ V) (hKV : K ≤ V) (hV : 0 < V) :
    unaryPowerChainCost K n m ≤ 17*T*V+1 := by
  have hcost := unaryPowerChainCost_le hK n m
  have hbill : 4*n*K^m+9*K+4 ≤ 17*V := by nlinarith only [hn,hKV,hV]
  have h₁ := Nat.mul_le_mul_left m hbill
  have h₂ := Nat.mul_le_mul_right (17*V) hm
  nlinarith only [hcost,h₁,h₂]

private theorem total_stock_le (T V C p b r : ℕ) (hV : 0 < V)
    (hp : p ≤ 17*T*V+1) (hb : b ≤ 17*T*V+1) (hr : r ≤ C*V) :
    (74*V+56)+(2*(4*V+4)+(2*(12*V+12)+(2*(p+b)+r)+(8*V+6))) ≤
      (C+68*T+212)*V := by nlinarith only [hp,hb,hr,hV]

namespace ArchiveTilePlan

noncomputable def stockCoefficient (T : ℕ) : ℕ := chunkStockCoefficient T+68*T+212

theorem stockAllowance_le {t₀ T Q c d W : ℕ} (plan : ArchiveTilePlan t₀ T Q c d W)
    (hW : 0 < W) : plan.stockAllowance ≤ stockCoefficient T*((2^d)^c*(2^d*W)) := by
  let K := 2^d
  let V := K^c*(K*W)
  have hK : 1 ≤ K := Nat.one_le_pow d 2 (by decide)
  have hKpos : 0 < K := by omega
  have hV : 0 < V := Nat.mul_pos (pow_pos hKpos _) (Nat.mul_pos hKpos hW)
  have hpc := congrArg List.length plan.hprefixes
  have hbc := congrArg List.length plan.hsuffixes
  simp only [List.length_ofFn,List.length_cons] at hpc hbc
  have hpT : plan.ps.length ≤ T := by
    have hh := plan.hp.length_le_card
    simp only [List.length_append,List.length_cons,List.length_nil,Fintype.card_fin] at hh
    omega
  have hbT : plan.bs.length ≤ T := by
    have hh := plan.hb.length_le_card
    simp only [List.length_append,List.length_cons,List.length_nil,Fintype.card_fin] at hh
    omega
  have hKV : K ≤ V := by
    have hh := Nat.le_mul_of_pos_left K (pow_pos hKpos c)
    have ht := Nat.le_mul_of_pos_right (K^c*K) hW
    dsimp only [V]
    nlinarith only [hh,ht]
  have hbig : K^c*W ≤ V := by
    have hh := Nat.le_mul_of_pos_right (K^c*W) hKpos
    dsimp only [V]
    nlinarith only [hh]
  have hpV : 1*K^plan.ps.length ≤ V := by
    have hh := Nat.pow_le_pow_right hK (show plan.ps.length ≤ c by omega)
    have ht := Nat.le_mul_of_pos_right (K^c) hW
    nlinarith only [hh,ht,hbig]
  have hbV : W*K^plan.bs.length ≤ V := by
    have hh := Nat.mul_le_mul_left W (Nat.pow_le_pow_right hK (show plan.bs.length ≤ c by omega))
    nlinarith only [hh,hbig]
  have hp := chain_cost_le T K 1 plan.ps.length V hK hpT hpV hKV hV
  have hb := chain_cost_le T K W plan.bs.length V hK hbT hbV hKV hV
  let rs := wiredChunkStages K W plan.one plan.exponent plan.prefixes plan.suffixes
  have hready := chunkStages_shape_ready d W c hW rs (wiredChunkStages_shape _ _ _ _ _ _)
  have hr : chunkStockAllowance T d rs ≤ chunkStockCoefficient T*V := by
    apply chunkStockAllowance_le
    · intro r hr; exact (hready r hr).1
    · intro r hr
      simpa only [V,K,Nat.mul_assoc] using (hready r hr).2
  exact total_stock_le T V (chunkStockCoefficient T) _ _ _ hV hp hb hr

theorem conditionalStockAllowance_le {t₀ T Q c d W : ℕ} (plan : ArchiveTilePlan t₀ T Q c d W)
    (N : ℕ) (hW : 0 < N → 0 < W) :
    plan.conditionalStockAllowance N ≤ stockCoefficient T*(capacity N ((2^d)^c)*(2^d*W)) := by
  by_cases hz : N = 0
  · simp [conditionalStockAllowance,capacity,hz]
  · simpa only [conditionalStockAllowance,capacity,hz,ite_false] using
      plan.stockAllowance_le (hW (Nat.pos_of_ne_zero hz))


theorem conditional_exec_within_volume {P U : Type} (plan : ArchiveTilePlan t₀ T Q c d W)
    (active : Fin T) (body : P → Pr P T Q (prime+K) U) (hA : 4 ≤ prime+K)
    (hW : 0 < N → 0 < W) (L w : ℕ) (hpacket : W = L*w) (hN : N ≤ (2^d)^c)
    (rows : Fin N → Fin (2^d) → List GaussianInt) (hlen : ∀ i j, (rows i j).length = L)
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K)) (hready : plan.Ready w rows S)
    (hactive : (S.R active).head?.isSome = decide (0 < N)) (depth : ℕ) :
    ∃ result : Result L rows, result.capacity = capacity N ((2^d)^c) ∧
      ∃ v' n, v'.user = v.user ∧ n ≤ plan.conditionalCost N S ∧
        ExecWithin body (fun z state => mnSize state+z ≤ mnSize (Host.mk v S)+depth+
          stockCoefficient T*(capacity N ((2^d)^c)*(2^d*W))) depth (plan.conditionalProgram active) (Host.mk v S) n
          (Host.mk v' {S with L := fun _ => [], R := (Function.update S.R plan.src
            ((List.ofFn fun j => cstream (prime+K) w (List.ofFn fun i => result.padded i j).flatten).flatten))}) := by
  obtain ⟨result,hcap,v',n,hu,hn,he⟩ := plan.conditional_exec_within active body hA hW L w hpacket hN
    rows hlen v S hready hactive depth
  refine ⟨result,hcap,v',n,hu,hn,?_⟩
  exact he.mono (by
    intro z state hs
    exact hs.trans (Nat.add_le_add_left (plan.conditionalStockAllowance_le N hW) _))

end ArchiveTilePlan
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
