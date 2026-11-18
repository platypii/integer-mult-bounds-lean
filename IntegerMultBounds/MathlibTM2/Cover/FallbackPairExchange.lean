module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackColumnHost
public import IntegerMultBounds.MathlibTM2.Cover.FallbackPlacedPairShear

/-! A signed exchange of two fields using three archived-weight shears. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable [M8.Machine.Net] {P U : Type} {d w W : ℕ}
local notation "N" => rowSwapBlock.tapes+35
local notation "M" => prime^(w+1)
local instance : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩

noncomputable def pairExchange (i k t : Fin d) (useOne : Bool := false) : Pr P (N+1) columnCapacity prime U :=
  let shear := fun neg => placedPairShear columnBank (le_max_left ..) prime i k t false neg useOne
  let swap := columnSwapProgram d k t
  .seq (shear false) (.seq swap (.seq (shear true) (.seq swap (shear false))))

theorem pairExchange_exec (i k t : Fin d) (hk : k < t) (a : Fin d → ZMod M) (unit : IsUnit (a i))
    (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (body : P → Pr P (N+1) columnCapacity prime U) (v : HS (N+1) columnCapacity prime U) (S : Stacks (N+1) prime)
    (tail rest : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^d*W : ℕ) → dest z = blank)
    (original : Fin (M^d*W) → ZMod 2) (addr : (Fin d → ZMod M) → Fin d → ZMod M) (useOne : Bool := false) :
    let weight := if useOne then 1 else a i
    let ready := fun y (D : Stacks (N+1) prime) =>
      ColumnReady columnBank H J (Matrix.diagonal a) tail SparseRoleCircuit.encode (fun _ => blank) dest 0 q original y D ∧
      (∀ j : Fin N, 35 ≤ j.val → D.L (columnPorts j) = [] ∧ D.R (columnPorts j) = []) ∧ D.R (Fin.last N) = rest
    let shearCost := fun neg => 1+cleanPairShearTime (P := Empty) (U := U) (A := prime) Empty.elim
      (Function.Embedding.refl _) i k t prime w W H J false neg useOne
    let swapCost := 1+completeSwapTime (P := Empty) (U := U) Empty.elim d k t w W H J
    ready addr S → ∃ z F n, z.user = v.user ∧ n ≤ 2*shearCost false + shearCost true + 2*swapCost ∧
      Exec body (pairExchange i k t useOne) (mk v S) n (mk z F) ∧
      ready (fun x => Function.update (Function.update (addr x) k (-Ring.inverse weight*addr x t)) t (weight*addr x k)) F := by
  intro weight ready shearCost swapCost before
  have shear (neg : Bool) y (u : HS (N+1) columnCapacity prime U) D (ok : ready y D) :
      ∃ z F n, z.user = u.user ∧ n ≤ shearCost neg ∧
        Exec body (placedPairShear columnBank (le_max_left ..) prime i k t false neg useOne) (mk u D) n (mk z F) ∧
        ready (fun x => Function.update (y x) t (y x t+(if neg then -Ring.inverse weight else weight)*y x k)) F := by
    obtain ⟨z,F,n,hz,hn,run,next,frame⟩ := placedPairShear_exec columnBank (le_max_left ..) i k t hk
      false neg a unit prime_prime body H J hm hw hW u D tail SparseRoleCircuit.encode (fun _ => blank) dest 0 q empty original y ok.1 useOne
    have keep (i : Fin (N+1)) (hi : 35 ≤ i.val) := frame i (fun j eq => by
      have h := congrArg Fin.val eq
      change j.val = i.val at h
      omega)
    refine ⟨z,F,n,hz,hn,run,next,fun i hi => ?_,?_⟩
    · have e := keep (columnPorts i) hi
      exact ⟨e.1.trans (ok.2.1 i hi).1,e.2.trans (ok.2.1 i hi).2⟩
    · exact (keep _ (by change 35 ≤ rowSwapBlock.tapes+35; omega)).2.trans ok.2.2
  have swap y (u : HS (N+1) columnCapacity prime U) D (ok : ready y D) :
      ∃ z F n, z.user = u.user ∧ n ≤ swapCost ∧ Exec body (columnSwapProgram d k t) (mk u D) n (mk z F) ∧
        ready (fun x => y x ∘ Equiv.swap k t) F := by
    obtain ⟨z,F,n,hz,hn,run,next,clean,_,stream⟩ := columnSwapProgram_exec k t hk H J hm hw hW
      body u D (Matrix.diagonal a) tail dest q original y ok.1 ok.2.1
    exact ⟨z,F,n,hz,hn,run,next,clean,stream.trans ok.2.2⟩
  have weightUnit : IsUnit weight := by cases useOne <;> simp_all [weight]
  obtain ⟨u,D,l,hu,hl,r₁,h₁⟩ := shear false addr v S before
  obtain ⟨y,E,m,hy,hm',r₂,h₂⟩ := swap _ u D h₁
  obtain ⟨z,F,n,hz,hn,r₃,h₃⟩ := shear true _ y E h₂
  obtain ⟨u',G,p,hu',hp,r₄,h₄⟩ := swap _ z F h₃
  obtain ⟨z',K,s,hz',hs,r₅,h₅⟩ := shear false _ u' G h₄
  refine ⟨z',K,_,hz'.trans (hu'.trans (hz.trans (hy.trans hu))),?_,Exec.seq r₁ (Exec.seq r₂ (Exec.seq r₃ (Exec.seq r₄ r₅))),?_⟩
  · omega
  · convert h₅ using 2
    funext j
    by_cases hit : j = t <;> by_cases control : j = k <;>
      simp_all [Function.comp_def,Equiv.swap_apply_of_ne_of_ne,hk.ne,mul_add,← mul_assoc,
        Ring.inverse_mul_cancel _ weightUnit,Ring.mul_inverse_cancel _ weightUnit]

end IntegerMultBounds.MathlibTM2.Cover.Fallback
