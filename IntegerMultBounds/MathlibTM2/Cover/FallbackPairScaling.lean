module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackPairExchange

/-! Execute reciprocal diagonal scaling without changing coordinate order. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable [M8.Machine.Net] {P U : Type} {d w W : ℕ}
local notation "N" => rowSwapBlock.tapes+35
local notation "M" => prime^(w+1)
local instance : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩

noncomputable def pairScaling (i k t : Fin d) : Pr P (N+1) columnCapacity prime U :=
  let swap := columnSwapProgram d k t
  .seq swap (.seq (pairExchange i k t true) (.seq swap (pairExchange i k t false)))

theorem pairScaling_exec (i k t : Fin d) (hk : k < t) (a : Fin d → ZMod M) (unit : IsUnit (a i))
    (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (body : P → Pr P (N+1) columnCapacity prime U) (v : HS (N+1) columnCapacity prime U) (S : Stacks (N+1) prime)
    (tail rest : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^d*W : ℕ) → dest z = blank)
    (original : Fin (M^d*W) → ZMod 2) (addr : (Fin d → ZMod M) → Fin d → ZMod M) :
    let ready := fun y (D : Stacks (N+1) prime) =>
      ColumnReady columnBank H J (Matrix.diagonal a) tail SparseRoleCircuit.encode (fun _ => blank) dest 0 q original y D ∧
      (∀ j : Fin N, 35 ≤ j.val → D.L (columnPorts j) = [] ∧ D.R (columnPorts j) = []) ∧ D.R (Fin.last N) = rest
    let shearCost := fun useOne neg => 1+cleanPairShearTime (P := Empty) (U := U) (A := prime) Empty.elim
      (Function.Embedding.refl _) i k t prime w W H J false neg useOne
    let swapCost := 1+completeSwapTime (P := Empty) (U := U) Empty.elim d k t w W H J
    let exchangeCost := fun one => 2*shearCost one false + shearCost one true + 2*swapCost
    ready addr S → ∃ z F n, z.user = v.user ∧ n ≤ 2*swapCost + exchangeCost true + exchangeCost false ∧
      Exec body (pairScaling i k t) (mk v S) n (mk z F) ∧
      ready (fun x => Function.update (Function.update (addr x) k (Ring.inverse (a i)*addr x k)) t (a i*addr x t)) F := by
  intro ready shearCost swapCost exchangeCost before
  have swap y (u : HS (N+1) columnCapacity prime U) D (ok : ready y D) :
      ∃ z F n, z.user = u.user ∧ n ≤ swapCost ∧ Exec body (columnSwapProgram d k t) (mk u D) n (mk z F) ∧
        ready (fun x => y x ∘ Equiv.swap k t) F := by
    obtain ⟨z,F,n,hz,hn,run,next,clean,_,stream⟩ := columnSwapProgram_exec k t hk H J hm hw hW
      body u D (Matrix.diagonal a) tail dest q original y ok.1 ok.2.1
    exact ⟨z,F,n,hz,hn,run,next,clean,stream.trans ok.2.2⟩
  obtain ⟨u,D,l,hu,hl,r₁,h₁⟩ := swap addr v S before
  obtain ⟨y,E,m,hy,hm',r₂,h₂⟩ := pairExchange_exec i k t hk a unit H J hm hw hW body u D tail rest dest q empty original _ true h₁
  obtain ⟨z,F,n,hz,hn,r₃,h₃⟩ := swap _ y E h₂
  obtain ⟨u',G,p,hu',hp,r₄,h₄⟩ := pairExchange_exec i k t hk a unit H J hm hw hW body z F tail rest dest q empty original _ false h₃
  change m ≤ exchangeCost true at hm'
  change p ≤ exchangeCost false at hp
  refine ⟨u',G,_,hu'.trans (hz.trans (hy.trans hu)),?_,Exec.seq r₁ (Exec.seq r₂ (Exec.seq r₃ r₄)),?_⟩
  · omega
  · convert h₄ using 2
    funext j
    by_cases hit : j = t <;> by_cases control : j = k <;>
      simp_all [Function.comp_def,Equiv.swap_apply_of_ne_of_ne,hk.ne]

end IntegerMultBounds.MathlibTM2.Cover.Fallback
