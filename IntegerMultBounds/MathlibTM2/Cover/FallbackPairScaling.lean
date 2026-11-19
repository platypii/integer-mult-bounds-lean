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

noncomputable def pairScalingTime (U : Type) (i k t : Fin d) (w W H J : ℕ) : ℕ :=
  let shearCost := fun useOne neg => 1+cleanPairShearTime (P := Empty) (U := U) (A := prime) Empty.elim
      (Function.Embedding.refl _) i k t prime w W H J false neg useOne
  let swapCost := 1+completeSwapTime (P := Empty) (U := U) Empty.elim d k t w W H J
  let exchangeCost := fun one => 2*shearCost one false + shearCost one true + 2*swapCost
  2*swapCost + exchangeCost true + exchangeCost false

/-- At fixed atom width, the whole reciprocal scaling has a per-symbol rate
independent of payload width and of the two counter widths. -/
theorem pairScalingTime_le_setup_add_volume (U : Type) (i k t : Fin d) (w : ℕ) :
    ∃ rate : ℕ, ∀ W H J, pairScalingTime U i k t w W H J ≤
      pairScalingTime U i k t w 0 H J + rate * ((prime^(w+1))^d * W) := by
  let shear := fun neg one W H J => cleanPairShearTime (P := Empty) (U := U) (A := prime)
    Empty.elim (Function.Embedding.refl _) i k t prime w W H J false neg one
  let swap := fun W H J => completeSwapTime (P := Empty) (U := U) Empty.elim d k t w W H J
  have shearRate (neg one : Bool) : ∃ r : ℕ, ∀ W H J, shear neg one W H J =
      shear neg one 0 H J + r * ((prime^(w+1))^d * W) :=
    ⟨_, fun W H J => cleanPairShearTime_eq_setup_add_volume _ _ i k t prime w W H J false neg one⟩
  have swapRate : ∃ r : ℕ, ∀ W H J, swap W H J ≤
      swap 0 H J + r * ((prime^(w+1))^d * W) :=
    ⟨_, fun W H J => completeSwapTime_le_setup_add_volume _ d k t w W H J⟩
  choose r hr using shearRate
  obtain ⟨s, hs⟩ := swapRate
  refine ⟨6*s + 2*r false true + r true true + 2*r false false + r true false, ?_⟩
  intro W H J
  unfold pairScalingTime
  change 2*(1+swap W H J) + (2*(1+shear false true W H J) + (1+shear true true W H J) +
    2*(1+swap W H J)) + (2*(1+shear false false W H J) + (1+shear true false W H J) +
    2*(1+swap W H J)) ≤ _
  rw [hr false true W, hr true true W, hr false false W, hr true false W]
  grw [hs W H J]
  dsimp only [shear, swap]
  exact le_of_eq (by ring)

theorem pairScaling_exec (i k t : Fin d) (hk : k < t) (a : Fin d → ZMod M) (unit : IsUnit (a i))
    (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (body : P → Pr P (N+1) columnCapacity prime U) (v : HS (N+1) columnCapacity prime U) (S : Stacks (N+1) prime)
    (tail rest : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^d*W : ℕ) → dest z = blank)
    (original : Fin (M^d*W) → ZMod 2) (addr : (Fin d → ZMod M) → Fin d → ZMod M) :
    let ready := fun y (D : Stacks (N+1) prime) =>
      ColumnReady columnBank H J (Matrix.diagonal a) tail SparseRoleCircuit.encode (fun _ => blank) dest 0 q original y D ∧
      (∀ j : Fin N, 35 ≤ j.val → D.L (columnPorts j) = [] ∧ D.R (columnPorts j) = []) ∧ D.R (Fin.last N) = rest
    ready addr S → ∃ z F n, z.user = v.user ∧ n ≤ pairScalingTime U i k t w W H J ∧
      Exec body (pairScaling i k t) (mk v S) n (mk z F) ∧
      ready (fun x => Function.update (Function.update (addr x) k (Ring.inverse (a i)*addr x k)) t (a i*addr x t)) F := by
  intro ready before
  let shearCost := fun useOne neg => 1+cleanPairShearTime (P := Empty) (U := U) (A := prime) Empty.elim
      (Function.Embedding.refl _) i k t prime w W H J false neg useOne
  let swapCost := 1+completeSwapTime (P := Empty) (U := U) Empty.elim d k t w W H J
  let exchangeCost := fun one => 2*shearCost one false + shearCost one true + 2*swapCost
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
  · change _ ≤ 2*swapCost + exchangeCost true + exchangeCost false
    omega
  · convert h₄ using 2
    funext j
    by_cases hit : j = t <;> by_cases control : j = k <;>
      simp_all [Function.comp_def,Equiv.swap_apply_of_ne_of_ne,hk.ne]

end IntegerMultBounds.MathlibTM2.Cover.Fallback
