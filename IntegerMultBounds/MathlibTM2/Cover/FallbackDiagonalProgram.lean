module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackPairScaling

/-! Apply all reciprocal pairs to a payload whose anchor already carries the diagonal sign. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable [M8.Machine.Net] {P U : Type} {d w W : ℕ}
local notation "N" => rowSwapBlock.tapes+35
local notation "M" => prime^(w+1)
local instance : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩

noncomputable def diagonalPairs : List (Fin d) → Pr P (N+1) columnCapacity prime U
  | [] => .act .done
  | i :: is => .seq (pairScaling i.succ 0 i.succ) (diagonalPairs is)

theorem diagonalPairs_exec (a : Fin (d+1) → (ZMod M)ˣ) (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (body : P → Pr P (N+1) columnCapacity prime U) (v : HS (N+1) columnCapacity prime U) (S : Stacks (N+1) prime)
    (tail rest : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^(d+1)*W : ℕ) → dest z = blank)
    (original : Fin (M^(d+1)*W) → ZMod 2) (s : (ZMod M)ˣ) (sign : ∏ j, a j = s) :
    let matrix := Matrix.diagonal (fun j => (a j : ZMod M))
    let ready := fun y (D : Stacks (N+1) prime) =>
      ColumnReady columnBank H J matrix tail SparseRoleCircuit.encode (fun _ => blank) dest 0 q original y D ∧
      (∀ j : Fin N, 35 ≤ j.val → D.L (columnPorts j) = [] ∧ D.R (columnPorts j) = []) ∧ D.R (Fin.last N) = rest
    let cost := fun i : Fin d => pairScalingTime U i.succ 0 i.succ w W H J
    let anchor := fun x j => ((Fin.cons s (fun _ => 1) : Fin (d+1) → (ZMod M)ˣ) j : ZMod M) * x j
    ready anchor S → ∃ z F n, z.user = v.user ∧ n ≤ ((List.finRange d).map cost).sum+1 ∧
      Exec body (diagonalPairs (List.finRange d)) (mk v S) n (mk z F) ∧ ready (fun x => matrix.mulVec x) F := by
  intro matrix ready cost anchor before
  let weight := fun i : Fin d => a i.succ
  have loop (is : List (Fin d)) y (u : HS (N+1) columnCapacity prime U) D (ok : ready y D) :
      ∃ z F n, z.user = u.user ∧ n ≤ (is.map cost).sum+1 ∧
        Exec body (diagonalPairs is) (mk u D) n (mk z F) ∧ ready (fun x => applyPairs weight is (y x)) F := by
    induction is generalizing y u D with
    | nil => exact ⟨u,D,1,rfl,by simp,Exec.act (body := body) .done _,ok⟩
    | cons i is ih =>
      obtain ⟨v',E,l,hv,hl,run,next⟩ := pairScaling_exec i.succ 0 i.succ (Fin.succ_pos i)
        (fun j => (a j : ZMod M)) (a i.succ).isUnit H J hm hw hW body u D tail rest dest q empty original y ok
      let scaled := fun x j => (pair i (weight i) j : ZMod M) * y x j
      have placed : ready scaled E := by
        convert next using 2
        funext j
        cases j using Fin.cases with
        | zero => simp [scaled,pair,weight,(Fin.succ_ne_zero i).symm]
        | succ j => by_cases eq : j = i <;> simp [scaled,pair,weight,eq,Fin.succ_ne_zero]
      obtain ⟨z,F,n,hz,hn,finish,result⟩ := ih scaled v' E placed
      exact ⟨z,F,l+n,hz.trans hv,by change l ≤ cost i at hl; simp only [List.map_cons,List.sum_cons]; omega,
        Exec.seq run finish,result⟩
  obtain ⟨z,F,n,hz,hn,run,result⟩ := loop (List.finRange d) anchor v S before
  refine ⟨z,F,n,hz,hn,run,?_⟩
  convert result using 2
  funext j
  have coord := congrFun (unit_pairs a) j
  rw [sign] at coord
  simp only [matrix,Matrix.mulVec_diagonal,applyPairs_eq,← List.ofFn_eq_map,List.prod_ofFn]
  rw [coord]
  simp [anchor,weight,Pi.mul_apply,Finset.prod_apply,Units.coe_prod,mul_left_comm,mul_assoc]

end IntegerMultBounds.MathlibTM2.Cover.Fallback
