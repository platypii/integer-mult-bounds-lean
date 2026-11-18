module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackColumnHost

/-! Execute either orientation of a reverse row addition on the shared column host. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable [M8.Machine.Net] {P U : Type} {d w W : ℕ}
local notation "N" => rowSwapBlock.tapes+35
local notation "M" => prime^(w+1)
local instance : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩

noncomputable def columnAddProgram (k t pivot : Fin d) : Pr P (N+1) columnCapacity prime U :=
  let shear := fun a b => placedShear columnBank (le_max_left ..) a b k t pivot prime
  if k < t then shear k t else
    .seq (columnSwapProgram d t k) (.seq (shear t k) (columnSwapProgram d t k))

theorem columnAddProgram_exec (k t pivot : Fin d) (ne : t ≠ k) (H J : ℕ)
    (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (body : P → Pr P (N+1) columnCapacity prime U) (v : HS (N+1) columnCapacity prime U) (S : Stacks (N+1) prime)
    (matrix : Matrix (Fin d) (Fin d) (ZMod M)) (unit : IsUnit (matrix pivot k)) (tail rest : List (Fin (prime+4)))
    (dest : ℤ → Fin 4) (q : ℤ) (empty : ∀ z, q ≤ z → z < q+(M^d*W : ℕ) → dest z = blank)
    (original : Fin (M^d*W) → ZMod 2) (addr : (Fin d → ZMod M) → Fin d → ZMod M) :
    let ready := fun y (D : Stacks (N+1) prime) =>
      ColumnReady columnBank H J matrix tail SparseRoleCircuit.encode (fun _ => blank) dest 0 q original y D ∧
      (∀ i : Fin N, 35 ≤ i.val → D.L (columnPorts i) = [] ∧ D.R (columnPorts i) = []) ∧ D.R (Fin.last N) = rest
    let shearCost := fun a b => 1+reverseRowTime (P := Empty) (U := U) (A := prime) Empty.elim
      (Function.Embedding.refl _) a b k t pivot prime w W H J
    let swapCost := 1+completeSwapTime (P := Empty) (U := U) Empty.elim d t k w W H J
    let c := matrix (Equiv.swap k pivot t) k * Ring.inverse (matrix pivot k)
    ready addr S → ∃ z F n, z.user = v.user ∧ n ≤ (if k < t then shearCost k t else swapCost+shearCost t k+swapCost) ∧
      Exec body (columnAddProgram k t pivot) (mk v S) n (mk z F) ∧
      ready (fun x => Function.update (addr x) t (addr x t+c*addr x k)) F := by
  intro ready shearCost swapCost c before
  have shear (a b : Fin d) (lt : a < b) y (u : HS (N+1) columnCapacity prime U) D (ok : ready y D) :
      ∃ z F n, z.user = u.user ∧ n ≤ shearCost a b ∧
        Exec body (placedShear columnBank (le_max_left ..) a b k t pivot prime) (mk u D) n (mk z F) ∧
        ready (fun x => Function.update (y x) b (y x b+c*y x a)) F := by
    obtain ⟨z,F,n,hz,hn,run,next,frame⟩ := placedShear_exec columnBank (le_max_left ..) a b k t pivot lt
      matrix prime_prime unit body H J hm hw hW u D tail SparseRoleCircuit.encode (fun _ => blank) dest 0 q empty original y ok.1
    have keep (i : Fin (N+1)) (hi : 35 ≤ i.val) := frame i (fun j eq => by
      have h := congrArg Fin.val eq
      change j.val = i.val at h
      omega)
    refine ⟨z,F,n,hz,hn,run,next,fun i hi => ?_,?_⟩
    · have e := keep (columnPorts i) hi
      exact ⟨e.1.trans (ok.2.1 i hi).1,e.2.trans (ok.2.1 i hi).2⟩
    · exact (keep _ (by change 35 ≤ rowSwapBlock.tapes+35; omega)).2.trans ok.2.2
  by_cases below : k < t
  · simpa only [columnAddProgram,ite_eq_left below] using shear k t below addr v S before
  have above := lt_of_le_of_ne (le_of_not_gt below) ne
  have swap y (u : HS (N+1) columnCapacity prime U) D (ok : ready y D) :
      ∃ z F n, z.user = u.user ∧ n ≤ swapCost ∧ Exec body (columnSwapProgram d t k) (mk u D) n (mk z F) ∧
        ready (fun x => y x ∘ Equiv.swap t k) F := by
    obtain ⟨z,F,n,hz,hn,run,next,clean,_,stream⟩ := columnSwapProgram_exec t k above H J hm hw hW
      body u D matrix tail dest q original y ok.1 ok.2.1
    exact ⟨z,F,n,hz,hn,run,next,clean,stream.trans ok.2.2⟩
  obtain ⟨u,D,l,hu,hl,first,swapped⟩ := swap addr v S before
  obtain ⟨y,E,m,hy,hm',middle,added⟩ := shear t k above _ u D swapped
  obtain ⟨z,F,n,hz,hn,last,doneRow⟩ := swap _ y E added
  simp only [columnAddProgram,ite_eq_right below]
  refine ⟨z,F,l+(m+n),hz.trans (hy.trans hu),by omega,Exec.seq first (Exec.seq middle last),?_⟩
  convert doneRow using 2
  funext i
  by_cases hit : i = t <;> by_cases control : i = k <;>
    simp_all [Function.comp_def,Equiv.swap_apply_of_ne_of_ne]

end IntegerMultBounds.MathlibTM2.Cover.Fallback
