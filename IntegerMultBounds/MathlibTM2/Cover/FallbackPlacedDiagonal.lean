module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackDiagonalProgram

/-! Run the diagonal pairs on the active archive and preserve the opposite archive. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable [M8.Machine.Net] {P U : Type} {d w W : ℕ}
local notation "N" => rowSwapBlock.tapes+35
local notation "M" => prime^(w+1)
local instance : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩

noncomputable def placedDiagonalPairs {T : ℕ} (ports : Fin (N+1) ↪ Fin T) (d : ℕ) : Pr P T columnCapacity prime U :=
  statePlacedNormalized ports le_rfl (lt_of_lt_of_le (by decide : 0 < 217) (le_max_left ..))
    Empty.elim (diagonalPairs (List.finRange d))

theorem placedDiagonalPairs_exec {T : ℕ} (ports : Fin (N+1) ↪ Fin T) (a : Fin (d+1) → (ZMod M)ˣ) (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (body : P → Pr P T columnCapacity prime U) (v : HS T columnCapacity prime U) (S : Stacks T prime)
    (tail rest : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^(d+1)*W : ℕ) → dest z = blank)
    (original : Fin (M^(d+1)*W) → ZMod 2) (s : (ZMod M)ˣ) (sign : ∏ j, a j = s) :
    let matrix := Matrix.diagonal (fun j => (a j : ZMod M))
    let ready := fun y (D : Stacks T prime) =>
      ColumnReady (columnBank.trans ports) H J matrix tail SparseRoleCircuit.encode (fun _ => blank) dest 0 q original y D ∧
      (∀ j : Fin N, 35 ≤ j.val → D.L (ports (columnPorts j)) = [] ∧ D.R (ports (columnPorts j)) = []) ∧ D.R (ports (Fin.last N)) = rest
    let cost := fun i : Fin d => pairScalingTime U i.succ 0 i.succ w W H J
    let anchor := fun x j => ((Fin.cons s (fun _ => 1) : Fin (d+1) → (ZMod M)ˣ) j : ZMod M) * x j
    ready anchor S → ∃ z F n, z.user = v.user ∧ n ≤ 1+(((List.finRange d).map cost).sum+1) ∧
      Exec body (placedDiagonalPairs ports d) (mk v S) n (mk z F) ∧ ready (fun x => matrix.mulVec x) F ∧
      ∀ j, (∀ i, ports i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro matrix ready cost anchor before
  let positive : 0 < columnCapacity := lt_of_lt_of_le (by decide : 0 < 217) (le_max_left ..)
  have project y D : ColumnReady (columnBank.trans ports) H J matrix tail SparseRoleCircuit.encode
      (fun _ => blank) dest 0 q original y D ↔ ColumnReady columnBank H J matrix tail SparseRoleCircuit.encode
      (fun _ => blank) dest 0 q original y (embStk ports D) :=
    (columnReady_project ..).trans (columnReady_project columnBank H J matrix tail SparseRoleCircuit.encode
      (fun _ => blank) dest 0 q original y (embStk ports D)).symm
  obtain ⟨u,D,n,hu,hn,run,next,free,stream⟩ := diagonalPairs_exec a H J hm hw hW (P := Empty) Empty.elim
    (stateLiftDown positive (embDn ports v)) (embStk ports S) tail rest dest q empty original s sign
    ⟨(project ..).1 before.1,before.2⟩
  obtain ⟨z,_,hz,placed⟩ := statePlaced_exec_normalized ports ports.injective le_rfl positive
    Empty.elim (body' := body) (fun e => nomatch e) v S run
  let F := embOvr ports D.get S
  have eq : embStk ports F = D := embStk_ovr ports.injective _ _
  rw [← eq] at next free stream
  exact ⟨z,F,_,hz.trans hu,Nat.add_le_add_left hn 1,placed,⟨(project ..).2 next,free,stream⟩,fun _ off => embOvr_off _ S off⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
