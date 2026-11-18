module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackColumnProgram

/-! Place a reverse column on the selected archive bank while preserving the other archive. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open Matrix GoodForm IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable [M8.Machine.Net] {P U : Type} {d w W : ℕ}
local notation "N" => rowSwapBlock.tapes+35
local notation "M" => prime^(w+1)
local instance : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩

noncomputable def placedColumn {T : ℕ} (ports : Fin (N+1) ↪ Fin T) (k : Fin d) : Pr P T columnCapacity prime U :=
  statePlacedNormalized ports le_rfl (lt_of_lt_of_le (by decide : 0 < 217) (le_max_left ..))
    Empty.elim (columnProgram k)

theorem placedColumn_exec {T : ℕ} (ports : Fin (N+1) ↪ Fin T) (k : Fin d) (rows : Fin d → Fin d) (H J : ℕ)
    (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (body : P → Pr P T columnCapacity prime U) (v : HS T columnCapacity prime U) (S : Stacks T prime)
    (matrix : Matrix (Fin d) (Fin d) (ZMod M)) (unit : IsUnit (matrix (rows k) k)) (tail rest : List (Fin (prime+4)))
    (dest : ℤ → Fin 4) (q : ℤ) (empty : ∀ z, q ≤ z → z < q+(M^d*W : ℕ) → dest z = blank)
    (original : Fin (M^d*W) → ZMod 2) (addr : (Fin d → ZMod M) → Fin d → ZMod M)
    (code : S.R (ports (Fin.last N)) = orderedScheduleCode (((List.finRange d).take (k.val+1)).reverse) rows ++ rest) :
    let r := rows k
    let ready := ColumnReady (columnBank.trans ports) H J matrix tail SparseRoleCircuit.encode (fun _ => blank) dest 0 q original
    let clean := fun (D : Stacks T prime) => ∀ i : Fin N, 35 ≤ i.val → D.L (ports (columnPorts i)) = [] ∧ D.R (ports (columnPorts i)) = []
    let remaining := orderedScheduleCode (((List.finRange d).take k.val).reverse) rows ++ rest
    ready (fun x => stepOp k r matrix (Ring.inverse (matrix r k)) *ᵥ addr x) S → clean S →
    ∃ z F n, z.user = v.user ∧ n ≤ 1+columnProgramTime U k r w W H J ∧
      Exec body (placedColumn ports k) (mk v S) n (mk z F) ∧ ready addr F ∧ clean F ∧ F.R (ports (Fin.last N)) = remaining ∧
      ∀ i, (∀ j, ports j ≠ i) → F.L i = S.L i ∧ F.R i = S.R i := by
  intro r ready clean remaining before free
  let positive : 0 < columnCapacity := lt_of_lt_of_le (by decide : 0 < 217) (le_max_left ..)
  have project y D : ready y D ↔ ColumnReady columnBank H J matrix tail SparseRoleCircuit.encode
      (fun _ => blank) dest 0 q original y (embStk ports D) :=
    (columnReady_project ..).trans (columnReady_project columnBank H J matrix tail SparseRoleCircuit.encode (fun _ => blank) dest 0 q original y (embStk ports D)).symm
  obtain ⟨u,D,n,hu,hn,run,next,freeD,stream⟩ := columnProgram_exec k rows H J hm hw hW
    (P := Empty) Empty.elim (stateLiftDown positive (embDn ports v)) (embStk ports S)
    matrix unit tail rest dest q empty original addr code ((project ..).1 before) free
  obtain ⟨z,_,hz,placed⟩ := statePlaced_exec_normalized ports ports.injective le_rfl positive
    Empty.elim (body' := body) (fun e => nomatch e) v S run
  let F := embOvr ports D.get S
  have eq : embStk ports F = D := embStk_ovr ports.injective _ _
  rw [← eq] at next freeD stream
  exact ⟨z,F,_,hz.trans hu,Nat.add_le_add_left hn 1,placed,(project ..).2 next,freeD,stream,
    fun _ off => embOvr_off _ S off⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
