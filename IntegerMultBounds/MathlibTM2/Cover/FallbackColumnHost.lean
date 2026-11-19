module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackSwapColumn
public import IntegerMultBounds.MathlibTM2.Cover.FallbackPlacedShear

/-! Shared control capacity and a separate pivot stream for the reverse-column machine. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable [M8.Machine.Net] {P U : Type}
local notation "N" => rowSwapBlock.tapes+35
local notation "Q" => rowSwapBlock.states
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos prime_prime.pos _).ne'⟩

noncomputable abbrev columnCapacity := max 217 Q
noncomputable def columnPorts : Fin N ↪ Fin (N+1) := Fin.castLEEmb (Nat.le_succ _)
noncomputable def columnBank : Fin 35 ↪ Fin (N+1) :=
  ((Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)).trans columnPorts

theorem swapStates_pos : 0 < Q := Nat.zero_lt_of_lt rowSwapBlock.program.start.isLt

noncomputable def columnSwapProgram (d i j : ℕ) : Pr P (N+1) columnCapacity prime U :=
  statePlacedNormalized columnPorts (le_max_right ..) swapStates_pos Empty.elim (completeSwap d i j)

theorem columnSwapRecord_exec {d w W : ℕ} (i j : Fin d) (lt : i < j) (H J : ℕ)
    (hm : prime^(w+1) < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (body : P → Pr P (N+1) columnCapacity prime U) (v : HS (N+1) columnCapacity prime U) (S : Stacks (N+1) prime)
    (record : List (Fin (prime+4)))
    (dest : ℤ → Fin 4) (q : ℤ) (original : Fin ((prime^(w+1))^d*W) → ZMod 2)
    (addr : (Fin d → ZMod (prime^(w+1))) → Fin d → ZMod (prime^(w+1))) :
    let ready := ColumnRecordReady columnBank H J record SparseRoleCircuit.encode (fun _ => blank) dest 0 q original
    let clean := fun (D : Stacks (N+1) prime) => ∀ k : Fin N, 35 ≤ k.val → D.L (columnPorts k) = [] ∧ D.R (columnPorts k) = []
    ready addr S → clean S →
    ∃ z F n, z.user = v.user ∧ n ≤ 1+completeSwapTime (P := Empty) (U := U) Empty.elim d i j w W H J ∧
      Exec body (columnSwapProgram d i j) (mk v S) n (mk z F) ∧
      ready (fun x => addr x ∘ Equiv.swap i j) F ∧ clean F ∧
      F.L (Fin.last N) = S.L (Fin.last N) ∧ F.R (Fin.last N) = S.R (Fin.last N) := by
  intro ready clean before free
  let bank : Fin 35 ↪ Fin N := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
  have projected := (columnRecordReady_project ..).mp before
  obtain ⟨u,D,n,hu,hn,run,next,freeD⟩ := columnRecord_swap i j lt H J hm hw hW (P := Empty) Empty.elim
    (stateLiftDown swapStates_pos (embDn columnPorts v)) (embStk columnPorts S) record dest q original addr
    ((columnRecordReady_project bank ..).mpr projected) free
  obtain ⟨z,_,hz,placed⟩ := statePlaced_exec_normalized columnPorts columnPorts.injective (le_max_right 217 Q)
    swapStates_pos Empty.elim (body' := body) (fun e => nomatch e) v S run
  let F := embOvr columnPorts D.get S
  have eq : embStk columnPorts F = D := embStk_ovr columnPorts.injective _ _
  refine ⟨z,F,_,hz.trans hu,Nat.add_le_add_left hn 1,placed,(columnRecordReady_project ..).mpr ?_,?_,?_⟩
  · have h := (columnRecordReady_project bank ..).mp next
    rw [← eq] at h
    exact h
  · intro k hk
    have h := freeD k hk
    rw [← eq] at h
    exact h
  · apply embOvr_off
    intro k e
    have h := congrArg Fin.val e
    change k.val = N at h
    exact k.isLt.ne h

theorem columnSwapProgram_exec {d w W : ℕ} (i j : Fin d) (lt : i < j) (H J : ℕ)
    (hm : prime^(w+1) < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (body : P → Pr P (N+1) columnCapacity prime U) (v : HS (N+1) columnCapacity prime U) (S : Stacks (N+1) prime)
    (matrix : Matrix (Fin d) (Fin d) (ZMod (prime^(w+1)))) (tail : List (Fin (prime+4)))
    (dest : ℤ → Fin 4) (q : ℤ) (original : Fin ((prime^(w+1))^d*W) → ZMod 2)
    (addr : (Fin d → ZMod (prime^(w+1))) → Fin d → ZMod (prime^(w+1))) :
    let ready := ColumnReady columnBank H J matrix tail SparseRoleCircuit.encode (fun _ => blank) dest 0 q original
    let clean := fun (D : Stacks (N+1) prime) => ∀ k : Fin N, 35 ≤ k.val → D.L (columnPorts k) = [] ∧ D.R (columnPorts k) = []
    ready addr S → clean S →
    ∃ z F n, z.user = v.user ∧ n ≤ 1+completeSwapTime (P := Empty) (U := U) Empty.elim d i j w W H J ∧
      Exec body (columnSwapProgram d i j) (mk v S) n (mk z F) ∧
      ready (fun x => addr x ∘ Equiv.swap i j) F ∧ clean F ∧
      F.L (Fin.last N) = S.L (Fin.last N) ∧ F.R (Fin.last N) = S.R (Fin.last N) :=
  columnSwapRecord_exec i j lt H J hm hw hW body v S (matrixWords prime H matrix ++ tail) dest q original addr

end IntegerMultBounds.MathlibTM2.Cover.Fallback
