module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackSignedResidual

/-! Consume one live record in the emitted pivot and sign streams. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable [M8.Machine.Net] {P U : Type} {d w W : ℕ}
local notation "N" => rowSwapBlock.tapes+35
local notation "M" => prime^(w+1)
local instance : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩

theorem residualRecord_exec {r : ℕ}
    (table : Matrix (Fin r) (Fin r) (ZMod prime) → Matrix (Fin (d+1)) (Fin (d+1)) (ZMod prime))
    (g : LabelPadding.Label r (w+1)) (m : Matrix (Fin (d+1)) (Fin (d+1)) (ZMod M))
    (det : m.det = 1 ∨ m.det = -1)
    (lift : (LabelRing.res prime (w+1) (by omega)).mapMatrix m = table ((LabelRing.res prime (w+1) (by omega)).mapMatrix g))
    (block count : ℕ) (index : block*M^(r*r)+(LabelAddress.address g).val < count) (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (body : P → Pr P (N+2) columnCapacity prime U) (v : HS (N+2) columnCapacity prime U) (S : Stacks (N+2) prime)
    (tail rest : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^(d+1)*W : ℕ) → dest z = blank) (original : Fin (M^(d+1)*W) → ZMod 2) :
    let bank := fun n => columnBank.trans (archivePorts n)
    let ready := ColumnReady (bank 0) H J m tail SparseRoleCircuit.encode
      (fun _ => blank) dest 0 q original
    let clean := fun (D : Stacks (N+2) prime) => ∀ i : Fin N, 35 ≤ i.val → D.L (columnPorts i).castSucc = [] ∧ D.R (columnPorts i).castSucc = []
    let anchor := fun (negative : Bool) x j => ((Fin.cons (if negative then -1 else 1) (fun _ => 1) : Fin (d+1) → (ZMod M)ˣ) j : ZMod M) * x j
    let j := block*M^(r*r)+(LabelAddress.address g).val
    let rows := classPivots (table ((LabelRing.res prime (w+1) (by omega)).mapMatrix g))
    let code := fun t =>
      let pivots := classPivots (table (LabelStock.residue r (w+1) 1 t))
      scheduleCode (A := prime) pivots ++ orderedScheduleCode (List.finRange (d+1)).reverse pivots
    let bit := (signStream (A := prime) table (w+1) count)[j]?
    let pairCost := ((List.finRange d).map fun i => pairScalingTime U i.succ 0 i.succ w W H J).sum
    let stepCost := 1+Finset.univ.sup (fun k => columnProgramTime U k (rows k) w W H J)+((d+1)*(d+1)*(4*H+4)+1)
    let forwardCost := (d+1)*(2*(d+1)+(4*w+4+columnTime (d+1) prime w H))+1
    (∀ neg, bit = some (bitSymbol neg) → ready (anchor neg) S) → clean S → S.R (Fin.last N).castSucc = ((List.range count).drop j).flatMap code ++ rest →
    ∃ z F n, z.user = v.user ∧ n ≤ forwardCost + ((1+(pairCost+1))+((d+1)*stepCost+1)) ∧
      Exec body (signedResidual d) (mk v S) n (mk z F) ∧ ready (fun x => m.mulVec x) F ∧
      clean F ∧ F.R (Fin.last N).castSucc = ((List.range count).drop (j+1)).flatMap code ++ rest ∧ F.R (bank 1 34) = S.R (bank 1 34) := by
  intro bank ready clean anchor j rows code bit pairCost stepCost forwardCost before free stream
  obtain ⟨neg,hbit,valid,sign⟩ := signStream_at (A := prime) table (by omega) g m block count det lift index
  let s : (ZMod M)ˣ := if neg then -1 else 1
  have sign' : (Itinerary.run rows m (d+1)).det = (s : ZMod M) := by cases neg <;> simpa [s,rows] using sign
  have addr := LabelStock.residue_at (by omega : 0 < w+1) block 1 0 (by decide) g
  simp only [Nat.mul_one,Nat.add_zero] at addr
  have head : code j = scheduleCode rows ++ orderedScheduleCode (List.finRange (d+1)).reverse rows := by
    simp only [code,j,addr,rows]
  have split := (List.getElem_cons_drop (show j < (List.range count).length by simpa [j] using index)).symm
  simp only [List.getElem_range] at split
  rw [split,List.flatMap_cons,head,List.append_assoc,List.append_assoc] at stream
  exact signedResidual_exec rows m valid s sign' H J hm hw hW body v S tail _ dest q empty original
    (before neg hbit) free stream

end IntegerMultBounds.MathlibTM2.Cover.Fallback
