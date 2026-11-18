module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackPlacedDiagonal
public import IntegerMultBounds.MathlibTM2.Cover.FallbackReverseStages

/-! Recover the residual matrix action on the signed payload. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable [M8.Machine.Net] {P U : Type} {d w W : ℕ}
local notation "N" => rowSwapBlock.tapes+35
local notation "M" => prime^(w+1)
local instance : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩

noncomputable def diagonalRewind (d : ℕ) : Pr P (N+2) columnCapacity prime U :=
  .seq (placedDiagonalPairs (archivePorts (d+1)) d) (reverseStages (d+1) (d+1))

theorem diagonalRewind_exec (rows : Fin (d+1) → Fin (d+1)) (m : Matrix (Fin (d+1)) (Fin (d+1)) (ZMod M))
    (valid : Itinerary.Valid rows m (d+1)) (a : Fin (d+1) → (ZMod M)ˣ)
    (diag : Itinerary.run rows m (d+1) = Matrix.diagonal fun j => (a j : ZMod M))
    (s : (ZMod M)ˣ) (sign : ∏ j, a j = s) (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (body : P → Pr P (N+2) columnCapacity prime U) (v : HS (N+2) columnCapacity prime U) (S : Stacks (N+2) prime)
    (tail destTail suffix rest : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^(d+1)*W : ℕ) → dest z = blank) (original : Fin (M^(d+1)*W) → ZMod 2) :
    let bank := fun n => columnBank.trans (archivePorts n)
    let ready := fun n t => ColumnReady (bank n) H J (Itinerary.run rows m n) t SparseRoleCircuit.encode
      (fun _ => blank) dest 0 q original
    let clean := fun (D : Stacks (N+2) prime) => ∀ i : Fin N, 35 ≤ i.val → D.L (columnPorts i).castSucc = [] ∧ D.R (columnPorts i).castSucc = []
    let anchor := fun x j => ((Fin.cons s (fun _ => 1) : Fin (d+1) → (ZMod M)ˣ) j : ZMod M) * x j
    let schedule := orderedScheduleCode (List.finRange (d+1)).reverse rows ++ rest
    let words := fun n => matrixWords prime H (Itinerary.run rows m n)
    let pairCost := ((List.finRange d).map fun i => pairScalingTime U i.succ 0 i.succ w W H J).sum
    let stepCost := 1+Finset.univ.sup (fun k => columnProgramTime U k (rows k) w W H J)+((d+1)*(d+1)*(4*H+4)+1)
    ready (d+1) suffix anchor S → clean S → S.R (Fin.last N).castSucc = schedule →
    (S.R (bank (d+1) 34),S.R (bank (d+2) 34)) = matrixArchive words (words 0 ++ tail) destTail (d+1) →
    ∃ z F n, z.user = v.user ∧ n ≤ (1+(pairCost+1))+((d+1)*stepCost+1) ∧
      Exec body (diagonalRewind d) (mk v S) n (mk z F) ∧ ready 0 tail (fun x => m.mulVec x) F ∧
      clean F ∧ F.R (Fin.last N).castSucc = rest ∧ F.R (bank 1 34) = destTail := by
  intro bank ready clean anchor schedule words pairCost stepCost before free code packed
  have initial := before
  unfold ready at initial
  rw [diag] at initial
  obtain ⟨u,D,l,hu,hl,scale,⟨next,freeD,stream⟩,frame⟩ := placedDiagonalPairs_exec (archivePorts (d+1)) a
    H J hm hw hW body v S suffix schedule dest q empty original s sign ⟨initial,
      fun j hj => by simpa only [archivePorts_workspace _ _ hj] using free j hj,by simpa only [archivePorts_stream] using code⟩
  have preserved : D.R (bank (d+1) 34) = S.R (bank (d+1) 34) :=
    next.choose_spec.1.archive.trans initial.choose_spec.1.archive.symm
  have other := (frame _ (archivePorts_other (d+1))).2
  rw [← diag] at next
  obtain ⟨z,F,n,hz,hn,rewind,result⟩ := reverseStages_exec rows H J hm hw hW body m tail destTail rest dest q empty original
    (d+1) le_rfl valid u D suffix next
    (fun j hj => by simpa only [archivePorts_workspace _ _ hj] using freeD j hj)
    ((Prod.ext preserved other).trans packed)
    (by rw [List.take_of_length_le (by simp)]; simpa only [archivePorts_stream] using stream)
  exact ⟨z,F,l+n,hz.trans hu,Nat.add_le_add hl hn,Exec.seq scale rewind,result⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
