module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackReverseStages
public import IntegerMultBounds.MathlibTM2.Cover.FallbackCorrectedExchange

/-! Execute the archived residual diagonal and the reverse elimination on one host. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback.Record
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host Mult.PhaseCellToeplitz
open M8 ActualAffineScaling FlatCoordinateLayout
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable [M8.Machine.Net] {P U : Type} {d w W : ℕ}
local notation "N" => rowSwapBlock.tapes+35
local notation "M" => prime^(w+1)
local instance : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩

theorem finishArchivedResidual_exec {r b T Q : ℕ} (columns : Fin (N+1) ↪ Fin T)
    (spare : Fin T) (off : ∀ i, columns i ≠ spare) (capacity : columnCapacity ≤ Q) (pivot : Fin r → ZMod M) (parent : Fin b → ZMod M)
    (rows : Fin d → Fin d) (m : Matrix (Fin d) (Fin d) (ZMod M)) (valid : Itinerary.Valid rows m d)
    (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (body : P → Pr P T Q prime U) (v : HS T Q prime U) (S : Stacks T prime)
    (tail destTail suffix rest : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^d*W : ℕ) → dest z = blank) (original : Fin (M^d*W) → ZMod 2) :
    let host := rewindPorts d columns spare off
    let stage := Itinerary.run rows m
    let words := fun n => matrixWords prime H (stage n)
    let bank := fun n => columnBank.trans (archivePorts n)
    let stream := (Fin.last N).castSucc
    let code := orderedScheduleCode (List.finRange d).reverse rows ++ rest
    let pack := fun {k : ℕ} (a : Fin k → ZMod M) => (List.ofFn fun j => binSyms (A := prime) H (a j).val).flatten
    let clean := fun (D : Stacks (N+2) prime) => ∀ j : Fin N, 35 ≤ j.val →
      D.L (columnPorts j).castSucc = [] ∧ D.R (columnPorts j).castSucc = []
    let pop := .seq (dropWords (bank d 2) (bank d 34) (bank d 0) r) (dropWords (bank d 2) stream (bank d 0) b)
    let cost := 1+Finset.univ.sup (fun k => columnProgramTime U k (rows k) w W H J)+(d*d*(4*H+4)+1)
    ∀ (diagonal : Pr P T Q prime U) (diagonalCost : ℕ),
    (∃ u D l, u.user = v.user ∧ l ≤ diagonalCost ∧ Exec body diagonal (mk v S) l (mk u D) ∧
      ColumnRecordReady (columnBank.trans columns) H J (pack pivot ++ (words d ++ suffix)) SparseRoleCircuit.encode
      (fun _ => blank) dest 0 q original (stage d).mulVec D ∧
    (∀ j : Fin N, 35 ≤ j.val → D.L (columns (columnPorts j)) = [] ∧ D.R (columns (columnPorts j)) = []) ∧
    D.R (columns (Fin.last N)) = pack parent ++ code ∧ D.R spare = S.R spare) →
    (words d ++ suffix,S.R spare) = matrixArchive words (words 0 ++ tail) destTail d →
    ∃ z F l, z.user = v.user ∧ l ≤ diagonalCost+(1+(((r*(4*H+4)+1)+(b*(4*H+4)+1))+(d*cost+1))) ∧
      Exec body (.seq diagonal (statePlacedNormalized host capacity (lt_of_lt_of_le (by decide : 0 < 217) (le_max_left ..)) Empty.elim (.seq pop (reverseStages d d)))) (mk v S) l (mk z F) ∧
      ColumnReady ((bank 0).trans host) H J m tail SparseRoleCircuit.encode (fun _ => blank) dest 0 q original m.mulVec F ∧
      clean (embStk host F) ∧ F.R (host stream) = rest ∧ F.R (host (bank 1 34)) = destTail := by
  intro host stage words bank stream code pack clean pop cost diagonal diagonalCost performed archive
  obtain ⟨u,D,l,hu,hl,scale,next,free,schedule,kept⟩ := performed
  obtain ⟨z,F,n,hz,hn,run,ready,cleanF,streamF,other,_⟩ := placedWeightedRewind_exec columns spare off capacity
    pivot parent rows m valid H J hm hw hW body u D tail destTail suffix rest dest q empty original next free schedule
    (by rw [kept]; exact archive)
  exact ⟨z,F,_,hz.trans hu,Nat.add_le_add hl hn,Exec.seq scale run,ready,cleanF,streamF,other⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback.Record
