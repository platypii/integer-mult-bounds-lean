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

omit [M8.Machine.Net] in
theorem shared_ne_last {c t : ℕ} (i : Fin c) :
    ((Fin.castAddEmb (n := c) t).trans (Fin.castAddEmb 1)) i ≠ Fin.last (c+t) :=
  fun eq => (i.castAdd t).isLt.ne (congrArg Fin.val eq)

/-- Run the signed residual diagonal and undo elimination on the same physical payload. -/
theorem archivedResidual_exec {Q T : ℕ} (parent : Fin d → (ZMod M)ˣ) (a : Fin (d+1) → (ZMod M)ˣ)
    (negative : Bool) (signValue : ∏ j, a j = if negative then -1 else 1)
    (capacity : columnCapacity ≤ Q) (signCapacity : (fieldSignProgram (0 : Fin (d+1)) true).1 ≤ Q)
    (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (pivots : Fin (d+1) → Fin (d+1)) (m : Matrix (Fin (d+1)) (Fin (d+1)) (ZMod M))
    (valid : Itinerary.Valid pivots m (d+1))
    (diag : Itinerary.run pivots m (d+1) = Matrix.diagonal fun j => (a j : ZMod M))
    (tail destTail suffix rest : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^(d+1)*W : ℕ) → dest z = blank)
    (original : Fin (M^(d+1)*W) → ZMod 2) :
    let words := fun n => matrixWords prime H (Itinerary.run pivots m n)
    let code := orderedScheduleCode (List.finRange (d+1)).reverse pivots ++ rest
    let rows := List.finRange d
    let weightsAt := fun i : Fin d => a i.succ
    let addr := signedAddress (b := w+1) negative (d := d)
    let reads := pivotReads rows
    let n := reads.length
    let k := fun _ : Fin n => (0 : Fin (d+1))
    let j := fun a => (reads.get a).1
    let t := fun a => (j a).succ
    let i := fun a => (reads.get a).2
    let pivot : Fin (d+1) → ZMod M := Fin.cons 1 (fun h => (weightsAt h : ZMod M))
    let width := fun a => 22+fieldSignSlots (k a)
    let total := Fintype.card (Σ a, Fin (width a))
    let ports := Fin.castAddEmb (n := (N+1)+total) 1
    let shared := (Fin.castAddEmb (n := N+1) total).trans ports
    let bank := fun a => (exchangeBank (N+1) width a).trans ports
    let record := (List.ofFn fun h => binSyms (A := prime) H (pivot h).val).flatten ++ (words (d+1) ++ suffix)
    let weights := (List.ofFn fun h => binSyms (A := prime) H (parent h : ZMod M).val).flatten ++ code
    let ready := fun y (D : Stacks (((N+1)+total)+1) prime) =>
      ColumnRecordReady (columnBank.trans shared) H J record SparseRoleCircuit.encode (fun _ => blank) dest 0 q original y D ∧
      (∀ h : Fin N, 35 ≤ h.val → D.L (shared (columnPorts h)) = [] ∧ D.R (shared (columnPorts h)) = []) ∧
      D.R (shared (Fin.last N)) = weights
    let program : Fin n → Pr Empty (((N+1)+total)+1) Q prime U := fun a =>
      let host := Fin.castAddEmb (n := N+1) (width a)
      let sign := extendSignBank columnBank (fieldSignSlots (k a))
      statePlacedNormalized (bank a) (le_refl Q) (lt_of_lt_of_le columnCapacity_pos capacity) Empty.elim
        (.seq (statePlacedNormalized host capacity columnCapacity_pos Empty.elim (childExchange (j a).val (i a).val (k a) (t a)))
          (.seq (installFieldHeaders ((installerPorts _).trans sign))
            (placedFieldNeg (k a) ((signPorts _).trans sign) signCapacity)))
    let cost := fun a =>
      let shear := fun neg => 1+cleanChildShearTime (P := Empty) (U := U) (A := prime) Empty.elim
        (Function.Embedding.refl _) prime (j a).val (i a).val (k a) (t a) neg w W H J
      let swap := 1+completeSwapTime (P := Empty) (U := U) Empty.elim (d+1) (k a) (t a) w W H J
      1+(1+(2*shear false+shear true+2*swap)+((10*J+12)+(21*(w+1)+12)+1+
        (1+(AtomSegment.chainConst (fieldSignOps (k a) true)*(M^(d+1)*W)*(width a+5)+6))))
    let spare := Fin.last ((N+1)+total)
    let off : ∀ h, shared h ≠ spare := shared_ne_last (t := total)
    let reverseHost := rewindPorts (d+1) shared spare off
    let reverseBank := fun n => columnBank.trans (archivePorts n)
    let active := reverseBank (d+1)
    let pop : Pr Empty (N+2) columnCapacity prime U := .seq (dropWords (active 2) (active 34) (active 0) (d+1))
      (dropWords (active 2) (Fin.last N).castSucc (active 0) d)
    let rewind : Pr Empty (((N+1)+total)+1) Q prime U := statePlacedNormalized reverseHost capacity columnCapacity_pos Empty.elim
      (.seq pop (reverseStages (d+1) (d+1)))
    let stageCost := 1+Finset.univ.sup (fun k => columnProgramTime U k (pivots k) w W H J)+((d+1)*(d+1)*(4*H+4)+1)
    let rewindCost := 1+(((d+1)*(4*H+4)+1+(d*(4*H+4)+1))+((d+1)*stageCost+1))
    let residual := .seq ((List.finRange n).foldr (fun a rest => .seq (program a) rest) (.act .done)) rewind
    let positive := lt_of_lt_of_le columnCapacity_pos capacity
    ∀ (host : Fin (((N+1)+total)+1) ↪ Fin T) (body : P → Pr P T Q prime U) v S,
      ready addr (embStk host S) →
      (∀ h : Fin total, S.L (host (ports (Fin.natAdd (N+1) h))) = [] ∧ S.R (host (ports (Fin.natAdd (N+1) h))) = []) →
      (words (d+1) ++ suffix,S.R (host spare)) = matrixArchive words (words 0 ++ tail) destTail (d+1) →
      ∃ z F l, z.user = v.user ∧ l ≤ 1+(((List.finRange n).map cost).sum+1+rewindCost) ∧
        Exec body (statePlacedNormalized host le_rfl positive Empty.elim residual) (mk v S) l (mk z F) ∧
        ColumnReady ((reverseBank 0).trans reverseHost) H J m tail SparseRoleCircuit.encode
          (fun _ => blank) dest 0 q original m.mulVec (embStk host F) ∧
        F.R (host (reverseHost (Fin.last N).castSucc)) = rest ∧
        F.R (host (reverseHost (reverseBank 1 34))) = destTail ∧
        ∀ j, (∀ i, host i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro words code rows weightsAt addr reads n k j t i pivot width total ports shared bank record weights ready program cost spare off reverseHost reverseBank active pop rewind stageCost rewindCost residual positive host body v S before aux archive
  let start := stateLiftDown positive (embDn host v)
  obtain ⟨u,D,l,hu,hl,scale,next,kept⟩ := archivedDiagonal_exec parent a negative signValue capacity signCapacity
    H J hm hw hW (words (d+1) ++ suffix) code dest q empty original (P := Empty) Empty.elim start (embStk host S) before aux
  have action : (Itinerary.run pivots m (d+1)).mulVec = (Matrix.diagonal fun j => (a j : ZMod M)).mulVec :=
    congrArg Matrix.mulVec diag
  have finish := finishArchivedResidual_exec shared spare off capacity pivot (fun j => (parent j : ZMod M))
    pivots m valid H J hm hw hW (P := Empty) Empty.elim start (embStk host S) tail destTail suffix rest dest q empty original
    ((List.finRange n).foldr (fun a rest => .seq (program a) rest) (.act .done)) (((List.finRange n).map cost).sum+1)
  obtain ⟨z,F,l',hz,hl',exec,result,_,stream,other⟩ := finish
    ⟨u,D,l,hu,hl,scale,action.symm ▸ next.1,next.2.1,next.2.2,kept⟩ archive
  obtain ⟨out,_,user,placed⟩ := statePlaced_exec_normalized host host.injective le_rfl positive Empty.elim
    (body' := body) (fun e => nomatch e) v S exec
  let final := embOvr host F.get S
  have view : embStk host final = F := embStk_ovr host.injective _ _
  rw [← view] at result stream other
  exact ⟨out,final,_,user.trans hz,Nat.add_le_add_left hl' 1,placed,result,stream,other,
    fun _ offHost => embOvr_off F.get S offHost⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback.Record
