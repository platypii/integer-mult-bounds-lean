module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackNextRecord
public import IntegerMultBounds.MathlibTM2.Cover.FallbackForwardStages
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

/-- Load a queued payload, run the signed residual diagonal, and undo elimination while preserving the queue tail. -/
theorem archivedResidual_exec {Q T r records : ℕ} (parent : Fin d → (ZMod M)ˣ) (a : Fin (d+1) → (ZMod M)ˣ)
    (negative : Bool)
    (capacity : columnCapacity ≤ Q) (signCapacity : (fieldSignProgram (0 : Fin (d+1)) true).1 ≤ Q)
    (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (table : Matrix (Fin r) (Fin r) (ZMod prime) → Matrix (Fin (d+1)) (Fin (d+1)) (ZMod prime))
    (g : LabelPadding.Label r (w+1)) (m : Matrix (Fin (d+1)) (Fin (d+1)) (ZMod M))
    (det : m.det = 1 ∨ m.det = -1)
    (lift : (LabelRing.res prime (w+1) (by omega)).mapMatrix m = table ((LabelRing.res prime (w+1) (by omega)).mapMatrix g))
    (block : ℕ) (live : block*M^(r*r)+(LabelAddress.address g).val < records)
    (inputs : ℕ → Array d 1 (w+1) W) (outs : List (Array d 1 (w+1) W))
    (result : (signedInputs table (w+1) records inputs).Forall₂ Correct outs)
    (tail destTail suffix rest : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^(d+1)*W : ℕ) → dest z = blank)
    (original : Fin (M^(d+1)*W) → ZMod 2) :
    let entry := block*M^(r*r)+(LabelAddress.address g).val
    let pivots := classPivots (table ((LabelRing.res prime (w+1) (by omega)).mapMatrix g))
    Itinerary.run pivots m (d+1) = Matrix.diagonal (fun j => (a j : ZMod M)) →
    let words := fun n => matrixWords prime H (Itinerary.run pivots m n)
    let code := orderedScheduleCode (List.finRange (d+1)).reverse pivots ++ rest
    let rows := List.finRange d
    let weightsAt := fun i : Fin d => a i.succ
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
    ∀ (host : Fin (((N+1)+total)+1) ↪ Fin T) (body : P → Pr P T Q prime U) v S
      (count src saved tmp : Fin T) (_outside : ∀ i, host i ≠ src) (tailWords : List (Fin (prime+4))),
      let queueTail := (outs.drop (entry+1)).flatMap payloadWord ++ tailWords
      let lane := (columnBank.trans shared).trans host
      let dst := lane 24
      [count,src,dst,saved,tmp].Nodup →
      (S.R count).length = M^(d+1)*W →
      S.R (lane 2) = binSyms H M → S.R (lane 27) = binSyms J W →
      S.R (lane 28) = binSyms 1 1 → S.R (lane 32) = binSyms H (1 : ZMod M).val →
      (S.R (lane 33)).length = w → S.R (lane 34) = record →
      (∀ i ∈ shearWork, S.L (lane i) = [] ∧ S.R (lane i) = []) →
      (∀ z, readAt blank (S.L (lane 25)) (S.R (lane 25)) (z-q) = RadixToBinary.binaryEncoding.encode (dest z)) →
      (∀ z, readAt blank (S.L dst) (S.R dst) z = blank) → S.R saved = [] → S.R tmp = [] →
      (signStream (A := prime) table (w+1) records)[entry]? = some (bitSymbol negative) →
      scalarArray (inputs entry) = SparseRoleCircuit.encode ∘ original →
      S.R src = (outs.drop entry).flatMap payloadWord ++ tailWords →
      (∀ h : Fin N, 35 ≤ h.val → S.L (host (shared (columnPorts h))) = [] ∧ S.R (host (shared (columnPorts h))) = []) →
      S.R (host (shared (Fin.last N))) = weights →
      (∀ h : Fin total, S.L (host (ports (Fin.natAdd (N+1) h))) = [] ∧ S.R (host (ports (Fin.natAdd (N+1) h))) = []) →
      (words (d+1) ++ suffix,S.R (host spare)) = matrixArchive words (words 0 ++ tail) destTail (d+1) →
      ∃ z F l, z.user = v.user ∧ l ≤ (6*(M^(d+1)*W)+6)+(1+(((List.finRange n).map cost).sum+1+rewindCost)) ∧
        Exec body (.seq (movePrefix count src dst saved tmp) (statePlacedNormalized host le_rfl positive Empty.elim residual)) (mk v S) l (mk z F) ∧
        ColumnReady ((reverseBank 0).trans reverseHost) H J m tail SparseRoleCircuit.encode
          (fun _ => blank) dest 0 q original m.mulVec (embStk host F) ∧
        (∀ h : Fin N, 35 ≤ h.val → F.L (host (reverseHost (columnPorts h).castSucc)) = [] ∧
          F.R (host (reverseHost (columnPorts h).castSucc)) = []) ∧
        F.R (host (reverseHost (Fin.last N).castSucc)) = rest ∧
        F.R (host (reverseHost (reverseBank 1 34))) = destTail ∧
        F.R src = queueTail ∧ ∀ j, j ≠ src → (∀ i, host i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro entry pivots diag words code rows weightsAt reads n k j t i pivot width total ports shared bank record weights program cost spare off reverseHost reverseBank active pop rewind stageCost rewindCost residual positive host body v S count src saved tmp outside tailWords queueTail lane dst distinct countLen modWord widthWord one padded clock recordWord scratch destination blankDst hs ht recorded input queue free headers aux archive
  obtain ⟨v₁,S₁,word,valid,sign,user₁,load,_,state,layout⟩ := loadAnchorRecord_exec table g m det lift block negative live
    inputs outs result body distinct v S tailWords original countLen lane rfl (fun i => outside _) H J record dest q
    modWord widthWord one padded clock recordWord scratch destination blankDst hs ht recorded input queue
  have signValue : ∏ j, a j = if negative then -1 else 1 := by
    apply Units.ext
    rw [Units.coe_prod,← Matrix.det_diagonal,← diag,sign]
    cases negative <;> rfl
  have keep (h) (ne : h ≠ shared (columnBank 24)) : S₁.R (host h) = S.R (host h) := by
    rw [state]
    exact (Function.update_of_ne (host.injective.ne ne) _ _).trans (Function.update_of_ne (outside h) _ _)
  have left : S₁.L = S.L := state ▸ rfl
  let ready := fun y (D : Stacks (((N+1)+total)+1) prime) =>
      ColumnRecordReady (columnBank.trans shared) H J record SparseRoleCircuit.encode (fun _ => blank) dest 0 q original y D ∧
      (∀ h : Fin N, 35 ≤ h.val → D.L (shared (columnPorts h)) = [] ∧ D.R (shared (columnPorts h)) = []) ∧
      D.R (shared (Fin.last N)) = weights
  have before : ready (signedAddress negative) (embStk host S₁) := by
    refine ⟨?_,?_,?_⟩
    · obtain ⟨word,lane,action⟩ := layout
      exact ⟨word,⟨lane.modulus,lane.width,lane.one,lane.padded,lane.clock,lane.archive,lane.scratch,lane.src,lane.dst⟩,action⟩
    · intro h hh
      refine ⟨(congrFun left _).trans (free h hh).1,(keep _ (shared.injective.ne ?_)).trans (free h hh).2⟩
      intro eq
      have e := congrArg Fin.val eq
      change h.val = 24 at e
      omega
    · exact (keep _ (shared.injective.ne (by intro eq; have e := congrArg Fin.val eq; change rowSwapBlock.tapes+35 = 24 at e; omega))).trans headers
  have aux₁ (h : Fin total) := And.intro ((congrFun left _).trans (aux h).1)
    ((keep _ (ports.injective.ne (by intro eq; have e := congrArg Fin.val eq; change (N+1)+h.val = 24 at e; omega))).trans (aux h).2)
  have archive₁ : (words (d+1) ++ suffix,S₁.R (host spare)) = _ :=
    (congrArg (fun x => (words (d+1) ++ suffix,x)) (keep _ (off _).symm)).trans archive
  let start := stateLiftDown positive (embDn host v₁)
  obtain ⟨u,D,l,hu,hl,scale,next,kept⟩ := archivedDiagonal_exec parent a negative signValue capacity signCapacity
    H J hm hw hW (words (d+1) ++ suffix) code dest q empty original (P := Empty) Empty.elim start (embStk host S₁) before aux₁
  have action : (Itinerary.run pivots m (d+1)).mulVec = (Matrix.diagonal fun j => (a j : ZMod M)).mulVec :=
    congrArg Matrix.mulVec diag
  have finish := finishArchivedResidual_exec shared spare off capacity pivot (fun j => (parent j : ZMod M))
    pivots m valid H J hm hw hW (P := Empty) Empty.elim start (embStk host S₁) tail destTail suffix rest dest q empty original
    ((List.finRange n).foldr (fun a rest => .seq (program a) rest) (.act .done)) (((List.finRange n).map cost).sum+1)
  obtain ⟨z,F,l',hz,hl',exec,result,clean,stream,other⟩ := finish
    ⟨u,D,l,hu,hl,scale,action.symm ▸ next.1,next.2.1,next.2.2,kept⟩ archive₁
  obtain ⟨out,_,user,placed⟩ := statePlaced_exec_normalized host host.injective le_rfl positive Empty.elim
    (body' := body) (fun e => nomatch e) v₁ S₁ exec
  let final := embOvr host F.get S₁
  have view : embStk host final = F := embStk_ovr host.injective _ _
  rw [← view] at result clean stream other
  refine ⟨out,final,_,user.trans (hz.trans user₁),Nat.add_le_add_left (Nat.add_le_add_left hl' 1) _,
    Exec.seq load placed,result,clean,stream,other,(embOvr_off F.get S₁ outside).2.trans ?_,?_⟩
  · rw [state]
    exact (Function.update_of_ne (outside _).symm _ _).trans (Function.update_self ..)
  · intro j ne offHost
    obtain ⟨hl,hr⟩ := embOvr_off F.get S₁ offHost
    refine ⟨hl.trans (congrFun left _),hr.trans ?_⟩
    rw [state]
    exact (Function.update_of_ne (offHost _).symm _ _).trans (Function.update_of_ne ne _ _)

/-- Prepare both archives, apply the live residual matrix, and collect the transformed payload. -/
theorem preparedResidual_exec {Q T r records : ℕ} (parent : Fin d → (ZMod M)ˣ)
    (capacity : columnCapacity ≤ Q) (signCapacity : (fieldSignProgram (0 : Fin (d+1)) true).1 ≤ Q)
    (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (table : Matrix (Fin r) (Fin r) (ZMod prime) → Matrix (Fin (d+1)) (Fin (d+1)) (ZMod prime))
    (g : LabelPadding.Label r (w+1)) (m : Matrix (Fin (d+1)) (Fin (d+1)) (ZMod M))
    (det : m.det = 1 ∨ m.det = -1)
    (lift : (LabelRing.res prime (w+1) (by omega)).mapMatrix m = table ((LabelRing.res prime (w+1) (by omega)).mapMatrix g))
    (block : ℕ) (live : block*M^(r*r)+(LabelAddress.address g).val < records)
    (inputs : ℕ → Array d 1 (w+1) W) (outs : List (Array d 1 (w+1) W))
    (result : (signedInputs table (w+1) records inputs).Forall₂ Correct outs)
    (tail rest : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^(d+1)*W : ℕ) → dest z = blank)
    (original : Fin (M^(d+1)*W) → ZMod 2) :
    let entry := block*M^(r*r)+(LabelAddress.address g).val
    let pivots := classPivots (table ((LabelRing.res prime (w+1) (by omega)).mapMatrix g))
    let rows := List.finRange d
    let reads := pivotReads rows
    let n := reads.length
    let k := fun _ : Fin n => (0 : Fin (d+1))
    let j := fun a => (reads.get a).1
    let t := fun a => (j a).succ
    let i := fun a => (reads.get a).2
    let width := fun a => 22+fieldSignSlots (k a)
    let total := Fintype.card (Σ a, Fin (width a))
    let ports := Fin.castAddEmb (n := (N+1)+total) 1
    let shared := (Fin.castAddEmb (n := N+1) total).trans ports
    let bank := fun a => (exchangeBank (N+1) width a).trans ports
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
    ∀ (host : Fin (((N+1)+total)+1) ↪ Fin T) (body : P → Pr P T Q prime U) v S
      (count src saved tmp : Fin T) (_outside : ∀ i, host i ≠ src) (tailWords : List (Fin (prime+4))),
      let queueTail := (outs.drop (entry+1)).flatMap payloadWord ++ tailWords
      let lane := (columnBank.trans shared).trans host
      let dst := lane 24
      let cols := shared.trans host
      let away : ∀ i, cols i ≠ host spare := fun i => host.injective.ne (off i)
      let prep := forwardBank.trans (rewindPorts (d+1) cols (host spare) away)
      let stream := cols (Fin.last N)
      let schedule := fun j =>
        let rows := classPivots (table (LabelStock.residue r (w+1) 1 j))
        scheduleCode (A := prime) rows ++ orderedScheduleCode (List.finRange (d+1)).reverse rows
      ∀ (parentTape : Fin T), (∀ i, prep i ≠ parentTape) → parentTape ≠ stream →
      S.R parentTape = (List.ofFn fun i => binSyms H (parent i : ZMod M).val).flatten →
      S.R (prep 15) = matrixWords prime H m ++ tail → S.R (prep 2) = binSyms H M →
      S.R (prep 20) = binSyms H (1 : ZMod M).val → (S.R (prep 22)).length = w →
      (∀ i : Fin 23, (i < 15 ∧ i ≠ 2) ∨ (17 ≤ i ∧ i ≤ 19) ∨ i = 21 → S.R (prep i) = []) →
      S.R stream = ((List.range records).drop entry).flatMap schedule ++ rest →
      let stable := fun i => i ≠ stream ∧ i ≠ lane 34 ∧ i ≠ host spare
      ∀ (acc : Fin T), (∀ i, host i ≠ count) → (∀ i, host i ≠ tmp) → (∀ i, host i ≠ acc) →
      acc ≠ src → [count,host (reverseHost (reverseBank 0 24)),acc,tmp].Nodup → stable saved →
      (S.R (lane 33)).length = w →
      [count,src,dst,saved,tmp].Nodup →
      (S.R count).length = M^(d+1)*W →
      S.R (lane 2) = binSyms H M → S.R (lane 27) = binSyms J W →
      S.R (lane 28) = binSyms 1 1 → S.R (lane 32) = binSyms H (1 : ZMod M).val →
      (∀ i ∈ shearWork, S.L (lane i) = [] ∧ S.R (lane i) = []) →
      (∀ z, readAt blank (S.L (lane 25)) (S.R (lane 25)) (z-q) = RadixToBinary.binaryEncoding.encode (dest z)) →
      (∀ z, readAt blank (S.L dst) (S.R dst) z = blank) → S.R saved = [] → S.R tmp = [] →
      scalarArray (inputs entry) = SparseRoleCircuit.encode ∘ original →
      S.R src = (outs.drop entry).flatMap payloadWord ++ tailWords →
      (∀ h : Fin N, 35 ≤ h.val → S.L (host (shared (columnPorts h))) = [] ∧ S.R (host (shared (columnPorts h))) = []) →
      (∀ h : Fin total, S.L (host (ports (Fin.natAdd (N+1) h))) = [] ∧ S.R (host (ports (Fin.natAdd (N+1) h))) = []) →
      let tapes := ((reverseBank 0).trans reverseHost).trans host
      ∃ z F l word, z.user = v.user ∧ l ≤ ((d+1)*(2*(d+1)+(4*w+4+columnTime (d+1) prime w H))+1 +
        (d*(8*((d+1)*(d+1)*H)+14*H+22)+1)+(6*H+6)+(4*((d+1)*H)+4)+(6*(d*H)+6)) + ((6*(M^(d+1)*W)+6)+(1+(((List.finRange n).map cost).sum+1+rewindCost))) + (4*(M^(d+1)*W)+4) + ((d+1)*(d+1)*(4*H+4)+1) ∧
        Exec body (.seq (.seq (.seq (.seq (.seq (.seq (recordWeights d prep stream) (copyWordHeader (prep 20) (prep 14) (prep 3) (prep 4)))
          (moveRightOrdered (prep 14) (prep 3) (stageBank prep (d+1) 15))) (copyWordHeader parentTape stream (prep 3) (prep 4)))
          (.seq (movePrefix count src dst saved tmp) (statePlacedNormalized host le_rfl positive Empty.elim residual)))
          (Mult.ShortConv.transfer count (host (reverseHost (reverseBank 0 24))) acc tmp)) (dropWords (tapes 2) (tapes 34) (tapes 0) ((d+1)*(d+1)))) (mk v S) l (mk z F) ∧
        (∀ x k, word (index (m.mulVec x) k) = original (index x k)) ∧
        F.R acc = (payloadWord (SparseRoleCircuit.encode ∘ word)).reverse ++ S.R acc ∧
        (∀ z, readAt blank (F.L (host (reverseHost (reverseBank 0 24)))) (F.R (host (reverseHost (reverseBank 0 24)))) z = blank) ∧
        F.R (tapes 34) = tail ∧
        (∀ next rest (input : Fin (M^(d+1)*W) → ZMod 2), tail = matrixWords prime H next ++ rest →
          ShearReady ((reverseBank 0).trans reverseHost) H J next rest (fun _ : ZMod 2 => blank)
            (fun _ => blank) dest 0 q input (embStk host F)) ∧
        (∀ h : Fin N, 35 ≤ h.val → F.L (host (reverseHost (columnPorts h).castSucc)) = [] ∧
          F.R (host (reverseHost (columnPorts h).castSucc)) = []) ∧
        F.R (host (reverseHost (Fin.last N).castSucc)) = ((List.range records).drop (entry+1)).flatMap schedule ++ rest ∧
        F.R (host (reverseHost (reverseBank 1 34))) = S.R (prep 16) ∧
        F.R src = queueTail ∧ ∀ j, j ≠ src → j ≠ acc → (∀ i, host i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro entry pivots rows reads n k j t i width total ports shared bank program cost spare off reverseHost reverseBank active pop rewind stageCost rewindCost residual positive host body v S count src saved tmp outside tailWords queueTail lane dst cols away prep stream schedule parentTape outsideParent separate parents matrix modulus one ticks prepFree code stable acc countOff tmpOff accOff accSrc collectPorts ss clock distinct countLen modWord widthWord binaryOne padded scratch destination blankDst hs ht input queue free aux tapes
  obtain ⟨u,D,l,a,neg,hu,hl,prepare,headers,⟨suffix,recordWord,archive⟩,left,keep,bit,diag⟩ :=
    prepareResidualArchives_exec body cols (host spare) away w H hm table g m det lift block records live v S tail rest
      parentTape parent outsideParent separate parents matrix modulus one ticks prepFree code
  have same {h} (ok : stable h) := keep h ok.1 ok.2.1 ok.2.2
  have laneKeep (h : Fin 35) (ne : h ≠ 34) : D.R (lane h) = S.R (lane h) := by
    apply same
    refine ⟨cols.injective.ne ?_,lane.injective.ne ne,away _⟩
    intro eq
    have e := congrArg Fin.val eq
    change h.val = N at e
    omega
  have srcKeep := same (h := src) ⟨(outside _).symm,(outside _).symm,(outside _).symm⟩
  have sc : stable count := ⟨(countOff _).symm,(countOff _).symm,(countOff _).symm⟩
  have st : stable tmp := ⟨(tmpOff _).symm,(tmpOff _).symm,(tmpOff _).symm⟩
  rw [parents] at headers
  obtain ⟨z,F,l',hz,hl',run,ready,clean,streamEnd,spareEnd,queueEnd,frame⟩ :=
    archivedResidual_exec parent a neg capacity signCapacity H J hm hw hW table g m det lift block live inputs outs result
      tail (S.R (prep 16)) suffix _ dest q empty original diag host body u D count src saved tmp outside tailWords distinct
      ((congrArg List.length (same sc)).trans countLen) ((laneKeep 2 (by decide)).trans modWord)
      ((laneKeep 27 (by decide)).trans widthWord) ((laneKeep 28 (by decide)).trans binaryOne)
      ((laneKeep 32 (by decide)).trans padded) ((congrArg List.length (laneKeep 33 (by decide))).trans clock)
      recordWord (fun h hh => ⟨(congrFun left _).trans (scratch h hh).1,
        (laneKeep h (fun eq => (by decide : (34 : Fin 35) ∉ shearWork) (eq ▸ hh))).trans (scratch h hh).2⟩)
      (by change ∀ z, readAt blank (D.L (lane 25)) (D.R (lane 25)) (z-q) = _
          simpa only [left,laneKeep 25 (by decide)] using destination)
      (by change ∀ z, readAt blank (D.L (lane 24)) (D.R (lane 24)) z = blank
          simpa only [left,laneKeep 24 (by decide)] using blankDst)
      ((same ss).trans hs) ((same st).trans ht) bit input (srcKeep.trans queue)
      (fun h hh => ⟨(congrFun left _).trans (free h hh).1,(keep _ (cols.injective.ne (fun eq => h.isLt.ne (congrArg Fin.val eq)))
        (cols.injective.ne (by intro eq; have e := congrArg Fin.val eq; change h.val = 34 at e; omega)) (away _)).trans (free h hh).2⟩)
      headers (fun h => ⟨(congrFun left _).trans (aux h).1,(keep _ (host.injective.ne (ports.injective.ne (by
        intro eq; have e := congrArg Fin.val eq; change (N+1)+h.val = N at e; omega)))
        (host.injective.ne (ports.injective.ne (by intro eq; have e := congrArg Fin.val eq; change (N+1)+h.val = 34 at e; omega)))
        (host.injective.ne (fun eq => (Fin.natAdd (N+1) h).isLt.ne (congrArg Fin.val eq)))).trans (aux h).2⟩) archive
  obtain ⟨word,layout,effect⟩ := ready
  have distinct' := distinct
  regs_ne distinct'
  have kept (h : Fin T) (ne : h ≠ src) (out : ∀ i, host i ≠ h) : F.R h = S.R h :=
    (frame h ne out).2.trans (keep h (out _).symm (out _).symm (out _).symm)
  let io := host (reverseHost (reverseBank 0 24))
  obtain ⟨y,hy,collect,blanked⟩ := collectPayload_exec body collectPorts (SparseRoleCircuit.encode ∘ word) z F
    (by rw [kept count ‹count ≠ src› countOff,countLen]) ((kept tmp ‹src ≠ tmp›.symm tmpOff).trans ht)
    (fun pos => by have h := (layout.src pos).symm; rw [sub_zero] at h; exact h)
  let G := {F with R := Function.update (Function.update F.R io ((F.R io).drop (M^(d+1)*W))) acc ((payloadWord (SparseRoleCircuit.encode ∘ word)).reverse ++ F.R acc)}
  have unchanged (h : Fin T) (ha : h ≠ acc) (hi : h ≠ io) : G.R h = F.R h :=
    (Function.update_of_ne ha _ _).trans (Function.update_of_ne hi _ _)
  have bankKeep (h : Fin (N+2)) (ne : h ≠ reverseBank 0 24) :=
    unchanged (host (reverseHost h)) (accOff _) (host.injective.ne (reverseHost.injective.ne ne))
  have readyG : ShearReady ((reverseBank 0).trans reverseHost) H J m tail (fun _ : ZMod 2 => blank)
          (fun _ => blank) dest 0 q original (embStk host G) := by
    have field (i : Fin 35) (hi : i ≠ 24) := bankKeep _ ((reverseBank 0).injective.ne hi)
    refine ⟨(field 2 (by decide)).trans layout.modulus,(field 27 (by decide)).trans layout.width,
      (field 28 (by decide)).trans layout.one,(field 32 (by decide)).trans layout.padded,
      (congrArg List.length (field 33 (by decide))).trans layout.clock,(field 34 (by decide)).trans layout.archive,
      fun i hi => ⟨(layout.scratch i hi).1,(field i (fun e => (by decide : (24 : Fin 35) ∉ shearWork) (e ▸ hi))).trans (layout.scratch i hi).2⟩,?_,?_⟩
    · intro pos
      have uniform (n : ℕ) (p : ℤ) : putWord (fun _ => (blank : Fin 4)) p (List.replicate n blank) = fun _ => blank := by
        induction n generalizing p with
        | zero => rfl
        | succ n ih => simp [List.replicate_succ,putWord,ih]
      simp only [sub_zero,Function.comp_def,List.ofFn_const,uniform]
      exact (blanked pos).trans (by rfl)
    · intro pos
      change readAt blank (F.L _) (G.R (host (reverseHost (reverseBank 0 25)))) _ = _
      rw [field 25 (by decide)]
      exact layout.dst pos
  obtain ⟨z',hz',advance⟩ := consumeMatrix_exec tapes body y G H m tail readyG.archive
    ((congrArg List.length readyG.modulus).trans (length_binSyms ..)) (readyG.scratch 0 (by decide)).2
  let final := {G with R := Function.update G.R (tapes 34) tail}
  have preserve (h : Fin T) (ne : h ≠ tapes 34) : final.R h = G.R h := Function.update_of_ne ne _ _
  have keepPort (h : Fin (N+2)) (ne : h ≠ reverseBank 0 34) :=
    preserve _ (host.injective.ne (reverseHost.injective.ne ne))
  have keptBank (h : Fin 35) (ne : h ≠ 34) := preserve _ (tapes.injective.ne ne)
  refine ⟨z',final,_,word,hz'.trans (hy.trans (hz.trans hu)),Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add hl hl') _) _,
    Exec.seq (Exec.seq (Exec.seq prepare run) collect) advance,effect,
    (preserve _ (accOff _).symm).trans ((Function.update_self ..).trans (congrArg _ (kept acc accSrc accOff))),
    ?_,Function.update_self ..,?_,?_,?_,?_,(preserve _ (outside _).symm).trans ((unchanged src accSrc.symm (outside _).symm).trans queueEnd),?_⟩
  · intro pos
    change readAt blank (G.L _) (final.R (tapes 24)) pos = blank
    rw [keptBank 24 (by decide)]
    exact blanked pos
  · intro next rest input eq
    exact readyG.next ((Function.update_self ..).trans eq) (fun _ => rfl) keptBank rfl
  · intro h hh
    have distinct (i : Fin 35) : (columnPorts h).castSucc ≠ reverseBank 0 i := by
      rw [← archivePorts_workspace 0 h hh]
      apply (archivePorts 0).injective.ne
      intro eq
      have e := congrArg Fin.val eq
      change h.val = i.val at e
      omega
    exact ⟨(clean h hh).1,(keepPort _ (distinct 34)).trans ((bankKeep _ (distinct 24)).trans (clean h hh).2)⟩
  · have distinct (i : Fin 35) : (Fin.last N).castSucc ≠ reverseBank 0 i := by
      rw [← archivePorts_stream 0]
      apply (archivePorts 0).injective.ne
      intro eq
      have e := congrArg Fin.val eq
      change N = i.val at e
      omega
    exact (keepPort _ (distinct 34)).trans ((bankKeep _ (distinct 24)).trans streamEnd)
  · exact (keepPort _ (archivePorts_other 0 _).symm).trans ((bankKeep _ (archivePorts_other 0 _).symm).trans spareEnd)
  · intro h ne ha beyond
    exact ⟨(frame h ne beyond).1.trans (congrFun left _),
      (preserve h (beyond _).symm).trans ((unchanged h ha (beyond _).symm).trans (kept h ne beyond))⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback.Record
