module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackReverseStages

/-! Diagonalize on the same two archive tapes read by reverse elimination. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable [M8.Machine.Net] {P U : Type} {d w : ℕ}
local notation "N" => rowSwapBlock.tapes+35
local notation "M" => prime^(w+1)
local instance : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩

def forwardSlots : Fin 23 ↪ Fin 35 :=
  ⟨![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,34,16,17,18,19,32,21,33],by decide⟩

noncomputable def forwardBank : Fin 23 ↪ Fin (N+2) where
  toFun i := if i = 16 then archivePorts 1 (columnBank 34) else archivePorts 0 (columnBank (forwardSlots i))
  inj' := by
    intro i j eq
    by_cases hi : i = 16 <;> by_cases hj : j = 16 <;> simp only [hi,hj,ite_true,ite_false] at eq ⊢
    · exact False.elim (archivePorts_other 0 _ eq.symm)
    · exact False.elim (archivePorts_other 0 _ eq)
    · exact forwardSlots.injective (columnBank.injective ((archivePorts 0).injective eq))

theorem forwardBank_archives (n : ℕ) :
    stageBank forwardBank n 15 = archivePorts n (columnBank 34) ∧
    stageBank forwardBank n 16 = archivePorts (n+1) (columnBank 34) := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih => simpa [stageBank,archivePorts_period] using And.intro ih.2 ih.1

theorem forwardBank_stream (i : Fin 23) : forwardBank i ≠ (Fin.last N).castSucc := by
  change (if _ then _ else _) ≠ _
  split
  · rw [← archivePorts_stream 0]
    exact (archivePorts_other 0 _).symm
  · rw [← archivePorts_stream 0]
    apply (archivePorts 0).injective.ne
    intro eq
    have h := congrArg Fin.val eq
    change (forwardSlots i).val = rowSwapBlock.tapes+35 at h
    have := (forwardSlots i).isLt
    omega

/-- Installing a record on the alternating forward archives preserves the signed column payload. -/
theorem preparedColumnReady {T W n : ℕ} (host : Fin (N+2) ↪ Fin T) (H J : ℕ)
    (record next : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
    (original : Fin (M^d*W) → ZMod 2) (addr : (Fin d → ZMod M) → Fin d → ZMod M)
    (S F : Stacks T prime) :
    let bank := (columnBank.trans (archivePorts n)).trans host
    let prep := forwardBank.trans host
    ColumnRecordReady bank H J record SparseRoleCircuit.encode (fun _ => blank) dest 0 q original addr S →
    F.L = S.L →
    (∀ h, h ≠ host (Fin.last N).castSucc → h ≠ stageBank prep n 15 → h ≠ stageBank prep n 16 → F.R h = S.R h) →
    F.R (stageBank prep n 15) = next →
    ColumnRecordReady bank H J next SparseRoleCircuit.encode (fun _ => blank) dest 0 q original addr F := by
  intro bank prep ready left keep archive
  have ports (k : ℕ) (i : Fin 23) : stageBank prep k i = host (stageBank forwardBank k i) := by
    induction k generalizing i with
    | zero => rfl
    | succ k ih => exact ih _
  rw [ports,(forwardBank_archives n).1] at archive
  apply ready.replaceArchive left _ archive
  intro i hi
  apply keep
  · rw [← archivePorts_stream n]
    apply host.injective.ne
    apply (archivePorts n).injective.ne
    intro eq
    have val := congrArg Fin.val eq
    change i.val = N at val
    omega
  · rw [ports,(forwardBank_archives n).1]
    exact bank.injective.ne hi
  · rw [ports,(forwardBank_archives n).2]
    exact host.injective.ne (archivePorts_other n _)

theorem forwardStages_exec (rows : Fin d → Fin d) (H : ℕ) (hm : M < 2^H)
    (body : P → Pr P (N+2) columnCapacity prime U) (v : HS (N+2) columnCapacity prime U) (S : Stacks (N+2) prime)
    (m : Matrix (Fin d) (Fin d) (ZMod M)) (valid : Itinerary.Valid rows m d)
    (tail rest : List (Fin (prime+4))) (matrix : S.R (forwardBank 15) = matrixWords prime H m ++ tail)
    (modulus : S.R (forwardBank 2) = binSyms H M) (one : S.R (forwardBank 20) = binSyms H (1 : ZMod M).val)
    (ticks : (S.R (forwardBank 22)).length = w)
    (free : ∀ i : Fin 23, (i < 15 ∧ i ≠ 2) ∨ (17 ≤ i ∧ i ≤ 19) ∨ i = 21 → S.R (forwardBank i) = [])
    (code : S.R (Fin.last N).castSucc = scheduleCode rows ++ rest) :
    let archive := fun n => archivePorts n (columnBank 34)
    let stage := Itinerary.run rows m
    ∃ z F l suffix, z.user = v.user ∧ l ≤ d*(2*d+(4*w+4+columnTime d prime w H))+1 ∧
      Exec body (streamedItinerary d prime forwardBank (Fin.last N).castSucc d) (mk v S) l (mk z F) ∧
      F.R (archive d) = matrixWords prime H (stage d) ++ suffix ∧
      (F.R (archive d),F.R (archive (d+1))) =
        matrixArchive (fun j => matrixWords prime H (stage j)) (matrixWords prime H m ++ tail) (S.R (archive 1)) d ∧
      F.R (Fin.last N).castSucc = rest ∧ F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      ∀ i, i ≠ (Fin.last N).castSucc → i ≠ archive d → i ≠ archive (d+1) → F.R i = S.R i := by
  intro archive stage
  obtain ⟨z,F,l,suffix,hz,hl,run,packed,pair,remaining,left,input,output,frame⟩ := streamedItinerary_exec
    body forwardBank (Fin.last N).castSucc forwardBank_stream prime w H prime_prime m rows hm v S tail
    matrix modulus one ticks free d le_rfl valid rest (by rw [List.take_of_length_le (by simp)]; exact code)
  rw [(forwardBank_archives d).1,(forwardBank_archives d).2] at pair frame
  rw [(forwardBank_archives d).1] at packed
  exact ⟨z,F,l,suffix,hz,hl,run,packed,matrix ▸ pair,remaining,left,input,output,frame⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
