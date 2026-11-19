module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackPlacedColumn

/-! Alternate the two matrix archive tapes while fixing the column workspace and pivot stream. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
variable [M8.Machine.Net]
local notation "N" => rowSwapBlock.tapes+35
local notation "archive" => columnBank 34

noncomputable def archivePorts (n : ℕ) : Fin (N+1) ↪ Fin (N+2) :=
  let ports := Fin.castLEEmb (Nat.le_succ (N+1))
  if Even n then ports else ports.trans (Equiv.swap (ports archive) (Fin.last (N+1))).toEmbedding

/-- Place the reverse machine around a fixed column bank, adjoining a single spare
archive tape. Parity decides which physical archive is active at entry. -/
noncomputable def rewindPorts {T : ℕ} (n : ℕ) (bank : Fin (N+1) ↪ Fin T) (spare : Fin T)
    (off : ∀ i, bank i ≠ spare) : Fin (N+2) ↪ Fin T :=
  let extend : Fin (N+2) ↪ Fin T := ⟨Fin.lastCases spare bank, by
    intro i j
    induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
      simp [off,Ne.symm (off _),bank.injective.eq_iff]⟩
  if Even n then extend else
    (Equiv.swap (columnBank 34).castSucc (Fin.last (N+1))).toEmbedding.trans extend

theorem rewindPorts_avoids {T : ℕ} (n : ℕ) (bank : Fin (N+1) ↪ Fin T) (spare : Fin T)
    (off : ∀ i, bank i ≠ spare) {h : Fin T} (columns : ∀ i, bank i ≠ h) (other : spare ≠ h)
    (i : Fin (N+2)) : rewindPorts n bank spare off i ≠ h := by
  have extend (j : Fin (N+2)) : Fin.lastCases spare bank j ≠ h := by
    induction j using Fin.lastCases with
    | last => simpa using other
    | cast j => simpa using columns j
  unfold rewindPorts
  split <;> exact extend _

theorem rewindPorts_active {T : ℕ} (n : ℕ) (bank : Fin (N+1) ↪ Fin T) (spare : Fin T)
    (off : ∀ i, bank i ≠ spare) : (archivePorts n).trans (rewindPorts n bank spare off) = bank := by
  ext i
  have cast (a : Fin (N+1)) : Fin.castLE (Nat.le_succ _) a = a.castSucc := rfl
  by_cases parity : Even n <;> simp [archivePorts,rewindPorts,parity,Fin.castLEEmb,cast]

theorem rewindPorts_spare {T : ℕ} (n : ℕ) (bank : Fin (N+1) ↪ Fin T) (spare : Fin T)
    (off : ∀ i, bank i ≠ spare) :
    rewindPorts n bank spare off (archivePorts (n+1) (columnBank 34)) = spare := by
  have cast (a : Fin (N+1)) : Fin.castLE (Nat.le_succ _) a = a.castSucc := rfl
  by_cases parity : Even n <;> simp [archivePorts,rewindPorts,Nat.even_add_one,parity,Fin.castLEEmb,cast]

theorem archivePorts_fixed (n : ℕ) (i : Fin (N+1)) (hi : i ≠ archive) :
    archivePorts n i = i.castSucc := by
  let ports := Fin.castLEEmb (Nat.le_succ (N+1))
  have distinct : ports i ≠ ports archive := ports.injective.ne hi
  have outside : ports i ≠ Fin.last (N+1) := fun e => i.isLt.ne (congrArg Fin.val e)
  unfold archivePorts
  split
  · rfl
  · exact Equiv.swap_apply_of_ne_of_ne distinct outside

theorem archivePorts_other (n : ℕ) (i : Fin (N+1)) :
    archivePorts n i ≠ archivePorts (n+1) archive := by
  let ports := Fin.castLEEmb (Nat.le_succ (N+1))
  have outside (j : Fin (N+1)) : ports j ≠ Fin.last (N+1) := fun e => j.isLt.ne (congrArg Fin.val e)
  by_cases h : Even n
  · simpa [archivePorts,Nat.even_add_one,h,ports] using outside i
  · simp only [archivePorts,Nat.even_add_one,h,ite_false,not_false_eq_true,ite_true,
      Function.Embedding.trans_apply,Equiv.toEmbedding_apply]
    intro eq
    have same := congrArg (Equiv.swap (ports archive) (Fin.last (N+1))) eq
    exact outside i (by simpa [ports] using same)

theorem archivePorts_period (n : ℕ) : archivePorts (n+2) = archivePorts n := by
  simp [archivePorts,Nat.even_add]

theorem archivePorts_previous (n : ℕ) (i : Fin (N+1)) :
    archivePorts (n+1) i ≠ archivePorts n archive := by
  rw [← archivePorts_period n]
  exact archivePorts_other (n+1) i

theorem archivePorts_stream (n : ℕ) :
    archivePorts n (Fin.last N) = (Fin.last N).castSucc := by
  apply archivePorts_fixed
  intro eq
  have h := congrArg Fin.val eq
  change rowSwapBlock.tapes+35 = 34 at h
  omega

theorem archivePorts_workspace (n : ℕ) (i : Fin N) (hi : 35 ≤ i.val) :
    archivePorts n (columnPorts i) = (columnPorts i).castSucc := by
  apply archivePorts_fixed
  intro eq
  have h := congrArg Fin.val eq
  change i.val = 34 at h
  omega

theorem archivePorts_bank_fixed (n : ℕ) (i : Fin 35) (hi : i ≠ 34) :
    archivePorts (n+1) (columnBank i) = archivePorts n (columnBank i) := by
  rw [archivePorts_fixed _ _ (columnBank.injective.ne hi),archivePorts_fixed _ _ (columnBank.injective.ne hi)]

end IntegerMultBounds.MathlibTM2.Cover.Fallback
