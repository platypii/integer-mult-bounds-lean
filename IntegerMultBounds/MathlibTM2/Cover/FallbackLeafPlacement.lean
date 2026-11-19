module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackLeafEntry
public import IntegerMultBounds.MathlibTM2.Cover.FallbackColumnHost

/-! Project the caller's column, reciprocal archive and private tapes into the leaf schedule. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
variable [M8.Machine.Net] {A b w d W : ℕ} {α : Type} [NeZero (b^(w+1))]
local notation "N" => rowSwapBlock.tapes+35
local notation "M" => b^(w+1)

theorem leafSchedule_column (total : ℕ) (fits : 35 ≤ N) :
    let host := ((Fin.castAddEmb (n := 62) (N-35)).trans (Fin.castAddEmb total)).trans (Fin.castAddEmb 1)
    let shared := (Fin.castAddEmb (n := N+1) total).trans (Fin.castAddEmb 1)
    (columnBank.trans shared).trans (leafScheduleBank N total fits) = leafColumn.trans host := by
  intro host shared
  let bank := leafScheduleBank N total fits
  have col (i : Fin 35) : bank (shared (columnBank i)) = host (leafColumn i) := by
    change leafScheduleBank N total fits (((columnBank i).castAdd total).castAdd 1) = _
    rw [leafScheduleBank_shared]
    change (((leafShared N fits (i.castLE (fits.trans (Nat.le_succ _)))).castAdd total).castAdd 1) = _
    rw [leafShared_column]
    rfl
  exact Function.Embedding.ext col

theorem leafSchedule_ready (total H J : ℕ) (record weights : List (Fin (A+4)))
    (sym : α → Fin 4) (source dest : ℤ → Fin 4) (p q : ℤ) (word : Fin (M^d*W) → α)
    (addr : (Fin d → ZMod M) → Fin d → ZMod M) (S : Stacks ((62+(N-35)+total)+1) A) :
    let fits : 35 ≤ N := Nat.le_add_left ..
    let host := ((Fin.castAddEmb (n := 62) (N-35)).trans (Fin.castAddEmb total)).trans (Fin.castAddEmb 1)
    let shared := (Fin.castAddEmb (n := N+1) total).trans (Fin.castAddEmb 1)
    let placed := embStk (leafScheduleBank N total fits) S
    ColumnRecordReady (leafColumn.trans host) H J record sym source dest p q word addr S →
    S.R (host 56) = weights →
    (∀ j, 62 ≤ j.val → S.L j = [] ∧ S.R j = []) →
    ColumnRecordReady (columnBank.trans shared) H J record sym source dest p q word addr placed ∧
      (∀ h : Fin N, 35 ≤ h.val → placed.L (shared (columnPorts h)) = [] ∧ placed.R (shared (columnPorts h)) = []) ∧
      placed.R (shared (Fin.last N)) = weights ∧
      ∀ j : Fin total, placed.L ((j.natAdd (N+1)).castAdd 1) = [] ∧
        placed.R ((j.natAdd (N+1)).castAdd 1) = [] := by
  intro fits host shared placed ready archive free
  let bank := leafScheduleBank N total fits
  have eq := leafSchedule_column total fits
  refine ⟨?_,?_,?_,?_⟩
  · rw [← eq] at ready
    have projected := (columnRecordReady_project ((columnBank.trans shared).trans bank) ..).mp ready
    exact (columnRecordReady_project (columnBank.trans shared) ..).mpr projected
  · intro j hj
    apply free
    change 62 ≤ (leafScheduleBank N total fits (((columnPorts j).castAdd total).castAdd 1)).val
    rw [leafScheduleBank_shared]
    change 62 ≤ (leafShared N fits j.castSucc).val
    rw [leafShared_work fits j hj]
    omega
  · have last : bank (shared (Fin.last N)) = host 56 := by
      apply Fin.ext
      change (leafScheduleBank N total fits (((Fin.last N).castAdd total).castAdd 1)).val = 56
      rw [leafScheduleBank_shared]
      exact leafShared_reciprocal fits
    change S.R (bank _) = weights
    rw [last,archive]
  · intro j
    apply free
    rw [leafScheduleBank_sign]
    change 62 ≤ 62+(N-35)+j.val
    omega

/-- Lift the concrete inner program's run to the caller. Its output column
remains readable and every tape outside the placement keeps both stacks. -/
theorem leafSchedule_place_exec {P U : Type} {Q Q' : ℕ} (total : ℕ)
    (capacity : Q ≤ Q') (positive : 0 < Q)
    (body : P → Pr P (62+(N-35)+total+1) Q' A U)
    (prog : Pr Empty (N+1+total+1) Q A U) (v : HS (62+(N-35)+total+1) Q' A U)
    (S : Stacks (62+(N-35)+total+1) A) (H J : ℕ) (record : List (Fin (A+4)))
    (sym : α → Fin 4) (source dest : ℤ → Fin 4) (p q : ℤ) (word : Fin (M^d*W) → α)
    (addr : (Fin d → ZMod M) → Fin d → ZMod M) :
    let fits : 35 ≤ N := Nat.le_add_left ..
    let bank := leafScheduleBank N total fits
    let host := ((Fin.castAddEmb (n := 62) (N-35)).trans (Fin.castAddEmb total)).trans (Fin.castAddEmb 1)
    let shared := (Fin.castAddEmb (n := N+1) total).trans (Fin.castAddEmb 1)
    ∀ u D n, Exec Empty.elim prog (mk (stateLiftDown positive (embDn bank v)) (embStk bank S)) n (mk u D) →
      ColumnRecordReady (columnBank.trans shared) H J record sym source dest p q word addr D →
      ∃ z F, z.user = u.user ∧
        Exec body (statePlacedNormalized bank capacity positive Empty.elim prog) (mk v S) (1+n) (mk z F) ∧
        ColumnRecordReady (leafColumn.trans host) H J record sym source dest p q word addr F ∧ embStk bank F = D ∧
        ∀ h, (∀ i, bank i ≠ h) → F.L h = S.L h ∧ F.R h = S.R h := by
  intro fits bank host shared u D n run ready
  obtain ⟨z,_,hz,placed⟩ := statePlaced_exec_normalized bank bank.injective capacity positive Empty.elim
    (body' := body) (fun e => nomatch e) v S run
  let F := embOvr bank D.get S
  have same : embStk bank F = D := embStk_ovr bank.injective _ _
  refine ⟨z,F,hz,placed,?_,same,fun h off => embOvr_off _ _ off⟩
  rw [← leafSchedule_column total fits]
  have projected := (columnRecordReady_project (columnBank.trans shared) ..).mp ready
  rw [← same] at projected
  exact (columnRecordReady_project ((columnBank.trans shared).trans bank) ..).mpr projected

end IntegerMultBounds.MathlibTM2.Cover.Fallback
