module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackRowSwap
public import IntegerMultBounds.MathlibTM2.Cover.FallbackSwapPlacement

/-! Exchange the prepared payload and erase the simulator bank, framing all other rows. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host M8.RevMachine
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
open RecursiveInterchangeLayout (volume)
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
variable [M8.Machine.Net] {P U : Type}
local notation "N" => rowSwapBlock.tapes
local notation "Q" => rowSwapBlock.states
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos prime_prime.pos _).ne'⟩

noncomputable def placedRowSwap : Pr P (N+35) Q prime U :=
  .seq (embProg swapSimulationPort Empty.elim (foreign rowSwapBlock.program))
    (clearWorkTapes (swapWorkspace (N+35)))

theorem placedRowSwap_exec {d w W : ℕ} (i j : Fin d) (lt : i < j) (hW : 0 < W)
    (body : P → Pr P (N+35) Q prime U) (v : HS (N+35) Q prime U) (S : Stacks (N+35) prime)
    (roles : Tapes 35 prime) :
    let view := payloadView prime d (w+1) W
    let headers := LabelPrepare.input view d i j (w+1)
    let cost := 3808274 * volume prime view + LeafCore.coreCost (volume prime view) (w+1)
    let slot := fun k : Fin 35 => Fin.castAdd 35 ((Fin.castAdd 24 k).castLE rowSwapFits)
    ∀ x : Fin (volume prime view) → ZMod 2, roles.head 24 = 0 → roles.tape 24 = sourceWord (v := view) x →
    RepT (SharedBankStageInput.raw (LabelCall.bank roles view headers) N)
      (S.L ∘ swapSimulationPort) (S.R ∘ swapSimulationPort) →
    ∃ (y : Fin (volume prime view) → ZMod 2), ∃ z F n, ∃ u, ∃ G : Stacks (N+35) prime,
      z.user = v.user ∧ n ≤ cost*(N+5)+6 ∧
      Exec body (embProg swapSimulationPort Empty.elim (foreign rowSwapBlock.program)) (mk v S) n (mk u G) ∧
      Exec body placedRowSwap (mk v S)
        (n+(((swapWorkspace (N+35)).map fun k => 4*(G.L k).length+2*(G.R k).length+4).sum+1)) (mk z F) ∧
      (∀ k : Fin (N+35), 35 ≤ k.val → F.L k = [] ∧ F.R k = []) ∧
      (∀ k : Fin 35, k ≠ 24 → F.L (slot k) = S.L (slot k) ∧ F.R (slot k) = S.R (slot k)) ∧
      (∀ pos, readAt blank (F.L (slot 24)) (F.R (slot 24)) pos = sourceWord (v := view) y pos) ∧
      ∀ (coords : Fin d → ZMod (prime^(w+1))) (k : Fin W),
        ext y (FlatCoordinateLayout.index (coords ∘ Equiv.swap i j) k).val = ext x (FlatCoordinateLayout.index coords k).val := by
  intro view headers cost slot x hh hx ready
  have swap := swapPayload_exec (P := Empty) (U := U) i j lt (Nat.succ_pos w) hW roles 24 x hh hx
  rw [← rowSwapBlock.eq_def] at swap
  obtain ⟨y,u,D,n,hu,hn,run,_,tape,effect⟩ := swap Empty.elim (embDn swapSimulationPort v) (embStk swapSimulationPort S) ready
  obtain ⟨u',G,placed,user,eq,frame⟩ := swapPlaced_exec body v S run
  rw [← eq] at tape
  have pos : (rowSwapBlock.slots (Fin.castAdd 24 (24 : Fin 35))).val = 24 := by rw [rowSwapBlock.eq_def]; rfl
  have pay : swapSimulationPort (rowSwapBlock.slots (Fin.castAdd 24 (24 : Fin 35))) = slot 24 := by
    apply Fin.ext
    have skip : ¬ ((rowSwapBlock.slots (Fin.castAdd 24 (24 : Fin 35))).val < 35 ∧ (rowSwapBlock.slots (Fin.castAdd 24 (24 : Fin 35))).val ≠ 24) := fun h => h.2 pos
    simp only [swapSimulationPort,dite_eq_right skip,Fin.val_castAdd]
    exact pos.trans (by simp [slot])
  let work := swapWorkspace (N+35)
  obtain ⟨z,hz,clear⟩ := clearWorkTapes_exec body work ((List.nodup_finRange _).filter _) u' G
  have keep (k : Fin 35) : slot k ∉ work := by simp [slot,work,swapWorkspace,k.isLt]
  refine ⟨y,z,_,n,u',G,hz.trans (user.trans hu),hn,placed,Exec.seq placed clear,?_,?_,?_,effect⟩
  · intro k hk; simp [work,swapWorkspace,hk]
  · intro k ne
    simpa only [ite_eq_right (keep k)] using frame ((Fin.castAdd 24 k).castLE rowSwapFits) k.isLt
      (fun e => ne (Fin.ext e))
  · intro p
    simpa only [embStk,Function.comp_apply,pay,ite_eq_right (keep 24),swap_source_word] using tape p

end IntegerMultBounds.MathlibTM2.Cover.Fallback
