module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackPlacedRowSwap

/-! A physical coordinate exchange from the row dimensions back to clean workspace. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host M8.RevMachine
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
open RecursiveInterchangeLayout (volume)
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
open Fast.Main
variable [M8.Machine.Net] {P U : Type}
local notation "N" => rowSwapBlock.tapes
local notation "Q" => rowSwapBlock.states
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos prime_prime.pos _).ne'⟩

theorem swapHostFits : 59 ≤ N+35 := rowSwapFits.trans (Nat.le_add_right ..)

noncomputable def completeSwap (d i j : ℕ) : Pr P (N+35) Q prime U :=
  .seq (swapSetup swapHostFits d i j) placedRowSwap

noncomputable def completeSwapTime [Fintype P] (body : P → Pr P (N+35) Q prime U) (d i j w W H J : ℕ) : ℕ :=
  let view := payloadView prime d (w+1) W
  let cost := 3808274 * volume prime view + LeafCore.coreCost (volume prime view) (w+1)
  let limit := dimensionTime H 1 d + (4*(d*H+1)+6) + (10*J+12) + (21*(w+1)+12) + 2 + (cost*(N+5)+6)
  let work := swapWorkspace (N+35)
  let push := max (mnPushC body) (mnProgPush (.seq (swapSetup swapHostFits d i j)
      (embProg swapSimulationPort Empty.elim (foreign rowSwapBlock.program)) : Pr P (N+35) Q prime U))
  limit + (4*work.length+1 + work.length*(6*(push*limit)))

/-- The row-swap charge per symbol before embedding and tape cleanup. -/
noncomputable def swapVolumeRate (w : ℕ) : ℕ :=
  3808274 + ⌈LeafCore.C * ((w+1 : ℕ) : ℝ) ^ M8.Machine.BudgetBound.tau⌉₊

theorem swapVolumeRate_le (w : ℕ) :
    (swapVolumeRate w : ℝ) ≤ (3808275 + LeafCore.C) *
      ((w+1 : ℕ) : ℝ) ^ M8.Machine.BudgetBound.tau := by
  let power := ((w+1 : ℕ) : ℝ) ^ M8.Machine.BudgetBound.tau
  have width : 1 ≤ power := Real.one_le_rpow (by exact_mod_cast Nat.le_add_left 1 w)
    M8.Machine.BudgetBound.exponent_range.1.le
  have pos : 0 < LeafCore.C :=
    (Classical.choose_spec M8.Machine.ArbitraryWidthOriginalTotalRun.uniform_bound).1
  have rounded := Nat.ceil_lt_add_one (mul_nonneg pos.le (zero_le_one.trans width))
  change ((3808274 + ⌈LeafCore.C * power⌉₊ : ℕ) : ℝ) ≤ (3808275 + LeafCore.C) * power
  push_cast
  linarith

/-- A swap pays setup once and a width-dependent charge per payload symbol. -/
theorem completeSwapTime_le_setup_add_volume [Fintype P] (body : P → Pr P (N+35) Q prime U)
    (d i j w W H J : ℕ) :
    let push := max (mnPushC body) (mnProgPush (.seq (swapSetup swapHostFits d i j)
      (embProg swapSimulationPort Empty.elim (foreign rowSwapBlock.program)) : Pr P (N+35) Q prime U))
    completeSwapTime body d i j w W H J ≤ completeSwapTime body d i j w 0 H J +
      (1 + (swapWorkspace (N+35)).length * 6 * push) * (N+5) *
        swapVolumeRate w * ((prime^(w+1))^d * W) := by
  unfold swapVolumeRate
  let V := (prime^(w+1))^d * W
  have size (x : ℕ) : volume prime (payloadView prime d (w+1) x) = (prime^(w+1))^d*x := by
    simp [payloadView, volume, ← pow_mul, Nat.mul_comm d]
  have bound : LeafCore.coreCost V (w+1) ≤
      ⌈LeafCore.C * ((w+1 : ℕ) : ℝ) ^ M8.Machine.BudgetBound.tau⌉₊ * V := by
    apply Nat.floor_le_of_le
    simp only [Nat.max_eq_right (by omega : 1 ≤ w+1), Nat.cast_mul]
    rw [mul_right_comm]
    exact mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Nat.cast_nonneg V)
  unfold completeSwapTime
  have empty : LeafCore.coreCost 0 (w+1) = 0 := by simp [LeafCore.coreCost]
  simp only [size, Nat.mul_zero, empty, Nat.add_zero, Nat.zero_add, Nat.zero_mul]
  dsimp [V] at bound
  grw [bound]
  exact le_of_eq (by ring)

theorem completeSwap_exec [Fintype P] {d w W : ℕ} (i j : Fin d) (lt : i < j) (H J : ℕ)
    (hm : prime^(w+1) < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (body : P → Pr P (N+35) Q prime U) (v : HS (N+35) Q prime U) (S : Stacks (N+35) prime) :
    let view := payloadView prime d (w+1) W
    let r := swapSetupPorts.trans (Fin.castLEEmb swapHostFits)
    let slot := fun k : Fin 35 => (Fin.castAdd 24 k).castLE swapHostFits
    let roles : Tapes 35 prime := ⟨fun _ => 0,fun k => readAt blank (S.L (slot k)) (S.R (slot k))⟩
    ∀ x : Fin (volume prime view) → ZMod 2, roles.tape 24 = sourceWord (v := view) x →
    S.R (r 0) = binSyms H (prime^(w+1)) → S.R (r 1) = binSyms 1 1 →
    S.R (r 10) = binSyms J W → (S.R (r 12)).length = w →
    (∀ k : Fin 14, 3 ≤ k → k < 9 → S.R (r k) = []) →
    (∀ k : Fin (N+35), 35 ≤ k.val → S.L k = [] ∧ S.R k = []) →
    ∃ (y : Fin (volume prime view) → ZMod 2), ∃ z F n, z.user = v.user ∧
      n ≤ completeSwapTime body d i j w W H J ∧
      Exec body (completeSwap d i j) (mk v S) n (mk z F) ∧
      (∀ k : Fin (N+35), 35 ≤ k.val → F.L k = [] ∧ F.R k = []) ∧
      (∀ k : Fin 35, k ≠ 24 → F.L (slot k) = S.L (slot k) ∧ F.R (slot k) = S.R (slot k)) ∧
      (∀ pos, readAt blank (F.L (slot 24)) (F.R (slot 24)) pos = sourceWord (v := view) y pos) ∧
      ∀ (coords : Fin d → ZMod (prime^(w+1))) (k : Fin W),
        ext y (FlatCoordinateLayout.index (coords ∘ Equiv.swap i j) k).val = ext x (FlatCoordinateLayout.index coords k).val := by
  intro view r slot roles x src base one width clock scratch empty
  let cost := 3808274 * volume prime view + LeafCore.coreCost (volume prime view) (w+1)
  let limit := dimensionTime H 1 d + (4*(d*H+1)+6) + (10*J+12) + (21*(w+1)+12) + 2 + (cost*(N+5)+6)
  let work := swapWorkspace (N+35)
  let push := max (mnPushC body) (mnProgPush (.seq (swapSetup swapHostFits d i j)
      (embProg swapSimulationPort Empty.elim (foreign rowSwapBlock.program)) : Pr P (N+35) Q prime U))
  obtain ⟨u,D,l,hu,hl,setup,saved,rep⟩ := swapSetup_exec swapHostFits body roles d i j w W H J hm hw v S
    base one width clock scratch (by intro k pos; simp [roles,slot])
    (fun k => empty _ (by change 35 ≤ 35+k.val; omega)) (fun k hk => empty k (by omega))
  obtain ⟨y,z,F,n,u',G,hz,hn,simulate,finish,clean,frame,tape,effect⟩ :=
    placedRowSwap_exec i j lt hW body u D roles x rfl src rep
  have time : l+n ≤ limit := Nat.add_le_add hl hn
  have cleanup := cleanup_cost_le work (Exec.seq setup simulate) (c := push) (le_max_right ..)
    (fun f => (mn_progPush_le_pushC body f).trans (le_max_left ..))
  have init : (work.map fun k => 4*(S.L k).length+2*(S.R k).length+4) = work.map (fun _ => 4) := by
    apply List.map_congr_left
    intro k hk
    have e := empty k (by simpa [work,swapWorkspace] using hk)
    simp [e]
  simp only [init,List.map_const',List.sum_replicate_nat] at cleanup
  refine ⟨y,z,F,_,hz.trans hu,?_,Exec.seq setup finish,clean,?_,tape,effect⟩
  · change _ ≤ limit + (4*work.length+1 + work.length*(6*(push*limit)))
    rw [← Nat.add_assoc]
    apply Nat.add_le_add time
    apply cleanup.trans
    rw [Nat.mul_comm work.length 4]
    gcongr
  · intro k ne
    have e := saved (slot k) (Or.inl k.isLt)
    exact ⟨(frame k ne).1.trans e.1,(frame k ne).2.trans e.2⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
