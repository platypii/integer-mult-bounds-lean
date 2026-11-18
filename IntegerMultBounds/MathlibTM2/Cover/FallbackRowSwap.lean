module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackSwapSetup

/-! Generate the headers and exchange two coordinates on row payload tape 24. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host M8.RevMachine
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
open RecursiveInterchangeLayout (volume)
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
local instance (w : ℕ) : NeZero (prime^(w+1)) := ⟨(pow_pos prime_prime.pos _).ne'⟩
variable [M8.Machine.Net] {P U : Type}

@[irreducible] noncomputable def rowSwapBlock : Graph.Block 59 prime := LabelSwap.program (24 : Fin 35)

theorem rowSwapFits : 59 ≤ rowSwapBlock.tapes := by
  have bound := (rowSwapBlock.slots (58 : Fin 59)).isLt
  have val : (rowSwapBlock.slots (58 : Fin 59)).val = 58 := by unfold rowSwapBlock; rfl
  rw [val] at bound
  exact bound

noncomputable def rowSwap (d i j : ℕ) : Pr P rowSwapBlock.tapes rowSwapBlock.states prime U :=
  .seq (swapSetup rowSwapFits d i j) (foreign rowSwapBlock.program)

theorem rowSwap_exec {d : ℕ} (i j : Fin d) (lt : i < j) (w W H J : ℕ)
    (hm : prime^(w+1) < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (body : P → Pr P rowSwapBlock.tapes rowSwapBlock.states prime U)
    (v : HS rowSwapBlock.tapes rowSwapBlock.states prime U) (S : Stacks rowSwapBlock.tapes prime) :
    let view := payloadView prime d (w+1) W
    let r := swapSetupPorts.trans (Fin.castLEEmb rowSwapFits)
    let port := swapHeaderPort (T := 35) rowSwapFits
    let slot := fun k : Fin 35 => (Fin.castAdd 24 k).castLE rowSwapFits
    let roles : Tapes 35 prime := ⟨fun _ => 0, fun k => readAt blank (S.L (slot k)) (S.R (slot k))⟩
    let cost := 3808274 * volume prime view + LeafCore.coreCost (volume prime view) (w+1)
    ∀ x : Fin (volume prime view) → ZMod 2, roles.tape 24 = sourceWord (v := view) x →
    S.R (r 0) = binSyms H (prime^(w+1)) → S.R (r 1) = binSyms 1 1 →
    S.R (r 10) = binSyms J W → (S.R (r 12)).length = w →
    (∀ k : Fin 14, 3 ≤ k → k < 9 → S.R (r k) = []) →
    (∀ k, S.L (port k) = [] ∧ S.R (port k) = []) →
    (∀ k : Fin rowSwapBlock.tapes, 59 ≤ k.val → S.L k = [] ∧ S.R k = []) →
    ∃ (y : Fin (volume prime view) → ZMod 2), ∃ z F n, z.user = v.user ∧
      n ≤ dimensionTime H 1 d + (4*(d*H+1)+6) + (10*J+12) + (21*(w+1)+12) + 2 + (cost*(rowSwapBlock.tapes+5)+6) ∧
      Exec body (rowSwap d i j) (mk v S) n (mk z F) ∧
      RepT (SharedBankStageInput.raw (LabelCall.bank (SharedPlacementAlphabet.setTape roles 24 (sourceWord (v := view) y) 0)
        view (LabelPrepare.input view d i j (w+1))) rowSwapBlock.tapes) F.L F.R ∧
      (∀ pos, readAt blank (F.L (slot 24)) (F.R (slot 24)) pos = sourceWord (v := view) y pos) ∧
      ∀ (coords : Fin d → ZMod (prime^(w+1))) (k : Fin W),
        ext y (FlatCoordinateLayout.index (coords ∘ Equiv.swap i j) k).val = ext x (FlatCoordinateLayout.index coords k).val := by
  intro view r port slot roles cost x src base one width clock scratch headers privateTapes
  obtain ⟨u,D,l,hu,hl,setup,ready⟩ := swapSetup_exec rowSwapFits body roles d i j w W H J hm hw v S
    base one width clock scratch (by intro k pos; simp [roles,slot]) headers privateTapes
  have swap := swapPayload_exec (P := P) (U := U) i j lt (Nat.succ_pos w) hW roles 24 x rfl src
  rw [← rowSwapBlock.eq_def] at swap
  obtain ⟨y,z,F,n,hz,hn,run,rep,tape,effect⟩ := swap body u D ready
  have position : rowSwapBlock.slots (Fin.castAdd 24 (24 : Fin 35)) = slot 24 := by
    apply Fin.ext
    change (rowSwapBlock.slots (Fin.castAdd 24 (24 : Fin 35))).val = 24
    rw [rowSwapBlock.eq_def]
    rfl
  rw [position] at tape
  exact ⟨y,z,F,l+n,hz.trans hu,Nat.add_le_add hl hn,Exec.seq setup run,rep,tape,effect⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
