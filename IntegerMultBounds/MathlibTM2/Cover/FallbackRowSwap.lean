module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackSwapSetup
public import IntegerMultBounds.MathlibTM2.Cover.FallbackShearCleanup

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

def swapWorkspace (N : ℕ) : List (Fin N) := (List.finRange N).filter fun i => 35 ≤ i.val

noncomputable def cleanRowSwap (d i j : ℕ) : Pr P rowSwapBlock.tapes rowSwapBlock.states prime U :=
  .seq (rowSwap d i j) (clearWorkTapes (swapWorkspace rowSwapBlock.tapes))

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
      ∃ u G, u.user = v.user ∧
        Exec body (cleanRowSwap d i j) (mk v S)
          (n+(((swapWorkspace rowSwapBlock.tapes).map fun k => 4*(F.L k).length+2*(F.R k).length+4).sum+1)) (mk u G) ∧
        (∀ k : Fin rowSwapBlock.tapes, 35 ≤ k.val → G.L k = [] ∧ G.R k = []) ∧
        (∀ k : Fin 35, ∀ pos, readAt blank (G.L (slot k)) (G.R (slot k)) pos =
          (SharedPlacementAlphabet.setTape roles 24 (sourceWord (v := view) y) 0).tape k pos) ∧
      (∀ pos, readAt blank (G.L (slot 24)) (G.R (slot 24)) pos = sourceWord (v := view) y pos) ∧
      ∀ (coords : Fin d → ZMod (prime^(w+1))) (k : Fin W),
        ext y (FlatCoordinateLayout.index (coords ∘ Equiv.swap i j) k).val = ext x (FlatCoordinateLayout.index coords k).val := by
  intro view r port slot roles cost x src base one width clock scratch headers privateTapes
  obtain ⟨u,D,l,hu,hl,setup,_,ready⟩ := swapSetup_exec rowSwapFits body roles d i j w W H J hm hw v S
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
  let work := swapWorkspace rowSwapBlock.tapes
  obtain ⟨u',hu',clear⟩ := clearWorkTapes_exec body work ((List.nodup_finRange _).filter _) z F
  have outside (k : Fin 35) : slot k ∉ work := by simp [work,swapWorkspace,slot,k.isLt]
  have whole := Exec.seq setup run
  refine ⟨y,z,F,l+n,hz.trans hu,Nat.add_le_add hl hn,whole,u',_,hu'.trans (hz.trans hu),Exec.seq whole clear,?_,?_,?_,effect⟩
  · intro k hk
    simp [work,swapWorkspace,hk]
  · intro k pos
    simp only [ite_eq_right (outside k)]
    have cell := swap_role_read _ view _ F rep k (slot k) rfl pos
    simpa [roles,SharedPlacementAlphabet.setTape,Function.update_apply] using cell
  · intro pos
    simpa only [ite_eq_right (outside 24),swap_source_word] using tape pos

end IntegerMultBounds.MathlibTM2.Cover.Fallback
