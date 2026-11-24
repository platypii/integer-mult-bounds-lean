module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackSwapSetup
public import IntegerMultBounds.MathlibTM2.M6.BitClearBank
import IntegerMultBounds.MathlibTM2.Host.WordCmdStock

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine Stack Host Cover Cover.Fallback
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

/-- Keep one caller role and the whole header and scratch region after the roles. -/
def portSwapPlacement {T : ℕ} (io : Fin T) (K : ℕ) : Fin (1+(24+K)) ↪ Fin (T+(24+K)) where
  toFun := Fin.addCases (fun _ => io.castAdd _) (Fin.natAdd T)
  inj' := by
    intro i j
    induction i using Fin.addCases <;> induction j using Fin.addCases <;> intro eq
    · congr 1
      exact Subsingleton.elim _ _
    · have h := congrArg Fin.val eq
      simp only [Fin.addCases_left,Fin.addCases_right,Fin.val_castAdd,Fin.val_natAdd] at h
      omega
    · have h := congrArg Fin.val eq
      simp only [Fin.addCases_left,Fin.addCases_right,Fin.val_castAdd,Fin.val_natAdd] at h
      omega
    · congr 1
      apply Fin.ext
      have h := congrArg Fin.val eq
      simp only [Fin.addCases_right,Fin.val_natAdd] at h
      omega

/-- Restrict a prepared swap bank to one owner. The correction uses the same
24 headers and trailing workspace as the row machine that prepared them. -/
theorem portSwapBank_rep {T K : ℕ} (roles : Tapes T prime) (io : Fin T)
    (view : RecursiveInterchangeLayout.Descriptor) (headers : Fin 22 → Option (List Bool))
    (S : Stacks (T+(24+K)) prime)
    (ready : RepT (SharedBankStageInput.raw (LabelCall.bank roles view headers) (T+(24+K))) S.L S.R) :
    let one : Tapes 1 prime := ⟨fun _ => roles.head io,fun _ => roles.tape io⟩
    let port := portSwapPlacement io K
    RepT (SharedBankStageInput.raw (LabelCall.bank one view headers) (1+(24+K))) (S.L ∘ port) (S.R ∘ port) := by
  intro one port j pos
  induction j using Fin.addCases with
  | left i =>
    have cell := ready (io.castAdd (24+K)) pos
    have small : io.val < T+24 := by omega
    have lhs : i.val < 1+24 := by omega
    have atLarge : (⟨io.val,small⟩ : Fin (T+24)) = io.castAdd 24 := rfl
    have atSmall : (⟨i.val,lhs⟩ : Fin (1+24)) = i.castAdd 24 := rfl
    simpa only [one,port,portSwapPlacement,Function.Embedding.coeFn_mk,Function.comp_apply,Fin.addCases_left,SharedBankStageInput.raw,Fin.val_castAdd,
      dite_eq_left small,dite_eq_left lhs,atLarge,atSmall,LabelCall.bank,Tapes.append,Fin.addCases_left] using cell
  | right i =>
    have cell := ready (i.natAdd T) pos
    by_cases h : i.val < 24
    · have left : 1+i.val < 1+24 := by omega
      have right : T+i.val < T+24 := by omega
      let k : Fin 24 := ⟨i.val,h⟩
      have atLarge : (⟨T+i.val,right⟩ : Fin (T+24)) = k.natAdd T := rfl
      have atSmall : (⟨1+i.val,left⟩ : Fin (1+24)) = k.natAdd 1 := rfl
      simpa only [port,portSwapPlacement,Function.Embedding.coeFn_mk,Function.comp_apply,Fin.addCases_right,SharedBankStageInput.raw,Fin.val_natAdd,
        dite_eq_left left,dite_eq_left right,atLarge,atSmall,LabelCall.bank,Tapes.append,Fin.addCases_right] using cell
    · have left : ¬ 1+i.val < 1+24 := by omega
      have right : ¬ T+i.val < T+24 := by omega
      simpa only [port,portSwapPlacement,Function.Embedding.coeFn_mk,Function.comp_apply,Fin.addCases_right,SharedBankStageInput.raw,Fin.val_natAdd,
        dite_eq_right left,dite_eq_right right] using cell

private theorem dimensionPower_noCalls {P U : Type} {T Q : ℕ} (r : Fin 10 ↪ Fin T) (d : ℕ) :
    WordCmd.NoCalls (dimensionPower (P := P) (Q := Q) (A := prime) (U := U) r d) := by
  induction d generalizing r with
  | zero => repeat constructor
  | succ d ih => exact ⟨ih _,by repeat constructor⟩

/-- Initialize the one-owner correction on a projection of the caller's tapes,
retaining all role tapes through the setup. -/
theorem preparePortSwap {T K Q : ℕ} {P U : Type}
    (body : P → Pr P (T+(24+K)) Q prime U) (roles : Tapes T prime) (io : Fin T)
    (r : Fin 14 ↪ Fin (T+(24+K))) (d i j w W H J : ℕ)
    (baseFits : prime^(w+1) < 2^H) (widthFits : W < 2^J) :
    let fits : T+24 ≤ T+(24+K) := by omega
    let hdr := swapHeaderPort fits
    let one : Tapes 1 prime := ⟨fun _ => roles.head io,fun _ => roles.tape io⟩
    let port := portSwapPlacement io K
    let view := payloadView prime d (w+1) W
    let setup : Pr P (T+(24+K)) Q prime U := (swapRuntimeHeaders r d).seq ((writeSwapConstants fits d i j).seq (markSwapHeaders fits))
    let setupTime := dimensionTime H 1 d + (4*(d*H+1)+6) + (10*J+12) + (21*(w+1)+12) + 2
    r 2 = hdr 5 → r 11 = hdr 14 → r 13 = hdr 8 →
    ∀ u (S : Stacks (T+(24+K)) prime),
    S.R (r 0) = binSyms H (prime^(w+1)) → S.R (r 1) = binSyms 1 1 →
    S.R (r 10) = binSyms J W → (S.R (r 12)).length = w →
    (∀ k : Fin 14, 3 ≤ k → k < 9 → S.R (r k) = []) →
    (∀ k pos, roles.tape k pos = readAt blank (S.L (k.castAdd _)) (S.R (k.castAdd _)) (pos-roles.head k)) →
    (∀ k, S.L (hdr k) = [] ∧ S.R (hdr k) = []) →
    (∀ k, T+24 ≤ k.val → S.L k = [] ∧ S.R k = []) →
    ∃ z F n, z.user = u.user ∧ n ≤ setupTime ∧
      Exec body setup (mk u S) n (mk z F) ∧
      CleanupBound S F n ((1+6*Fast.Main.mnProgPush setup)*setupTime) ∧
      (∀ k : Fin T, F.L (k.castAdd _) = S.L (k.castAdd _) ∧ F.R (k.castAdd _) = S.R (k.castAdd _)) ∧
      RepT (SharedBankStageInput.raw (LabelCall.bank one view (LabelPrepare.input view d i j (w+1))) (1+(24+K)))
        (F.L ∘ port) (F.R ∘ port) := by
  intro fits hdr one port view setup setupTime power spectator exponent u S base unit width clock scratch represented fresh tail
  obtain ⟨z,F,n,user,time,exec,keep,ready⟩ := swapSetupAt_exec fits r body roles d i j w W H J baseFits widthFits
    u S power spectator exponent base unit width clock scratch represented fresh tail
  have closed : WordCmd.NoCalls setup := ⟨⟨⟨dimensionPower_noCalls _ _,by repeat constructor⟩,by repeat constructor⟩,by repeat constructor⟩
  have charge := nativeCleanupBound exec (WordCmd.native_of_noCalls closed le_rfl)
  refine ⟨z,F,n,user,time,exec,?_,fun k => keep _ (Or.inl k.isLt),portSwapBank_rep roles io view _ F ready⟩
  intro js distinct
  exact (charge js distinct).trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ time) _)

local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos w).ne'⟩

/-- Prepare and run the digit correction on the selected owner's physical row. -/
theorem runPortSwap [M8.Machine.Net] {T K Q : ℕ} {P U : Type}
    (body : P → Pr P (T+(24+K)) Q prime U) (roles : Tapes T prime) (io : Fin T)
    (r : Fin 14 ↪ Fin (T+(24+K))) {d : ℕ} (i j : Fin d) (lt : i < j) (w W H J : ℕ) (pos : 0 < W)
    (baseFits : prime^(w+1) < 2^H) (widthFits : W < 2^J) :
    let block := LabelSwap.program (0 : Fin 1)
    ∀ (capacity : block.states ≤ Q) (fitsBlock : block.tapes ≤ 1+(24+K)),
    let fits : T+24 ≤ T+(24+K) := by omega
    let hdr := swapHeaderPort fits
    let port := portSwapPlacement io K
    let bank := (Fin.castLEEmb fitsBlock).trans port
    let view := payloadView prime d (w+1) W
    let setup : Pr P (T+(24+K)) Q prime U := (swapRuntimeHeaders r d).seq ((writeSwapConstants fits d i j).seq (markSwapHeaders fits))
    let setupTime := dimensionTime H 1 d + (4*(d*H+1)+6) + (10*J+12) + (21*(w+1)+12) + 2
    let runTime := (3808274*RecursiveInterchangeLayout.volume prime view +
      M8.RevMachine.LeafCore.coreCost (RecursiveInterchangeLayout.volume prime view) (w+1))*(block.tapes+5)+6
    let work := (List.finRange (24+K)).map (Fin.natAdd T)
    ∀ (x : Fin (RecursiveInterchangeLayout.volume prime view) → ZMod 2),
    roles.head io = 0 → roles.tape io = M8.Machine.ArbitraryWidthHighExchangeShared.sourceWord (v := view) x →
    r 2 = hdr 5 → r 11 = hdr 14 → r 13 = hdr 8 →
    ∀ u (S : Stacks (T+(24+K)) prime),
    S.R (r 0) = binSyms H (prime^(w+1)) → S.R (r 1) = binSyms 1 1 →
    S.R (r 10) = binSyms J W → (S.R (r 12)).length = w →
    (∀ k : Fin 14, 3 ≤ k → k < 9 → S.R (r k) = []) →
    (∀ k pos, roles.tape k pos = readAt blank (S.L (k.castAdd _)) (S.R (k.castAdd _)) (pos-roles.head k)) →
    (∀ k, S.L (hdr k) = [] ∧ S.R (hdr k) = []) →
    (∀ k, T+24 ≤ k.val → S.L k = [] ∧ S.R k = []) →
    ∃ y z F n, z.user = u.user ∧
      Exec body ((setup.seq (embProg bank Empty.elim (foreign (liftQ block.program capacity)))).seq (clearWorkTapes work)) (mk u S) n (mk z F) ∧
      CleanupBound S F n ((1+6*Fast.Main.mnProgPush setup)*setupTime+13*runTime+4*(24+K)+1) ∧
      (∀ k : Fin (24+K), F.L (k.natAdd T) = [] ∧ F.R (k.natAdd T) = []) ∧
      (∀ k : Fin T, k ≠ io → F.L (k.castAdd _) = S.L (k.castAdd _) ∧ F.R (k.castAdd _) = S.R (k.castAdd _)) ∧
      (∀ h, readAt blank (F.L (io.castAdd (24+K)))
        (F.R (io.castAdd (24+K))) h =
          M8.Machine.ArbitraryWidthHighExchangeShared.sourceWord (v := view) y h) ∧
      ∀ (coords : Fin d → ZMod (prime^(w+1))) (k : Fin W), M8.RevMachine.ext y (FlatCoordinateLayout.index (coords ∘ Equiv.swap i j) k).val =
        M8.RevMachine.ext x (FlatCoordinateLayout.index coords k).val := by
  intro block capacity fitsBlock fits hdr port bank view setup setupTime runTime work x head word power spectator exponent
    u S base unit width clock scratch represented fresh tail
  obtain ⟨v,D,l,same,_,start,charge,kept,ready⟩ := preparePortSwap body roles io r d i j w W H J baseFits widthFits
    power spectator exponent u S base unit width clock scratch represented fresh tail
  let one : Tapes 1 prime := ⟨fun _ => roles.head io,fun _ => roles.tape io⟩
  obtain ⟨y,swap,effect⟩ := swapPayload_runs i j lt (Nat.succ_pos w) pos one 0 x head word
  obtain ⟨z,G,_,rfl,rep,user,_,_,_,n,time,run⟩ := foreign_exec (P := Empty) Empty.elim
    (liftQ block.program capacity) (HoareTime.liftQ capacity swap) (embDn bank v) (embStk bank D) _ rfl
    (fun k h => ready (k.castLE fitsBlock) h)
  have out h := swap_role_read _ view (LabelPrepare.input view d i.val j.val (w+1)) G rep 0
    (block.slots (Fin.castAdd 24 0)) rfl h
  simp only [SharedPlacementAlphabet.setTape,Function.update_self,sub_zero] at out
  obtain ⟨z',F,placed,_,last,projection,off⟩ := exec_emb (ι := Empty.elim) (body' := body) bank.injective
    (fun f => nomatch f) run v rfl D rfl
  have unique : work.Nodup := (List.nodup_finRange _).map (Fin.natAdd_injective _ T)
  obtain ⟨v',zu,clear⟩ := clearWorkTapes_exec body work unique z' F
  let B := {F with L := fun j => if j ∈ work then [] else F.L j,
                   R := fun j => if j ∈ work then [] else F.R j}
  have clean (j) (hj : j ∈ work) : B.L j = [] ∧ B.R j = [] := by simp [B,hj]
  have outside (k : Fin T) : k.castAdd (24+K) ∉ work := by
    intro mem
    obtain ⟨i,_,eq⟩ := List.mem_map.mp mem
    have val := congrArg Fin.val eq
    change T+i.val = k.val at val
    omega
  have initial (j) (hj : j ∈ work) : S.L j = [] ∧ S.R j = [] := by
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hj
    by_cases small : i.val < 24
    · exact fresh ⟨i.val,small⟩
    · exact tail _ (by change T+24 ≤ T+i.val; omega)
  have cost : tapeCharge cleanupWeight work S = 4*(24+K) := by
    unfold tapeCharge
    rw [List.map_congr_left (g := fun _ => 4) (fun j hj => by simp [cleanupWeight,(initial j hj).1,(initial j hj).2])]
    rw [List.map_const',List.sum_replicate_nat]
    simp [work,Nat.mul_comm]
  refine ⟨y,v',B,_,zu.trans (last.trans (user.trans same)),(start.seq placed).seq clear,?_,
    fun k => clean _ (List.mem_map_of_mem (List.mem_finRange k)),?_,?_,effect⟩
  · have paid := cleanupBound_clearBank work unique (charge.seq (foreignCleanupBound placed))
      (le_refl (tapeCharge cleanupWeight work F+1)) clean
      (fun j => by by_cases h : j ∈ work <;> simp [B,h])
    rw [cost] at paid
    intro js nd
    exact (paid js nd).trans (by gcongr)
  · intro k ne
    have away (j : Fin (1+(24+K))) : port j ≠ k.castAdd (24+K) := by
      induction j using Fin.addCases with
      | left j =>
        intro eq
        have val := congrArg Fin.val eq
        simp only [port,portSwapPlacement,Function.Embedding.coeFn_mk,Fin.addCases_left,Fin.val_castAdd] at val
        exact ne (Fin.ext val.symm)
      | right j =>
        intro eq
        have val := congrArg Fin.val eq
        simp only [port,portSwapPlacement,Function.Embedding.coeFn_mk,Fin.addCases_right,Fin.val_natAdd,Fin.val_castAdd] at val
        omega
    have frame := off _ (fun i => away (i.castLE fitsBlock))
    simpa only [B,ite_eq_right (outside k)] using And.intro (frame.1.trans (kept k).1) (frame.2.trans (kept k).2)
  · intro h
    rw [← projection] at out
    simp only [B,ite_eq_right (outside io)]
    exact out h

end IntegerMultBounds.MathlibTM2.M6.BitNode
