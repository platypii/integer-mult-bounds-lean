module

public import IntegerMultBounds.MathlibTM2.M6.BitCopyOwners
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

/-- A flat pass of any fitting size shares the swap's owner tape. Every
positive slot uses the scratch suffix, starting at its first tape. -/
def portPassPlacement {T K n : ℕ} (io : Fin T) (fits : n ≤ 1+(24+K)) :
    Fin n ↪ Fin (T+(24+K)) :=
  (Fin.castLEEmb fits).trans (portSwapPlacement io K)

theorem portPassPlacement_row {T K n : ℕ} (io : Fin T) (fits : n ≤ 1+(24+K))
    (pos : 0 < n) : portPassPlacement io fits ⟨0,pos⟩ = io.castAdd _ := by
  change (Fin.addCases (fun _ : Fin 1 => io.castAdd (24+K)) (Fin.natAdd T) ((0 : Fin 1).castAdd (24+K)) : Fin (T+(24+K))) = _
  rw [Fin.addCases_left]

theorem portPassPlacement_scratch {T K n : ℕ} (io : Fin T) (fits : n ≤ 1+(24+K))
    (i : Fin n) (pos : 0 < i.val) :
    portPassPlacement io fits i = (⟨i.val-1,by omega⟩ : Fin (24+K)).natAdd T := by
  let j : Fin (24+K) := ⟨i.val-1,by omega⟩
  have eq : i.castLE fits = j.natAdd 1 := by
    apply Fin.ext
    change i.val = 1+(i.val-1)
    omega
  change (Fin.addCases (fun _ : Fin 1 => io.castAdd (24+K)) (Fin.natAdd T) (i.castLE fits) : Fin (T+(24+K))) = _
  rw [eq,Fin.addCases_right]

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

/-- The same suffix installed by the runtime initializer represents the
digit-swap metadata when the owner slot is stripped. -/
theorem swapPrivateStacks_rep (K : ℕ) (view : RecursiveInterchangeLayout.Descriptor) (d i j w : ℕ) :
    let seed := swapPrivateStacks K view d i j w
    let bank := LabelCall.bank (SharedBank.empty 1 prime) view (LabelPrepare.input view d i j w)
    RepT (SharedBankStageInput.raw bank (1+(24+K)))
      (Fin.append (fun _ : Fin 1 => []) seed.L) (Fin.append (fun _ : Fin 1 => []) seed.R) := by
  intro seed bank
  let S : Stacks (1+(24+K)) prime := ⟨[],[],Fin.append (fun _ : Fin 1 => []) seed.L,
    Fin.append (fun _ : Fin 1 => []) seed.R⟩
  apply swap_bank_rep (by omega : 1+24 ≤ 1+(24+K)) _ _ _ S
  · intro k pos
    have eq : (k.castAdd 24).castLE (by omega : 1+24 ≤ 1+(24+K)) = k.castAdd (24+K) := Fin.ext rfl
    simp [eq,S,SharedBank.empty,readAt_nil_left,wordTape_nil]
  · intro k
    have eq : (k.natAdd 1).castLE (by omega : 1+24 ≤ 1+(24+K)) = (k.castAdd K).natAdd 1 := Fin.ext rfl
    simp only [eq,S,Fin.append_right,seed,swapPrivateStacks,Fin.append_left]
    exact ⟨rfl,rfl⟩
  · intro k beyond
    let a : Fin K := ⟨k.val-25,by omega⟩
    have eq : k = (a.natAdd 24).natAdd 1 := Fin.ext (by dsimp [a]; omega)
    rw [eq]
    simp [S,seed,swapPrivateStacks]

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
      (∀ k : Fin (24+K), let seed := swapPrivateStacks K view d i j (w+1)
        F.L (k.natAdd T) = seed.L k ∧ F.R (k.natAdd T) = seed.R k) ∧
      RepT (SharedBankStageInput.raw (LabelCall.bank one view (LabelPrepare.input view d i j (w+1))) (1+(24+K)))
        (F.L ∘ port) (F.R ∘ port) := by
  intro fits hdr one port view setup setupTime power spectator exponent u S base unit width clock scratch represented fresh tail
  obtain ⟨z,F,n,user,time,exec,keep,headers,ready⟩ := swapSetupAt_exec fits r body roles d i j w W H J baseFits widthFits
    u S power spectator exponent base unit width clock scratch represented fresh tail
  have closed : WordCmd.NoCalls setup := ⟨⟨⟨dimensionPower_noCalls _ _,by repeat constructor⟩,by repeat constructor⟩,by repeat constructor⟩
  have charge := nativeCleanupBound exec (WordCmd.native_of_noCalls closed le_rfl)
  refine ⟨z,F,n,user,time,exec,?_,fun k => keep _ (Or.inl k.isLt),?_,portSwapBank_rep roles io view _ F ready⟩
  · intro js distinct
    exact (charge js distinct).trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ time) _)
  · intro k
    induction k using Fin.addCases with
    | left k =>
      have index : swapHeaderPort fits k = (k.castAdd K).natAdd T := Fin.ext rfl
      simpa only [index,view,swapPrivateStacks,Fin.append_left] using headers k
    | right k =>
      have beyond : T+24 ≤ ((k.natAdd 24).natAdd T).val := by simp
      have off := keep _ (Or.inr beyond)
      simpa only [swapPrivateStacks,Fin.append_right] using
        And.intro (off.1.trans (tail _ beyond).1) (off.2.trans (tail _ beyond).2)

/-- The quadratic arithmetic on the radix header fits in two of the chart's
digits, uniformly in the spectator count. -/
theorem swapPortSetupTime_le (d w W : ℕ) (degree : 2 ≤ d) (pos : 0 < W) :
    let M := prime^(w+1)
    let V := M^d*W
    dimensionTime M.size 1 d + (4*(d*M.size+1)+6) + (10*W.size+12) + (21*(w+1)+12) + 2 ≤
      (30*d^2+80*d+100)*V := by
  intro M V
  have hm : 0 < M := pow_pos IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos _
  have size (n : ℕ) : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  have mass : M^d ≤ V := Nat.le_mul_of_pos_right _ pos
  have radix : M ≤ V := (Nat.le_self_pow (by omega : d ≠ 0) M).trans mass
  have square : M.size*M.size ≤ V := (Nat.mul_le_mul (size M) (size M)).trans
    ((sq M).symm ▸ (Nat.pow_le_pow_right hm degree).trans mass)
  have width := (size M).trans radix
  have clock : w+1 ≤ V := (Nat.lt_pow_self IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.one_lt).le.trans radix
  have spectator : W ≤ V := Nat.le_mul_of_pos_left _ (pow_pos hm _)
  have unit := pos.trans_le spectator
  have quadratic := Nat.mul_le_mul_left (12*d^2) square
  have linear := Nat.mul_le_mul_left (18*d^2+36*d) width
  have fixed := Nat.mul_le_mul_left (44*d) (show 1 ≤ V from unit)
  have dims := dimensionTime_le M.size 1 d
  have rest := (size W).trans spectator
  nlinarith only [quadratic,linear,fixed,dims,rest,clock,unit]

/-- Install one correction's private suffix at an arbitrary host placement.
The 35 caller registers and every off-bank tape retain both stacks. -/
theorem placedSwapPortLoader {P U : Type} {T Q K : ℕ} (body : P → Pr P T Q prime U)
    (bank : Fin (35+(24+K)) ↪ Fin T) (d i j : ℕ) (degree : 2 ≤ d) :
    let caller := (Fin.castAddEmb (24+K) (n := 35)).trans bank
    let suffix := (Fin.natAddEmb 35 (m := 24+K)).trans bank
    ∃ rate : ℕ, ∃ code, ∀ w W, 0 < W → ∀ u (S : Stacks T prime),
      let M := prime^(w+1)
      S.R (caller 2) = binSyms M.size M → S.R (caller 28) = binSyms 1 1 →
      S.R (caller 27) = binSyms W.size W → (S.R (caller 33)).length = w →
      (∀ k : Fin 35, 3 ≤ k.val → k.val < 9 → S.R (caller k) = []) →
      (∀ k, S.L (suffix k) = [] ∧ S.R (suffix k) = []) →
      ∃ z F n, Exec body code (mk u S) n (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F n (rate*(M^d*W)) ∧
        (∀ k, let seed := swapPrivateStacks K (payloadView prime d (w+1) W) d i j (w+1)
          F.L (suffix k) = seed.L k ∧ F.R (suffix k) = seed.R k) ∧
        ∀ k, (∀ h, suffix h ≠ k) → F.L k = S.L k ∧ F.R k = S.R k := by
  intro caller suffix
  let fits : 59 ≤ 35+(24+K) := by omega
  let r := swapSetupPorts.trans (Fin.castLEEmb fits)
  let setup : Pr Empty (35+(24+K)) Q prime U := swapSetup fits d i j
  let factor := 1+6*Fast.Main.mnProgPush setup
  refine ⟨factor*(30*d^2+80*d+100),embProg bank Empty.elim setup,?_⟩
  intro w W pos u S M base one width clock scratch free
  let D := embStk bank S
  let roles : Tapes 35 prime := ⟨fun _ => 0,fun k => readAt blank (D.L (k.castAdd _)) (D.R (k.castAdd _))⟩
  obtain ⟨v,G,n,user,_,run,charge,kept,loaded,_⟩ := preparePortSwap (P := Empty) (U := U) (Q := Q)
    Empty.elim roles 0 r d i j w W M.size W.size (Nat.lt_size_self _) (Nat.lt_size_self _) rfl rfl rfl
    (embDn bank u) D base one width clock (by
      intro k lo hi
      let h : Fin 35 := k.castLE (by decide)
      have reg : ∀ k : Fin 14, 3 ≤ k.val → k.val < 9 → (swapSetupPorts k).val = k.val := by decide
      have eq : r k = h.castAdd (24+K) := Fin.ext (reg k lo hi)
      change S.R (bank (r k)) = []
      rw [eq]
      exact scratch h lo hi)
    (by intro k h; simp [roles]) (fun k => free (k.castAdd K)) (by
      intro k beyond
      let h : Fin (24+K) := ⟨k.val-35,by omega⟩
      have eq : k = h.natAdd 35 := Fin.ext (by dsimp [h]; omega)
      rw [eq]
      exact free h)
  obtain ⟨z,F,exec,_,same,view,off⟩ := exec_emb (ι := Empty.elim) (body' := body) bank.injective
    (fun f => nomatch f) run u rfl S rfl
  refine ⟨z,F,n,exec,same.trans user,?_,?_,?_⟩
  · have bound := Nat.mul_le_mul_left factor (swapPortSetupTime_le d w W degree pos)
    rw [← Nat.mul_assoc] at bound
    rw [← view] at charge
    intro js nd
    exact (placedCleanup_cost_le bank S F cleanupWeight n _ off charge js nd).trans (Nat.add_le_add_left bound _)
  · intro k
    rw [← view] at loaded
    exact loaded k
  · intro k outside
    by_cases hit : ∃ h, bank h = k
    · obtain ⟨h,rfl⟩ := hit
      induction h using Fin.addCases with
      | left h => rw [← view] at kept; exact kept h
      | right h => exact False.elim (outside h rfl)
    · exact off k (fun h eq => hit ⟨h,eq⟩)

local instance (w : ℕ) : NeZero (prime^w) := ⟨(pow_pos IntegerMultBounds.Networks.Shared50ModularControl.prime_prime.pos w).ne'⟩

/-- Prepare and run the digit correction on the selected owner's physical row. -/
theorem runPortSwap [M8.Machine.Net] {T K Q : ℕ} {P U : Type}
    (body : P → Pr P (T+(24+K)) Q prime U) (io : Fin T)
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
    ∀ (x : Fin ((prime^(w+1))^d*W) → ZMod 2),
    r 2 = hdr 5 → r 11 = hdr 14 → r 13 = hdr 8 →
    ∀ u (S : Stacks (T+(24+K)) prime),
    S.R (r 0) = binSyms H (prime^(w+1)) → S.R (r 1) = binSyms 1 1 →
    S.R (r 10) = binSyms J W → (S.R (r 12)).length = w →
    (∀ k : Fin 14, 3 ≤ k → k < 9 → S.R (r k) = []) →
    (∀ h, readAt blank (S.L (io.castAdd _)) (S.R (io.castAdd _)) h = (portOwner x).tape 0 h) →
    (∀ k, S.L (hdr k) = [] ∧ S.R (hdr k) = []) →
    (∀ k, T+24 ≤ k.val → S.L k = [] ∧ S.R k = []) →
    ∃ (y : Fin ((prime^(w+1))^d*W) → ZMod 2), ∃ z F n, z.user = u.user ∧
      Exec body ((setup.seq (embProg bank Empty.elim (foreign (liftQ block.program capacity)))).seq (clearWorkTapes work)) (mk u S) n (mk z F) ∧
      CleanupBound S F n ((1+6*Fast.Main.mnProgPush setup)*setupTime+13*runTime+4*(24+K)+1) ∧
      (∀ k : Fin (24+K), F.L (k.natAdd T) = [] ∧ F.R (k.natAdd T) = []) ∧
      (∀ k : Fin T, k ≠ io → F.L (k.castAdd _) = S.L (k.castAdd _) ∧ F.R (k.castAdd _) = S.R (k.castAdd _)) ∧
      (∀ h, readAt blank (F.L (io.castAdd (24+K)))
        (F.R (io.castAdd (24+K))) h =
          (portOwner y).tape 0 h) ∧
      ∀ (coords : Fin d → ZMod (prime^(w+1))) (k : Fin W), y (FlatCoordinateLayout.index (coords ∘ Equiv.swap i j) k) =
        x (FlatCoordinateLayout.index coords k) := by
  intro block capacity fitsBlock fits hdr port bank view setup setupTime runTime work x power spectator exponent
    u S base unit width clock scratch owner fresh tail
  let roles : Tapes T prime := ⟨fun _ => 0,fun k => readAt blank (S.L (k.castAdd _)) (S.R (k.castAdd _))⟩
  have represented k h : roles.tape k h = readAt blank (S.L (k.castAdd _)) (S.R (k.castAdd _)) (h-roles.head k) := by simp [roles]
  have size : RecursiveInterchangeLayout.volume prime view = (prime^(w+1))^d*W := by
    simp [view,payloadView,RecursiveInterchangeLayout.volume,← pow_mul,Nat.mul_comm]
  have word := (funext owner).trans (sourceWord_cast size x).symm
  obtain ⟨v,D,l,same,_,start,charge,kept,_,ready⟩ := preparePortSwap body roles io r d i j w W H J baseFits widthFits
    power spectator exponent u S base unit width clock scratch represented fresh tail
  let one : Tapes 1 prime := ⟨fun _ => roles.head io,fun _ => roles.tape io⟩
  obtain ⟨y,swap,effect⟩ := swapPayload_runs i j lt (Nat.succ_pos w) pos one 0 (fun k => x (k.cast size)) rfl word
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
  let result := fun k => y (Fin.cast size.symm k)
  refine ⟨result,v',B,_,zu.trans (last.trans (user.trans same)),(start.seq placed).seq clear,?_,
    fun k => clean _ (List.mem_map_of_mem (List.mem_finRange k)),?_,?_,?_⟩
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
    have output := sourceWord_cast size result
    simp only [result,Fin.cast_cast,Fin.cast_refl] at output
    exact (out h).trans (congrFun output h)
  · intro coords k
    have action := effect coords k
    have atIndex (f : Fin (RecursiveInterchangeLayout.volume prime view) → ZMod 2)
        (k : Fin ((prime^(w+1))^d*W)) : M8.RevMachine.ext f k.val = f (k.cast size.symm) := by
      exact dite_eq_left (size.symm ▸ k.isLt)
    exact (atIndex y _).symm.trans (action.trans (atIndex (fun k => x (k.cast size)) _))

end IntegerMultBounds.MathlibTM2.M6.BitNode
