module

public import IntegerMultBounds.MathlibTM2.M6.BitExactSplitEntry
public import IntegerMultBounds.MathlibTM2.M6.BitFlatNodeHandoff

/-! The packed recursive node supplies the row action of the fixed-bank MOVE. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open RecursiveInterchangeLayout (Descriptor volume)
open Shared50ModularControl (prime)

/-- The original serialized tape and the two inner loop counters. -/
def moveReturnPorts : Fin 3 ↪ Fin (intervalSplitTapes+1) :=
  ⟨![(0 : Fin intervalSplitTapes).succ,(mergeInnerPort 0).succ,(mergeInnerPort 1).succ],by decide⟩

theorem moveReturnPorts_disjoint (j : Fin 3) (i : Fin (142081+2)) :
    moveReturnPorts j ≠ withHelperPort (intervalOwners 142080) i := by
  let k : Fin intervalSplitTapes := (![0,mergeInnerPort 0,mergeInnerPort 1] : Fin 3 → _ ) j
  have eq : moveReturnPorts j = k.succ := by fin_cases j <;> rfl
  rw [eq]
  apply Ne.symm
  apply withHelperPort_avoids
  intro r
  induction r using Fin.addCases with
  | left r =>
    simp only [intervalOwners,Function.Embedding.coeFn_mk,Fin.addCases_left]
    intro h
    have e := congrArg Fin.val h
    fin_cases j <;> simp [k,mergeInnerPort] at e <;> omega
  | right r => fin_cases j <;> fin_cases r <;> decide

/-- Place the splitter around the installed child's actual input fan.
The three return tapes exhaust the complement of that fan in the splitter. -/
theorem splitBankForInput {T : ℕ} (src : Fin (142081+2) ↪ Fin T) (saved : Fin 3 ↪ Fin T)
    (apart : ∀ j i, saved j ≠ src i) :
    ∃ bank : Fin (intervalSplitTapes+1) ↪ Fin T,
      (withHelperPort (intervalOwners 142080)).trans bank = src ∧ moveReturnPorts.trans bank = saved ∧
      ∀ j, (∃ i, bank j = saved i) ∨ ∃ i, bank j = src i := by
  let localFan := withHelperPort (intervalOwners 142080)
  let order : Fin (3+(142081+2)) ↪ Fin (intervalSplitTapes+1) :=
    Fin.Embedding.append (Set.disjoint_range_iff.mpr moveReturnPorts_disjoint)
  let physical : Fin (3+(142081+2)) ↪ Fin T := Fin.Embedding.append (Set.disjoint_range_iff.mpr apart)
  let e := Equiv.ofBijective order ((Fintype.bijective_iff_injective_and_card _).2 ⟨order.injective,rfl⟩)
  refine ⟨e.symm.toEmbedding.trans physical,?_,?_,?_⟩
  · apply Function.Embedding.ext; intro i
    have eq : e (i.natAdd 3) = localFan i := by simp [e,order,localFan,Fin.Embedding.append]
    change physical (e.symm (localFan i)) = src i
    rw [← eq,e.symm_apply_apply]
    simp [physical,Fin.Embedding.append]
  · apply Function.Embedding.ext; intro j
    have eq : e (j.castAdd (142081+2)) = moveReturnPorts j := by simp [e,order,Fin.Embedding.append]
    change physical (e.symm (moveReturnPorts j)) = saved j
    rw [← eq,e.symm_apply_apply]
    simp [physical,Fin.Embedding.append]

  · intro j
    change (∃ i, physical (e.symm j) = saved i) ∨ ∃ i, physical (e.symm j) = src i
    induction e.symm j using Fin.addCases with
    | left i => exact Or.inl ⟨i,by simp [physical,Fin.Embedding.append]⟩
    | right i => exact Or.inr ⟨i,by simp [physical,Fin.Embedding.append]⟩

/-- A packed node transposes the whole wide record when called on its rows.
The wrapper is uniform in both the atom width and spectator count. -/
theorem packedMoveTranspose {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U) (entry : P)
    (bank : Fin (intervalSplitTapes+1) ↪ Fin T) (tmp buf : Fin T)
    (tmpOff : ∀ i, bank i ≠ tmp) (bufOff : ∀ i, bank i ≠ buf) (distinct : tmp ≠ buf)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    let fan := (withHelperPort (intervalOwners 142080)).trans bank
    ∀ dst : Fin (142081+2) ↪ Fin T,
    (∀ j i, bank (moveReturnPorts j) ≠ childReturnFan dst i) →
    ∃ code : Pr P T Q prime U, ∀ atom W price seed,
      let lane := packedDescriptor (64*atom) W
      let m := volume prime lane
      let wide := {lane with afterD := lane.afterD*142080}
      let size : m*142080 = volume prime wide := by simp [m,wide,volume,Nat.mul_assoc]
      PackedPieceHandoffWithCharge cleanupWeight m (packedChildOutput atom m) body (body entry) fan dst seed price →
      0 < m → ∀ (x : Fin (volume prime wide) → ZMod 2) u (S : Stacks T prime),
      S.R (bank (Fin.succ 0)) = List.ofFn (fun i => SparseRoleCircuit.encode (x (i.cast size))) →
      (∀ i, S.L (bank i) = []) → (∀ i, i ≠ Fin.succ 0 → S.R (bank i) = []) →
      S.L tmp = [] → S.R tmp = [] → S.R buf = [] →
      (∀ j, (∀ i, fan i ≠ bank j) → seed.L (bank j) = [] ∧ seed.R (bank j) = []) →
      (∀ j, (∀ i, bank i ≠ j) → S.L j = seed.L j ∧ S.R j = seed.R j) →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        RecordPayload (bank (Fin.succ 0)) (fun _ => blank) 0
          (Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) x) F ∧
        t ≤ price+214000000*volume prime wide := by
  intro fan dst disjoint
  obtain ⟨code,run⟩ := exactSplitReturnOn body entry bank tmp buf tmpOff bufOff distinct capacity dst
    (moveReturnPorts.trans bank) disjoint (fun j i => bank.injective.ne (moveReturnPorts_disjoint j i))
  refine ⟨code,?_⟩
  intro atom W price seed lane m wide size worker pos x u S source left empty tl tr br localSeed outerSeed
  obtain ⟨z,F,t,y,exec,user,effect,out,bill⟩ := run _ seed worker pos
    (fun i => x (i.cast size)) u S source left empty tl tr br localSeed outerSeed
  refine ⟨z,F,t,exec,user,?_,?_⟩
  · have position : packedChildPosition lane rfl = Equiv.refl _ := by
      ext i
      exact packActive_packed (64*atom) W i
    have cell (k : Fin (m*142080)) : y (finProdFinEquiv.symm k).2.castSucc (finProdFinEquiv.symm k).1 =
        Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) x (k.cast size) := by
      obtain ⟨⟨i,r⟩,rfl⟩ := finProdFinEquiv.surjective k
      have row := congrFun (effect r lane rfl rfl) i
      rw [position] at row
      simp only [Equiv.refl_apply,Function.comp_def,Fin.lastCases_castSucc] at row
      simpa only [Equiv.symm_apply_apply] using
        row.trans (transpose_trailingRows lane 142080 x i r).symm
    apply castPayload size
    simpa only [cell,Function.Embedding.trans_apply,show moveReturnPorts 0 = Fin.succ 0 by rfl] using out
  · have charge : tapeCharge cleanupWeight ((List.finRange 3).map (moveReturnPorts.trans bank)) S = 2*(m*142080)+12 := by
      change cleanupWeight (S.L (bank (Fin.succ 0))) (S.R (bank (Fin.succ 0))) +
        (cleanupWeight (S.L (bank (mergeInnerPort 0).succ)) (S.R (bank (mergeInnerPort 0).succ)) +
        (cleanupWeight (S.L (bank (mergeInnerPort 1).succ)) (S.R (bank (mergeInnerPort 1).succ)) + 0)) = _
      rw [source,empty _ (show (mergeInnerPort 0).succ ≠ Fin.succ 0 by decide),
        empty _ (show (mergeInnerPort 1).succ ≠ Fin.succ 0 by decide)]
      simp [cleanupWeight,left]
    rw [charge] at bill
    rw [← size]
    dsimp only [intervalSplitTapes] at bill
    omega

theorem scheduledMoveSpectators (child : Descriptor) (atom : ℕ) (groups : 142080 ∣ child.rows) :
    let W := CopyChildLayout.spectators child / 142080
    CopyChildLayout.spectators (packedDescriptor (64*atom) (W*142080)) = CopyChildLayout.spectators child := by
  intro W
  obtain ⟨g,rows⟩ := groups
  have divides : 142080 ∣ CopyChildLayout.spectators child :=
    ⟨child.beforeRows*g*child.beforeH*child.between*child.afterD,by
      rw [CopyChildLayout.spectators,rows]; ring⟩
  simpa only [W,CopyChildLayout.spectators,packedDescriptor,one_mul] using Nat.div_mul_cancel divides

/-- Execute a scheduled MOVE in the descriptor's own coordinate order.
Packing and unpacking here name physical addresses; the program is the
same uniform split, recursive call, and merge. -/
theorem scheduledPackedMove {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U) (entry : P)
    (bank : Fin (intervalSplitTapes+1) ↪ Fin T) (tmp buf : Fin T)
    (tmpOff : ∀ i, bank i ≠ tmp) (bufOff : ∀ i, bank i ≠ buf) (distinct : tmp ≠ buf)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    let fan := (withHelperPort (intervalOwners 142080)).trans bank
    ∀ dst : Fin (142081+2) ↪ Fin T,
    (∀ j i, bank (moveReturnPorts j) ≠ childReturnFan dst i) →
    ∃ code : Pr P T Q prime U, ∀ (child : Descriptor) atom price seed
      (width : child.width = 64*atom) (groups : 142080 ∣ child.rows),
      let W := CopyChildLayout.spectators child / 142080
      let lane := packedDescriptor (64*atom) W
      let m := volume prime lane
      let wide := packedDescriptor (64*atom) (W*142080)
      let size : m*142080 = volume prime wide := by simp [m,lane,wide,volume,packedDescriptor,Nat.mul_assoc]
      let layout := CopyChildLayout.changeLayout wide child width.symm (scheduledMoveSpectators child atom groups)
      let position := (CopyChildLayout.flatAddress wide).symm.trans (layout.trans (CopyChildLayout.flatAddress child))
      PackedPieceHandoffWithCharge cleanupWeight m (packedChildOutput atom m) body (body entry) fan dst seed price →
      0 < m → ∀ (x : Fin (volume prime child) → ZMod 2) u (S : Stacks T prime),
      S.R (bank (Fin.succ 0)) = List.ofFn (fun i => SparseRoleCircuit.encode (x (position (i.cast size)))) →
      (∀ i, S.L (bank i) = []) → (∀ i, i ≠ Fin.succ 0 → S.R (bank i) = []) →
      S.L tmp = [] → S.R tmp = [] → S.R buf = [] →
      (∀ j, (∀ i, fan i ≠ bank j) → seed.L (bank j) = [] ∧ seed.R (bank j) = []) →
      (∀ j, (∀ i, bank i ≠ j) → S.L j = seed.L j ∧ S.R j = seed.R j) →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        RecordPayload (bank (Fin.succ 0)) (fun _ => blank) 0
          ((Shared50RecursiveNodeRows.transpose (one_dvd child.rows) x) ∘ position) F ∧
        t ≤ price+214000000*volume prime child := by
  intro fan dst disjoint
  obtain ⟨code,run⟩ := packedMoveTranspose body entry bank tmp buf tmpOff bufOff distinct capacity dst disjoint
  refine ⟨code,?_⟩
  intro child atom price seed width groups W lane m wide size layout position worker pos x u S source left empty tl tr br localSeed outerSeed
  obtain ⟨z,F,t,exec,user,out,bill⟩ := run atom W price seed worker pos (x ∘ position) u S
    source left empty tl tr br localSeed outerSeed
  have physical : Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) (x ∘ position) =
      Shared50RecursiveNodeRows.transpose (one_dvd child.rows) x ∘ position :=
    funext (transpose_changeLayout wide child width.symm (scheduledMoveSpectators child atom groups) x)
  refine ⟨z,F,t,exec,user,?_,?_⟩
  · rw [← physical]
    exact out
  · have volumes := Fintype.card_congr position
    simp only [Fintype.card_fin] at volumes
    rw [← volumes]
    exact bill

end IntegerMultBounds.MathlibTM2.M6.BitNode
