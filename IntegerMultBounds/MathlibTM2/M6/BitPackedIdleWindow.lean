module

public import IntegerMultBounds.MathlibTM2.M6.BitIntervalChildMerge
public import IntegerMultBounds.MathlibTM2.M6.BitIdleWorkspace

/-! Execute packed recursive children on the scheduled idle owners. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks RecursiveInterchangeLayout
open Stack Host Cover.Fallback
open Shared50ModularControl (prime)

theorem packedIdleWorker {P U : Type} {B Q atom price : ℕ} (i : Fin 9) (j : Fin 222) (w W : ℕ)
    (positive : 0 < W) (capacity : rowSwapBlock.states ≤ Q)
    (mergeCap : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    {body : P → Pr P B Q prime U} {code src dst seed} :
    let e := idleInterval i j
    let lane := phaseIntervalChild (e.1+1) (e.2+1) (w+1) W 64
    let V := (prime^(w+1))^128*W
    let m := (prime^(w+1))^128*(W*142080)
    lane.width = 64*atom →
    PackedPieceHandoff V (packedChildOutput atom _) body code src dst seed price →
    ∃ (H : ℕ) (slot : Fin H) (host : Empty ⊕ P → Pr (Empty ⊕ P) H Q prime U)
      (program : Pr (Empty ⊕ P) H Q prime U) (stock : Stacks H prime),
    ∀ (x : Fin m → ZMod 2) u (S : Stacks H prime), S.L slot = [] →
      S.R slot = List.ofFn (fun k => SparseRoleCircuit.encode (x k)) →
      (∀ k, k ≠ slot → S.L k = stock.L k ∧ S.R k = stock.R k) →
      ∃ z F n y, Exec host program (mk u S) n (mk z F) ∧
        n ≤ (149*(intervalSplitTapes+5)+5)*(V*142080)+24 + ((21*(w+1)+13) +
          (intervalChildToll U (e.1+1) (e.2+1) w W + price + (149*(V*142080)*(intervalSplitTapes+5)+6))) ∧
        z.user = u.user ∧ RecordPayload slot (fun _ => blank) 0 y F ∧ parentIntervalRead i j (w+1) (W*142080) x y := by
  intro e lane V m width child
  have ordered := Nat.succ_le_succ (idleBounds i j).1
  have fits := Nat.succ_le_succ (idleBounds i j).2
  obtain ⟨H,host,program,bank,stock,run⟩ := packedInterval_exec capacity mergeCap ordered fits positive width child
  refine ⟨H,bank 0,host,program,stock,?_⟩
  let wide := {lane with afterD := lane.afterD*142080}
  have size : volume prime lane = V := intervalChild_volume ordered fits (w+1) W
  have interleave : volume prime lane*142080 = volume prime wide := by simp [wide,volume,Nat.mul_assoc]
  have physical : volume prime wide = m := by rw [← interleave,size]; exact Nat.mul_assoc _ _ _
  apply transportWorker physical _ host program stock (parentIntervalRead i j (w+1) (W*142080))
  intro x u S left right ready
  obtain ⟨z,F,n,exec,paid,user,result⟩ := run x u S left
    (right.trans (castWord interleave (fun k => SparseRoleCircuit.encode (x k))).symm) ready
  refine ⟨z,F,n,Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) x,exec,?_,user,?_,?_⟩
  · rw [← size]
    exact paid
  · exact castPayload interleave _ _ _ (mergedPayload bank F _ _ result)
  · exact idleInterleaved_read i j (w+1) W x

/-- Install one packed child per scheduled owner and return the exact words
needed by the following node stage. -/
theorem packedIdleWindow {U : Type} {Q : ℕ} (i : Fin 9) (w W : ℕ) (positive : 0 < W)
    (capacity : rowSwapBlock.states ≤ Q)
    (mergeCap : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) :
    let Job := (Fin 32 × Fin 5) × Fin 222
    let V := (prime^(w+1))^128*W
    let m := (prime^(w+1))^128*(W*142080)
    ∀ (atom price : Job → ℕ),
      (∀ k, let e := idleInterval i k.2
        (phaseIntervalChild (e.1+1) (e.2+1) (w+1) W 64).width = 64*atom k) →
      (∀ k, ∃ (P : Type) (B : ℕ) (body : P → Pr P B Q prime U), ∃ code src dst seed,
        PackedPieceHandoff V (packedChildOutput (atom k) _) body code src dst seed (price k)) →
      let charge : Job → ℕ := fun k => let e := idleInterval i k.2
        (149*(intervalSplitTapes+5)+5)*(V*142080)+24 + ((21*(w+1)+13) +
          (intervalChildToll U (e.1+1) (e.2+1) w W + price k + (149*(V*142080)*(intervalSplitTapes+5)+6)))
      ∃ (P : Type) (H : ℕ) (host : P → Pr P H Q prime U), ∃ program src dst stock,
        PackedPieceHandoff m (fun x y =>
          (∀ k, parentIntervalRead i k.2 (w+1) (W*142080) (x (idleTape i k)) (y (idleTape i k))) ∧
          ∀ j, (∀ k, j ≠ idleTape i k) → y j = x j) host program src dst stock
          ((idleCopies.map charge).sum+1+142081*(8*m+10)+1) := by
  intro Job V m atom price widths children charge
  choose P B body code src dst seed child using children
  choose H slot host program stock run using fun k : Job =>
    packedIdleWorker i k.2 w W positive capacity mergeCap (widths k) (child k)
  obtain ⟨T,fan,table,window,prepared,exec⟩ := allocatedIdleWindow_exec (V := m) i H (fun k => Empty ⊕ P k) slot host program stock
    charge (fun k => parentIntervalRead i k.2 (w+1) (W*142080)) run
  obtain ⟨out,initial,handoff⟩ := flatWordStageHandoff fan table window prepared
    (fun x y => (∀ k, parentIntervalRead i k.2 (w+1) (W*142080) (x (idleTape i k)) (y (idleTape i k))) ∧
      ∀ j, (∀ k, j ≠ idleTape i k) → y j = x j) (((idleCopies.map charge).sum+1 : ℕ) : ℝ) (by
    intro x u D words fresh
    obtain ⟨F,z,n,y,ran,paid,result⟩ := exec x D u words.helperFan
      (fun k => ⟨words.left (idleTape i k),words.right (idleTape i k)⟩) fresh
    exact ⟨z,F,n,y,ran,by exact_mod_cast paid,result⟩)
  exact ⟨_,_,_,out,_,_,initial,by simpa only [Nat.floor_natCast] using handoff⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
