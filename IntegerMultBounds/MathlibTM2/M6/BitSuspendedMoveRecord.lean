module

public import IntegerMultBounds.MathlibTM2.M6.BitSuspendedMove

/-! Open the scheduled MOVE record and run its installed suspended row worker. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback RecursiveInterchangeLayout
open Shared50ModularControl (prime)

theorem openedSuspendedRows {P R U : Type} {T H Q k : ℕ} (body : P → Pr P T Q prime U) (entry : P)
    (src dst : Fin (142081+2) ↪ Fin T) (ret : Fin 3 ↪ Fin T) (tmp buf : Fin T)
    (place : Fin T ↪ Fin H) (host : R → Pr R H Q prime U) (bank : Fin 35 ↪ Fin H)
    (spectator count saved aux : Fin H) (apart : ∀ i, bank i ≠ spectator) (ports : Fin k ↪ Fin H)
    (rows : SuspendedRows body entry src dst ret tmp buf place host (bank 24) count saved aux ports)
    (rank : ℕ) (work : List (Fin H)) (unique : work.Nodup)
    (separate : ∀ j ∈ work, j ≠ bank 1 ∧ j ≠ bank 24 ∧ j ≠ bank 34 ∧ j ≠ spectator)
    (covered : ∀ j, place j ∈ frameSlots ports ∨ place j ∈ work)
    (widthOff : bank 1 ∉ frameSlots ports) :
    let slots := frameSlots ports
    let Label := (Fin k × Bool) ⊕ R
    ∃ (table : Label → Pr Label H Q prime U) (code : Pr Label H Q prime U),
      (∀ f, table (.inr f) = stateMapProg id id Sum.inr (host f)) ∧
      ∀ (child : Descriptor) (atom w W L cutoff price : ℕ) seed,
      child.width = 64*atom → 142080 ∣ child.rows → child.width = (w+1)*rank →
      let m := volume prime (packedDescriptor (64*atom) (CopyChildLayout.spectators child/142080))
      PackedPieceHandoffWithCharge cleanupWeight m (packedChildOutput atom m) body (body entry) src dst seed price →
      0 < m → let V := (prime^(w+1))^16*W
      ∀ position : Fin (volume prime child) ≃ Fin V,
      (∀ i, (position i).val = (CopyChildLayout.packActive child i).val) →
      let stored := RecordReady (b := prime) (w := w) (d := 16) (W := W) bank (prime^(w+1)).size W.size
        (binSyms L cutoff) SparseRoleCircuit.encode (fun _ => blank) (fun _ => blank) 0 0
      ∀ u (S : Stacks H prime) x, stored x S →
      S.R spectator = binSyms (CopyChildLayout.spectators child).size (CopyChildLayout.spectators child) →
      (∀ j ∈ work, S.L j = [] ∧ S.R j = []) →
      let opened := {S with R := Function.update S.R (bank 1) (binSyms child.width.size child.width)}
      let D := clearSlots slots opened
      let B := embStk place D
      D.R count = [] → D.R saved = [] → D.L aux = [] → D.R aux = [] →
      B.L tmp = [] → B.R tmp = [] → B.R buf = [] →
      (∀ i, seed.L (ret i) = [] ∧ seed.R (ret i) = []) →
      (∀ j, (∀ i, src i ≠ j) → (∀ i, ret i ≠ j) → B.L j = seed.L j ∧ B.R j = seed.R j) →
      let charge := price+1000000034*V+49+4*slots.length+1+
        (prime+8)*(slots.map (fun j => (S.L j).length+(S.R j).length+2)).sum
      ∃ z F t y, Exec table code (mk u S) t (mk z F) ∧
        CleanupBound S F t (charge+4*work.length+4*w+23*child.width+16*child.width.size+37) ∧
        z.user = u.user ∧ stored y F ∧ (∀ j, j ≠ bank 24 → F.L j = S.L j ∧ F.R j = S.R j) ∧
        ∀ i, y (position i) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (x ∘ position) i := by
  intro slots Label
  obtain ⟨table,wrapper,labels,run⟩ := rows
  refine ⟨table,openedPackedMoveProgram wrapper bank rank work,labels,?_⟩
  intro child atom w W L cutoff price seed aligned groups width m handoff pos V position packed
    stored u S x ready spec free opened D B hc hs al ar tl tr br vacant stock charge
  apply openedPackedMoveCallerAt table wrapper bank spectator apart rank work unique separate child w W L cutoff
    charge position width packed u S x ready spec free
  intro v G _ _ _ payload
  let wide := packedDescriptor child.width (CopyChildLayout.spectators child)
  have size : volume prime wide = V := by
    have h := Fintype.card_congr position
    simp only [Fintype.card_fin] at h
    rw [← h]
    simp only [wide,volume,packedDescriptor,CopyChildLayout.spectators,one_mul,mul_one]
    ring
  let data := fun i : Fin (volume prime wide) => x (i.cast size)
  have castWord {a b : ℕ} (h : a = b) (f : Fin b → ZMod 2) :
      List.ofFn (fun i : Fin a => f (i.cast h)) = List.ofFn f := by subst b; rfl
  change RecordPayload (bank 24) (fun _ => blank) 0 x opened at payload
  have castPayload : RecordPayload (bank 24) (fun _ => blank) 0 data opened := by
    intro j
    simpa only [data,castWord] using payload j
  obtain ⟨z,F,t,exec,user,paid,out,frame⟩ := run child atom price seed aligned groups handoff pos data v opened
    castPayload hc hs al ar tl tr br vacant stock
  have lengths : (slots.map (fun j => (opened.L j).length+(opened.R j).length+2)) =
      slots.map (fun j => (S.L j).length+(S.R j).length+2) := by
    apply List.map_congr_left
    intro j mem
    have ne : j ≠ bank 1 := fun e => widthOff (e ▸ mem)
    simp [opened,ne]
  refine ⟨z,F,t,exec,?_,user,?_,?_⟩
  · change CleanupBound opened F t charge
    change CleanupBound opened F t (price+1000000034*volume prime wide+49+4*slots.length+1+
      (prime+8)*(slots.map (fun j => (opened.L j).length+(opened.R j).length+2)).sum) at paid
    simpa only [charge,size,lengths] using paid
  · intro j
    simpa only [castWord] using out j
  · intro j off outside
    apply frame j
    by_cases h : j ∈ slots
    · exact Or.inl h
    · exact Or.inr ⟨off,fun i eq => by subst j; exact (covered i).elim h outside⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
