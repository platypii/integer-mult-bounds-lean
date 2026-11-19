module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackLeafPlacement
public import IntegerMultBounds.MathlibTM2.Cover.FallbackLeafSchedule

/-! Execute the stopped-leaf schedule on the parent's placed column. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback.Record
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
open M8 ActualAffineScaling FlatCoordinateLayout
open IntegerMultBounds.Networks.Shared50ModularControl (prime prime_prime)
variable [M8.Machine.Net] {P U : Type} {d w W Q : ℕ}
local notation "fields" => d+1
local notation "N" => rowSwapBlock.tapes+35
local notation "M" => prime^(w+1)
local instance : NeZero M := ⟨(pow_pos prime_prime.pos _).ne'⟩

/-- The control program depends only on the selected pairs and their archive indices. -/
noncomputable def placedLeafProgram {n m : ℕ} (k t : Fin n → Fin m) (read : Fin n → ℕ)
    (capacity : columnCapacity ≤ Q) (signCapacity : ∀ a, (fieldSignProgram (k a) true).1 ≤ Q) :
    let total := Fintype.card (Σ a, Fin (22+fieldSignSlots (k a)))
    Pr P (62+(N-35)+total+1) Q prime U :=
  let width := fun a => 22+fieldSignSlots (k a)
  let total := Fintype.card (Σ a, Fin (width a))
  let ports := Fin.castAddEmb (n := N+1+total) 1
  let bank := leafScheduleBank N total (Nat.le_add_left ..)
  let program := fun a =>
    let host := Fin.castAddEmb (n := N+1) (width a)
    let sign := extendSignBank columnBank (fieldSignSlots (k a))
    statePlacedNormalized ((exchangeBank (N+1) width a).trans ports) (le_refl Q)
      (lt_of_lt_of_le columnCapacity_pos capacity) Empty.elim
      (.seq (statePlacedNormalized host capacity columnCapacity_pos Empty.elim (childExchange (read a) 0 (k a) (t a)))
        (.seq (installFieldHeaders ((installerPorts _).trans sign))
          (placedFieldNeg (k a) ((signPorts _).trans sign) (signCapacity a))))
  statePlacedNormalized bank (le_refl Q) (lt_of_lt_of_le columnCapacity_pos capacity) Empty.elim
    ((List.finRange n).foldr (fun a rest => .seq (program a) rest) (.act .done))

theorem placedPackedLeaf_exec (rank : ℕ) (weight inv : Fin rank → ZMod M)
    (unit : ∀ i, weight i * inv i = 1) (H J : ℕ) (hm : M < 2^H) (hw : W < 2^J) (hW : 0 < W)
    (tail rest : List (Fin (prime+4))) (dest : ℤ → Fin 4) (q : ℤ)
    (empty : ∀ z, q ≤ z → z < q+(M^(fields+fields)*W : ℕ) → dest z = blank)
    (original : Fin (M^(fields+fields)*W) → ZMod 2) :
    let coords := (List.finRange fields).filter (fun i => i.val < rank)
    let read := fun a : Fin coords.length => (⟨(coords.get a).val,
      of_decide_eq_true (List.mem_filter.mp (coords.get_mem a)).2⟩ : Fin rank)
    let k : Fin coords.length → Fin ((fields+d)+1) := fun a => (coords.get a).castAdd fields
    let t : Fin coords.length → Fin ((fields+d)+1) := fun a => (coords.get a).rev.natAdd fields
    ∀ (capacity : columnCapacity ≤ Q) (signCapacity : ∀ a : Fin coords.length, (fieldSignProgram (n := (fields+d)+1) (k a) true).1 ≤ Q),
    let width := fun a => 22+fieldSignSlots (k a)
    let total := Fintype.card (Σ a, Fin (width a))
    let host := ((Fin.castAddEmb (n := 62) (N-35)).trans (Fin.castAddEmb total)).trans (Fin.castAddEmb 1)
    let bank := leafScheduleBank N total (Nat.le_add_left ..)
    let record := binSyms (A := prime) H (1 : ZMod M).val ++ tail
    let archive := (List.ofFn fun i => binSyms (A := prime) H (inv i).val).flatten ++ rest
    let cost := fun a => exchangeTime U (read a).val 0 (k a) (t a) (width a) w W H J
    let ready := ColumnRecordReady (leafColumn.trans host) H J record SparseRoleCircuit.encode
      (fun _ => blank) dest 0 q original
    let prog := placedLeafProgram (P := P) (U := U) k t (fun a => (read a).val) capacity signCapacity
    ∀ body v S,
      ready id S → S.R (host 56) = archive → (∀ j, 62 ≤ j.val → S.L j = [] ∧ S.R j = []) →
      ∃ z F l, z.user = v.user ∧ l ≤ 1+((List.finRange coords.length).map cost).sum+1 ∧
        Exec body prog (mk v S) l (mk z F) ∧
        ready (fun x => let y := Weighted.child rank (extendLeafWeight weight) (extendLeafWeight inv)
                          (leafFields x)
                        Fin.append (m := fields) (n := fields) y.1 y.2) F ∧
        F.R (host 56) = S.R (host 56) ∧
        ∀ h, (∀ i, bank i ≠ h) → F.L h = S.L h ∧ F.R h = S.R h := by
  intro coords read k t capacity signCapacity width total host bank record archive cost ready
  have inner := packedLeaf_exec (P := Empty) (U := U) rank weight inv unit H J hm hw hW tail rest dest q
    empty original capacity signCapacity
  unfold CorrectedScheduleRuns at inner
  extract_lets innerWidth innerTotal ports shared slots innerRecord innerWeights innerReady program innerCost at inner
  let positive := lt_of_lt_of_le columnCapacity_pos capacity
  let schedule : Pr Empty (N+1+total+1) Q prime U :=
    (List.finRange coords.length).foldr (fun a rest => .seq (program a) rest) (.act .done)
  intro prog body v S before weights free
  obtain ⟨layout,clean,stored,privateTapes⟩ := leafSchedule_ready total H J record archive _ _ dest 0 q
    original id S before weights free
  have singleton : innerRecord = record := by simp [innerRecord,record,List.ofFn_succ]
  obtain ⟨u,D,n,hu,hn,run,after,spare⟩ := inner Empty.elim (stateLiftDown positive (embDn bank v)) (embStk bank S)
    ⟨singleton.symm ▸ layout,clean,stored⟩ privateTapes
  obtain ⟨z,F,hz,placed,out,projection,frame⟩ := leafSchedule_place_exec total (le_refl Q) positive body schedule v S H J
    record _ _ dest 0 q original _ u D n run (singleton ▸ after.1)
  change n ≤ ((List.finRange coords.length).map cost).sum+1 at hn
  have reciprocal : bank (((Fin.last N).castAdd total).castAdd 1) = host 56 := by
    apply Fin.ext
    rw [show bank = leafScheduleBank N total (Nat.le_add_left ..) from rfl,leafScheduleBank_shared]
    exact leafShared_reciprocal _
  have saved := after.2.2
  rw [← projection] at saved
  change F.R (bank (((Fin.last N).castAdd total).castAdd 1)) = archive at saved
  rw [reciprocal] at saved
  exact ⟨z,F,_,hz.trans hu,by omega,placed,out,saved.trans weights.symm,frame⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback.Record
