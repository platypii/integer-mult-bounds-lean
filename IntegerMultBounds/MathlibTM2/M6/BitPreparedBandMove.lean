module

public import IntegerMultBounds.MathlibTM2.M6.BitBandHeaderPorts

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine RecursiveInterchangeLayout
open Shared50ModularControl (prime)

/-- The ten temporary header tapes, including the intermediate divisor. -/
def bandWork {H : ℕ} (bank : Fin 15 ↪ Fin H) (aux : Fin 17 ↪ Fin H) :=
  ([1,2,7,9,16] : List (Fin 17)).map aux ++ ([1,2,11,12,13] : List (Fin 15)).map bank

private theorem bandSetupBound (a : ActiveBandRecord) (rank w L : ℕ)
    (shape : a.input.node.width = (w+1)*rank) (precision : L ≤ a.input.cutoff) :
    let width := a.input.node.width
    let atom := width/64
    let n := CopyChildLayout.spectators a.input.node
    let v := bandRoot width a.input.cutoff n
    (8*width.size+6)+(((18*atom+11*atom.size+17)+(47*prime^atom+15))+
      (6*(4*w+23*((w+1)*rank*42^5)+22*(30+L)+53)+1+2*v.rows.size+8000468*n))+41 ≤
      18100000000*n := by
  intro width atom n v
  have rows : 0 < a.input.node.rows := a.input.rows ▸ Nat.mul_pos (by decide) (Nat.mul_pos (by decide) a.input.positive.2.1)
  have np : 0 < n := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos a.input.positive.1 rows)
    a.input.positive.2.2.1) a.input.positive.2.2.2.1) a.input.positive.2.2.2.2
  have stock : v.rows*v.beforeH ≤ n := Nat.le_of_dvd np (bandHeaderDivisors a).2
  have label : prime^(64*width) ≤ n := (Nat.le_mul_of_pos_left v.beforeH (show 0 < v.rows from pow_pos (by decide) _)).trans stock
  have row := (Nat.le_mul_of_pos_right v.rows (show 0 < v.beforeH from pow_pos Shared50ModularControl.prime_prime.pos _)).trans stock
  have small : atom ≤ width := Nat.div_le_self ..
  have radix := (Nat.pow_le_pow_right Shared50ModularControl.prime_prime.pos (show atom ≤ 64*width by omega)).trans label
  have wide : width ≤ n := (Nat.lt_two_pow_self (n := width)).le.trans
    ((Nat.pow_le_pow_left Shared50ModularControl.prime_prime.two_le _).trans
      ((Nat.pow_le_pow_right Shared50ModularControl.prime_prime.pos (show width ≤ 64*width by omega)).trans label))
  have live : a.input.cutoff < width := a.active
  have eq : width = (w+1)*rank := shape
  have positive : 0 < rank := Nat.pos_of_mul_pos_left (eq ▸ Nat.zero_lt_of_lt live)
  have clock : w+1 ≤ width := eq ▸ Nat.le_mul_of_pos_right _ positive
  have digits (x : ℕ) : x.size ≤ x := Nat.size_le.mpr Nat.lt_two_pow_self
  rw [← eq]
  have := digits width
  have := digits atom
  have := digits v.rows
  omega

/-- Prepare the canonical headers, run the compact transpose and clear the
temporary directory. The child frame charge is measured on the incoming bank. -/
theorem preparedBandMove {U : Type} :
    let _ := BinaryRadixEqualShared.supplierNet
    ∃ states : ℕ, ∀ {Q : ℕ}, states ≤ Q → ∃ minimum leafRate : ℝ, ∀ D, minimum ≤ D →
      ∃ B : ℕ, ∀ {H : ℕ} (place : Fin B ↪ Fin H) (ports : Fin 4 ↪ Fin H)
        (cmp : Fin 10 ↪ Fin H) (bank : Fin 15 ↪ Fin H) (aux : Fin 17 ↪ Fin H)
        (rank : ℕ), rank ≤ 8 → (∀ i j, bank i ≠ aux j) → (∀ i j, cmp i ≠ aux j) →
        (∀ i j, place i ≠ ports j) → (∀ i j, place i ≠ bank j) → (∀ i j, place i ≠ aux j) →
        (∀ i, ports i ∉ bandWork bank aux) →
      ∃ (P : Type) (table : P → Pr P H Q prime U) (code : Pr P H Q prime U) (rate : ℕ),
      ∀ (a : ActiveBandRecord) (w L : ℕ), let p := a.input
      let width := p.node.width
      let n := CopyChildLayout.spectators p.node
      let lane := packedDescriptor width n
      let M := prime^(w+1)
      ∀ (x : Fin (volume prime lane) → ZMod 2) u (S : Stacks H prime),
        width = (w+1)*rank → ((w+1)*rank).size ≤ L → p.cutoff < 2^L → L ≤ p.cutoff →
        (S.R (cmp 0)).length = w → S.R (cmp 1) = binSyms L p.cutoff →
        (∀ i : Fin 10, 2 ≤ i.val → S.R (cmp i) = []) →
        S.R (bank 0) = binSyms M.size M → S.R (bank 10) = binSyms n.size n →
        (∀ i : Fin 15, i ≠ 0 → i ≠ 10 → S.R (bank i) = []) →
        S.R (aux 0) = binSyms width.size width → (∀ i : Fin 17, i ≠ 0 → S.R (aux i) = []) →
        (∀ j ∈ bandWork bank aux, S.L j = []) →
        RecordPayload (ports 0) (fun _ => blank) 0 x S →
        S.R (ports 1) = [] → S.R (ports 2) = [] → S.L (ports 3) = [] → S.R (ports 3) = [] →
        ∃ z F t, Exec table code (mk u S) t (mk z F) ∧ z.user = u.user ∧
          CleanupBound S F t (18100000000*n+(cutoffTreeBudget D leafRate p.cutoff (p.depth-p.path.length) p.node+
            rate*p.cells+1000000034*volume prime lane+
            (prime+8)*((frameSlots place).map (fun j => (S.L j).length+(S.R j).length+2)).sum)) ∧
          RecordPayload (ports 0) (fun _ => blank) 0
            (Shared50RecursiveNodeRows.transpose (v := lane) (one_dvd lane.rows) x) F ∧
          ∀ j, j ≠ ports 0 → F.L j = S.L j ∧ F.R j = S.R j := by
  intro inst
  obtain ⟨q,compile⟩ := canonicalBandMove (U := U)
  refine ⟨q,?_⟩
  intro Q enough
  obtain ⟨minCost,R,build⟩ := compile enough
  refine ⟨minCost,R,?_⟩
  intro D large
  obtain ⟨B,move⟩ := build D large
  refine ⟨B,?_⟩
  intro H place ports cmp bank aux rank fits separate away childPorts childBank childAux clearPorts
  let headers := bandHeaderPorts bank (aux ∘ bandAuxPorts)
  obtain ⟨P,table,child,rate,call⟩ := move place ports headers childPorts (by
    intro i j
    fin_cases j <;> first | apply childBank | apply childAux)
  obtain ⟨load,prepare⟩ := prepareBandHeaders_exec table cmp bank aux separate away rank fits
  let work := bandWork bank aux
  have unique : work.Nodup := List.nodup_append.mpr ⟨(by decide : ([1,2,7,9,16] : List (Fin 17)).Nodup).map aux.injective,
    (by decide : ([1,2,11,12,13] : List (Fin 15)).Nodup).map bank.injective,by
      intro j hj k hk eq
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hj
      obtain ⟨l,_,rfl⟩ := List.mem_map.mp hk
      exact separate l i eq.symm⟩
  refine ⟨P,table,load.seq (child.seq (clearWorkTapes work)),rate,?_⟩
  intro a w L p width n lane M x u S shape precision cutFits precisionBound clock cut scratch base spectators free digits vacant left payload r1 r2 l3 r3
  obtain ⟨y,A,k,loaded,user,paid,words,frame⟩ := prepare a w L u S shape precision cutFits clock cut scratch
    base spectators free digits vacant
  have kept (j : Fin H) (off : j ∉ work) := frame j (fun i hi eq => off (List.mem_append_left _
    (List.mem_map.mpr ⟨i,((by decide : ∀ i : Fin 17, i.val ∈ [1,2,7,9,16] → i ∈ [1,2,7,9,16]) i hi),eq⟩))) (fun i hi eq => off (List.mem_append_right _
    (List.mem_map.mpr ⟨i,((by decide : ∀ i : Fin 15, i.val ∈ [1,2,11,12,13] → i ∈ [1,2,11,12,13]) i hi),eq⟩)))
  have samePort i := kept (ports i) (clearPorts i)
  obtain ⟨z,E,t,exec,same,cost,out,rest⟩ := call a x y A (by
    intro i; simpa only [(samePort 0).1,(samePort 0).2] using payload i) words
    ((samePort 1).2.trans r1) ((samePort 2).2.trans r2) ((samePort 3).1.trans l3) ((samePort 3).2.trans r3)
  have frameCost : ((frameSlots place).map (fun j => (A.L j).length+(A.R j).length+2)) =
      ((frameSlots place).map (fun j => (S.L j).length+(S.R j).length+2)) := by
    apply List.map_congr_left
    intro j hj
    obtain ⟨i,rfl⟩ := (mem_frameSlots place j).mp hj
    have keep := frame (place i) (fun l _ => (childAux i l).symm) (fun l _ => (childBank i l).symm)
    rw [keep.1,keep.2]
  rw [frameCost] at cost
  obtain ⟨v,vu,erase⟩ := clearWorkTapes_exec table work unique z E
  let F := {E with L := fun j => if j ∈ work then [] else E.L j, R := fun j => if j ∈ work then [] else E.R j}
  have right (j) (hj : j ∈ work) : S.R j = [] := by
    rcases List.mem_append.mp hj with h | h <;> obtain ⟨i,mem,rfl⟩ := List.mem_map.mp h
    · exact vacant i ((by decide : ∀ i : Fin 17, i ∈ [1,2,7,9,16] → i ≠ 0) i mem)
    · obtain ⟨nz,ne⟩ := (by decide : ∀ i : Fin 15, i ∈ [1,2,11,12,13] → i ≠ 0 ∧ i ≠ 10) i mem
      exact free i nz ne
  have charge : tapeCharge cleanupWeight work S = 40 := by
    unfold tapeCharge
    have eq := List.map_congr_left (l := work) (f := fun j => cleanupWeight (S.L j) (S.R j)) (g := fun _ => 4) (fun j hj => by
      simp [cleanupWeight,left j hj,right j hj])
    rw [eq]; rfl
  refine ⟨v,F,_,loaded.seq (exec.seq erase),vu.trans (same.trans user),?_,?_,?_⟩
  · have bill := cleanupBound_clearBank work unique (paid.seq cost) (Nat.le_refl (tapeCharge cleanupWeight work E+1))
      (F := F) (fun j hj => by simp [F,hj]) (fun j => by by_cases h : j ∈ work <;> simp [F,h])
    rw [charge,Nat.add_assoc k] at bill
    intro js nd
    apply (bill js nd).trans (Nat.add_le_add_left ?_ _)
    have allowance := bandSetupBound a rank w L shape precisionBound
    dsimp only at allowance
    dsimp only [n,width,lane,p]
    omega
  · intro i
    have off : ports 0 ∉ work := clearPorts 0
    simpa [F,off] using out i
  · intro j ne
    by_cases h : j ∈ work
    · simp [F,h,left j h,right j h]
    · simpa [F,h] using And.intro ((rest j ne).1.trans (kept j h).1) ((rest j ne).2.trans (kept j h).2)

end IntegerMultBounds.MathlibTM2.M6.BitNode
