module

public import IntegerMultBounds.MathlibTM2.M6.BitMixedIdleCost

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover.Fallback Stack Host
open RecursiveInterchangeLayout
open Shared50ModularControl (prime)

private theorem transposeRead {child wide interval : Descriptor} {m : ℕ}
    (position : Fin (volume prime child) ≃ Fin m) (size : volume prime wide = m)
    (same : wide = interval) (span : volume prime interval = m)
    (coords : InheritedIntervalPositions child interval span position) (width : wide.width = child.width)
    (x : Fin (volume prime wide) → ZMod 2) :
    ∀ k, Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) x ((position k).cast size.symm) =
      Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (fun j => x ((position j).cast size.symm)) k := by
  subst interval
  exact (coords.transpose_iff width (fun k => x (k.cast size.symm))
    (fun k => Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) x (k.cast size.symm))).2
    (by simp only [Fin.cast_cast,Fin.cast_eq_self])

private theorem copyIntervalRead {child : Descriptor} {w W : ℕ}
    (width : child.width = 7*w)
    (position : Fin (volume prime child) ≃ Fin ((prime^w)^16*(W*142080)))
    (coords : CopyIntervalPositions child w (W*142080) position) :
    let lane := phaseIntervalChild 0 7 w W
    let wide := {lane with afterD := lane.afterD*142080}
    ∀ (size : volume prime wide = (prime^w)^16*(W*142080)) (x : Fin (volume prime wide) → ZMod 2) k,
      Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) x ((position k).cast size.symm) =
        Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (fun j => x ((position j).cast size.symm)) k := by
  intro lane wide size x
  have shape : wide = phaseIntervalChild 0 7 w (W*142080) := by
    simp only [wide,lane,phaseIntervalChild,Nat.mul_assoc]
  exact transposeRead position size shape _ coords (by simpa only [wide,lane,phaseIntervalChild] using width.symm) x

/-- Run a recursive COPY in the inherited lane order. The only work around
the child is a cyclic split and merge, both linear in the physical volume. -/
theorem inheritedActiveCopyWorker {P U : Type} {Q N price w W : ℕ} (child : Descriptor)
    (width : child.width = 7*w) (live : 0 < W)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    {body : P → Pr P N Q prime U} {code src dst seed} :
    let lane := phaseIntervalChild 0 7 w W
    let m := (prime^w)^16*(W*142080)
    ∀ (position : Fin (volume prime child) ≃ Fin m), CopyIntervalPositions child w (W*142080) position →
    PackedPieceHandoff (volume prime lane) (fun x y => ∀ r : Fin 142080,
      y r.castSucc = Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (x r.castSucc))
      body code src dst seed price →
    ∃ (H : ℕ) (slot : Fin H) (host : Empty ⊕ P → Pr (Empty ⊕ P) H Q prime U)
      (program : Pr (Empty ⊕ P) H Q prime U) (stock : Stacks H prime),
    ∀ (x : Fin m → ZMod 2) u (S : Stacks H prime), S.L slot = [] →
      S.R slot = List.ofFn (fun k => SparseRoleCircuit.encode (x k)) →
      (∀ k, k ≠ slot → S.L k = stock.L k ∧ S.R k = stock.R k) →
      ∃ z F n y, Exec host program (mk u S) n (mk z F) ∧
        n ≤ price+(298*(intervalSplitTapes+5)+25)*m ∧ z.user = u.user ∧
        RecordPayload slot (fun _ => blank) 0 y F ∧ ∀ k, y (position k) =
          Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (x ∘ position) k := by
  intro lane m position coords worker
  let wide := {lane with afterD := lane.afterD*142080}
  have span : volume prime lane = (prime^w)^16*W := phaseIntervalChild_volume (by decide) (by decide) _ _
  have positive : 0 < volume prime lane := span ▸ Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) live
  have total : volume prime wide = volume prime lane*142080 := by simp [wide,volume,Nat.mul_assoc]
  have physical : volume prime wide = m := by rw [total,span]; exact Nat.mul_assoc _ _ _
  obtain ⟨host,program,stock,run⟩ := inheritedSeededWorker_exec lane
    (intervalRun_of_transpose lane positive capacity worker (fun x y => ∀ k, y ((position k).cast physical.symm) =
      Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (fun j => x ((position j).cast physical.symm)) k)
      (copyIntervalRead width position coords physical))
  let slot := ((0 : Fin intervalSplitTapes).natAdd 142082).castAdd N
  refine ⟨_,slot,host,program,stock,?_⟩
  apply transportWorker physical _ host program stock (fun x y => ∀ k, y (position k) =
    Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (x ∘ position) k)
  intro x u S left right fresh
  obtain ⟨z,F,n,y,exec,paid,user,payload,reads⟩ := run x u S left right fresh
  refine ⟨z,F,n,y,exec,?_,user,payload,reads⟩
  rw [← physical,total]
  change n ≤ (149*(intervalSplitTapes+5)+5)*(volume prime lane*142080)+24+
    ((142081*(8*volume prime lane+10)+1+price)+(149*(volume prime lane*142080)*(intervalSplitTapes+5)+6)) at paid
  norm_num [intervalSplitTapes] at paid ⊢
  omega

theorem copyLaneVolume {atom w : ℕ} (aligned : 7*w = 64*atom) (W : ℕ) :
    (prime^atom)^128*((prime^w)^2*W) = volume prime (phaseIntervalChild 0 7 w W) := by
  rw [phaseIntervalChild_volume (by decide) (by decide),← Nat.mul_assoc,
    ← pow_mul,← pow_mul,← pow_add,← pow_mul]
  congr 2
  omega

open Certificates.PR589.Nine in
/-- Assemble the rank-seven recursive child directly at the COPY offsets.
The two exterior atoms contribute to its spectator stock. -/
theorem assembledActiveCopy {U : Type} :
    ∃ states : ℕ, ∀ {Q atom w W : ℕ} (child : Descriptor), states ≤ Q →
    child.width = 7*w → (aligned : 7*w = 64*atom) → 0 < W →
    (let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) →
    let lane := phaseIntervalChild 0 7 w W
    let V := volume prime lane
    let spectators := (prime^w)^2*W
    let m := (prime^w)^16*(W*142080)
    ∀ (position : Fin (volume prime child) ≃ Fin m), CopyIntervalPositions child w (W*142080) position →
    let size : (prime^atom)^128*spectators = V := copyLaneVolume aligned W
    let address := fun (j : Fin spectators) s =>
      (packedChildPosition lane rfl).symm ((flatWindowEquiv atom spectators (s,j)).cast size)
    let reads := fun (piece : Piece) (x y : Fin 142081 → Fin V → ZMod 2) =>
      ∀ j, let addr := fun z => address j (windowState atom z)
        readRoles addr y = piece.run (readRoles addr x)
    ∀ (sweepCost idleCost : Fin 9 → ℕ),
    (∀ n, ∃ (P : Type) (T : ℕ) (body : P → Pr P T Q prime U), ∃ code src dst seed,
      PackedPieceHandoff V (reads (.stage n)) body code src dst seed (sweepCost n)) →
    (∀ n, ∃ (P : Type) (T : ℕ) (body : P → Pr P T Q prime U), ∃ code src dst seed,
      PackedPieceHandoff V (reads (.remainder n.val)) body code src dst seed (idleCost n)) →
    ∃ (P : Type) (H : ℕ) (slot : Fin H) (host : P → Pr (P) H Q prime U)
      (program : Pr (P) H Q prime U) (stock : Stacks H prime),
    ∀ (x : Fin m → ZMod 2) u (S : Stacks H prime), S.L slot = [] →
      S.R slot = List.ofFn (fun k => SparseRoleCircuit.encode (x k)) →
      (∀ k, k ≠ slot → S.L k = stock.L k ∧ S.R k = stock.R k) →
      ∃ z F n y, Exec host program (mk u S) n (mk z F) ∧
        n ≤ (∑ i, sweepCost i)+(∑ i, idleCost i)+3452147597090*V+(298*(intervalSplitTapes+5)+25)*m ∧ z.user = u.user ∧
        RecordPayload slot (fun _ => blank) 0 y F ∧ ∀ k, y (position k) =
          Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (x ∘ position) k := by
  obtain ⟨states,assemble⟩ := assembledInheritedNode (U := U)
  refine ⟨states,?_⟩
  intro Q atom w W child room width aligned live capacity lane V spectators m position coords size address reads sweepCost idleCost sweeps windows
  have positive : 0 < V := by
    rw [← size]
    exact Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _)
      (Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) live)
  obtain ⟨P,N,body,code,src,dst,seed,run⟩ := assemble lane room aligned size positive (Equiv.refl _)
    sweepCost idleCost sweeps windows
  have worker : PackedPieceHandoff V (fun x y => ∀ r : Fin 142080, y r.castSucc =
      Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (x r.castSucc)) body code src dst seed
      ((∑ i, sweepCost i)+(∑ i, idleCost i)+3452147597090*V) := by
    intro x u S words fresh
    obtain ⟨z,F,n,y,exec,paid,user,out,effect⟩ := run x u S words fresh
    exact ⟨z,F,n,y,exec,paid,user,out,fun r => funext (effect r)⟩
  exact ⟨Empty ⊕ P,inheritedActiveCopyWorker child width live capacity position coords worker⟩

/-- The advertised COPY tariff pays seven full-lane leaf exchanges in each
direction on every row, even before the scheduled recursive child runs. -/
theorem copyIntervalToll_leaf (U : Type) (w W : ℕ) :
    let V := volume prime (payloadView prime 16 (w+1) W)
    142080*14*M8.RevMachine.LeafCore.coreCost V (w+1) ≤ intervalChildToll U 0 7 w W 8 := by
  intro V
  let fee := M8.RevMachine.LeafCore.coreCost V (w+1)
  let swap := fun i => completeSwapTime (U := U) (P := Empty) Empty.elim 16 i (i+1) w W
    (prime^(w+1)).size W.size
  have one (i : ℕ) : fee ≤ swap i := by
    have inner : fee ≤ (3808274*V+fee)*(rowSwapBlock.tapes+5) :=
      (Nat.le_add_left fee (3808274*V)).trans (Nat.le_mul_of_pos_right _ (by omega))
    dsimp only [swap, completeSwapTime]
    change fee ≤ (_ + ((3808274*V+fee)*(rowSwapBlock.tapes+5)+6)) + _
    omega
  have bill (is : List ℕ) : is.length*fee ≤ (is.map swap).sum := by
    induction is with
    | nil => simp
    | cons i is ih =>
      simp only [List.length_cons, Nat.add_mul, one_mul, List.map_cons, List.sum_cons]
      have := one i
      omega
  have seven : (intervalPackSchedule 0 7 1).length = 7 := by
    simp [intervalPackSchedule, middleTailSchedule_length]
  have pass := bill (intervalPackSchedule 0 7 1)
  rw [seven] at pass
  change 142080*14*fee ≤ _
  unfold intervalChildToll intervalPassTime
  change _ ≤ 142080*(_+(1+(((intervalPackSchedule 0 7 1).map swap).sum+1)))+1+_+
    (142080*(1+(((intervalPackSchedule 0 7 1).map swap).sum+1))+1)
  omega

private theorem copyIntervalBill (U : Type) :
    ∃ C : ℝ, 0 < C ∧ ∀ w W price n : ℕ, 0 < W →
      let V := (prime^(w+1))^16*W
      n ≤ (149*(intervalSplitTapes+5)+5)*(V*142080)+24 + ((21*(w+1)+13) +
        (intervalChildToll U 0 7 w W 8 + price + (149*(V*142080)*(intervalSplitTapes+5)+6))) →
      (n : ℝ) ≤ price+C*V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau := by
  obtain ⟨a,b,toll⟩ := intervalChildToll_fixed_le U 0 7 8 (by decide)
  let fixed := (298*(intervalSplitTapes+5)+5)*142080+64
  obtain ⟨C,pos,bound⟩ := copyReturn_parentCost (a+fixed) b
  refine ⟨C,pos,?_⟩
  intro w W price n hW V paid
  have volumeBound : w+1 ≤ V := (Nat.lt_pow_self Shared50ModularControl.prime_prime.one_lt).le.trans
    ((Nat.le_self_pow (by decide : 16 ≠ 0) _).trans (Nat.le_mul_of_pos_right _ hW))
  have fee := toll w W hW
  change _ ≤ (a+b*swapVolumeRate w)*V at fee
  apply bound
  rw [show a+fixed+b*swapVolumeRate w = (a+b*swapVolumeRate w)+fixed by omega,Nat.add_mul]
  dsimp only [fixed]
  norm_num [intervalSplitTapes] at paid ⊢
  omega

/-- Run the rank-seven COPY on a prepared bank using the scheduled recursive
child. Split, pack, execute, unpack and merge at the caller's COPY positions. -/
theorem activeCopyWorker (U : Type) :
    ∃ C : ℝ, 0 < C ∧ ∀ {Q price : ℕ} (child : Descriptor) (w W : ℕ),
    child.width = 7*(w+1) → 0 < W → 142080 ∣ W → rowSwapBlock.states ≤ Q →
    (let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q) →
    ∀ (position : Fin (volume prime child) ≃ Fin ((prime^(w+1))^16*W)),
    CopyIntervalPositions child (w+1) W position → PackedDescriptorHandoff U Q child price →
    let V := volume prime child / 142080
    let m := (prime^(w+1))^16*W
    ∃ (P : Type) (H : ℕ) (slot : Fin H) (host : P → Pr P H Q prime U)
      (program : Pr P H Q prime U) (stock : Stacks H prime),
    ∀ (x : Fin m → ZMod 2) u (S : Stacks H prime), S.L slot = [] →
      S.R slot = List.ofFn (fun k => SparseRoleCircuit.encode (x k)) →
      (∀ k, k ≠ slot → S.L k = stock.L k ∧ S.R k = stock.R k) →
      ∃ z F n y, Exec host program (mk u S) n (mk z F) ∧
        n ≤ ⌊(price : ℝ)+C*V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau⌋₊ ∧
        z.user = u.user ∧ RecordPayload slot (fun _ => blank) 0 y F ∧
          ∀ k, y (position k) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (x ∘ position) k := by
  obtain ⟨C,pos,bound⟩ := copyIntervalBill U
  refine ⟨C,pos,?_⟩
  intro Q price child w W width live stock capacity mergeCap
  obtain ⟨suffix,rfl⟩ := stock
  rw [Nat.mul_comm 142080 suffix] at live ⊢
  have positive := Nat.pos_of_mul_pos_right live
  intro position coords recursive V m
  obtain ⟨aligned,call⟩ := recursive
  have count := Fintype.card_congr position
  simp only [Fintype.card_fin,← Nat.mul_assoc] at count
  have perRow : volume prime child / 142080 = (prime^(w+1))^16*suffix := by rw [count,Nat.mul_div_cancel _ (by decide)]
  rw [perRow] at call
  obtain ⟨P,B,body,code,src,dst,seed,worker⟩ := call
  let lane := phaseIntervalChild 0 7 (w+1) suffix 8
  have widthAt : lane.width = 64*(child.width/64) := by
    rw [Nat.mul_div_cancel' aligned,width]; rfl
  obtain ⟨H,host,program,bank,stock,run⟩ := packedInterval_exec capacity mergeCap (by decide : 0 ≤ 7)
    (by decide : 7 ≤ 8) positive widthAt worker
  refine ⟨_,H,bank 0,host,program,stock,?_⟩
  let wide := {lane with afterD := lane.afterD*142080}
  have size : volume prime lane = (prime^(w+1))^16*suffix := phaseIntervalChild_volume (by decide) (by decide) _ _
  have interleave : volume prime lane*142080 = volume prime wide := by simp [wide,volume,Nat.mul_assoc]
  have physical : volume prime wide = m := by rw [← interleave,size]; exact Nat.mul_assoc _ _ _
  apply transportWorker physical _ host program stock (fun x y => ∀ k, y (position k) =
    Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (x ∘ position) k)
  intro x u S left right ready
  obtain ⟨z,F,n,exec,paid,user,result⟩ := run x u S left
    (right.trans (castWord interleave (fun k => SparseRoleCircuit.encode (x k))).symm) ready
  refine ⟨z,F,n,Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) x,exec,?_,user,?_,?_⟩
  · apply Nat.le_floor
    dsimp only [V]
    rw [perRow]
    apply bound w suffix price n positive
    simpa only [phaseIntervalChild_volume (by decide : 0 ≤ 7) (by decide : 7 ≤ 8)] using paid
  · exact castPayload interleave _ _ _ (mergedPayload bank F _ _ result)
  · exact copyIntervalRead width position coords physical x

end IntegerMultBounds.MathlibTM2.M6.BitNode
