module

public import IntegerMultBounds.MathlibTM2.M6.BitStageSetupSeed

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout

private def widthBank : Fin 10 ↪ Fin 12 := ⟨![0,1,5,3,6,7,8,9,10,11],by decide⟩
private def middleBank : Fin 10 ↪ Fin 12 := ⟨![1,2,4,5,6,7,8,9,10,11],by decide⟩

/-- The child changes just the width and middle field of its parent's role.
Compute both binary words on one scratch bank. -/
theorem scheduledChildHeaders {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (r : Fin 12 ↪ Fin T) (i : Fin nodeChildren5.length) :
    let rank := nodeChildren5[i.val]
    let degree := 2*(64-rank)
    ∃ code, ∀ (c : CutoffNodeInput) u (S : Stacks T prime),
      let M := prime^(c.w+1)
      let child := scheduledChild prime c.node i
      (S.R (r 0)).length = c.w →
      S.R (r 1) = binSyms M.size M → S.R (r 2) = (Routines.hdr c.node 4).map bitSymbol →
      (∀ j : Fin 12, 3 ≤ j.val → S.R (r j) = []) →
      let F := {S with R := Function.update (Function.update S.R (r 3) ((Routines.hdr child 3).map bitSymbol)) (r 4) ((Routines.hdr child 4).map bitSymbol)}
      ∃ z t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        t ≤ 4*c.w+23*child.width+22+stagePowerTime M c.node.between degree := by
  intro rank degree
  let a := widthBank.trans r
  let b := middleBank.trans r
  let push : Pr P T Q prime U := Prog.act (.push (.rt (a 0)) (fun _ => Node.tick) .done)
  let pop : Pr P T Q prime U := Prog.act (.pop (.rt (a 0)) (fun v _ => v) .done)
  let width := ((push.seq (Node.umul rank (a 0) (a 2) (a 4))).seq pop).seq
    ((unaryBinary (a 2) (a 3) (a 4) (a 5) (a 6) (a 7) (a 8) (a 9)).seq (bclear (a 2)))
  refine ⟨width.seq (swapPrefix b degree),?_⟩
  intro c u S M child clock radix middle free F
  obtain ⟨v,n,user,paid,start⟩ := packedMoveWidth_exec body a rank c.w u S clock (fun j hj =>
    free (widthBank j) ((by decide : ∀ j : Fin 10, 2 ≤ j.val → 3 ≤ (widthBank j).val) j hj))
  have divide : c.node.width/64 = c.w+1 := by rw [c.width,Nat.mul_div_cancel_left _ (by decide)]
  have cw : child.width = (c.w+1)*rank := by
    change rank*(c.node.width/64) = _
    rw [divide,Nat.mul_comm]
  have gap : M^degree*c.node.between = child.between := by
    change (prime^(c.w+1))^(2*(64-rank))*c.node.between =
      prime^((64-rank)*(c.node.width/64))*c.node.between*prime^((64-rank)*(c.node.width/64))
    rw [divide,two_mul,pow_add,← pow_mul,Nat.mul_comm (c.w+1)]
    ring
  rw [← cw] at start paid
  let D := {S with R := Function.update S.R (r 3) (binSyms child.width.size child.width)}
  have keep (j : Fin 12) (ne : j ≠ 3) : D.R (r j) = S.R (r j) := Function.update_of_ne (r.injective.ne ne) ..
  obtain ⟨z,t,same,cost,finish⟩ := scaledPrefix_exec body b degree M.size c.node.between.size M c.node.between
    (Nat.lt_size_self _) (Nat.lt_size_self _) v D ((keep 1 (by decide)).trans radix)
    ((keep 2 (by decide)).trans (middle.trans (canonicalBits_symbols _))) (fun j lo hi => by
      obtain ⟨ne,bound⟩ := (by decide : ∀ j : Fin 10, 2 ≤ j → j < 9 → middleBank j ≠ 3 ∧ 3 ≤ (middleBank j).val) j lo hi
      exact (keep _ ne).trans (free _ bound))
  rw [gap] at finish
  refine ⟨z,n+t,?_,same.trans user,Nat.add_le_add paid cost⟩
  have hwidth : (Routines.hdr child 3).map (bitSymbol (a := prime)) = binSyms child.width.size child.width :=
    canonicalBits_symbols _
  dsimp only [F]
  rw [hwidth]
  exact start.seq finish

/-- The rank-dependent header time is uniformly linear in the stage's cells. -/
theorem scheduledChildHeaders_time (c : CutoffNodeInput) (i : Fin nodeChildren5.length) :
    let M := prime^(c.w+1)
    let rank := nodeChildren5[i.val]
    4*c.w+23*(scheduledChild prime c.node i).width+22+
      stagePowerTime M c.node.between (2*(64-rank)) ≤ 512000*c.cells := by
  intro M rank
  let b := c.node.between
  have hm : 0 < M := pow_pos Shared50ModularControl.prime_prime.pos _
  have hb : 0 < b := c.positive.2.2.2.1
  have tail : b ≤ c.idleWidth*142080 := by
    have live := Nat.mul_pos (Nat.mul_pos c.positive.1 c.positive.2.1) c.positive.2.2.1
    exact ((Nat.le_mul_of_pos_left b live).trans
      (Nat.le_mul_of_pos_right _ c.positive.2.2.2.2)).trans (Nat.le_mul_of_pos_right _ (by decide))
  have square : M^2*b ≤ c.cells := Nat.mul_le_mul (Nat.pow_le_pow_right hm (by decide : 2 ≤ 128)) tail
  have radix : M ≤ M^2 := by simpa [pow_two] using Nat.le_mul_of_pos_right M hm
  have md : M.size ≤ M := Nat.size_le.mpr Nat.lt_two_pow_self
  have bd : b.size ≤ b := Nat.size_le.mpr Nat.lt_two_pow_self
  have h := md.trans (radix.trans ((Nat.le_mul_of_pos_right _ hb).trans square))
  have k := bd.trans ((Nat.le_mul_of_pos_left _ (pow_pos hm 2)).trans square)
  have cross := (Nat.mul_le_mul (md.trans radix) bd).trans square
  have sq : M.size*M.size ≤ c.cells := (Nat.mul_le_mul md md).trans (by simpa [pow_two] using (Nat.le_mul_of_pos_right _ hb).trans square)
  have wBound : c.w+1 ≤ c.cells := (Nat.lt_pow_self Shared50ModularControl.prime_prime.one_lt).le.trans
    (radix.trans ((Nat.le_mul_of_pos_right _ hb).trans square))
  have positive : 0 < c.cells := Nat.lt_of_lt_of_le (Nat.succ_pos _) wBound
  have width : (scheduledChild prime c.node i).width ≤ 42*c.cells := by
    change rank*(c.node.width/64) ≤ _
    rw [c.width,Nat.mul_div_cancel_left _ (by decide)]
    exact Nat.mul_le_mul (nodeChildren5_bounds i).2 wBound
  have degree : 2*(64-rank) ≤ 128 := by omega
  have price : stagePowerTime M b (2*(64-rank)) ≤ 510000*c.cells := by
    unfold stagePowerTime
    grw [dimensionTime_le,degree]
    nlinarith only [h,k,cross,sq,positive]
  change _ + stagePowerTime M b _ ≤ _
  omega

/-- Four source ports come from the row-divided role. Slots three and four
hold the two canonical words produced by the rank-dependent computation. -/
def scheduledHeaderPorts {T : ℕ} (fields : Fin 6 → Fin T) (r : Fin 12 ↪ Fin T) : Fin 6 → Fin T :=
  Function.update (Function.update fields 3 (r 3)) 4 (r 4)

theorem scheduledHeaderPorts_ready {T : ℕ} (fields : Fin 6 → Fin T) (r : Fin 12 ↪ Fin T)
    (v : Descriptor) (i : Fin nodeChildren5.length) (S : Stacks T prime)
    (prior : ∀ j, j ≠ 3 → j ≠ 4 → S.R (fields j) = (Routines.hdr (role v 142080) j).map bitSymbol)
    (apart : ∀ j, j ≠ 3 → j ≠ 4 → fields j ≠ r 3 ∧ fields j ≠ r 4) :
    let child := scheduledChild prime v i
    let R := Function.update (Function.update S.R (r 3) ((Routines.hdr child 3).map bitSymbol))
      (r 4) ((Routines.hdr child 4).map bitSymbol)
    ∀ j, R (scheduledHeaderPorts fields r j) = (Routines.hdr child j).map bitSymbol := by
  intro child R j
  by_cases width : j = 3
  · subst j
    simp [scheduledHeaderPorts,R,r.injective.eq_iff]
  by_cases middle : j = 4
  · subst j
    simp [scheduledHeaderPorts,R]
  rw [scheduledHeaderPorts,Function.update_of_ne middle,Function.update_of_ne width]
  dsimp only [R]
  rw [Function.update_of_ne (apart j width middle).2,Function.update_of_ne (apart j width middle).1,
    prior j width middle]
  fin_cases j <;> first | rfl | contradiction

theorem scheduledChildVolume (c : CutoffNodeInput) (i : Fin nodeChildren5.length) :
    volume prime (scheduledChild prime c.node i) = c.cells := by
  have mass := (scheduledChild_measures prime c.node ⟨_,c.width⟩ ⟨_,c.rows⟩ i).2
  have total := c.cells_share
  omega

/-- Prepare all six child fields, charging the retained binary words on
every subset of tapes used by the cleanup potential. -/
theorem prepareScheduledHeaders {P U : Type} {T Q : ℕ} (body : P → Pr P T Q prime U)
    (r : Fin 12 ↪ Fin T) (fields : Fin 6 → Fin T) (i : Fin nodeChildren5.length)
    (apart : ∀ j, j ≠ 3 → j ≠ 4 → fields j ≠ r 3 ∧ fields j ≠ r 4) :
    ∃ code, ∀ (c : CutoffNodeInput) u (S : Stacks T prime),
      let M := prime^(c.w+1)
      let child := scheduledChild prime c.node i
      (S.R (r 0)).length = c.w → S.R (r 1) = binSyms M.size M →
      S.R (r 2) = (Routines.hdr c.node 4).map bitSymbol →
      (∀ j : Fin 12, 3 ≤ j.val → S.R (r j) = []) →
      (∀ j, j ≠ 3 → j ≠ 4 → S.R (fields j) = (Routines.hdr (role c.node 142080) j).map bitSymbol) →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F t (512008*c.cells) ∧
        (∀ j, F.R (scheduledHeaderPorts fields r j) = (Routines.hdr child j).map bitSymbol) ∧
        ∀ j, j ≠ r 3 → j ≠ r 4 → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨code,run⟩ := scheduledChildHeaders body r i
  refine ⟨code,?_⟩
  intro c u S M child clock radix middle free inherited
  obtain ⟨z,t,exec,user,paid⟩ := run c u S clock radix middle free
  let word := fun j => (Routines.hdr child j).map (bitSymbol (a := prime))
  let D := {S with R := Function.update S.R (r 3) (word 3)}
  let F := {D with R := Function.update D.R (r 4) (word 4)}
  refine ⟨z,F,t,exec,user,?_,scheduledHeaderPorts_ready fields r _ i S inherited apart,?_⟩
  · intro js nd
    have pos : 0 < c.cells := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) (Nat.mul_pos c.idlePositive (by decide))
    have mass : volume prime child = c.cells := scheduledChildVolume c i
    have size j : (word j).length ≤ 2*c.cells := by
      simpa only [word,List.length_map,mass] using RecursiveRowsNode.header_length child
        (LeafCore.positive_of_volume (mass ▸ pos)) _ (Routines.hdr_headers child) j
    have a := prependedWordCharge S (r 3) (word 3) js nd
    have b := prependedWordCharge D (r 4) (word 4) js nd
    have clear : D.R (r 4) = [] := by simp [D,r.injective.eq_iff,free]
    simp only [free 3 (by decide),List.append_nil] at a
    simp only [clear,List.append_nil] at b
    change tapeCharge cleanupWeight js D ≤ _ at a
    change tapeCharge cleanupWeight js F ≤ _ at b
    have time := paid.trans (scheduledChildHeaders_time c i)
    change t+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+512008*c.cells
    have := size 3
    have := size 4
    omega
  · intro j a b
    exact ⟨rfl,by simp [F,D,a,b]⟩

/-- On an active edge, generate the scheduled descriptor and install the
child stage's private archive on the same host. -/
theorem loadScheduledStageSeed {P U : Type} {T R H Q k : ℕ} (body : P → Pr P H Q prime U)
    (shared : Fin k ↪ Fin T) (place : Fin (80+((T+273)+R)) ↪ Fin H)
    (fields : Fin 6 → Fin H) (h : Fin 12 ↪ Fin H) (i : Fin nodeChildren5.length)
    (r : Fin 7 ↪ Fin H) (power : Fin 10 ↪ Fin H) (tmp saved : Fin H) :
    let source := scheduledHeaderPorts fields h
    let owner := ((Fin.castAddEmb 273 (n := T)).trans (Fin.castAddEmb R)).trans (Fin.natAddEmb 80)
    let archive := archiveSetupPlacement 80 T R
    let bank := archive.trans place
    let away := fun j => j ≠ h 3 ∧ j ≠ h 4
    (∀ j, j ≠ 3 → j ≠ 4 → away (fields j)) →
    (∀ j, away (place j)) → (∀ j : Fin 7, j ≠ 0 → away (r j)) →
    (∀ j : Fin 10, j ≠ 0 → away (power j)) → away tmp → away saved →
    r 0 = source 3 → power 0 = r 1 → (∀ j, r 2 ≠ power j) →
    (∀ j, outsideArchiveOutputs r power (source j)) → (∀ j, outsideArchiveOutputs r power (place j)) →
    outsideArchiveOutputs r power tmp → outsideArchiveOutputs r power saved →
    (∀ j l, bank (parentArchivePorts j) ≠ descriptorArchiveSources source r power l) →
    (∀ j, [descriptorArchiveSources source r power j,bank (parentArchivePorts j),tmp,saved].Nodup) →
    ∃ code, ∀ (c d : CutoffNodeInput), d.node = scheduledChild prime c.node i →
      ∀ (initial : Stacks T prime) u (S : Stacks H prime),
      let M := prime^(c.w+1)
      (S.R (h 0)).length = c.w → S.R (h 1) = binSyms M.size M →
      S.R (h 2) = (Routines.hdr c.node 4).map bitSymbol →
      (∀ j : Fin 12, 3 ≤ j.val → S.R (h j) = []) →
      (∀ j, j ≠ 3 → j ≠ 4 → S.R (fields j) = (Routines.hdr (role c.node 142080) j).map bitSymbol) →
      (∀ j : Fin 7, j ≠ 0 → S.R (r j) = []) → (∀ j : Fin 10, j ≠ 0 → S.R (power j) = []) →
      (∀ j, S.L (bank j) = [] ∧ S.R (bank j) = []) → S.R tmp = [] → S.R saved = [] →
      PrivateTapes shared initial (embStk (owner.trans place) S) →
      (∀ j, (∀ l, owner l ≠ j) → (∀ l, archive l ≠ j) → S.L (place j) = [] ∧ S.R (place j) = []) →
      ∃ z F t, Exec body code (mk u S) t (mk z F) ∧ z.user = u.user ∧
        CleanupBound S F t (512322*c.cells) ∧
        PrivateTapes (shared.trans owner) (stageSetupSeed R initial d) (embStk place F) ∧
        ∀ j, (∀ l, archive l ≠ j) → F.L (place j) = S.L (place j) ∧ F.R (place j) = S.R (place j) := by
  intro source owner archive bank away fieldsOff placeOff clockOff powerOff tmpOff savedOff width long short sources outputs tmpOut savedOut apart regs
  obtain ⟨first,prepare⟩ := prepareScheduledHeaders body h fields i fieldsOff
  obtain ⟨install,load⟩ := loadStageSetupSeed body shared place source r power tmp saved width long short sources outputs tmpOut savedOut apart regs
  refine ⟨first.seq install,?_⟩
  intro c d edge initial u S M clock radix middle blank inherited clocks temps free ht hs workers empty
  obtain ⟨v,D,n,start,user,paid,words,frame⟩ := prepare c u S clock radix middle blank inherited
  have keep j (off : away j) := frame j off.1 off.2
  have kept j := keep _ (placeOff j)
  obtain ⟨z,F,t,finish,same,charge,ready,last⟩ := load d initial v D (edge ▸ words)
    (fun j ne => (keep _ (clockOff j ne)).2.trans (clocks j ne))
    (fun j ne => (keep _ (powerOff j ne)).2.trans (temps j ne))
    (fun j => ⟨(kept (archive j)).1.trans (free j).1,(kept (archive j)).2.trans (free j).2⟩)
    ((keep _ tmpOff).2.trans ht) ((keep _ savedOff).2.trans hs)
    (fun j ne => ⟨(kept (owner j)).1.trans (workers j ne).1,(kept (owner j)).2.trans (workers j ne).2⟩)
    (fun j a b => ⟨(kept j).1.trans (empty j a b).1,(kept j).2.trans (empty j a b).2⟩)
  refine ⟨z,F,n+t,start.seq finish,same.trans user,?_,ready,fun j off =>
    ⟨(last j off).1.trans (kept j).1,(last j off).2.trans (kept j).2⟩⟩
  have total := paid.seq charge
  rw [edge,scheduledChildVolume,← Nat.add_mul] at total
  exact total

end IntegerMultBounds.MathlibTM2.M6.BitNode
