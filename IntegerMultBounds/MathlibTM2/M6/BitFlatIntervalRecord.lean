module

public import IntegerMultBounds.MathlibTM2.M6.BitIntervalFlatHeaders

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Node Mult.PhaseCellToeplitz
open Shared50ModularControl (prime)
open M8.RevMachine RecursiveInterchangeLayout IntervalDescriptor

local notation "N" => rowSwapBlock.tapes

/-- Full price of one ordinary-order interval call, including private-bank cleanup. -/
noncomputable def flatIntervalCost (U : Type) (lo hi w W axes V push setupRate passRate privateCount price : ℕ) : ℕ :=
  let M := prime^(w+1)
  let pass := intervalPassTime U lo hi w W axes
  let header := 16*M.size+8*W.size+6*(w+1)+11*(w+1).size+58
  let volume := V*142080
  let entryGrowth := 2*volume+6*(push*((149*(intervalSplitTapes+5)+5)*volume+24))
  let localCost := setupRate*(6*(M.size+W.size)+27*(w+1)+44)+
          passRate*(142080*(header+pass)+1+(142080*pass+1))+
          (142081*(8*V+10+2*V)+1+price)+13*(149*volume*(intervalSplitTapes+5)+6)
  (149*(intervalSplitTapes+5)+13)*volume+34+
    (4*privateCount+entryGrowth+localCost)+18*volume+23+1136*V+2

/-- For a fixed tape bank and local program rates, all 64-axis intervals have
one pair of volume coefficients. The recursive child retains coefficient one. -/
theorem flatIntervalCost_le (U : Type) (push setupRate passRate privateCount : ℕ) :
    ∃ a b : ℕ, ∀ lo hi, lo ≤ hi → hi ≤ 64 → ∀ w W, 0 < W → ∀ price,
      let V := (prime^(w+1))^128*W
      flatIntervalCost U lo hi w W 64 V push setupRate passRate privateCount price ≤
        price+(a+b*swapVolumeRate w)*V := by
  obtain ⟨setup,swaps,bound⟩ := intervalChildToll_le U
  let tapes := intervalSplitTapes+5
  let linear := ((149*tapes+13)+2+6*push*(149*tapes+5)+13*149*tapes+18)*142080+142081*10+1136
  let fixed := 34+4*privateCount+6*push*24+142081*10+1+13*6+23+2
  let rate := setupRate+passRate
  refine ⟨linear+fixed+rate*setup,rate*swaps,?_⟩
  intro lo hi ordered fits w W hW price V
  let M := prime^(w+1)
  let pass := intervalPassTime U lo hi w W 64
  let header := 16*M.size+8*W.size+6*(w+1)+11*(w+1).size+58
  let prep := 6*(M.size+W.size)+27*(w+1)+44
  let scans := 142080*(header+pass)+1+(142080*pass+1)
  let toll := intervalChildToll U lo hi w W
  have prepBound : prep ≤ toll := by
    dsimp only [prep,toll,intervalChildToll,M]
    omega
  have scansBound : scans ≤ toll := by
    dsimp only [scans,toll,intervalChildToll,header,pass,M]
    omega
  have pos : 0 < V := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) hW
  calc
    _ = price+linear*V+fixed+(setupRate*prep+passRate*scans) := by
      unfold flatIntervalCost
      dsimp only [linear,fixed,tapes,prep,scans,header,M,pass]
      ring
    _ ≤ price+linear*V+fixed*V+rate*((setup+swaps*swapVolumeRate w)*V) := by
      have both := Nat.add_le_add (Nat.mul_le_mul_left setupRate prepBound) (Nat.mul_le_mul_left passRate scansBound)
      rw [← Nat.add_mul] at both
      exact Nat.add_le_add (Nat.add_le_add_left (Nat.le_mul_of_pos_right fixed pos) _)
        (both.trans (Nat.mul_le_mul_left rate (bound lo hi ordered fits w W hW)))
    _ = _ := by ring

/-- The cutoff tree can reserve the child's integer budget verbatim and round
only the local volume-width term. -/
theorem flatIntervalCost_cutoff (U : Type) (push setupRate passRate privateCount : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lo hi, lo ≤ hi → hi ≤ 64 → ∀ w W, 0 < W → ∀ price,
      let V := (prime^(w+1))^128*W
      flatIntervalCost U lo hi w W 64 V push setupRate passRate privateCount price ≤
        price+⌊C*V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau⌋₊ := by
  obtain ⟨a,b,bound⟩ := flatIntervalCost_le U push setupRate passRate privateCount
  obtain ⟨C,positive,scale⟩ := copyReturn_parentCost a b
  refine ⟨C,positive,?_⟩
  intro lo hi ordered fits w W pos price V
  have twice (n : ℕ) : n ≤ 0+2*n := by omega
  have localBound := scale w V 0 _ (twice ((a+b*swapVolumeRate w)*V))
  rw [Nat.cast_zero,zero_add] at localBound
  have rounded : (a+b*swapVolumeRate w)*V ≤ ⌊C*V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau⌋₊ :=
    Nat.le_floor localBound
  exact (bound lo hi ordered fits w W pos price).trans (Nat.add_le_add_left rounded price)

/-- Run a packed recursive child from an ordinary interval descriptor. Only the
right stack on the product tape is temporary; its left stack belongs to the caller. -/
theorem flatIntervalRecord {P U : Type} {B Q T w W atom lo hi axes price : ℕ}
    (capacity : rowSwapBlock.states ≤ Q)
    (mergeCap : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    (ordered : lo ≤ hi) (fits : hi ≤ axes) (positive : 0 < W)
    (width : (phaseIntervalChild lo hi (w+1) W axes).width = 64*atom)
    {body : P → Pr P B Q prime U} {code src dst seed} (slots : Fin 6 ↪ Fin B)
    (left : ∀ j, seed.L j = [])
    (unused : ∀ j, (∀ i, slots i ≠ j) → seed.R j = [])
    (headers : let lane := phaseIntervalChild lo hi (w+1) W axes
      ∀ i, seed.R (slots i) = (Routines.hdr (flatNodeDescriptor atom (CopyChildLayout.spectators lane)) i).map bitSymbol)
    (child : let V := volume prime (phaseIntervalChild lo hi (w+1) W axes)
      PackedPieceHandoffWithCharge cleanupWeight V (packedChildOutput atom V) body code src dst seed price) :
    ∀ (splitter : Fin intervalSplitTapes ↪ Fin T) (directory : Fin 72 ↪ Fin T)
    (_apart : ∀ i j, splitter i ≠ directory j) (source : Fin 72 ↪ Fin T)
    (_separate : ∀ i j, directory i ≠ source j) (_outside : ∀ i j, splitter i ≠ source j),
    let H := 142082+T+B
    let caller := (Fin.natAddEmb 142082 (m := T)).trans (Fin.castAddEmb B)
    let extend := Fin.castAddEmb (n := H) (142080*(N+35))
    let raw := (source.trans caller).trans extend
    let lane := phaseIntervalChild lo hi (w+1) W axes
    let V := volume prime lane
    let wide := {lane with afterD := lane.afterD*142080}
    let work := (List.finRange (H+142080*(N+35))).filter fun j => j ∉ (List.finRange 72).map raw
    ∃ (host : Empty ⊕ P → Pr (Empty ⊕ P) (H+142080*(N+35)) Q prime U)
      (program : Pr (Empty ⊕ P) (H+142080*(N+35)) Q prime U)
      (setupRate passRate : ℕ), ∀ (word : Fin (volume prime wide) → ZMod 2) u S,
      RecordPayload (raw 24) (fun _ => blank) 0 word S → S.L (raw 59) = [] → (∀ i : Fin 72, 59 ≤ i.val → i.val ≤ 65 → S.R (raw i) = []) →
      (∀ j, (∀ i, raw i ≠ j) → S.L j = [] ∧ S.R j = []) →
      S.R (raw 2) = binSyms (prime^(w+1)).size (prime^(w+1)) →
      S.R (raw 53) = binSyms W.size W → S.R (raw 28) = binSyms 1 1 →
      (S.R (raw 71)).length = w+1 →
      (∀ i, S.R (raw (descriptorPorts i)) = (Routines.hdr lane i).map bitSymbol) →
      let split : Pr Empty intervalSplitTapes Q prime U := intervalPrepare.seq
        (foreign (liftQ (CyclicRowNormalized.splitProgram 142080 prime) mergeCap))
      ∃ z F n, Exec host program (mk u S) n (mk z F) ∧
        CleanupBound S F n (flatIntervalCost U lo hi w W axes V (Fast.Main.mnProgPush split)
          setupRate passRate work.length price) ∧
        z.user = u.user ∧ RecordPayload (raw 24) (fun _ => blank) 0 (Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) word) F ∧
        ∀ j, j ≠ raw 24 → F.L j = S.L j ∧ F.R j = S.R j := by
  intro splitter directory apart source separate outside H caller extend raw lane V wide work
  let live := (intervalOwners 142080).trans splitter
  let initial := (splitter.trans caller).trans extend
  let regs := (directory.trans caller).trans extend
  let small := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
  let ports := intervalRecordBank (live.trans caller) (small 24)
  have mem (j) : j ∈ work ↔ ∀ i, raw i ≠ j := by simp [work,List.mem_map]
  have unique : work.Nodup := (List.nodup_finRange _).filter _
  have initialOff i k : raw k ≠ initial i := extend.injective.ne (caller.injective.ne (outside i k).symm)
  have protectedPort i : raw i ∉ work := fun h => (mem _).mp h i rfl
  have inside := (mem _).2 (initialOff 0)
  have scratch := protectedPort 65
  have away := protectedPort 24
  let count := CopyChildLayout.spectators lane
  let flat := flatNodeDescriptor atom count
  have size : volume prime flat = V := flatSpectatorVolume lane width
  have volumeEq : V = (prime^(w+1))^(axes+axes)*W := intervalChild_volume ordered fits _ _
  have handoff : PackedPieceHandoffWithCharge cleanupWeight _ (packedChildOutput atom ((prime^(w+1))^(axes+axes)*W)) body code src dst seed price := volumeEq ▸ child
  have build := seededIntervalRecord (T := T) (B := B) (Q := Q) (w := w) (W := W) (axes := axes) capacity mergeCap
    ordered fits positive width handoff slots flat size intervalFlatSources (by decide) left headers unused
    splitter directory apart source separate outside true
  obtain ⟨host,worker,bank,setupRate,passRate,_,run⟩ := build work unique inside away
  refine ⟨host,((middleRowDescriptor (intervalSpectatorPorts.trans raw)).seq worker).seq (bclear (raw 65)),setupRate,passRate,?_⟩
  intro word u S payload tl free privateBlank base suffix unit atomWord fields
    split
  let M := prime^(w+1)
  let pass := intervalPassTime U lo hi w W axes
  let header := 16*M.size+8*W.size+6*(w+1)+11*(w+1).size+58
  let total := V*142080
  let entryGrowth := 2*total+6*(Fast.Main.mnProgPush split*((149*(intervalSplitTapes+5)+5)*total+24))
  let localCost := setupRate*(6*(M.size+W.size)+27*(w+1)+44)+
          passRate*(142080*(header+pass)+1+(142080*pass+1))+
          (142081*(8*V+10+2*V)+1+price)+13*(149*total*(intervalSplitTapes+5)+6)
  obtain ⟨v,D,k,prepare,user,_,words,bill,leftSame,off⟩ := intervalFlatHeaders_exec host raw lo hi (w+1) W axes atom positive
    width u S fields free
  have rawOff (i : Fin 72) (ne : i ≠ 65) := off _ (raw.injective.ne ne)
  have rawRead : RecordPayload (raw 24) (fun _ => blank) 0 word D := by
    intro j
    simpa only [leftSame,rawOff 24 (by decide)] using payload j
  have fresh i := privateBlank _ (initialOff i)
  have dims i := privateBlank (regs i) (fun k => extend.injective.ne (caller.injective.ne (separate i k).symm))
  have portsFree r j (_ : j ≠ small 24) := privateBlank (ports r j) (fun k =>
    (intervalRecordBank_outside (live.trans caller) (small 24) (caller (source k))
      (fun i => caller.injective.ne (outside _ _)) r j).symm)
  have front (i : Fin 142082) := privateBlank (extend ((i.castAdd T).castAdd B)) (fun k =>
    extend.injective.ne (by intro eq; have h := congrArg Fin.val eq; change 142082+(source k).val = i.val at h; omega))
  have empty (i : Fin B) := privateBlank (extend (i.natAdd (142082+T))) (fun k =>
    extend.injective.ne (by intro eq; have h := congrArg Fin.val eq; change 142082+(source k).val = 142082+T+i.val at h; omega))
  obtain ⟨z,F,n,exec,paid,same,result,clean,frame⟩ := run word v D rawRead (leftSame ▸ tl)
    ((rawOff 59 (by decide)).trans (free _ (by decide) (by decide)))
    ((rawOff 60 (by decide)).trans (free _ (by decide) (by decide)))
    ((rawOff 61 (by decide)).trans (free _ (by decide) (by decide)))
    (fun i => ⟨leftSame ▸ (fresh i).1,(off _ (extend.injective.ne (caller.injective.ne (outside i 65)))).trans (fresh i).2⟩)
    ((rawOff 2 (by decide)).trans base) ((rawOff 53 (by decide)).trans suffix)
    ((rawOff 28 (by decide)).trans unit) ((congrArg List.length (rawOff 71 (by decide))).trans atomWord)
    (fun i => ⟨leftSame ▸ (dims i).1,(off _ (extend.injective.ne (caller.injective.ne (separate i 65)))).trans (dims i).2⟩)
    (fun r j ne => ⟨leftSame ▸ (portsFree r j ne).1,(off _ (intervalRecordBank_outside (live.trans caller) (small 24)
      (caller (source 65)) (fun i => caller.injective.ne (outside _ _)) r j)).trans (portsFree r j ne).2⟩)
    (fun i => ⟨leftSame ▸ (front i).1,(off _ (extend.injective.ne (by
      intro eq
      have h := congrArg Fin.val eq
      change i.val = 142082+(source 65).val at h
      omega))).trans (front i).2⟩)
    (fun i => ⟨leftSame ▸ (empty i).1,(off _ (extend.injective.ne (by
      intro eq
      have h := congrArg Fin.val eq
      change 142082+T+i.val = 142082+(source 65).val at h
      omega))).trans (empty i).2⟩) words
  have product := frame (source 65) scratch (source.injective.ne (by decide))
    (fun i => outside i 65) (fun i => separate i 65)
  have digits : D.R (raw 65) = binSyms count.size count :=
    (words 5).trans (canonicalBits_symbols count)
  have len : (F.R (raw 65)).length = count.size := by
    exact (congrArg List.length (product.2.trans digits)).trans (length_binSyms ..)
  obtain ⟨y,returned,_,clear⟩ := bclear_exec host (raw 65) z F
  let G := {F with R := Function.update F.R (raw 65) []}
  refine ⟨y,G,_,(prepare.seq exec).seq clear,?_,returned.trans (same.trans user),?_,?_⟩
  · intro js nd
    have h := paid js nd
    have inputs := bill work unique
    have seen := bill js nd
    have sizeCount : count.size ≤ count := Nat.size_le.mpr Nat.lt_two_pow_self
    have vol : count ≤ V := flatSpectators_le_volume lane
    have erased (xs : List _) : tapeCharge cleanupWeight xs G ≤ tapeCharge cleanupWeight xs F := by
      induction xs with
      | nil => rfl
      | cons j xs ih =>
        by_cases eq : j = raw 65
        · subst j; simp [tapeCharge,G,cleanupWeight] at ih ⊢; omega
        · simp [tapeCharge,G,Function.update_of_ne eq] at ih ⊢; omega
    change n+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js D+
      ((149*(intervalSplitTapes+5)+13)*total+34+
        (tapeCharge cleanupWeight work D+entryGrowth+localCost)+18*total+23+133*V+133*V) at h
    change k+tapeCharge cleanupWeight work D ≤ tapeCharge cleanupWeight work S+434*count at inputs
    change k+tapeCharge cleanupWeight js D ≤ tapeCharge cleanupWeight js S+434*count at seen
    change k+n+(2*(F.R (raw 65)).length+2)+tapeCharge cleanupWeight js G ≤ tapeCharge cleanupWeight js S+_
    have reserve (xs : List _) (hin : ∀ j ∈ xs, j ∈ work) : tapeCharge cleanupWeight xs S = 4*xs.length := by
      induction xs with
      | nil => rfl
      | cons j xs ih =>
        have blank := privateBlank j ((mem j).1 (hin _ List.mem_cons_self))
        have tail := ih (fun x hx => hin x (List.mem_cons_of_mem _ hx))
        simp [tapeCharge,cleanupWeight,blank] at tail ⊢
        omega
    rw [reserve work (fun _ h => h)] at inputs
    have := erased js
    change _ ≤ tapeCharge cleanupWeight js S+((149*(intervalSplitTapes+5)+13)*total+34+(4*work.length+entryGrowth+localCost)+18*total+23+1136*V+2)
    omega
  · simpa only [G,RecordPayload,Function.update_of_ne (raw.injective.ne (by decide : (24 : Fin 72) ≠ 65))] using result
  · intro j ne
    by_cases hj : j ∈ work
    · have diff : j ≠ raw 65 := fun eq => scratch (eq ▸ hj)
      have before := privateBlank j ((mem j).1 hj)
      simpa only [G,Function.update_of_ne diff,before.1,before.2] using clean j hj
    · obtain ⟨i,rfl⟩ : ∃ i, raw i = j := by simpa [mem,not_forall] using hj
      have keep := frame (source i) (protectedPort i) (fun eq => ne (congrArg (fun k => extend (caller k)) eq))
        (fun k => outside k i) (fun k => separate k i)
      refine ⟨keep.1.trans (congrFun leftSame _),?_⟩
      by_cases eq : i = 65
      · subst i; simp [G,free _ (by decide : 59 ≤ (65 : Fin 72).val) (by decide : (65 : Fin 72).val ≤ 65)]
      · exact (Function.update_of_ne (raw.injective.ne eq) ..).trans (keep.2.trans (off _ (raw.injective.ne eq)))

end IntegerMultBounds.MathlibTM2.M6.BitNode
