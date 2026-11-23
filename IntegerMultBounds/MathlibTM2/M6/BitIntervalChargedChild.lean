module

public import IntegerMultBounds.MathlibTM2.M6.BitIntervalChildRun

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout

/-- Run the recursive child between interval layout passes. Owner preparation
and recursive execution jointly pay for growth on any private cleanup list. -/
theorem runIntervalPackedChildWithCharge {P U : Type} {B T N Q V w price : ℕ} {body : P → Pr P N Q prime U}
    {code src dst seed} (run : PackedPieceHandoffWithCharge cleanupWeight V (packedChildOutput w V) body code src dst seed price)
    (live : Fin (142080+2) ↪ Fin T) (payload : Fin B) :
    let H := 142082+T+N
    let caller := (Fin.natAddEmb 142082 (m := T)).trans (Fin.castAddEmb N)
    let extend := Fin.castAddEmb (n := H) (142080*B)
    let ports := intervalRecordBank (live.trans caller) payload
    ∃ (bank : Fin N ↪ Fin H) (host : Empty ⊕ P → Pr (Empty ⊕ P) (H+142080*B) Q prime U)
      (program : Pr (Empty ⊕ P) (H+142080*B) Q prime U),
    (∀ j, (∀ i : Fin 2, live (i.natAdd 142080) ≠ j) → ∀ h, bank h ≠ caller j) ∧
    ∀ (lane : Descriptor) (_width : lane.width = 64*w) (size : volume prime lane = V)
      (data : Fin 142080 → Fin (volume prime lane) → ZMod 2) u S,
      let position := packedChildPosition lane size
      HelperFan ((live.trans caller).trans extend) (fun r => data r ∘ position.symm) S →
      (∀ i : Fin 142082, let j := extend ((i.castAdd T).castAdd N)
        S.L j = [] ∧ S.R j = []) →
      (∀ i : Fin N, let j := extend (i.natAdd (142082+T))
        S.L j = seed.L i ∧ S.R j = seed.R i) →
      ∃ z F n, ∃ y : Fin 142081 → Fin V → ZMod 2, Exec host program (mk u S) n (mk z F) ∧
        (∀ js : List (Fin (H+142080*B)), js.Nodup → n+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+(142081*(8*V+10+2*V)+1+price)) ∧ z.user = u.user ∧
        ParentStageWords (fun i => dst (i.castAdd 2)) dst V y (embStk (bank.trans extend) F) ∧
        HelperFan (((childReturnFan dst).trans bank).trans extend) (fun r =>
          Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (data r) ∘ position.symm) F ∧
        (∀ r k, k ≠ payload → F.L (ports r k) = S.L (ports r k) ∧ F.R (ports r k) = S.R (ports r k)) ∧
        ∀ j, (∀ i : Fin 2, live (i.natAdd 142080) ≠ j) →
          let t := extend ((j.natAdd 142082).castAdd N)
          F.L t = S.L t ∧ F.R t = S.R t := by
  intro H caller extend ports
  obtain ⟨bank,inner,call,apart,exec⟩ := runSplitOwnersWithCharge (effect := packedChildOutput w V)
    cleanupWeight (2*V) (by intro word length; simp [cleanupWeight,length]; omega) run live
  refine ⟨bank,fun p => embProg extend id (inner p),embProg extend id call,apart,?_⟩
  intro lane width size data u S position rep empty privateTapes
  obtain ⟨z,F,n,y,ran,paid,user,words,reads,owners,keep⟩ :=
    exec _ (embDn extend u) (embStk extend S) rep empty privateTapes
  obtain ⟨v,D,lifted,_,same,view,frame⟩ := exec_emb (ι := id)
    (body' := fun p => embProg extend id (inner p)) extend.injective (fun _ => rfl) ran u rfl S rfl
  have rows : (fun r : Fin 142080 => y r.castSucc) = fun r =>
      Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (data r) ∘ position.symm := by
    funext r i
    have read := congrFun (reads r lane width size) (position.symm i)
    simpa [position,Function.comp_def] using read
  rw [← view] at paid words owners keep
  refine ⟨v,D,n,y,lifted,placedCleanup_cost_le extend S D cleanupWeight n _ frame paid,
    same.trans user,words,rows ▸ owners,?_,keep⟩
  intro r k ne
  apply frame
  intro j eq
  change finSumFinEquiv (Sum.inl j) = finSumFinEquiv _ at eq
  have impossible := finSumFinEquiv.injective eq
  simp [ne] at impossible

local notation "N" => rowSwapBlock.tapes
variable {P U : Type}

/-- The two layout passes pay for their own stack growth at a fixed rate. -/
theorem withIntervalBankWithCharge {T Q axes : ℕ} (capacity : rowSwapBlock.states ≤ Q)
    (src dst : Fin (142080+2) ↪ Fin T)
    (headers : Fin 6 ↪ Fin T) (width : Fin T)
    (separate : ∀ r : Fin 142080, ∀ i, src (r.castAdd 2) ≠ headers i)
    (widthFree : ∀ r : Fin 142080, src (r.castAdd 2) ≠ width)
    (body : P → Pr P (T+142080*(N+35)) Q prime U)
    (lo hi : ℕ) (ordered : lo ≤ hi) (fits : hi ≤ axes) :
    let extend := Fin.castAddEmb (142080*(N+35)) (n := T)
    let small := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
    let ports := intervalRecordBank src (small 24)
    ∃ (enter leave : Pr P (T+142080*(N+35)) Q prime U) (rate : ℕ),
    ∀ w W, 0 < W →
      let M := prime^(w+1)
      let size := intervalChild_volume ordered fits (w+1) W
      let position := packedChildPosition _ size
      ∀ (input output : Fin 142080 → Fin (volume prime (phaseIntervalChild lo hi (w+1) W axes)) → ZMod 2)
        (child : Pr P (T+142080*(N+35)) Q prime U) (price : ℕ) (preserved : Fin T → Prop) u S,
      (∀ j, preserved j → ∀ r : Fin 142080, src (r.castAdd 2) ≠ j ∧ dst (r.castAdd 2) ≠ j) →
      IntervalHeaderInputs (headers.trans extend) (extend width) w W S →
      HelperFan (src.trans extend) (fun r i => input r (i.cast size.symm)) S →
      (∀ r k, k ≠ small 24 → S.L (ports r k) = [] ∧ S.R (ports r k) = []) →
      (∀ v D, HelperFan (src.trans extend) (fun r => input r ∘ position.symm) D →
        (∀ j, (∀ r k, ports r k ≠ j) → D.L j = S.L j ∧ D.R j = S.R j) →
        ∃ z F n, Exec body child (mk v D) n (mk z F) ∧ (∀ js : List _, js.Nodup → n+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js D+price) ∧ z.user = v.user ∧
          HelperFan (dst.trans extend) (fun r => output r ∘ position.symm) F ∧
          (∀ r k, k ≠ small 24 → F.L (ports r k) = D.L (ports r k) ∧ F.R (ports r k) = D.R (ports r k)) ∧
          ∀ j, preserved j → F.L (extend j) = D.L (extend j) ∧ F.R (extend j) = D.R (extend j)) →
      ∃ z F n, Exec body ((enter.seq child).seq leave) (mk u S) n (mk z F) ∧
        (∀ js : List _, js.Nodup → n+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+rate*(((List.finRange 142080).map (fun _ =>
          (16*M.size+8*W.size+6*(w+1)+11*(w+1).size+58)+intervalPassTime U lo hi w W axes)).sum+1
          + (((List.finRange 142080).map (fun _ => intervalPassTime U lo hi w W axes)).sum+1))+price) ∧
        z.user = u.user ∧ HelperFan (dst.trans extend) (fun r i => output r (i.cast size.symm)) F ∧
        ∀ j, preserved j → F.L (extend j) = S.L (extend j) ∧ F.R (extend j) = S.R (extend j) := by
  intro extend small ports
  have pack := initializePackBank_exec capacity ports
    (fun _ _ ne => intervalRecordBank_apart src _ ne) (headers.trans extend) (extend width)
    (fun r i k => (intervalRecordBank_outside src _ _ (fun s => separate s i) r k).symm)
    (fun r k => (intervalRecordBank_outside src _ _ widthFree r k).symm) (P := Empty) (U := U) Empty.elim lo hi ordered fits
  have unpack := placedIntervalPass_exec capacity dst (P := Empty) (U := U) Empty.elim lo hi ordered fits true
  let schedule := intervalPackSchedule lo (hi-lo) (axes-hi+lo)
  let enter : Fin 142080 → Pr Empty (T+142080*(N+35)) Q prime U := fun r => (copyRecordSetup (headers.trans extend) (small.trans (ports r)) (extend width)).seq
    (statePlacedNormalized (ports r) capacity swapStates_pos Empty.elim (packSchedule (axes+axes) schedule))
  let leave : Fin 142080 → Pr Empty (T+142080*(N+35)) Q prime U := fun r => statePlacedNormalized (intervalRecordBank dst (small 24) r) capacity
    swapStates_pos Empty.elim (packSchedule (axes+axes) schedule.reverse)
  let packCode := Prog.seqList ((List.finRange 142080).map enter)
  let unpackCode := Prog.seqList ((List.finRange 142080).map leave)
  let push := max (Fast.Main.mnProgPush packCode) (Fast.Main.mnProgPush unpackCode)
  refine ⟨embProg id Empty.elim packCode,embProg id Empty.elim unpackCode,1+6*push,?_⟩
  intro w W hW M size position input output child price preserved u S off dimensions live free call
  obtain ⟨v,D,t,entry,first,user,packed,records,keep⟩ :=
    pack w W hW u S input (src.trans extend) (intervalRecordBank_payload src _)
      (fun j r k => intervalRecordBank_outside src _ _ (fun i => src.injective.ne (by
        intro eq
        have h := congrArg Fin.val eq
        change i.val = 142080+j.val at h
        omega)) r k) dimensions live free
  obtain ⟨z,F,n,ran,paid,same,returned,frame,childKeep⟩ := call v D packed keep
  obtain ⟨y,G,m,exit,last,after,owners,_,leaveKeep⟩ := unpack w W hW z F (fun _ => [])
    (fun _ _ => blank) (fun _ => 0) output returned (fun r => by
      refine ⟨_,F,intervalReturnedRecord (axes := axes) src dst r D F _ _ (records r) returned (frame r),?_⟩
      exact fun _ _ => ⟨rfl,rfl⟩)
  have project (a : HS (T+142080*(N+35)) Q prime U) : embDn id a = a := by
    cases a with
    | mk flag sym st scan nxt user => cases nxt <;> rfl
  obtain ⟨v',D',entry',state,_,view,_⟩ := exec_emb (e := id) (ι := Empty.elim) (body' := body)
    Function.injective_id (fun f => nomatch f) entry u (project u) S rfl
  rw [project] at state
  change D' = D at view
  subst v' D'
  obtain ⟨y',G',exit',state,_,view,_⟩ := exec_emb (e := id) (ι := Empty.elim) (body' := body)
    Function.injective_id (fun f => nomatch f) exit z (project z) F rfl
  rw [project] at state
  change G' = G at view
  subst y' G'
  refine ⟨y,G,t+n+m,(entry'.seq ran).seq exit',?_,after.trans (same.trans user),owners,?_⟩
  · intro js unique
    have entryGrowth := recordCleanup_cost_le js unique entry (c := push) (Nat.le_max_left ..) (fun f => nomatch f)
    have exitGrowth := recordCleanup_cost_le js unique exit (c := push) (Nat.le_max_right ..) (fun f => nomatch f)
    change tapeCharge cleanupWeight js D+1 ≤ tapeCharge cleanupWeight js S+1+6*(push*t) at entryGrowth
    change tapeCharge cleanupWeight js G+1 ≤ tapeCharge cleanupWeight js F+1+6*(push*m) at exitGrowth
    have localCost := Nat.mul_le_mul_left (1+6*push) (Nat.add_le_add first last)
    have childCost := paid js unique
    linarith only [entryGrowth,exitGrowth,localCost,childCost]
  · intro j hj
    have before := keep (extend j) (intervalRecordBank_outside src _ j (fun r => (off j hj r).1))
    have middle := childKeep j hj
    have afterCall := leaveKeep j (fun r => (off j hj r).2)
    exact ⟨afterCall.1.trans (middle.1.trans before.1),afterCall.2.trans (middle.2.trans before.2)⟩

theorem runIntervalChildWithCharge {P U : Type} {T B Q w W atom price lo hi axes : ℕ}
    (capacity : rowSwapBlock.states ≤ Q) (ordered : lo ≤ hi) (fits : hi ≤ axes) (positive : 0 < W)
    (widthAt : (phaseIntervalChild lo hi (w+1) W axes).width = 64*atom)
    {body : P → Pr P B Q prime U} {code src dst seed}
    (child : PackedPieceHandoffWithCharge cleanupWeight ((prime^(w+1))^(axes+axes)*W) (packedChildOutput atom _) body code src dst seed price)
    (live : Fin (142080+2) ↪ Fin T) (headers : Fin 6 ↪ Fin T) (width : Fin T)
    (apart : ∀ r : Fin 142080, ∀ i, live (r.castAdd 2) ≠ headers i)
    (widthFree : ∀ r : Fin 142080, live (r.castAdd 2) ≠ width) :
    let H := 142082+T+B
    let caller := (Fin.natAddEmb 142082 (m := T)).trans (Fin.castAddEmb B)
    let extend := Fin.castAddEmb (n := H) (142080*(N+35))
    let small := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
    let ports := intervalRecordBank (live.trans caller) (small 24)
    let lane := phaseIntervalChild lo hi (w+1) W axes
    let size := intervalChild_volume ordered fits (w+1) W
    ∃ (host : Empty ⊕ P → Pr (Empty ⊕ P) (H+142080*(N+35)) Q prime U)
      (program : Pr (Empty ⊕ P) (H+142080*(N+35)) Q prime U)
      (returned : Fin (142080+2) ↪ Fin H) (rate : ℕ),
    (∀ j, (∀ i, live i ≠ j) → ∀ r, returned r ≠ caller j) ∧
    ∀ (input : Fin 142080 → Fin (volume prime lane) → ZMod 2) u S,
      IntervalHeaderInputs ((headers.trans caller).trans extend) (extend (caller width)) w W S →
      HelperFan ((live.trans caller).trans extend) (fun r i => input r (i.cast size.symm)) S →
      (∀ r k, k ≠ small 24 → S.L (ports r k) = [] ∧ S.R (ports r k) = []) →
      (∀ i : Fin 142082, let j := extend ((i.castAdd T).castAdd B)
        S.L j = [] ∧ S.R j = []) →
      (∀ i : Fin B, let j := extend (i.natAdd (142082+T))
        S.L j = seed.L i ∧ S.R j = seed.R i) →
      ∃ z F n, Exec host program (mk u S) n (mk z F) ∧
        (∀ js : List _, js.Nodup →
          let M := prime^(w+1)
          let V := M^(axes+axes)*W
          let pass := intervalPassTime U lo hi w W axes
          let header := 16*M.size+8*W.size+6*(w+1)+11*(w+1).size+58
          n+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+
            rate*(142080*(header+pass)+1+(142080*pass+1))+(142081*(8*V+10+2*V)+1+price)) ∧
        z.user = u.user ∧ HelperFan (returned.trans extend)
          (fun r i => Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (input r) (i.cast size.symm)) F ∧
        ∀ j, (∀ i, live i ≠ j) → F.L (extend (caller j)) = S.L (extend (caller j)) ∧
          F.R (extend (caller j)) = S.R (extend (caller j)) := by
  intro H caller extend small ports lane size
  obtain ⟨bank,host,call,disjoint,run⟩ := runIntervalPackedChildWithCharge child live (small 24)
  let returned := (childReturnFan dst).trans bank
  obtain ⟨enter,leave,rate,passes⟩ := withIntervalBankWithCharge capacity (live.trans caller) returned
    (headers.trans caller) (caller width) (fun r i => caller.injective.ne (apart r i))
    (fun r => caller.injective.ne (widthFree r)) host lo hi ordered fits
  let M := prime^(w+1)
  let V := M^(axes+axes)*W
  have away j (outside : ∀ i, live i ≠ j) (r) : returned r ≠ caller j :=
    disjoint j (fun i => outside _) _
  refine ⟨host,(enter.seq call).seq leave,returned,rate,away,?_⟩
  intro input u S dimensions owners free fresh prepared
  let output := fun r => Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (input r)
  obtain ⟨z,F,n,exec,paid,user,rows,frame⟩ := passes w W positive input output call
    (142081*(8*V+10+2*V)+1+price) (fun k => ∃ j, k = caller j ∧ ∀ i, live i ≠ j) u S (by
      rintro _ ⟨j,rfl,outside⟩ r
      exact ⟨caller.injective.ne (outside _),away j outside _⟩) dimensions owners free (by
      intro v D packed keep
      have untouched (j : Fin H) (outside : ∀ r : Fin 142080, caller (live (r.castAdd 2)) ≠ j) :=
        keep (extend j) (intervalRecordBank_outside (live.trans caller) _ j outside)
      obtain ⟨y,G,t,_,ran,bill,same,_,words,privateTapes,childFrame⟩ := run lane widthAt size input v D packed (fun i => by
          have frame := untouched ((i.castAdd T).castAdd B) (fun r eq => by
            have h := congrArg Fin.val eq
            change 142082+(live (r.castAdd 2)).val = i.val at h
            omega)
          exact ⟨frame.1.trans (fresh i).1,frame.2.trans (fresh i).2⟩) (fun i => by
          have frame := untouched (i.natAdd (142082+T)) (fun r eq => by
            have h := congrArg Fin.val eq
            change 142082+(live (r.castAdd 2)).val = 142082+T+i.val at h
            omega)
          exact ⟨frame.1.trans (prepared i).1,frame.2.trans (prepared i).2⟩)
      refine ⟨y,G,t,ran,bill,same,words,privateTapes,?_⟩
      rintro _ ⟨j,rfl,outside⟩
      exact childFrame j (fun i => outside _))
  refine ⟨z,F,n,exec,?_,user,rows,fun j outside => frame _ ⟨j,rfl,outside⟩⟩
  intro js unique
  simpa only [List.map_const',List.length_finRange,List.sum_replicate_nat] using paid js unique

end IntegerMultBounds.MathlibTM2.M6.BitNode
