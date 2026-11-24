module

public import IntegerMultBounds.MathlibTM2.M6.BitIntervalChargedChild
public import IntegerMultBounds.MathlibTM2.M6.BitInheritedReturnMerge

/-! Return a recursive packed interval to its original cyclic merge target. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (volume)
local notation "N" => rowSwapBlock.tapes

theorem castFan {c T m n : ℕ} (eq : m = n) (fan : Fin (c+2) ↪ Fin T)
    (x : Fin c → Fin m → ZMod 2) (S : Stacks T prime) :
    HelperFan fan (fun r i => x r (i.cast eq.symm)) S ↔ HelperFan fan x S := by
  subst n
  rfl

theorem placedOwners {T H A m c : ℕ} (splitter : Fin (((1+c)+2)+2) ↪ Fin T)
    (caller : Fin T ↪ Fin H) (extend : Fin H ↪ Fin A) (target : ℤ → Fin (prime+4))
    (data : Fin c → Fin m → ZMod 2) (S : Stacks A prime)
    (split : RepT (intervalOwnerBank target data) (embStk ((splitter.trans caller).trans extend) S).L
      (embStk ((splitter.trans caller).trans extend) S).R) :
    HelperFan ((((intervalOwners c).trans splitter).trans caller).trans extend) data S :=
  intervalOwners_ready target data _ split

theorem outsideReturnedMergeBank {c T : ℕ} (saved : Fin 3 ↪ Fin T) (returned : Fin (c+2) ↪ Fin T)
    (apart : ∀ i j, saved i ≠ returned j) {j : Fin T} (savedOff : ∀ i, saved i ≠ j)
    (returnedOff : ∀ i, returned i ≠ j) : ∀ i, returnedMergeBank saved returned apart i ≠ j := by
  refine Fin.addCases ?_ ?_
  · refine Fin.addCases ?_ ?_
    · refine Fin.addCases ?_ ?_
      · intro i; simpa [returnedMergeBank] using savedOff 0
      · intro i; simpa [returnedMergeBank] using returnedOff (i.castAdd 2)
    · intro i; simpa [returnedMergeBank] using savedOff i.succ
  · intro i; simpa [returnedMergeBank] using returnedOff (i.natAdd c)

theorem packedIntervalMerge {P U : Type} {T B Q w W atom price lo hi axes : ℕ}
    (capacity : rowSwapBlock.states ≤ Q)
    (mergeCap : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    (ordered : lo ≤ hi) (fits : hi ≤ axes) (positive : 0 < W)
    (widthAt : (phaseIntervalChild lo hi (w+1) W axes).width = 64*atom)
    {body : P → Pr P B Q prime U} {code src dst seed}
    (child : PackedPieceHandoff ((prime^(w+1))^(axes+axes)*W) (packedChildOutput atom _) body code src dst seed price)
    (splitter : Fin intervalSplitTapes ↪ Fin T) (headers : Fin 6 ↪ Fin T) (width : Fin T)
    (apart : ∀ r : Fin 142080, ∀ i, splitter (intervalOwners _ (r.castAdd 2)) ≠ headers i)
    (widthFree : ∀ r : Fin 142080, splitter (intervalOwners _ (r.castAdd 2)) ≠ width) :
    let live := (intervalOwners 142080).trans splitter
    let H := 142082+T+B
    let caller := (Fin.natAddEmb 142082 (m := T)).trans (Fin.castAddEmb B)
    let extend := Fin.castAddEmb (n := H) (142080*(N+35))
    let initial := (splitter.trans caller).trans extend
    let small := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
    let ports := intervalRecordBank (live.trans caller) (small 24)
    let lane := phaseIntervalChild lo hi (w+1) W axes
    let V := volume prime lane
    ∃ (host : Empty ⊕ P → Pr (Empty ⊕ P) (H+142080*(N+35)) Q prime U)
      (program : Pr (Empty ⊕ P) (H+142080*(N+35)) Q prime U)
      (bank : Fin intervalSplitTapes ↪ Fin (H+142080*(N+35))),
    bank 0 = initial 0 ∧ ∀ target (data : Fin 142080 → Fin V → ZMod 2) u S,
      RepT (intervalOwnerBank target data) (embStk initial S).L (embStk initial S).R →
      IntervalHeaderInputs ((headers.trans caller).trans extend) (extend (caller width)) w W S →
      (∀ r k, k ≠ small 24 → S.L (ports r k) = [] ∧ S.R (ports r k) = []) →
      (∀ i : Fin 142082, let j := extend ((i.castAdd T).castAdd B)
        S.L j = [] ∧ S.R j = []) →
      (∀ i : Fin B, let j := extend (i.natAdd (142082+T))
        S.L j = seed.L i ∧ S.R j = seed.R i) →
      let output := fun r => Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (data r)
      let word := fun k : Fin (V*142080) => let p := finProdFinEquiv.symm k
                                            SparseRoleCircuit.encode (a := prime) (output p.2 p.1)
      ∃ z F n, Exec host program (mk u S) n (mk z F) ∧
        n ≤ intervalChildToll U lo hi w W axes + price + (149*(V*142080)*(intervalSplitTapes+5)+6) ∧
        z.user = u.user ∧ RepT (intervalOwnerBank (putWord target 0 (List.ofFn word)) output)
          (embStk bank F).L (embStk bank F).R ∧
        ∀ j, (∀ i, splitter i ≠ j) → F.L (extend (caller j)) = S.L (extend (caller j)) ∧
          F.R (extend (caller j)) = S.R (extend (caller j)) := by
  intro live H caller extend initial small ports lane V
  obtain ⟨host,call,returned,disjoint,run⟩ :=
    runIntervalChild capacity ordered fits positive widthAt child live headers width apart widthFree
  let saved := (mergeSaved 142080).trans initial
  have outside i j : live j ≠ splitter (mergeSaved 142080 i) :=
    splitter.injective.ne (mergeSaved_outsideFan _ i j)
  have separate i j : saved i ≠ (returned.trans extend) j :=
    extend.injective.ne (disjoint _ (outside i) j).symm
  let bank := returnedMergeBank saved (returned.trans extend) separate
  refine ⟨host,call.seq (embProg bank Empty.elim (foreign (liftQ
    (CyclicRowNormalized.mergeProgram 142080 prime) mergeCap))),bank,returnedMergeBank_target _ _ _,?_⟩
  intro target data u S split dimensions free fresh prepared output word
  have size : V = (prime^(w+1))^(axes+axes)*W := intervalChild_volume ordered fits (w+1) W
  have vol : 0 < V := by
    rw [size]
    exact Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) positive
  have owners : HelperFan ((live.trans caller).trans extend) data S :=
    placedOwners (c := 142080) splitter caller extend target data S split
  obtain ⟨v,D,k,exec,paid,user,rows,frame⟩ := run data u S dimensions
    ((castFan size ((live.trans caller).trans extend) data S).2 owners) free fresh prepared
  obtain ⟨z,F,n,merged,cost,same,result,_,keep,_⟩ :=
    placedMergeReturnedOwners_exec host bank mergeCap vol target data output (embStk initial S) v D split
      (by rw [returnedMergeBank_owners]; exact (castFan size _ output D).1 rows)
      (by rw [returnedMergeBank_target]; exact frame _ (outside 0))
      (fun j => by dsimp only; rw [returnedMergeBank_inner]; exact frame _ (outside j.succ))
  refine ⟨z,F,k+n,exec.seq merged,Nat.add_le_add paid cost,same.trans user,result,?_⟩
  intro j off
  have away (i) : live i ≠ j := off _
  have savedOff (i) : saved i ≠ extend (caller j) := extend.injective.ne (caller.injective.ne (off _))
  have returnedOff (i) : (returned.trans extend) i ≠ extend (caller j) := extend.injective.ne (disjoint j away i)
  have bankOff := outsideReturnedMergeBank saved (returned.trans extend) separate savedOff returnedOff
  exact ⟨(keep _ bankOff).1.trans (frame j away).1,(keep _ bankOff).2.trans (frame j away).2⟩

theorem packedIntervalMergeWithCharge {P U : Type} {T B Q w W atom price lo hi axes : ℕ}
    (capacity : rowSwapBlock.states ≤ Q)
    (mergeCap : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    (ordered : lo ≤ hi) (fits : hi ≤ axes) (positive : 0 < W)
    (widthAt : (phaseIntervalChild lo hi (w+1) W axes).width = 64*atom)
    {body : P → Pr P B Q prime U} {code src dst seed}
    (child : PackedPieceHandoffWithCharge cleanupWeight ((prime^(w+1))^(axes+axes)*W) (packedChildOutput atom _) body code src dst seed price)
    (splitter : Fin intervalSplitTapes ↪ Fin T) (headers : Fin 6 ↪ Fin T) (width : Fin T)
    (apart : ∀ r : Fin 142080, ∀ i, splitter (intervalOwners _ (r.castAdd 2)) ≠ headers i)
    (widthFree : ∀ r : Fin 142080, splitter (intervalOwners _ (r.castAdd 2)) ≠ width) :
    let live := (intervalOwners 142080).trans splitter
    let H := 142082+T+B
    let caller := (Fin.natAddEmb 142082 (m := T)).trans (Fin.castAddEmb B)
    let extend := Fin.castAddEmb (n := H) (142080*(N+35))
    let initial := (splitter.trans caller).trans extend
    let small := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
    let ports := intervalRecordBank (live.trans caller) (small 24)
    let lane := phaseIntervalChild lo hi (w+1) W axes
    let V := volume prime lane
    ∃ (host : Empty ⊕ P → Pr (Empty ⊕ P) (H+142080*(N+35)) Q prime U)
      (program : Pr (Empty ⊕ P) (H+142080*(N+35)) Q prime U)
      (bank : Fin intervalSplitTapes ↪ Fin (H+142080*(N+35))) (rate : ℕ),
    bank 0 = initial 0 ∧ ∀ target (data : Fin 142080 → Fin V → ZMod 2) u S,
      RepT (intervalOwnerBank target data) (embStk initial S).L (embStk initial S).R →
      IntervalHeaderInputs ((headers.trans caller).trans extend) (extend (caller width)) w W S →
      (∀ r k, k ≠ small 24 → S.L (ports r k) = [] ∧ S.R (ports r k) = []) →
      (∀ i : Fin 142082, let j := extend ((i.castAdd T).castAdd B)
        S.L j = [] ∧ S.R j = []) →
      (∀ i : Fin B, let j := extend (i.natAdd (142082+T))
        S.L j = seed.L i ∧ S.R j = seed.R i) →
      let output := fun r => Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (data r)
      let word := fun k : Fin (V*142080) => let p := finProdFinEquiv.symm k
                                            SparseRoleCircuit.encode (a := prime) (output p.2 p.1)
      ∃ z F n, Exec host program (mk u S) n (mk z F) ∧
        (∀ js : List _, js.Nodup →
          let M := prime^(w+1)
          let pass := intervalPassTime U lo hi w W axes
          let header := 16*M.size+8*W.size+6*(w+1)+11*(w+1).size+58
          n+tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js S+
            rate*(142080*(header+pass)+1+(142080*pass+1))+
            (142081*(8*V+10+2*V)+1+price)+13*(149*(V*142080)*(intervalSplitTapes+5)+6)) ∧
        z.user = u.user ∧ RepT (intervalOwnerBank (putWord target 0 (List.ofFn word)) output)
          (embStk bank F).L (embStk bank F).R ∧
        ∀ j, (∀ i, splitter i ≠ j) → F.L (extend (caller j)) = S.L (extend (caller j)) ∧
          F.R (extend (caller j)) = S.R (extend (caller j)) := by
  intro live H caller extend initial small ports lane V
  obtain ⟨host,call,returned,rate,disjoint,run⟩ :=
    runIntervalChildWithCharge capacity ordered fits positive widthAt child live headers width apart widthFree
  let saved := (mergeSaved 142080).trans initial
  have outside i j : live j ≠ splitter (mergeSaved 142080 i) :=
    splitter.injective.ne (mergeSaved_outsideFan _ i j)
  have separate i j : saved i ≠ (returned.trans extend) j :=
    extend.injective.ne (disjoint _ (outside i) j).symm
  let bank := returnedMergeBank saved (returned.trans extend) separate
  refine ⟨host,call.seq (embProg bank Empty.elim (foreign (liftQ
    (CyclicRowNormalized.mergeProgram 142080 prime) mergeCap))),bank,rate,returnedMergeBank_target _ _ _,?_⟩
  intro target data u S split dimensions free fresh prepared output word
  have size : V = (prime^(w+1))^(axes+axes)*W := intervalChild_volume ordered fits (w+1) W
  have vol : 0 < V := by
    rw [size]
    exact Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) positive
  have owners : HelperFan ((live.trans caller).trans extend) data S :=
    placedOwners (c := 142080) splitter caller extend target data S split
  obtain ⟨v,D,k,exec,paid,user,rows,frame⟩ := run data u S dimensions
    ((castFan size ((live.trans caller).trans extend) data S).2 owners) free fresh prepared
  obtain ⟨z,F,n,merged,cost,same,result,_,keep,growth⟩ :=
    placedMergeReturnedOwners_exec host bank mergeCap vol target data output (embStk initial S) v D split
      (by rw [returnedMergeBank_owners]; exact (castFan size _ output D).1 rows)
      (by rw [returnedMergeBank_target]; exact frame _ (outside 0))
      (fun j => by dsimp only; rw [returnedMergeBank_inner]; exact frame _ (outside j.succ))
  refine ⟨z,F,k+n,exec.seq merged,?_,same.trans user,result,?_⟩
  · intro js unique
    have childBill := paid js unique
    dsimp only at childBill ⊢
    rw [← size] at childBill
    have mergeGrowth := growth js unique
    change tapeCharge cleanupWeight js F ≤ tapeCharge cleanupWeight js D+12*n at mergeGrowth
    omega
  · intro j off
    have away (i) : live i ≠ j := off _
    have savedOff (i) : saved i ≠ extend (caller j) := extend.injective.ne (caller.injective.ne (off _))
    have returnedOff (i) : (returned.trans extend) i ≠ extend (caller j) := extend.injective.ne (disjoint j away i)
    have bankOff := outsideReturnedMergeBank saved (returned.trans extend) separate savedOff returnedOff
    exact ⟨(keep _ bankOff).1.trans (frame j away).1,(keep _ bankOff).2.trans (frame j away).2⟩

theorem directoryIntervalMerge {P U : Type} {T B Q w W atom price lo hi axes : ℕ}
    (capacity : rowSwapBlock.states ≤ Q)
    (mergeCap : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    (ordered : lo ≤ hi) (fits : hi ≤ axes) (positive : 0 < W)
    (widthAt : (phaseIntervalChild lo hi (w+1) W axes).width = 64*atom)
    {body : P → Pr P B Q prime U} {code src dst seed}
    (child : PackedPieceHandoff ((prime^(w+1))^(axes+axes)*W) (packedChildOutput atom _) body code src dst seed price)
    (splitter : Fin intervalSplitTapes ↪ Fin T) (directory : Fin 72 ↪ Fin T)
    (apart : ∀ i j, splitter i ≠ directory j) :
    let live := (intervalOwners 142080).trans splitter
    let H := 142082+T+B
    let caller := (Fin.natAddEmb 142082 (m := T)).trans (Fin.castAddEmb B)
    let extend := Fin.castAddEmb (n := H) (142080*(N+35))
    let initial := (splitter.trans caller).trans extend
    let regs := (directory.trans caller).trans extend
    let small := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
    let ports := intervalRecordBank (live.trans caller) (small 24)
    let lane := phaseIntervalChild lo hi (w+1) W axes
    let V := volume prime lane
    ∃ (host : Empty ⊕ P → Pr (Empty ⊕ P) (H+142080*(N+35)) Q prime U)
      (program : Pr (Empty ⊕ P) (H+142080*(N+35)) Q prime U)
      (bank : Fin intervalSplitTapes ↪ Fin (H+142080*(N+35))),
    bank 0 = initial 0 ∧ ∀ target (data : Fin 142080 → Fin V → ZMod 2) u S,
      RepT (intervalOwnerBank target data) (embStk initial S).L (embStk initial S).R →
      S.R (regs 2) = binSyms (prime^(w+1)).size (prime^(w+1)) →
      S.R (regs 53) = binSyms W.size W → S.R (regs 28) = binSyms 1 1 →
      (∀ i, S.L (regs (intervalDirectoryPorts (copyRecordSources i))) = []) →
      (S.R (regs 71)).length = w+1 →
      (∀ i : Fin 72, 59 ≤ i.val → i.val ≤ 65 → S.R (regs i) = []) →
      (∀ r k, k ≠ small 24 → S.L (ports r k) = [] ∧ S.R (ports r k) = []) →
      (∀ i : Fin 142082, let j := extend ((i.castAdd T).castAdd B)
        S.L j = [] ∧ S.R j = []) →
      (∀ i : Fin B, let j := extend (i.natAdd (142082+T))
        S.L j = seed.L i ∧ S.R j = seed.R i) →
      let output := fun r => Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (data r)
      let word := fun k : Fin (V*142080) => let p := finProdFinEquiv.symm k
                                            SparseRoleCircuit.encode (a := prime) (output p.2 p.1)
      ∃ z F n, Exec host program (mk u S) n (mk z F) ∧
        n ≤ (21*(w+1)+13) + (intervalChildToll U lo hi w W axes + price + (149*(V*142080)*(intervalSplitTapes+5)+6)) ∧
        z.user = u.user ∧ RepT (intervalOwnerBank (putWord target 0 (List.ofFn word)) output)
          (embStk bank F).L (embStk bank F).R := by
  intro live H caller extend initial regs small ports lane V
  obtain ⟨host,call,bank,targetBank,merge⟩ := packedIntervalMerge capacity mergeCap ordered fits positive
    widthAt child splitter (intervalDirectoryPorts.trans directory) (directory 59)
    (fun _ _ => apart _ _) (fun _ => apart _ _)
  obtain ⟨setup,prepare⟩ := intervalDirectorySetup_exec host regs
  refine ⟨host,setup.seq call,bank,targetBank,?_⟩
  intro target data u S split base suffix unit left atom blank free fresh prepared output word
  obtain ⟨v,D,t,ran,paid,user,inputs,leftFrame,rightFrame⟩ :=
    prepare w W u S base suffix unit left atom blank
  have frame (j) (off : ∀ i, regs i ≠ j) : D.L j = S.L j ∧ D.R j = S.R j :=
    ⟨leftFrame j (fun i => off _),rightFrame j (off _)⟩
  have same i := frame (initial i) (fun j =>
    extend.injective.ne (caller.injective.ne (apart i j).symm))
  have represented : RepT (intervalOwnerBank target data) (embStk initial D).L (embStk initial D).R := by
    intro i z
    simpa only [embStk,Function.comp_apply,(same i).1,(same i).2] using split i z
  obtain ⟨z,F,n,exec,cost,result,out,_⟩ := merge target data v D represented inputs (by
    intro r k ne
    have h := frame (ports r k) (fun i => (intervalRecordBank_outside (live.trans caller) (small 24)
      (caller (directory i)) (fun r => caller.injective.ne (apart _ _)) r k).symm)
    exact ⟨h.1.trans (free r k ne).1,h.2.trans (free r k ne).2⟩) (by
    intro i
    have h := frame (extend ((i.castAdd T).castAdd B)) (fun j => extend.injective.ne (by
      intro eq
      have val := congrArg Fin.val eq
      change 142082+(directory j).val = i.val at val
      omega))
    exact ⟨h.1.trans (fresh i).1,h.2.trans (fresh i).2⟩) (by
    intro i
    have h := frame (extend (i.natAdd (142082+T))) (fun j => extend.injective.ne (by
      intro eq
      have val := congrArg Fin.val eq
      change 142082+(directory j).val = 142082+T+i.val at val
      omega))
    exact ⟨h.1.trans (prepared i).1,h.2.trans (prepared i).2⟩)
  exact ⟨z,F,t+n,ran.seq exec,Nat.add_le_add paid cost,result.trans user,out⟩

theorem allocatedIntervalMerge {P U : Type} {A B Q w W atom price lo hi axes : ℕ}
    (capacity : rowSwapBlock.states ≤ Q)
    (mergeCap : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    (ordered : lo ≤ hi) (fits : hi ≤ axes) (positive : 0 < W)
    (widthAt : (phaseIntervalChild lo hi (w+1) W axes).width = 64*atom)
    {body : P → Pr P B Q prime U} {code src dst seed}
    (child : PackedPieceHandoff ((prime^(w+1))^(axes+axes)*W) (packedChildOutput atom _) body code src dst seed price)
    (slots : Fin intervalSplitTapes ↪ Fin A) :
    let lane := phaseIntervalChild lo hi (w+1) W axes
    let V := volume prime lane
    ∃ (H : ℕ) (host : Empty ⊕ P → Pr (Empty ⊕ P) H Q prime U)
      (program : Pr (Empty ⊕ P) H Q prime U) (initial bank : Fin intervalSplitTapes ↪ Fin H)
      (stock : Stacks H prime), bank 0 = initial 0 ∧ ∀ target (data : Fin 142080 → Fin V → ZMod 2) u S,
      RepT (intervalOwnerBank target data) (embStk initial S).L (embStk initial S).R →
      (∀ j, (∀ i, initial i ≠ j) → S.L j = stock.L j ∧ S.R j = stock.R j) →
      let output := fun r => Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (data r)
      let word := fun k : Fin (V*142080) => let p := finProdFinEquiv.symm k
                                            SparseRoleCircuit.encode (a := prime) (output p.2 p.1)
      ∃ z F n, Exec host program (mk u S) n (mk z F) ∧
        n ≤ (21*(w+1)+13) + (intervalChildToll U lo hi w W axes + price + (149*(V*142080)*(intervalSplitTapes+5)+6)) ∧
        z.user = u.user ∧ RepT (intervalOwnerBank (putWord target 0 (List.ofFn word)) output)
          (embStk bank F).L (embStk bank F).R := by
  intro lane V
  let T := A+72
  let splitter := slots.trans (Fin.castAddEmb 72)
  let directory := Fin.natAddEmb A (m := 72)
  have apart i j : splitter i ≠ directory j := by
    intro eq
    have v := congrArg Fin.val eq
    change (slots i).val = A+j.val at v
    omega
  obtain ⟨host,program,bank,targetBank,run⟩ := directoryIntervalMerge capacity mergeCap ordered fits positive
    widthAt child splitter directory apart
  let caller := (Fin.natAddEmb 142082 (m := T)).trans (Fin.castAddEmb B)
  let extend := Fin.castAddEmb (n := 142082+T+B) (142080*(N+35))
  let initial := (splitter.trans caller).trans extend
  let regs := (directory.trans caller).trans extend
  let words (i : Fin 72) : List (Fin (prime+4)) :=
    if i = 2 then binSyms (prime^(w+1)).size (prime^(w+1)) else
    if i = 53 then binSyms W.size W else if i = 28 then binSyms 1 1 else
    if i = 71 then List.replicate (w+1) (bitSymbol true) else []
  let side (dir : Fin 72 → List (Fin (prime+4))) (privateWords : Fin B → List (Fin (prime+4))) :
      Fin ((142082+T+B)+142080*(N+35)) → List (Fin (prime+4)) :=
    Fin.addCases (Fin.addCases (Fin.addCases (fun _ : Fin 142082 => [])
      (Fin.addCases (fun _ : Fin A => []) dir)) privateWords)
      (fun _ : Fin (142080*(N+35)) => [])
  let stock : Stacks _ prime := ⟨[],[],side (fun _ => []) seed.L,side words seed.R⟩
  refine ⟨_,host,program,initial,bank,stock,targetBank,?_⟩
  intro target data u S split ready
  have dir i := ready (regs i) (fun j => extend.injective.ne (caller.injective.ne (apart j i)))
  have l i : S.L (regs i) = [] := by simpa [stock,regs,extend,caller,directory,side] using (dir i).1
  have r i : S.R (regs i) = words i := by simpa [stock,regs,extend,caller,directory,side] using (dir i).2
  apply run target data u S split ((r 2).trans (by simp [words])) ((r 53).trans (by simp [words]))
    ((r 28).trans (by simp [words])) (fun i => l _) (by rw [r]; simp [words])
    (fun i low high => by
      have off : i ≠ 2 ∧ i ≠ 53 ∧ i ≠ 28 ∧ i ≠ 71 := by
        exact (by decide : ∀ k : Fin 72, 59 ≤ k.val → k.val ≤ 65 → k ≠ 2 ∧ k ≠ 53 ∧ k ≠ 28 ∧ k ≠ 71) i low high
      exact (r i).trans (by simp [words,off]))
  · intro row k ne
    let fan := ((intervalOwners 142080).trans splitter).trans caller
    let p := ((Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)) 24
    have pos : intervalRecordBank fan p row k = (finProdFinEquiv (row,k)).natAdd (142082+T+B) := by
      simp [intervalRecordBank,show k ≠ p from ne]
    rw [pos]
    have frame := ready ((finProdFinEquiv (row,k)).natAdd (142082+T+B)) (fun i eq => by
      have h := congrArg Fin.val eq
      change (caller (splitter i)).val = 142082+T+B+(finProdFinEquiv (row,k)).val at h
      omega)
    simpa [stock,side] using frame
  · intro i
    have frame := ready (extend ((i.castAdd T).castAdd B)) (fun j => extend.injective.ne (by
      intro eq
      have h := congrArg Fin.val eq
      change 142082+(splitter j).val = i.val at h
      omega))
    simpa [stock,side,extend] using frame
  · intro i
    have frame := ready (extend (i.natAdd (142082+T))) (fun j => extend.injective.ne (by
      intro eq
      have h := congrArg Fin.val eq
      change 142082+(splitter j).val = 142082+T+i.val at h
      omega))
    simpa [stock,side,extend] using frame

theorem packedInterval_exec {P U : Type} {B Q w W atom price lo hi axes : ℕ}
    (capacity : rowSwapBlock.states ≤ Q)
    (mergeCap : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    (ordered : lo ≤ hi) (fits : hi ≤ axes) (positive : 0 < W)
    (widthAt : (phaseIntervalChild lo hi (w+1) W axes).width = 64*atom)
    {body : P → Pr P B Q prime U} {code src dst seed}
    (child : PackedPieceHandoff ((prime^(w+1))^(axes+axes)*W) (packedChildOutput atom _) body code src dst seed price)
    :
    let lane := phaseIntervalChild lo hi (w+1) W axes
    let V := volume prime lane
    let wide := {lane with afterD := lane.afterD*142080}
    let size : V*142080 = volume prime wide := by simp [V,wide,volume,Nat.mul_assoc]
    ∃ (H : ℕ) (host : Empty ⊕ P → Pr (Empty ⊕ P) H Q prime U) (program : Pr (Empty ⊕ P) H Q prime U)
      (bank : Fin intervalSplitTapes ↪ Fin H) (stock : Stacks H prime),
    ∀ (input : Fin (volume prime wide) → ZMod 2) u S,
      let x := fun k : Fin (V*142080) => SparseRoleCircuit.encode (a := prime) (input (k.cast size))
      S.L (bank 0) = [] → S.R (bank 0) = List.ofFn x →
      (∀ j, j ≠ bank 0 → S.L j = stock.L j ∧ S.R j = stock.R j) →
      let y := fun k : Fin (V*142080) => Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) input (k.cast size)
      let rows := fun r (i : Fin V) => y (finProdFinEquiv (i,r))
      ∃ z F n, Exec host program (mk u S) n (mk z F) ∧
        n ≤ (149*(intervalSplitTapes+5)+5)*(V*142080)+24 + ((21*(w+1)+13) +
          (intervalChildToll U lo hi w W axes + price + (149*(V*142080)*(intervalSplitTapes+5)+6))) ∧
        z.user = u.user ∧ RepT (intervalOwnerBank (putWord (fun _ => blank) 0
          (List.ofFn fun k => SparseRoleCircuit.encode (y k))) rows) (embStk bank F).L (embStk bank F).R := by
  intro lane V wide size
  obtain ⟨H,host,worker,initial,bank,seeded,target,run⟩ :=
    allocatedIntervalMerge capacity mergeCap ordered fits positive widthAt child (Function.Embedding.refl _)
  classical
  let clear := fun (f : Fin H → List (Fin (prime+4))) j => if ∃ i, initial i = j then [] else f j
  let stock : Stacks H prime := {seeded with L := clear seeded.L, R := clear seeded.R}
  let split : Pr Empty intervalSplitTapes Q prime U := intervalPrepare.seq
    (foreign (liftQ (CyclicRowNormalized.splitProgram 142080 prime) mergeCap))
  refine ⟨H,host,(embProg initial Empty.elim split).seq worker,bank,stock,?_⟩
  intro input u S x left source fresh y rows
  have atSplitter i (hi : i ≠ 0) := fresh (initial i) (target ▸ initial.injective.ne hi)
  have atPort (i : Fin intervalSplitTapes) : ∃ j, initial j = initial i := ⟨i,rfl⟩
  have vol : 0 < V := by
    change 0 < volume prime (phaseIntervalChild lo hi (w+1) W axes)
    rw [intervalChild_volume ordered fits]
    exact Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) positive
  let data := fun r (i : Fin V) => input ((finProdFinEquiv (i,r)).cast size)
  let original := putWord (fun _ => blank) 0 (List.ofFn x)
  obtain ⟨a,E,t,placed,user,paid,start,off⟩ := splitEncoded_exec host initial mergeCap vol
    (fun k => input (k.cast size)) u S (target ▸ source) (fun i => by
      by_cases h : i = 0
      · simpa only [h,← target] using left
      · simpa [stock,clear,atPort] using (atSplitter i h).1) (fun i h => by
        simpa [stock,clear,atPort] using (atSplitter i h).2)
  obtain ⟨z,F,n,ran,bill,same,result⟩ := run original data a E (by exact start) (fun j away => by
    have keep := off j away
    have before := fresh j (by rw [target]; exact (away 0).symm)
    have outside : ¬ ∃ i, initial i = j := by simpa using away
    simpa [stock,clear,outside] using And.intro (keep.1.trans before.1) (keep.2.trans before.2))
  have changed : (fun r => Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (data r)) = rows := by
    funext r i
    exact (transpose_trailingRows lane 142080 input i r).symm
  rw [changed] at result
  have merged (k : Fin (V*142080)) : rows (finProdFinEquiv.symm k).2 (finProdFinEquiv.symm k).1 = y k := by
    exact congrArg y (finProdFinEquiv.apply_symm_apply k)
  simp only [merged] at result
  have overwrite : putWord original 0 (List.ofFn fun k => SparseRoleCircuit.encode (a := prime) (y k)) =
      putWord (fun _ => blank) 0 (List.ofFn fun k => SparseRoleCircuit.encode (a := prime) (y k)) :=
    FlatControlledShiftArray.overwrite _ _ _ _ (by simp)
  rw [overwrite] at result
  exact ⟨z,F,t+n,placed.seq ran,Nat.add_le_add paid bill,same.trans user,result⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
