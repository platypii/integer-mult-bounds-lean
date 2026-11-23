module

public import IntegerMultBounds.MathlibTM2.M6.BitIntervalChildRun
public import IntegerMultBounds.MathlibTM2.M6.BitInheritedReturnMerge

/-! Return a recursive packed interval to its original cyclic merge target. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (volume)
local notation "N" => rowSwapBlock.tapes

private theorem castFan {c T m n : ℕ} (eq : m = n) (fan : Fin (c+2) ↪ Fin T)
    (x : Fin c → Fin m → ZMod 2) (S : Stacks T prime) :
    HelperFan fan (fun r i => x r (i.cast eq.symm)) S ↔ HelperFan fan x S := by
  subst n
  rfl

private theorem placedOwners {T H A m c : ℕ} (splitter : Fin (((1+c)+2)+2) ↪ Fin T)
    (caller : Fin T ↪ Fin H) (extend : Fin H ↪ Fin A) (target : ℤ → Fin (prime+4))
    (data : Fin c → Fin m → ZMod 2) (S : Stacks A prime)
    (split : RepT (intervalOwnerBank target data) (embStk ((splitter.trans caller).trans extend) S).L
      (embStk ((splitter.trans caller).trans extend) S).R) :
    HelperFan ((((intervalOwners c).trans splitter).trans caller).trans extend) data S :=
  intervalOwners_ready target data _ split

theorem packedIntervalMerge {P U : Type} {T B Q w W atom price lo hi : ℕ}
    (capacity : rowSwapBlock.states ≤ Q)
    (mergeCap : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    (ordered : lo ≤ hi) (fits : hi ≤ 64) (positive : 0 < W)
    (widthAt : (phaseIntervalChild lo hi (w+1) W 64).width = 64*atom)
    {body : P → Pr P B Q prime U} {code src dst seed}
    (child : PackedPieceHandoff ((prime^(w+1))^128*W) (packedChildOutput atom _) body code src dst seed price)
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
    let lane := phaseIntervalChild lo hi (w+1) W 64
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
        n ≤ intervalChildToll U lo hi w W + price + (149*(V*142080)*(intervalSplitTapes+5)+6) ∧
        z.user = u.user ∧ RepT (intervalOwnerBank (putWord target 0 (List.ofFn word)) output)
          (embStk bank F).L (embStk bank F).R := by
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
  have size : V = (prime^(w+1))^128*W := intervalChild_volume ordered fits (w+1) W
  have vol : 0 < V := by
    rw [size]
    exact Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) positive
  apply mergeAfterReturnedRows host call saved _ separate mergeCap vol target data output (embStk initial S) u S split
  have owners : HelperFan ((live.trans caller).trans extend) data S :=
    placedOwners (c := 142080) splitter caller extend target data S split
  obtain ⟨v,D,k,exec,paid,user,rows,frame⟩ := run data u S dimensions
    ((castFan size ((live.trans caller).trans extend) data S).2 owners) free fresh prepared
  exact ⟨v,D,k,exec,paid,user,(castFan size _ output D).1 rows,fun i => frame _ (outside i)⟩

theorem directoryIntervalMerge {P U : Type} {T B Q w W atom price lo hi : ℕ}
    (capacity : rowSwapBlock.states ≤ Q)
    (mergeCap : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    (ordered : lo ≤ hi) (fits : hi ≤ 64) (positive : 0 < W)
    (widthAt : (phaseIntervalChild lo hi (w+1) W 64).width = 64*atom)
    {body : P → Pr P B Q prime U} {code src dst seed}
    (child : PackedPieceHandoff ((prime^(w+1))^128*W) (packedChildOutput atom _) body code src dst seed price)
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
    let lane := phaseIntervalChild lo hi (w+1) W 64
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
        n ≤ (21*(w+1)+13) + (intervalChildToll U lo hi w W + price + (149*(V*142080)*(intervalSplitTapes+5)+6)) ∧
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
  obtain ⟨z,F,n,exec,cost,result,out⟩ := merge target data v D represented inputs (by
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

end IntegerMultBounds.MathlibTM2.M6.BitNode
