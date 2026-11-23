module

public import IntegerMultBounds.MathlibTM2.M6.BitIntervalChildMerge
public import IntegerMultBounds.MathlibTM2.M6.BitWorkerIntervalDimensions

/-! Pack, execute and merge recursive rows using the caller’s runtime dimensions. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (volume)
local notation "N" => rowSwapBlock.tapes

theorem workerIntervalMerge {P U : Type} {T B Q w W atom price lo hi axes : ℕ}
    (capacity : rowSwapBlock.states ≤ Q)
    (mergeCap : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    (ordered : lo ≤ hi) (fits : hi ≤ axes) (positive : 0 < W)
    (widthAt : (phaseIntervalChild lo hi (w+1) W axes).width = 64*atom)
    {body : P → Pr P B Q prime U} {code src dst seed}
    (child : PackedPieceHandoff ((prime^(w+1))^(axes+axes)*W) (packedChildOutput atom _) body code src dst seed price)
    (splitter : Fin intervalSplitTapes ↪ Fin T) (directory : Fin 72 ↪ Fin T)
    (apart : ∀ i j, splitter i ≠ directory j) (source : Fin 72 ↪ Fin T)
    (separate : ∀ i j, directory i ≠ source j) :
    let live := (intervalOwners 142080).trans splitter
    let H := 142082+T+B
    let caller := (Fin.natAddEmb 142082 (m := T)).trans (Fin.castAddEmb B)
    let extend := Fin.castAddEmb (n := H) (142080*(N+35))
    let initial := (splitter.trans caller).trans extend
    let regs := (directory.trans caller).trans extend
    let raw := (source.trans caller).trans extend
    let small := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
    let ports := intervalRecordBank (live.trans caller) (small 24)
    let lane := phaseIntervalChild lo hi (w+1) W axes
    let V := volume prime lane
    ∃ (host : Empty ⊕ P → Pr (Empty ⊕ P) (H+142080*(N+35)) Q prime U)
      (program : Pr (Empty ⊕ P) (H+142080*(N+35)) Q prime U)
      (bank : Fin intervalSplitTapes ↪ Fin (H+142080*(N+35))),
    bank 0 = initial 0 ∧ ∀ target (data : Fin 142080 → Fin V → ZMod 2) u S,
      RepT (intervalOwnerBank target data) (embStk initial S).L (embStk initial S).R →
      S.R (raw 2) = binSyms (prime^(w+1)).size (prime^(w+1)) →
      S.R (raw 53) = binSyms W.size W → S.R (raw 28) = binSyms 1 1 →
      (S.R (raw 71)).length = w+1 →
      (∀ i, S.L (regs i) = [] ∧ S.R (regs i) = []) →
      (∀ r k, k ≠ small 24 → S.L (ports r k) = [] ∧ S.R (ports r k) = []) →
      (∀ i : Fin 142082, let j := extend ((i.castAdd T).castAdd B)
        S.L j = [] ∧ S.R j = []) →
      (∀ i : Fin B, let j := extend (i.natAdd (142082+T))
        S.L j = seed.L i ∧ S.R j = seed.R i) →
      let output := fun r => Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (data r)
      let word := fun k : Fin (V*142080) => let p := finProdFinEquiv.symm k
                                            SparseRoleCircuit.encode (a := prime) (output p.2 p.1)
      ∃ z F n, Exec host program (mk u S) n (mk z F) ∧
        n ≤ (6*((prime^(w+1)).size+W.size)+27*(w+1)+44) + (intervalChildToll U lo hi w W axes + price + (149*(V*142080)*(intervalSplitTapes+5)+6)) ∧
        z.user = u.user ∧ RepT (intervalOwnerBank (putWord target 0 (List.ofFn word)) output)
          (embStk bank F).L (embStk bank F).R ∧
        ∀ j, (∀ i, splitter i ≠ j) → (∀ i, directory i ≠ j) →
          F.L (extend (caller j)) = S.L (extend (caller j)) ∧ F.R (extend (caller j)) = S.R (extend (caller j)) := by
  intro live H caller extend initial regs raw small ports lane V
  obtain ⟨host,call,bank,targetBank,merge⟩ := packedIntervalMerge capacity mergeCap ordered fits positive
    widthAt child splitter (intervalDirectoryPorts.trans directory) (directory 59)
    (fun _ _ => apart _ _) (fun _ => apart _ _)
  obtain ⟨setup,prepare⟩ := prepareWorkerIntervalDimensions host raw regs (fun i j => extend.injective.ne (caller.injective.ne (separate i j)))
  refine ⟨host,setup.seq call,bank,targetBank,?_⟩
  intro target data u S split base suffix unit atom blank free fresh prepared output word
  obtain ⟨v,D,t,ran,user,paid,inputs,frame⟩ :=
    prepare w W u S base suffix unit atom blank
  have same i := frame (initial i) (fun j =>
    extend.injective.ne (caller.injective.ne (apart i j).symm))
  have represented : RepT (intervalOwnerBank target data) (embStk initial D).L (embStk initial D).R := by
    intro i z
    simpa only [embStk,Function.comp_apply,(same i).1,(same i).2] using split i z
  obtain ⟨z,F,n,exec,cost,result,out,keep⟩ := merge target data v D represented inputs (by
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
  refine ⟨z,F,t+n,ran.seq exec,Nat.add_le_add paid cost,result.trans user,out,?_⟩
  intro j outside privateOff
  have before := frame (extend (caller j)) (fun i => extend.injective.ne (caller.injective.ne (privateOff i)))
  exact ⟨(keep j outside).1.trans before.1,(keep j outside).2.trans before.2⟩

theorem workerIntervalMergeWithCharge {P U : Type} {T B Q w W atom price lo hi axes : ℕ}
    (capacity : rowSwapBlock.states ≤ Q)
    (mergeCap : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    (ordered : lo ≤ hi) (fits : hi ≤ axes) (positive : 0 < W)
    (widthAt : (phaseIntervalChild lo hi (w+1) W axes).width = 64*atom)
    {body : P → Pr P B Q prime U} {code src dst seed}
    (child : PackedPieceHandoffWithCharge cleanupWeight ((prime^(w+1))^(axes+axes)*W) (packedChildOutput atom _) body code src dst seed price)
    (splitter : Fin intervalSplitTapes ↪ Fin T) (directory : Fin 72 ↪ Fin T)
    (apart : ∀ i j, splitter i ≠ directory j) (source : Fin 72 ↪ Fin T)
    (separate : ∀ i j, directory i ≠ source j) :
    let live := (intervalOwners 142080).trans splitter
    let H := 142082+T+B
    let caller := (Fin.natAddEmb 142082 (m := T)).trans (Fin.castAddEmb B)
    let extend := Fin.castAddEmb (n := H) (142080*(N+35))
    let initial := (splitter.trans caller).trans extend
    let regs := (directory.trans caller).trans extend
    let raw := (source.trans caller).trans extend
    let small := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)
    let ports := intervalRecordBank (live.trans caller) (small 24)
    let lane := phaseIntervalChild lo hi (w+1) W axes
    let V := volume prime lane
    ∃ (host : Empty ⊕ P → Pr (Empty ⊕ P) (H+142080*(N+35)) Q prime U)
      (program : Pr (Empty ⊕ P) (H+142080*(N+35)) Q prime U)
      (bank : Fin intervalSplitTapes ↪ Fin (H+142080*(N+35))) (setupRate passRate : ℕ),
    bank 0 = initial 0 ∧ ∀ target (data : Fin 142080 → Fin V → ZMod 2) u S,
      RepT (intervalOwnerBank target data) (embStk initial S).L (embStk initial S).R →
      S.R (raw 2) = binSyms (prime^(w+1)).size (prime^(w+1)) →
      S.R (raw 53) = binSyms W.size W → S.R (raw 28) = binSyms 1 1 →
      (S.R (raw 71)).length = w+1 →
      (∀ i, S.L (regs i) = [] ∧ S.R (regs i) = []) →
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
            setupRate*(6*(M.size+W.size)+27*(w+1)+44)+
            passRate*(142080*(header+pass)+1+(142080*pass+1))+
            (142081*(8*V+10+2*V)+1+price)+13*(149*(V*142080)*(intervalSplitTapes+5)+6)) ∧
        z.user = u.user ∧ RepT (intervalOwnerBank (putWord target 0 (List.ofFn word)) output)
          (embStk bank F).L (embStk bank F).R ∧
        ∀ j, (∀ i, splitter i ≠ j) → (∀ i, directory i ≠ j) →
          F.L (extend (caller j)) = S.L (extend (caller j)) ∧ F.R (extend (caller j)) = S.R (extend (caller j)) := by
  intro live H caller extend initial regs raw small ports lane V
  obtain ⟨host,call,bank,rate,targetBank,merge⟩ := packedIntervalMergeWithCharge capacity mergeCap ordered fits positive
    widthAt child splitter (intervalDirectoryPorts.trans directory) (directory 59)
    (fun _ _ => apart _ _) (fun _ => apart _ _)
  obtain ⟨setup,prepare⟩ := prepareWorkerIntervalDimensions (P := Empty) (U := U) Empty.elim raw regs (fun i j => extend.injective.ne (caller.injective.ne (separate i j)))
  refine ⟨host,(embProg id Empty.elim setup).seq call,bank,1+6*Fast.Main.mnProgPush setup,rate,targetBank,?_⟩
  intro target data u S split base suffix unit atom blank free fresh prepared output word
  obtain ⟨v,D,t,ran,user,paid,inputs,frame⟩ :=
    prepare w W u S base suffix unit atom blank
  have same i := frame (initial i) (fun j =>
    extend.injective.ne (caller.injective.ne (apart i j).symm))
  have represented : RepT (intervalOwnerBank target data) (embStk initial D).L (embStk initial D).R := by
    intro i z
    simpa only [embStk,Function.comp_apply,(same i).1,(same i).2] using split i z
  obtain ⟨z,F,n,exec,cost,result,out,keep⟩ := merge target data v D represented inputs (by
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
  have project (a : HS (H+142080*(N+35)) Q prime U) : embDn id a = a := by
    cases a with
    | mk flag sym st scan nxt user => cases nxt <;> rfl
  obtain ⟨a,E,lifted,state,_,view,_⟩ := exec_emb (e := id) (ι := Empty.elim) (body' := host)
    Function.injective_id (fun f => nomatch f) ran u (project u) S rfl
  rw [project] at state
  change E = D at view
  subst a E
  refine ⟨z,F,t+n,lifted.seq exec,?_,result.trans user,out,?_⟩
  · intro js unique
    have growth := recordCleanup_cost_le js unique ran (c := Fast.Main.mnProgPush setup)
      le_rfl (fun f => nomatch f)
    change tapeCharge cleanupWeight js D+1 ≤ tapeCharge cleanupWeight js S+1+
      6*(Fast.Main.mnProgPush setup*t) at growth
    have bound := Nat.mul_le_mul_left (1+6*Fast.Main.mnProgPush setup) paid
    have childBill := cost js unique
    dsimp only at childBill ⊢
    linarith only [growth,bound,childBill]
  · intro j outside privateOff
    have before := frame (extend (caller j)) (fun i => extend.injective.ne (caller.injective.ne (privateOff i)))
    exact ⟨(keep j outside).1.trans before.1,(keep j outside).2.trans before.2⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
