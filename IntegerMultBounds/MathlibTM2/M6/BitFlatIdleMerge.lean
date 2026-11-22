module

public import IntegerMultBounds.MathlibTM2.M6.BitFlatIdleRows
public import IntegerMultBounds.MathlibTM2.M6.BitIntervalOwners

/-! Split a recursive remainder payload, run its lane worker once and merge the answer. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover.Fallback Stack Host
open RecursiveInterchangeLayout (Descriptor volume)
open Shared50ModularControl (prime)

private theorem mergedPayload {m c V : ℕ} (span : m*c = V) (word : Fin V → ZMod 2)
    (data : Fin c → Fin m → ZMod 2) (S : Stacks (((1+c)+2)+2) prime)
    (rep : RepT (intervalOwnerBank (putWord (fun _ => blank) 0
      (List.ofFn fun a : Fin (m*c) => SparseRoleCircuit.encode (a := prime) (word (a.cast span)))) data) S.L S.R) :
    RecordPayload 0 (fun _ => blank) 0 word S := by
  subst V
  intro j
  rw [encodedOwnerCell]
  let src := (((0 : Fin 1).castAdd c).castAdd 2).castAdd 2
  have h := (rep src j).symm
  have zero : src = 0 := Fin.ext (by simp [src])
  rw [← zero]
  simpa only [src,intervalOwnerBank,CyclicRowSplit.bank,CyclicRowCopy.bank,CyclicRowCopy.payload,
    CountedLoopReuseAlphabet.bank,Tapes.append,Fin.addCases_left,Fin.cast_eq_self] using h

theorem flatIdleMergeSpace_exec {P U : Type} {Q b : ℕ} (body : P → Pr P intervalSplitTapes Q prime U)
    (worker : Pr P intervalSplitTapes Q prime U)
    (returned : Stacks intervalSplitTapes prime → Prop)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    (parent child : Descriptor) (i : Fin 9) (j : Fin 222) (w rows : ℕ) (stock : 142080 ∣ rows) :
    let tail := fun r => parent.beforeRows*r*parent.beforeH*parent.between*parent.afterD
    let W := tail rows
    let V := (prime^w)^128*W
    let e := idleInterval i j
    let lane := phaseIntervalChild e.1 e.2 w (tail (rows/142080)) 64
    let m := volume prime lane
    ∀ (position : Fin (volume prime child) ≃ Fin V), IdleChildPositions i j w W child position →
    ∃ span : m*142080 = V, ∀ (word : Fin V → ZMod 2) u (S : Stacks intervalSplitTapes prime),
      let source := fun (x : Fin V → ZMod 2) => List.ofFn fun a : Fin (m*142080) => SparseRoleCircuit.encode (a := prime) (x (a.cast span))
      let data := fun (r : Fin 142080) (a : Fin m) => word ((finProdFinEquiv (a,r)).cast span)
      let output := fun r => Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (data r)
      0 < m → S.R 0 = source word → (∀ t, S.L t = []) → (∀ t, t ≠ 0 → S.R t = []) →
      (∀ v D, HelperFan (intervalOwners 142080) data D →
        (∀ j, (D.L j).length+(D.R j).length ≤ 301*V+2) →
        ∃ z F k, Exec body worker (mk v D) k (mk z F) ∧ k ≤ b ∧ z.user = v.user ∧
          HelperFan (intervalOwners 142080) output F ∧ (F.L 0 = D.L 0 ∧ F.R 0 = D.R 0) ∧
          (∀ l : Fin 2, let t := (l.natAdd (1+142080)).castAdd 2
            F.L t = D.L t ∧ F.R t = D.R t) ∧
          returned F) →
      ∃ z F k changed, Exec body ((intervalPrepare.seq (foreign (liftQ (CyclicRowNormalized.splitProgram 142080 prime) capacity))).seq
          (worker.seq (foreign (liftQ (CyclicRowNormalized.mergeProgram 142080 prime) capacity)))) (mk u S) k (mk z F) ∧
        k ≤ (298*(intervalSplitTapes+5)+5)*V+b+30 ∧ z.user = u.user ∧
        RecordPayload 0 (fun _ => blank) 0 changed F ∧
        (∃ E, returned E ∧ ∀ t, (F.L t).length+(F.R t).length ≤ (E.L t).length+(E.R t).length+298*V) ∧
        ∀ a, changed (position a) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (word ∘ position) a := by
  intro tail W V e lane m position coords
  obtain ⟨span,reads⟩ := coords.internalRows_iff parent i j w rows stock position
  change m*142080 = V at span
  refine ⟨span,?_⟩
  intro word u S source data output pos stored left empty run
  let changed := fun a : Fin V => let p := finProdFinEquiv.symm (a.cast span.symm)
                                  output p.2 p.1
  have cell (r : Fin 142080) (a : Fin m) : changed ((finProdFinEquiv (a,r)).cast span) = output r a := by
    simp only [changed,Fin.cast_cast,Fin.cast_eq_self,Equiv.symm_apply_apply]
  have lanes : (fun r a => changed ((finProdFinEquiv (a,r)).cast span)) = output := funext fun r => funext (cell r)
  let enc := fun (x : Fin V → ZMod 2) (a : Fin (m*142080)) => SparseRoleCircuit.encode (a := prime) (x (a.cast span))
  obtain ⟨z,F,k,user,paid,exec,out,growth⟩ := intervalWorkerSpace_exec body worker returned capacity pos (enc word) (enc changed)
    u S stored left empty (by
      intro v D ready roomIn
      let src := putWord (fun _ => blank) 0 (source word)
      change RepT (intervalOwnerBank src data) D.L D.R at ready
      obtain ⟨z,F,k,exec,paid,user,result,keep,inner,room⟩ := run v D (intervalOwners_ready _ _ _ ready) (by simpa only [← span] using roomIn)
      refine ⟨z,F,k,user,paid,exec,?_,room⟩
      have bank := intervalOwners_return src data output D F ready result keep inner
      change RepT (intervalOwnerBank src (fun r a => changed ((finProdFinEquiv (a,r)).cast span))) F.L F.R
      rw [lanes]
      exact bank)
  refine ⟨z,F,k,changed,exec,by simpa only [← span] using paid,user,?_,by simpa only [← span] using growth,(reads word changed).2 (fun a r => cell r a)⟩
  change RepT (intervalOwnerBank _ (fun r a => changed ((finProdFinEquiv (a,r)).cast span))) F.L F.R at out
  rw [lanes] at out
  exact mergedPayload span changed output F out

theorem flatIdleMerge_exec {P U : Type} {Q b : ℕ} (body : P → Pr P intervalSplitTapes Q prime U)
    (worker : Pr P intervalSplitTapes Q prime U)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    (parent child : Descriptor) (i : Fin 9) (j : Fin 222) (w rows : ℕ) (stock : 142080 ∣ rows) :
    let tail := fun r => parent.beforeRows*r*parent.beforeH*parent.between*parent.afterD
    let W := tail rows
    let V := (prime^w)^128*W
    let e := idleInterval i j
    let lane := phaseIntervalChild e.1 e.2 w (tail (rows/142080)) 64
    let m := volume prime lane
    ∀ (position : Fin (volume prime child) ≃ Fin V), IdleChildPositions i j w W child position →
    ∃ span : m*142080 = V, ∀ (word : Fin V → ZMod 2) u (S : Stacks intervalSplitTapes prime),
      let source := fun (x : Fin V → ZMod 2) => List.ofFn fun a : Fin (m*142080) => SparseRoleCircuit.encode (a := prime) (x (a.cast span))
      let data := fun (r : Fin 142080) (a : Fin m) => word ((finProdFinEquiv (a,r)).cast span)
      let output := fun r => Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (data r)
      0 < m → S.R 0 = source word → (∀ t, S.L t = []) → (∀ t, t ≠ 0 → S.R t = []) →
      (∀ v D, HelperFan (intervalOwners 142080) data D →
        ∃ z F k, Exec body worker (mk v D) k (mk z F) ∧ k ≤ b ∧ z.user = v.user ∧
          HelperFan (intervalOwners 142080) output F ∧ (F.L 0 = D.L 0 ∧ F.R 0 = D.R 0) ∧
          ∀ l : Fin 2, let t := (l.natAdd (1+142080)).castAdd 2
            F.L t = D.L t ∧ F.R t = D.R t) →
      ∃ z F k changed, Exec body ((intervalPrepare.seq (foreign (liftQ (CyclicRowNormalized.splitProgram 142080 prime) capacity))).seq
          (worker.seq (foreign (liftQ (CyclicRowNormalized.mergeProgram 142080 prime) capacity)))) (mk u S) k (mk z F) ∧
        k ≤ (298*(intervalSplitTapes+5)+5)*V+b+30 ∧ z.user = u.user ∧
        RecordPayload 0 (fun _ => blank) 0 changed F ∧
        ∀ a, changed (position a) = Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (word ∘ position) a := by
  intro tail W V e lane m position coords
  obtain ⟨span,build⟩ := flatIdleMergeSpace_exec body worker (fun _ => True) capacity parent child i j w rows stock position coords
  refine ⟨span,?_⟩
  intro word u S source data output pos stored left empty run
  obtain ⟨z,F,k,changed,exec,paid,user,out,_,act⟩ := build word u S pos stored left empty (by
    intro v D ready _
    obtain ⟨y,G,l,ran,time,same,rep,source,inner⟩ := run v D ready
    exact ⟨y,G,l,ran,time,same,rep,source,inner,trivial⟩)
  exact ⟨z,F,k,changed,exec,paid,user,out,act⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
