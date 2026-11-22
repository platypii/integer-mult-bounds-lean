module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepOwnerSchedule
public import IntegerMultBounds.MathlibTM2.M6.BitRemainderCompactRead
public import IntegerMultBounds.MathlibTM2.M6.BitSweepCropOwners

/-! Copy represented owner words into the compact return registers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback Cover.LabelTraversal
open Shared50ModularControl (prime)

/-- One temporary tape suffices for the whole bank, including its spare owner. -/
theorem materializeOwners_exec {k T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (source dest : Fin k ↪ Fin T) (tmp : Fin T)
    (apart : ∀ i j, source i ≠ dest j) (srcTmp : ∀ i, source i ≠ tmp) (dstTmp : ∀ i, dest i ≠ tmp) :
    ∃ code, ∀ {V : ℕ} (x : Fin k → Fin V → ZMod 2) (u : HS T Q prime U) (S : Stacks T prime),
      RepT (phaseOwners x) (embStk source S).L (embStk source S).R →
      S.L tmp = [] → S.R tmp = [] → (∀ i, S.R (dest i) = []) →
      ∃ z R t, Exec body code (mk u S) t (mk z {S with R := R}) ∧
        t ≤ k*(8*V+10)+1 ∧ z.user = u.user ∧
        (∀ i, R (dest i) = List.ofFn fun j => SparseRoleCircuit.encode (x i j)) ∧
        ∀ j, (∀ i, dest i ≠ j) → R j = S.R j := by
  let copy : Fin k → Pr P T Q prime U := fun i => loadCompactWord (source i) tmp (dest i)
  refine ⟨sequence copy (List.finRange k),?_⟩
  intro V x u S rep left right empty
  let word := fun i => List.ofFn fun j => SparseRoleCircuit.encode (a := prime) (x i j)
  obtain ⟨z,R,t,user,paid,run,written,off⟩ := distinctTapeSequence body dest copy
    (List.finRange k) (List.nodup_finRange _) (fun _ => []) word (fun _ => 8*V+10) u S empty (by
      intro i v F same vacant keep
      have ready : WordAtZero (x i) (F.L (source i)) (F.R (source i)) := by
        intro j
        rw [same,keep _ (fun a => (apart i a).symm)]
        have h := (rep i j).symm
        change readAt blank (S.L (source i)) (S.R (source i)) (j-0) = _ at h
        rwa [sub_zero] at h
      obtain ⟨y,hy,copyWord⟩ := loadCompactWord_exec body (source i) tmp (dest i)
        (by simp [List.nodup_cons,srcTmp,apart,(dstTmp i).symm]) (x i) v F ready
        (same ▸ left) ((keep _ dstTmp).trans right)
      exact ⟨y,_,hy,le_rfl,by simpa only [vacant,List.append_nil,word,copy] using copyWord⟩)
  exact ⟨z,R,t,run,by simpa only [List.map_const',List.sum_replicate_nat,List.length_finRange] using paid,
    user,fun i => written i (List.mem_finRange _),fun j h => off j (fun i _ => h i)⟩

/-- Produce the return conversion's exact input words from the recursive stage handoff. -/
theorem stageExitWords_exec {w B K T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (port : Fin 142081 → Fin 12 ↪ Fin T)
    (shared : ∀ i k j, j ≠ 0 → j ≠ 1 → port i j = port k j)
    (apart : ∀ i k, i ≠ k → ∀ j, port i j ≠ port k 0 ∧ port i j ≠ port k 1)
    (fits : 215 ≤ Q) (hb : 0 < B) (hk : 0 < K) :
    let A := (prime^w)^16
    let N := prime^(64*(w*64))
    ∀ (leave : SharedBankStage.Stage _ 142081 prime (phaseOwners (N := A*(B*K))))
      (chart : Fin leave.tapes ↪ Fin T) (_room : leave.states ≤ Q)
      (fan : Fin (142081+2) ↪ Fin T) (dest : Fin 142081 ↪ Fin T) (tmp : Fin T),
      (∀ i h, port i h ≠ tmp) → (∀ i, chart i ≠ tmp) →
      (∀ i h j, port i h ≠ dest j) → (∀ i j, chart i ≠ dest j) → (∀ j, dest j ≠ tmp) →
      (∀ i, port i 0 = fan (i.castAdd 2)) → (∀ i, chart (leave.slots i) = port i 1) →
      (∀ j, (∀ i, leave.slots i ≠ j) → ∀ i h, port i h ≠ chart j) →
      ∃ code, ∀ x u S, HelperFan fan (singleLabelBank (firstRowLabel w) x) S →
        ChartPrivateReady leave (embStk chart S) → CropCounters (port 0) (A*B) N K S →
        (∀ i z, readAt blank (S.L (port i 1)) (S.R (port i 1)) z = blank) →
        S.L tmp = [] → S.R tmp = [] → (∀ i, S.R (dest i) = []) →
        ∃ z F t, Exec body code (mk u S) t (mk z F) ∧
          t ≤ 142081*(7021*(A*B)*(N*K)+6)+1 + (leave.cost*(leave.tapes+5)+6) + (142081*(8*(A*(B*K))+10)+1) ∧
          z.user = u.user ∧ (∀ i, F.R (dest i) = List.ofFn fun j => SparseRoleCircuit.encode (leave.transform x i j)) ∧
          ∀ j, (∀ i h, port i h ≠ j) → (∀ h, chart h ≠ j) → (∀ i, dest i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro A N leave chart room fan dest tmp portTmp chartTmp portDest chartDest dstTmp src dst separation
  obtain ⟨correct,run⟩ := cropAndCorrectSweep_exec (w := w) body port shared apart fits hb hk leave chart room fan src dst separation
  let source : Fin 142081 ↪ Fin T := ⟨fun i => port i 1,fun i j eqn => by
    by_contra ne
    exact (apart i j ne 1).2 eqn⟩
  obtain ⟨copy,load⟩ := materializeOwners_exec body source dest tmp (fun i j => portDest i 1 j)
    (fun i => portTmp i 1) dstTmp
  refine ⟨correct.seq copy,?_⟩
  intro x u S live privateReady headers empty left right fresh
  obtain ⟨v,D,k,exec,paid,user,output,off⟩ := run x u S live privateReady headers empty
  have scratch := off tmp portTmp chartTmp
  obtain ⟨z,R,l,copied,bill,same,words,frame⟩ := load (leave.transform x) v D output
    (scratch.1.trans left) (scratch.2.trans right)
    (fun j => (off _ (fun i h => portDest i h j) (fun h => chartDest h j)).2.trans (fresh j))
  refine ⟨z,_,k+l,Exec.seq exec copied,Nat.add_le_add paid bill,same.trans user,words,?_⟩
  intro j hp hc hd
  exact ⟨(off j hp hc).1,(frame j hd).trans (off j hp hc).2⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
