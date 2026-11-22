module

public import IntegerMultBounds.MathlibTM2.M6.BitSweepNodeAddress
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

/-- Loading a stream leaves a prepared transpose bank ready with precisely
that unread word. Its other seven registers carry the original counters. -/
private theorem transpose_loaded {T : ℕ} (port : Fin 8 ↪ Fin T) (S F : Stacks T prime)
    (word record row : List (Fin (prime+4)))
    (initial : embStk port S = transposeStacks (embStk port S) [] [] [] record row)
    (loaded : F.R (port 6) = word) (keep : ∀ i, i ≠ 6 → F.R (port i) = S.R (port i)) :
    embStk port F = transposeStacks (embStk port F) [] word [] record row := by
  suffices h : (embStk port F).R = (transposeStacks (embStk port F) [] word [] record row).R by
    cases F
    simp only [embStk,transposeStacks] at h ⊢
    rw [h]
  funext i
  have h := congrArg (fun X => X.R i) initial
  change S.R (port i) = _ at h
  change F.R (port i) = _
  by_cases atWord : i = 6
  · subst i
    exact loaded
  · rw [keep i atWord]
    fin_cases i <;> first | exact h | contradiction

theorem encodedFrameWord {N V : ℕ} (size : N = V) (word : Fin V → ZMod 2) :
    (List.ofFn fun i : Fin N => SparseRoleCircuit.encode (a := prime) (M8.RevMachine.ext word i.val)) =
      List.ofFn (fun i => SparseRoleCircuit.encode (word i)) := by
  subst N
  simp only [M8.RevMachine.ext_apply]

/-- Convert the selected owners in the shared packing workspace, then write
the exact right-stack words consumed by the allocated sweep. All registers
outside the workspace and destination bank retain both stacks. -/
theorem flatFrameWords_exec [M8.Machine.Net] {k T Q : ℕ} {P U : Type}
    (body : P → Pr P T Q prime U) (selected : List (Fin k)) (distinct : selected.Nodup)
    (bank : Fin ((rowSwapBlock.tapes+35)+k) ↪ Fin T) (capacity : rowSwapBlock.states ≤ Q)
    (dest : Fin k ↪ Fin T) (tmp : Fin T)
    (apart : ∀ i j, bank i ≠ dest j) (scratch : ∀ i, bank i ≠ tmp) (dstTmp : ∀ i, dest i ≠ tmp) :
    let src := (Fin.natAddEmb (rowSwapBlock.tapes+35) (m := k)).trans bank
    ∃ code C, ∀ w W : ℕ, 0 < W →
      let V := (prime^(w+1))^128*W
      ∀ (data : Fin k → Fin V → ZMod 2) (v : HS T Q prime U) (S : Stacks T prime),
      embStk bank S = helperPackInput w W (embStk src S) →
      RepT (phaseOwners data) (embStk src S).L (embStk src S).R →
      S.L tmp = [] → S.R tmp = [] → (∀ i, S.R (dest i) = []) →
      ∃ z F, ∃ time : ℕ, ∃ out : Fin k → Fin V → ZMod 2,
        Exec body code (mk v S) time (mk z F) ∧ z.user = v.user ∧
        (time : ℝ) ≤ C*V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau ∧
        (∀ i, F.R (dest i) = List.ofFn fun j => SparseRoleCircuit.encode (out i j)) ∧
        (∀ j, (∀ i, bank i ≠ j) → (∀ i, dest i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j) ∧
        (∀ i (port : Fin 8 ↪ Fin T) record row, port 6 = dest i →
          (∀ j, j ≠ 6 → (∀ a, bank a ≠ port j) ∧ (∀ a, dest a ≠ port j)) →
          embStk port S = transposeStacks (embStk port S) [] [] [] record row →
          let framed := fun j : Fin ((prime^(w+1))^16*(1*((prime^(w+1))^112*W))) => M8.RevMachine.ext (out i) j.val
          embStk port F = transposeStacks (embStk port F) []
            (List.ofFn fun j => SparseRoleCircuit.encode (framed j)) [] record row) ∧
        (∀ i ∉ selected, out i = data i) ∧
        ∀ i ∈ selected, ∀ a : Fin V, let node := flatToNode (w+1) W (fun _ => 1) (fun _ => isUnit_one) a
          M8.RevMachine.ext (out i) node.val = data i a ∧ out i a = M8.RevMachine.ext (data i) node.val := by
  intro src
  obtain ⟨pack,C,run⟩ := flatToNode_unit_owners_exec (P := Empty) (U := U) selected distinct Empty.elim
  obtain ⟨copy,load⟩ := materializeOwners_exec body src dest tmp (fun i => apart _) (fun i => scratch _) dstTmp
  refine ⟨(statePlacedNormalized bank capacity swapStates_pos Empty.elim pack).seq copy,C+18*k+2,?_⟩
  intro w W hW V data v S init represented left right empty
  obtain ⟨u,D,m,out,exec,user,paid,reads,unchanged,frame⟩ := run w W hW
    (stateLiftDown swapStates_pos (embDn bank v)) (embStk src S) data ((phaseOwner_reads ..).1 represented)
  rw [← init] at exec
  obtain ⟨u',_,same,placed⟩ := statePlaced_exec_normalized bank bank.injective capacity swapStates_pos
    Empty.elim (body' := body) (fun e => nomatch e) v S exec
  have projected := embStk_ovr bank.injective D S
  have live : RepT (phaseOwners out) (embStk src (embOvr bank D.get S)).L (embStk src (embOvr bank D.get S)).R := by
    apply (phaseOwner_reads ..).2
    intro i j
    have cell := reads i j
    rw [← projected] at cell
    exact cell
  have off := fun j (h : ∀ i, bank i ≠ j) => embOvr_off D.get S h
  obtain ⟨z,R,n,copied,bill,finalUser,words,kept⟩ := load out u' _ live
    ((off tmp scratch).1.trans left) ((off tmp scratch).2.trans right)
    (fun i => (off _ (fun j => apart j i)).2.trans (empty i))
  refine ⟨z,_,1+m+n,out,Exec.seq placed copied,finalUser.trans (same.trans user),?_,words,?_,?_,unchanged,frame⟩
  · have pos : 0 < V := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _) hW
    have one : (1 : ℝ) ≤ V := by exact_mod_cast pos
    have power : 1 ≤ ((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau :=
      Real.one_le_rpow (by exact_mod_cast Nat.le_add_left 1 w) M8.Machine.BudgetBound.exponent_range.1.le
    have scale := le_mul_of_one_le_right (show (0 : ℝ) ≤ V by positivity) power
    have copyTime : n ≤ 18*k*V+1 := by
      have h : 8*V+10 ≤ 18*V := by omega
      exact bill.trans ((Nat.add_le_add_right (Nat.mul_le_mul_left k h) 1).trans_eq (by ring))
    have nle : (n : ℝ) ≤ 18*k*V+1 := by exact_mod_cast copyTime
    change (m : ℝ) ≤ C*V*((w+1 : ℕ) : ℝ)^M8.Machine.BudgetBound.tau at paid
    simp only [Nat.cast_add,Nat.cast_one,add_mul] at paid scale ⊢
    nlinarith only [paid,nle,one,scale,mul_le_mul_of_nonneg_left scale (show (0 : ℝ) ≤ 18*k by positivity)]
  · intro j outside away
    exact ⟨(off j outside).1,(kept j away).trans (off j outside).2⟩
  · intro i port record row atWord privateRegs initial framed
    have size : (prime^(w+1))^16*(1*((prime^(w+1))^112*W)) = V := by
      simp only [V,one_mul,← Nat.mul_assoc,← pow_add]
    apply transpose_loaded port S _ _ record row initial
    · rw [atWord]
      exact (words i).trans (encodedFrameWord size (out i)).symm
    · intro j apart
      obtain ⟨outside,away⟩ := privateRegs j apart
      exact (kept _ away).trans (off _ outside).2

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
