module

public import IntegerMultBounds.MathlibTM2.M6.BitIntervalRows
public import IntegerMultBounds.MathlibTM2.M6.BitIntervalCounter
public import IntegerMultBounds.MathlibTM2.M6.BitOrdinaryDirectoryChart

/-! Initialize the cyclic COPY splitter on its own source and empty role tapes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover.Fallback Stack Host
open Shared50ModularControl (prime)

abbrev intervalSplitTapes := ((1+142080)+2)+2

/-- The quotient goes directly to the outer loop header. The remaining
workspace borrows seven role tapes while they are still empty. -/
def intervalCounterPorts : Fin 9 ↪ Fin intervalSplitTapes :=
  ⟨![0,1,roleSplitControls 142080 3,2,3,4,5,6,7],by decide⟩

noncomputable def intervalMarkers {P U : Type} {Q : ℕ} : Pr P intervalSplitTapes Q prime U :=
  (Prog.act (.push (.rt (roleSplitControls 142080 1)) (fun _ => bitSymbol true) .done)).seq
    (Prog.act (pushMarkers ((List.finRange 4).map (roleSplitControls 142080))))

noncomputable def intervalPrepare {P U : Type} {Q : ℕ} : Pr P intervalSplitTapes Q prime U :=
  (intervalCounter intervalCounterPorts).seq
    intervalMarkers

theorem intervalMarkers_exec {P U : Type} {Q : ℕ} (body : P → Pr P intervalSplitTapes Q prime U)
    (m : ℕ) (u : HS intervalSplitTapes Q prime U) (S : Stacks intervalSplitTapes prime)
    (left : ∀ i, S.L i = [])
    (empty : ∀ i, i ≠ 0 → S.R i = []) :
    let B := {S with R := Function.update S.R (roleSplitControls 142080 3) ((FlatCoordinateSchedule.bits m).map bitSymbol)}
    ∃ D, Exec body intervalMarkers (mk u B) 2 (mk u D) ∧
      RepT (CyclicRowSplit.bank (CyclicRowCopy.bank (putWord (fun _ => blank) 0 (S.R 0))
        (fun _ _ => blank) 0 (fun _ => 0) (FlatCoordinateSchedule.bits 1))
        (FlatCoordinateSchedule.bits m)) D.L D.R := by
  intro B
  let ctrl := roleSplitControls 142080
  let C := {B with R := Function.update B.R (ctrl 1) (bitSymbol true :: B.R (ctrl 1))}
  have push : Exec body (.act (.push (.rt (ctrl 1)) (fun _ => bitSymbol true) .done))
      (mk u B) 1 (mk u C) := by
    apply (Exec.act _ _).cast rfl
    simp [Action.run,C,get_rt,update_rt]
  have nonzero (i) : ctrl i ≠ 0 := by intro h; have := congrArg Fin.val h; change 1+142080+i.val = 0 at this; omega
  obtain ⟨mark,repr⟩ := prepareRoleSplit_exec body u C (S.R 0) 1 m left
    (by change Function.update B.R (ctrl 1) (bitSymbol true :: B.R (ctrl 1)) 0 = _; rw [Function.update_of_ne (Ne.symm (nonzero 1))]; change Function.update S.R (ctrl 3) ((FlatCoordinateSchedule.bits m).map bitSymbol) 0 = _; rw [Function.update_of_ne (Ne.symm (nonzero 3))])
    (by intro j
        have off (i) : ((j.natAdd 1).castAdd 2).castAdd 2 ≠ ctrl i := by
          intro h; have := congrArg Fin.val h; change 1+j.val = 1+142080+i.val at this; omega
        have nz : ((j.natAdd 1).castAdd 2).castAdd 2 ≠ (0 : Fin intervalSplitTapes) := by
          intro h; have := congrArg Fin.val h; change 1+j.val = 0 at this; omega
        exact (Function.update_of_ne (off 1) ..).trans ((Function.update_of_ne (off 3) ..).trans (empty _ nz)))
    (by intro i
        change C.R (ctrl i) = _
        fin_cases i <;> simp [C,B,Function.update_apply,ctrl.injective.eq_iff,roleSplitControls,
          empty,nonzero,canonicalBits_symbols,ctrl] <;> first | rfl | apply empty <;> decide | change bitSymbol true :: S.R (ctrl 1) = binSyms 1 1; rw [empty _ (nonzero 1)]; rfl)
  exact ⟨_,Exec.seq push mark,repr⟩

theorem intervalPrepare_exec {P U : Type} {Q : ℕ} (body : P → Pr P intervalSplitTapes Q prime U)
    (m : ℕ) (u : HS intervalSplitTapes Q prime U) (S : Stacks intervalSplitTapes prime)
    (size : (S.R 0).length = m*142080) (left : ∀ i, S.L i = [])
    (empty : ∀ i, i ≠ 0 → S.R i = []) :
    ∃ z D t, z.user = u.user ∧ t ≤ 4*(m*142080)+23*m+18 ∧
      Exec body intervalPrepare (mk u S) t (mk z D) ∧
      RepT (CyclicRowSplit.bank (CyclicRowCopy.bank (putWord (fun _ => blank) 0 (S.R 0))
        (fun _ _ => blank) 0 (fun _ => 0) (FlatCoordinateSchedule.bits 1))
        (FlatCoordinateSchedule.bits m)) D.L D.R := by
  obtain ⟨z,t,user,time,count⟩ := intervalCounter_exec body intervalCounterPorts m u S size
    (fun i hi => empty _ (intervalCounterPorts.injective.ne hi))
  obtain ⟨D,mark,ready⟩ := intervalMarkers_exec body m z S left empty
  exact ⟨z,D,_,user,by omega,Exec.seq count mark,ready⟩

/-- Allocate the zero helper at port zero and initialize the splitter on the
successor ports in a single pass over the payload. -/
theorem intervalPrepareHelper_exec {P U : Type} {Q m : ℕ}
    (body : P → Pr P (intervalSplitTapes+1) Q prime U) (u : HS (intervalSplitTapes+1) Q prime U)
    (S : Stacks (intervalSplitTapes+1) prime) (size : (S.R (Fin.succ 0)).length = m*142080)
    (left : ∀ i, S.L i = []) (empty : ∀ i, i ≠ Fin.succ 0 → S.R i = []) :
    let r := intervalCounterPorts.trans (Fin.succEmb _)
    let init := (intervalHeaders r).seq (moveR (r 1) 0 (fun _ => bitSymbol false))
    ∃ z F t, z.user = u.user ∧ t ≤ 4*(m*142080)+23*m+18 ∧
      Exec body (init.seq (embProg Fin.succ (Empty.elim : Empty → P) intervalMarkers)) (mk u S) t (mk z F) ∧
      F.L 0 = [] ∧ F.R 0 = List.replicate m (bitSymbol false) ∧
      RepT (CyclicRowSplit.bank (CyclicRowCopy.bank (putWord (fun _ => blank) 0 (S.R (Fin.succ 0)))
        (fun _ _ => blank) 0 (fun _ => 0) (FlatCoordinateSchedule.bits 1)) (FlatCoordinateSchedule.bits m))
        (embStk Fin.succ F).L (embStk Fin.succ F).R := by
  intro r init
  have apart (i) : (0 : Fin (intervalSplitTapes+1)) ≠ r i := Ne.symm (Fin.succ_ne_zero _)
  obtain ⟨v,t,user,time,fill⟩ := intervalHeadersHelper_exec body r 0 apart m u S size
    (fun i hi => empty _ (r.injective.ne hi)) (empty _ (Ne.symm (Fin.succ_ne_zero _)))
  let B := {S with R := Function.update (Function.update S.R (r 2) ((FlatCoordinateSchedule.bits m).map bitSymbol)) 0 (List.replicate m (bitSymbol false))}
  let small := embStk Fin.succ S
  obtain ⟨D,mark,ready⟩ := intervalMarkers_exec (P := Empty) Empty.elim m (embDn Fin.succ v) small
    (fun i => left _) (fun i hi => empty _ (Fin.succ_injective _ |>.ne hi))
  have view : embStk Fin.succ B = {small with R := Function.update small.R (roleSplitControls 142080 3) ((FlatCoordinateSchedule.bits m).map bitSymbol)} := by
    unfold embStk
    congr 1
    funext j
    change Function.update (Function.update S.R (r 2) ((FlatCoordinateSchedule.bits m).map bitSymbol)) (0 : Fin (intervalSplitTapes+1)) (List.replicate m (bitSymbol false)) j.succ = _
    rw [Function.update_of_ne (Fin.succ_ne_zero _)]
    change Function.update S.R (roleSplitControls 142080 3).succ ((FlatCoordinateSchedule.bits m).map bitSymbol) j.succ = _
    by_cases eq : j = roleSplitControls 142080 3 <;> simp [eq,small,embStk,Function.comp_apply]
  obtain ⟨z,F,run,_,zu,slice,off⟩ := exec_emb (body' := body) (ι := Empty.elim)
    (Fin.succ_injective _) (fun f => f.elim) mark v rfl B view
  have keep := off 0 (fun i => Fin.succ_ne_zero i)
  refine ⟨z,F,_,zu.trans user,by omega,Exec.seq fill run,keep.1.trans (left _),?_,?_⟩
  · simp [keep.2,B]
  · rw [slice]; exact ready

/-- Split an inherited payload starting with empty workspace. The host bill includes
both counter generation and the simulation of every splitter transition. -/
theorem intervalSplit_exec {P U : Type} {Q m : ℕ}
    (body : P → Pr P intervalSplitTapes Q prime U)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    (positive : 0 < m) (x : Fin (m*142080) → Fin (prime+4))
    (u : HS intervalSplitTapes Q prime U) (S : Stacks intervalSplitTapes prime)
    (source : S.R 0 = List.ofFn x) (left : ∀ i, S.L i = [])
    (empty : ∀ i, i ≠ 0 → S.R i = []) :
    let bs := FlatCoordinateSchedule.bits 1
    let gs := FlatCoordinateSchedule.bits m
    let src := putWord (fun _ => blank) 0 (List.ofFn x)
    let roles := fun j => putWord (fun _ => blank) 0 (List.ofFn fun i => x (finProdFinEquiv (i,j)))
    ∃ z F t, z.user = u.user ∧ t ≤ (149*(intervalSplitTapes+5)+5)*(m*142080)+24 ∧
      Exec body (intervalPrepare.seq (foreign (liftQ (CyclicRowNormalized.splitProgram 142080 prime) capacity)))
        (mk u S) t (mk z F) ∧ RepT (CyclicRowSplit.bank (CyclicRowCopy.bank src roles 0 (fun _ => 0) bs) gs) F.L F.R := by
  intro bs gs src roles
  obtain ⟨v,D,k,user,time,prep,ready⟩ := intervalPrepare_exec body m u S (by simp [source]) left empty
  rw [source] at ready
  let rows := fun (i : Fin m) (j : Fin 142080) => [x (finProdFinEquiv (i,j))]
  have split := CyclicRowNormalized.split_hoare (fun _ => blank) (fun _ _ => blank) 0 (fun _ => 0)
    rows 1 (fun _ _ => rfl) bs gs (FlatCoordinateSchedule.bits_value _) (FlatCoordinateSchedule.bits_value _)
  obtain ⟨sx,px⟩ := singletonRows x
  change CyclicRowSplit.sourceWord rows = _ at sx
  change ∀ j, CyclicRowSplit.roleWord rows j = _ at px
  simp only [sx,px] at split
  obtain ⟨z,F,_,rfl,rep,same,_,_,_,t,paid,run⟩ := foreign_exec (body := body)
    (liftQ _ capacity) (HoareTime.liftQ capacity split) v _ _ rfl ready
  have bound := CyclicRowNormalized.cost_linear 1 bs gs (by decide : 0 < 142080) positive (by decide)
    (FlatCoordinateSchedule.bits_value _) (FlatCoordinateSchedule.bits_value _)
    (FlatCoordinateSchedule.bits_canonical _) (FlatCoordinateSchedule.bits_canonical _)
  rw [Nat.mul_one] at bound
  have scale := Nat.mul_le_mul_right (intervalSplitTapes+5) bound
  refine ⟨z,F,_,same.trans user,?_,Exec.seq prep run,rep⟩
  change t ≤ CyclicRowNormalized.cost 142080 m 1 bs gs*(intervalSplitTapes+5)+6 at paid
  dsimp only [intervalSplitTapes] at *
  omega

/-- Execute a host worker on the separated roles and merge its output into
the original payload tape, charging the worker's own price exactly once. -/
theorem intervalWorkerSpace_exec {P U : Type} {Q m b : ℕ}
    (body : P → Pr P intervalSplitTapes Q prime U) (worker : Pr P intervalSplitTapes Q prime U)
    (returned : Stacks intervalSplitTapes prime → Prop)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    (positive : 0 < m) (x y : Fin (m*142080) → Fin (prime+4))
    (u : HS intervalSplitTapes Q prime U) (S : Stacks intervalSplitTapes prime)
    (source : S.R 0 = List.ofFn x) (left : ∀ i, S.L i = [])
    (empty : ∀ i, i ≠ 0 → S.R i = []) :
    let src := fun (word : Fin (m*142080) → Fin (prime+4)) => putWord (fun _ => blank) 0 (List.ofFn word)
    let bank := fun dest (word : Fin (m*142080) → Fin (prime+4)) =>
      CyclicRowSplit.bank (CyclicRowCopy.bank dest
        (fun j => putWord (fun _ => blank) 0 (List.ofFn fun i => word (finProdFinEquiv (i,j))))
        0 (fun _ => 0) (FlatCoordinateSchedule.bits 1)) (FlatCoordinateSchedule.bits m)
    (∀ (v : HS intervalSplitTapes Q prime U) (D : Stacks intervalSplitTapes prime), RepT (bank (src x) x) D.L D.R →
      ∃ (w : HS intervalSplitTapes Q prime U) (E : Stacks intervalSplitTapes prime) (k : ℕ), w.user = v.user ∧ k ≤ b ∧ Exec body worker (mk v D) k (mk w E) ∧ RepT (bank (src x) y) E.L E.R ∧
        returned E) →
    ∃ z F t, z.user = u.user ∧ t ≤ (298*(intervalSplitTapes+5)+5)*(m*142080)+b+30 ∧
      Exec body ((intervalPrepare.seq (foreign (liftQ (CyclicRowNormalized.splitProgram 142080 prime) capacity))).seq
        (worker.seq (foreign (liftQ (CyclicRowNormalized.mergeProgram 142080 prime) capacity))))
        (mk u S) t (mk z F) ∧ RepT (bank (src y) y) F.L F.R ∧
      ∃ E, returned E ∧ ∀ j, (F.L j).length+(F.R j).length ≤ (E.L j).length+(E.R j).length+298*(m*142080) := by
  intro src bank inner
  obtain ⟨v,D,s,vu,st,split,parts⟩ := intervalSplit_exec body capacity positive x u S source left empty
  obtain ⟨w,E,k,wu,kt,run,ready,room⟩ := inner v D parts
  let rows := fun (i : Fin m) (j : Fin 142080) => [y (finProdFinEquiv (i,j))]
  let bs := FlatCoordinateSchedule.bits 1
  let gs := FlatCoordinateSchedule.bits m
  have merge := CyclicRowNormalized.merge_hoare (src x) (fun _ _ => blank) 0 (fun _ => 0)
    rows 1 (fun _ _ => rfl) bs gs (FlatCoordinateSchedule.bits_value _) (FlatCoordinateSchedule.bits_value _)
  obtain ⟨sy,py⟩ := singletonRows y
  change CyclicRowSplit.sourceWord rows = _ at sy
  change ∀ j, CyclicRowSplit.roleWord rows j = _ at py
  have overwrite : putWord (src x) 0 (List.ofFn y) = src y :=
    FlatControlledShiftArray.overwrite _ _ _ _ (by simp)
  simp only [sy,py,overwrite] at merge
  obtain ⟨z,F,_,rfl,rep,zu,_,_,growth,t,paid,finish⟩ := foreign_exec (body := body)
    (liftQ _ capacity) (HoareTime.liftQ capacity merge) w _ _ rfl ready
  have bound := CyclicRowNormalized.cost_linear 1 bs gs (by decide : 0 < 142080) positive (by decide)
    (FlatCoordinateSchedule.bits_value _) (FlatCoordinateSchedule.bits_value _)
    (FlatCoordinateSchedule.bits_canonical _) (FlatCoordinateSchedule.bits_canonical _)
  rw [Nat.mul_one] at bound
  have scale := Nat.mul_le_mul_right (intervalSplitTapes+5) bound
  refine ⟨z,F,_,zu.trans (wu.trans vu),?_,Exec.seq split (Exec.seq run finish),rep,?_⟩
  · change t ≤ CyclicRowNormalized.cost 142080 m 1 bs gs*(intervalSplitTapes+5)+6 at paid
    dsimp only [intervalSplitTapes] at *
    omega
  · refine ⟨E,room,fun j => ?_⟩
    have h := growth j
    omega

theorem intervalWorker_exec {P U : Type} {Q m b : ℕ}
    (body : P → Pr P intervalSplitTapes Q prime U) (worker : Pr P intervalSplitTapes Q prime U)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    (positive : 0 < m) (x y : Fin (m*142080) → Fin (prime+4))
    (u : HS intervalSplitTapes Q prime U) (S : Stacks intervalSplitTapes prime)
    (source : S.R 0 = List.ofFn x) (left : ∀ i, S.L i = [])
    (empty : ∀ i, i ≠ 0 → S.R i = []) :
    let src := fun (word : Fin (m*142080) → Fin (prime+4)) => putWord (fun _ => blank) 0 (List.ofFn word)
    let bank := fun dest (word : Fin (m*142080) → Fin (prime+4)) =>
      CyclicRowSplit.bank (CyclicRowCopy.bank dest
        (fun j => putWord (fun _ => blank) 0 (List.ofFn fun i => word (finProdFinEquiv (i,j))))
        0 (fun _ => 0) (FlatCoordinateSchedule.bits 1)) (FlatCoordinateSchedule.bits m)
    (∀ (v : HS intervalSplitTapes Q prime U) (D : Stacks intervalSplitTapes prime), RepT (bank (src x) x) D.L D.R →
      ∃ (w : HS intervalSplitTapes Q prime U) (E : Stacks intervalSplitTapes prime) (k : ℕ), w.user = v.user ∧ k ≤ b ∧ Exec body worker (mk v D) k (mk w E) ∧ RepT (bank (src x) y) E.L E.R) →
    ∃ z F t, z.user = u.user ∧ t ≤ (298*(intervalSplitTapes+5)+5)*(m*142080)+b+30 ∧
      Exec body ((intervalPrepare.seq (foreign (liftQ (CyclicRowNormalized.splitProgram 142080 prime) capacity))).seq
        (worker.seq (foreign (liftQ (CyclicRowNormalized.mergeProgram 142080 prime) capacity))))
        (mk u S) t (mk z F) ∧ RepT (bank (src y) y) F.L F.R := by
  intro src bank inner
  obtain ⟨z,F,t,user,paid,run,out,_⟩ := intervalWorkerSpace_exec body worker (fun _ => True)
    capacity positive x y u S source left empty (by
      intro v D ready
      obtain ⟨w,E,k,same,time,exec,rep⟩ := inner v D ready
      exact ⟨w,E,k,same,time,exec,rep,trivial⟩)
  exact ⟨z,F,t,user,paid,run,out⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
