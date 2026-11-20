module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackPivotStream
public import IntegerMultBounds.MathlibTM2.Cover.FallbackPhysicalLabel
public import IntegerMultBounds.MathlibTM2.Cover.LabelSpectators
public import IntegerMultBounds.MathlibTM2.Cover.LabelPadProgram
public import IntegerMultBounds.MathlibTM2.Cover.FallbackShearCleanup

/-! Generate both selector streams for the classified scan on shared residue counters. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host LabelTraversal
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

noncomputable def residualSchedule {A d : ℕ} (C : Matrix (Fin d) (Fin d) (ZMod prime)) :
    List (Fin (A+4)) :=
  let rows := classPivots C
  bitSymbol (negativeAnchor rows C) :: (scheduleCode rows ++ orderedScheduleCode (List.finRange d).reverse rows)

/-- The exceptional branch reads its sign followed by both pivot schedules.
The other branches leave this queue in place. -/
theorem fallbackSchedule_writes {T Q A m d r : ℕ} {P U : Type} (body : P → Pr P T Q A U)
    (hr : r ≤ m) (request : Matrix (Fin m) (Fin m) (ZMod prime))
    (table : Matrix (Fin m) (Fin m) (ZMod prime) → Matrix (Fin d) (Fin d) (ZMod prime))
    (rs : List (Pair T)) (size : rs.length = m*m) (out count saved : Fin T)
    (regs : (count :: saved :: (slots rs ++ [out])).Nodup) :
    ∃ program : Pr P T Q A U, ∀ (v : RecursiveInterchangeLayout.Descriptor) (w B : ℕ)
      (proj : LabelPadding.Label m (w+1)), (LabelRing.res prime (w+1) (by omega)).mapMatrix proj = request →
      v.beforeH = B*prime^(m*((w+1)*m)) →
      Writes body (fun R => ready (prime^w) R rs ∧ R saved = [] ∧
        (R count).length = v.beforeRows*v.rows*B) out program
        ((List.range (LabelMask.records v)).flatMap fun j =>
          if fallbackBit hr proj (physicalLabel m (w+1) j) then
            residualSchedule (table (LabelStock.residue m (w+1) 1 j))
          else [])
        ((v.beforeRows*v.rows*B)*(time (prime^w) (m*m) 1+5)+4) := by
  classical
  let emit := fun g : Matrix (Fin m) (Fin m) (ZMod prime) =>
    if decide (g.det ≠ 0) && !LabelProjector.good request r hr g then
      residualSchedule (A := A) (table g)
    else []
  obtain ⟨program,run⟩ := recordWords_writes (body := body) m
    (fun a => emit (LabelSelectors.matrix m a)) rs size out count saved regs
  refine ⟨program,?_⟩
  intro v w B proj reduction shape
  simpa only [LabelSelectors.recordMap,LabelSelectors.residue_eq,List.flatMap_def,emit,
    fallbackBit_eq (by omega : 0 < w+1),reduction,LabelStock.live,Nat.add_one_sub_one] using
    run v (w+1) B (by omega) shape

/-- Each residue digit uses one counter in each half of a private tape interval. -/
def residuePairs {k : ℕ} (n : ℕ) (room : n+n ≤ k) : List (Pair (66+k)) :=
  (List.finRange n).map fun i =>
    ((i.castAdd n |>.castLE room).natAdd 66, (i.natAdd n |>.castLE room).natAdd 66)

theorem residuePairs_layout {k n : ℕ} (room : n+n ≤ k) :
    let rs := residuePairs n room
    rs.length = n ∧ (slots rs).Nodup ∧ ∀ j ∈ slots rs, 66 ≤ j.val := by
  intro rs
  let a := ((Fin.castAddEmb (n := n) n).trans (Fin.castLEEmb room)).trans (Fin.natAddEmb 66)
  let b := ((Fin.natAddEmb n (m := n)).trans (Fin.castLEEmb room)).trans (Fin.natAddEmb 66)
  have apart (i j : Fin n) : a i ≠ b j := by
    intro eq
    have h := congrArg Fin.val eq
    change 66+i.val = 66+(n+j.val) at h
    omega
  have cells : slots rs = (List.finRange n).flatMap fun i => [a i,b i] := by
    simp [rs,residuePairs,slots,List.flatMap_map,a,b]
  refine ⟨by simp [rs,residuePairs],?_,?_⟩
  · rw [cells,List.nodup_flatMap]
    refine ⟨fun i _ => by simp [apart],(List.nodup_finRange n).imp ?_⟩
    intro i j h
    simp [Function.onFun,List.disjoint_left,a.injective.ne h,b.injective.ne h,apart,fun i j => (apart i j).symm]
  · intro j hj
    rw [cells] at hj
    obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp hj
    rcases (by simpa using hi : j = a i ∨ j = b i) with rfl | rfl <;>
      exact Nat.le_add_right _ _

theorem recordMasks_exec {T Q A m r : ℕ} {P U : Type} (body : P → Pr P T Q A U)
    (hr : r ≤ m) (request : Matrix (Fin m) (Fin m) (ZMod prime))
    (rs : List (Pair T)) (size : rs.length = m*m) (mask mode parents saved : Fin T)
    (apart : mask ≠ mode) (maskRegs : (parents :: saved :: (slots rs ++ [mask])).Nodup)
    (modeRegs : (parents :: saved :: (slots rs ++ [mode])).Nodup) :
    ∃ program : Pr P T Q A U, ∀ (v : RecursiveInterchangeLayout.Descriptor) (w B : ℕ)
      (proj : LabelPadding.Label m (w+1)), (LabelRing.res prime (w+1) (by omega)).mapMatrix proj = request →
      v.beforeH = B*prime^(m*((w+1)*m)) →
      ∀ (u : HS T Q A U) (S : Stacks T A), ready (prime^w) S.R rs → S.R saved = [] →
      (S.R parents).length = v.beforeRows*v.rows*B → S.R mask = [] → S.R mode = [] →
      let labels := List.range (LabelMask.records v)
      let live := labels.map fun i => bitSymbol (a := A) (LabelStock.live m (w+1) 1 i)
      let bad := labels.map fun i => bitSymbol (a := A) (fallbackBit hr proj (physicalLabel m (w+1) i))
      ∃ z n, z.user = u.user ∧ n ≤ 2*((6+10*(m*m))*labels.length+4) ∧
        Exec body program (mk u S) n (mk z {S with R := Function.update (Function.update S.R mask live) mode bad}) := by
  obtain ⟨writeLive,hl⟩ := record_writes (body := body) m rs size mask parents saved maskRegs
  obtain ⟨writeBad,hb⟩ := fallbackMask_writes body r hr request rs size mode parents saved modeRegs
  refine ⟨writeLive.seq writeBad,?_⟩
  intro v w B proj reduction shape u S radix scratch count freeMask freeMode labels live bad
  obtain ⟨y,n,hy,hn,emit⟩ := hl v (w+1) B (by omega) shape u S ⟨radix,scratch,count⟩
  simp only [freeMask,List.append_nil,LabelMask.selectors,List.map_map,Function.comp_def] at emit
  let R := Function.update S.R mask live
  have hp := (List.nodup_cons.mp maskRegs).1
  have hs := (List.nodup_cons.mp (List.nodup_cons.mp maskRegs).2).1
  have sep := (List.nodup_append.mp (List.nodup_cons.mp (List.nodup_cons.mp maskRegs).2).2).2.2
  have keep (k : Fin T) (hk : k ∈ slots rs) : R k = S.R k :=
    Function.update_of_ne (sep k hk mask (by simp)) _ _
  have radix' : ready (prime^w) R rs := by
    intro pair h
    rw [keep _ (List.mem_flatMap.mpr ⟨pair,h,by simp⟩),keep _ (List.mem_flatMap.mpr ⟨pair,h,by simp⟩)]
    exact radix pair h
  have savedOff : saved ≠ mask := by rintro rfl; exact hs (by simp)
  have parentsOff : parents ≠ mask := by rintro rfl; exact hp (by simp)
  obtain ⟨z,t,hz,ht,emitBad⟩ := hb v w B proj reduction shape y {S with R := R}
    ⟨radix',(Function.update_of_ne savedOff ..).trans scratch,by simpa [R,parentsOff] using count⟩
  have empty : R mode = [] := (Function.update_of_ne apart.symm live S.R).trans freeMode
  simp only [empty,List.append_nil,List.map_map,Function.comp_def] at emitBad
  have bill := LabelPadProgram.selector_cost v m (w+1) B (by omega) shape
  simp only [Nat.add_sub_cancel] at bill hn
  refine ⟨z,n+t,hz.trans hy,?_,Exec.seq emit emitBad⟩
  simp only [labels,List.length_range]
  omega

/-- Generate the exceptional schedules and both selectors with a single
initialized residue bank and parent counter. -/
theorem recordControls_exec {T Q A m r d : ℕ} {P U : Type} (body : P → Pr P T Q A U)
    (hr : r ≤ m) (request : Matrix (Fin m) (Fin m) (ZMod prime))
    (table : Matrix (Fin m) (Fin m) (ZMod prime) → Matrix (Fin d) (Fin d) (ZMod prime))
    (rs : List (Pair T)) (size : rs.length = m*m) (queue mask mode parents saved : Fin T)
    (apart : mask ≠ mode) (mq : mask ≠ queue) (bq : mode ≠ queue)
    (regs : ∀ j ∈ [queue,mask,mode], (parents :: saved :: (slots rs ++ [j])).Nodup) :
    ∃ program : Pr P T Q A U, ∀ (v : RecursiveInterchangeLayout.Descriptor) (w B : ℕ)
      (proj : LabelPadding.Label m (w+1)), (LabelRing.res prime (w+1) (by omega)).mapMatrix proj = request →
      v.beforeH = B*prime^(m*((w+1)*m)) →
      ∀ (u : HS T Q A U) (S : Stacks T A), ready (prime^w) S.R rs → S.R saved = [] →
      (S.R parents).length = v.beforeRows*v.rows*B → S.R queue = [] → S.R mask = [] → S.R mode = [] →
      let labels := List.range (LabelMask.records v)
      let bad := fun j => fallbackBit hr proj (physicalLabel m (w+1) j)
      let codes := labels.flatMap fun j => if bad j then residualSchedule (A := A) (table (LabelStock.residue m (w+1) 1 j)) else []
      let live := labels.map fun j => bitSymbol (a := A) (LabelStock.live m (w+1) 1 j)
      let modes := labels.map fun j => bitSymbol (a := A) (bad j)
      ∃ z n, z.user = u.user ∧ n ≤ 3*((6+10*(m*m))*labels.length+4) ∧
        Exec body program (mk u S) n (mk z {S with R := Function.update (Function.update (Function.update S.R queue codes) mask live) mode modes}) := by
  have qr := regs queue (by simp)
  obtain ⟨schedule,write⟩ := fallbackSchedule_writes body hr request table rs size queue parents saved qr
  obtain ⟨masks,select⟩ := recordMasks_exec body hr request rs size mask mode parents saved apart
    (regs mask (by simp)) (regs mode (by simp))
  refine ⟨schedule.seq masks,?_⟩
  intro v w B proj reduction shape u S radix scratch count blank emptyMask emptyMode labels bad codes live modes
  obtain ⟨y,n,user,time,run⟩ := write v w B proj reduction shape u S ⟨radix,scratch,count⟩
  simp only [blank,List.append_nil] at run
  let D := {S with R := Function.update S.R queue codes}
  have sep := (List.nodup_append.mp qr.tail.tail).2.2
  have keep (i) (hi : i ∈ slots rs) : D.R i = S.R i := Function.update_of_ne (sep i hi queue (by simp)) _ _
  have readyD : ready (prime^w) D.R rs := by
    intro pair h
    rw [keep _ (List.mem_flatMap.mpr ⟨pair,h,by simp⟩),keep _ (List.mem_flatMap.mpr ⟨pair,h,by simp⟩)]
    exact radix pair h
  have savedOff : saved ≠ queue := by rintro rfl; exact qr.tail.notMem (by simp)
  have parentsOff : parents ≠ queue := by rintro rfl; exact qr.notMem (by simp)
  obtain ⟨z,t,hz,ht,dispatch⟩ := select v w B proj reduction shape y D readyD
    ((Function.update_of_ne savedOff ..).trans scratch) (by simpa [D,parentsOff] using count)
    ((Function.update_of_ne mq ..).trans emptyMask) ((Function.update_of_ne bq ..).trans emptyMode)
  have traversal := LabelPadProgram.selector_cost v m (w+1) B (by omega) shape
  simp only [Nat.add_one_sub_one] at traversal
  simp only [List.length_range] at ht
  refine ⟨z,n+t,hz.trans user,?_,Exec.seq run dispatch⟩
  simp only [labels,List.length_range]
  omega

/-- The directory reader needs one more digit than the reciprocal clock.
Borrow the clock for the read and restore it before computing the reciprocal. -/
def readWithSuccessorClock {T Q A : ℕ} {P U : Type} (clock : Fin T) (reader : Pr P T Q A U) : Pr P T Q A U :=
  Prog.seq (.act (.push (.rt clock) (fun _ => Node.tick) .done)) (reader.seq (.act (Node.dropTop clock .done)))

open LabelTraversal in
theorem readWithSuccessorClock_writes {T Q A : ℕ} {P U : Type} (body : P → Pr P T Q A U)
    (clock dst : Fin T) (apart : clock ≠ dst) (ok : Node.Regs T A → Prop)
    (reader : Pr P T Q A U) (word : List (Fin (A+4))) (cost : ℕ)
    (read : Writes body ok dst reader word cost) :
    Writes body (fun R => ok (Function.update R clock (Node.tick :: R clock))) dst
      (readWithSuccessorClock clock reader) word (1+(cost+1)) := by
  intro u S ready
  let D := {S with R := Function.update S.R clock (Node.tick :: S.R clock)}
  have push : Exec body (.act (.push (.rt clock) (fun _ => Node.tick) .done)) (mk u S) 1 (mk u D) := by
    simpa [D,Action.run,update_rt] using Exec.act (body := body) (.push (.rt clock) (fun _ => Node.tick) .done) (mk u S)
  obtain ⟨y,n,hy,hn,run⟩ := read u D ready
  let E := {D with R := Function.update D.R dst (word ++ D.R dst)}
  have pop := Exec.act (body := body) (Node.dropTop clock .done) (mk y E)
  refine ⟨y,1+(n+1),hy,by omega,Exec.seq push (Exec.seq run ?_)⟩
  have restore (xs) : Function.update (Function.update S.R dst xs) clock (S.R clock) = Function.update S.R dst xs := by
    funext i; by_cases h : i = clock <;> simp [h,apart]
  simpa [restore,E,D,Node.dropTop,Action.run,update_rt,Function.update_comm apart,apart,apart.symm] using pop

/-- Count spectator prefixes from the three directory dimensions and the exponent clock. -/
noncomputable def parentCounter {T Q A : ℕ} {P U : Type} (m : ℕ) (r : Fin 8 ↪ Fin T) : Pr P T Q A U :=
  if m = 0 then LabelSpectators.countRecords (r 0) (r 1) (r 2) (r 4) (r 5) (r 6) (r 7)
  else readWithSuccessorClock (r 3) (LabelSpectators.program m (r 0) (r 1) (r 2) (r 3) (r 4) (r 5) (r 6) (r 7))

theorem parentCounter_exec {T Q A : ℕ} {P U : Type} (body : P → Pr P T Q A U) (m : ℕ) (r : Fin 8 ↪ Fin T)
    (v : RecursiveInterchangeLayout.Descriptor) (positive : v.Positive) (w B : ℕ)
    (shape : v.beforeH = B*prime^(m*((w+1)*m))) (u : HS T Q A U) (S : Stacks T A)
    (br : (S.R (r 0)).length = v.beforeRows) (rows : (S.R (r 1)).length = v.rows)
    (bh : (S.R (r 2)).length = v.beforeH) (clock : (S.R (r 3)).length = w)
    (fresh : ∀ k : Fin 8, 4 ≤ k → S.R (r k) = []) :
    ∃ z n, z.user = u.user ∧ n ≤ 44*LabelMask.records v+13*(w+1)+16 ∧
      Exec body (parentCounter m r) (mk u S) n (mk z {S with R := Function.update S.R (r 5) (List.replicate (v.beforeRows*v.rows*B) Node.tick)}) := by
  have empty : ∀ k ∈ [r 4,r 5,r 6,r 7], S.R k = [] := by
    intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> apply fresh <;> decide
  by_cases zero : m = 0
  · subst m
    simp at shape
    obtain ⟨z,n,user,cost,run⟩ := LabelSpectators.records_exec body _ _ _ _ _ _ _ (by simp) v positive u S br rows bh empty
    exact ⟨z,n,user,by omega,by simpa only [parentCounter,ite_true,LabelMask.records,shape] using run⟩
  · let ok := fun (R : Node.Regs T A) => (R (r 0)).length = v.beforeRows ∧ (R (r 1)).length = v.rows ∧
      (R (r 2)).length = v.beforeH ∧ (R (r 3)).length = w+1 ∧ ∀ k ∈ [r 4,r 5,r 6,r 7], R k = []
    have writer : Writes body ok (r 5) (LabelSpectators.program m (r 0) (r 1) (r 2) (r 3) (r 4) (r 5) (r 6) (r 7))
        (List.replicate (v.beforeRows*v.rows*B) Node.tick) (44*LabelMask.records v+13*(w+1)+14) := by
      intro y D ⟨a,b,c,t,e⟩
      obtain ⟨z,n,user,cost,run⟩ := LabelSpectators.runs body m (Nat.pos_of_ne_zero zero) _ _ _ _ _ _ _ _ (by simp)
        v positive (w+1) B shape y D a b c t e
      exact ⟨z,n,user,cost,by simpa only [e _ (by simp : r 5 ∈ [r 4,r 5,r 6,r 7]),List.append_nil] using run⟩
    obtain ⟨z,n,user,cost,run⟩ := readWithSuccessorClock_writes body (r 3) (r 5) (r.injective.ne (by decide)) ok _ _ _ writer u S
      (by refine ⟨?_,?_,?_,?_,?_⟩
          · simpa [r.injective.eq_iff] using br
          · simpa [r.injective.eq_iff] using rows
          · simpa [r.injective.eq_iff] using bh
          · simp [clock]
          · intro k hk
            have off : k ≠ r 3 := by rintro rfl; simp [r.injective.eq_iff] at hk
            simpa [off] using empty k hk)
    exact ⟨z,n,user,by omega,by simpa [parentCounter,zero,fresh 5 (by decide)] using run⟩

def parentCountPorts : Fin 8 ↪ Fin 66 := ⟨![29,30,31,45,63,50,64,65],by decide⟩

theorem parentCountPorts_scratch (k : Fin 8) (hk : 4 ≤ k) :
    parentCountPorts k = 50 ∨ 58 < (parentCountPorts k).val := by
  exact (by decide : ∀ k : Fin 8, 4 ≤ k → parentCountPorts k = 50 ∨ 58 < (parentCountPorts k).val) k hk

theorem countedRecordControls_exec {T Q A m d k : ℕ} {P U : Type} (body : P → Pr P T Q A U)
    (hd : d ≤ m) (request : Matrix (Fin m) (Fin m) (ZMod prime))
    (table : Matrix (Fin m) (Fin m) (ZMod prime) → Matrix (Fin k) (Fin k) (ZMod prime))
    (rs : List (Pair T)) (size : rs.length = m*m) (r : Fin 8 ↪ Fin T) (queue mask mode saved : Fin T)
    (apart : mask ≠ mode) (mq : mask ≠ queue) (bq : mode ≠ queue)
    (queueRegs : (r 5 :: saved :: (slots rs ++ [queue])).Nodup) (maskRegs : (r 5 :: saved :: (slots rs ++ [mask])).Nodup)
    (modeRegs : (r 5 :: saved :: (slots rs ++ [mode])).Nodup) :
    ∃ program : Pr P T Q A U, ∀ (v : RecursiveInterchangeLayout.Descriptor) (w B : ℕ)
      (proj : LabelPadding.Label m (w+1)), (LabelRing.res prime (w+1) (by omega)).mapMatrix proj = request →
      v.Positive → v.beforeH = B*prime^(m*((w+1)*m)) →
      ∀ (u : HS T Q A U) (S : Stacks T A), ready (prime^w) S.R rs → S.R saved = [] →
      (S.R (r 0)).length = v.beforeRows → (S.R (r 1)).length = v.rows → (S.R (r 2)).length = v.beforeH →
      (S.R (r 3)).length = w → (∀ k : Fin 8, 4 ≤ k → S.R (r k) = []) → S.R queue = [] → S.R mask = [] → S.R mode = [] →
      let labels := List.range (LabelMask.records v)
      let codes := labels.flatMap fun j => if fallbackBit hd proj (physicalLabel m (w+1) j) then residualSchedule (A := A) (table (LabelStock.residue m (w+1) 1 j)) else []
      let live := labels.map fun i => bitSymbol (a := A) (LabelStock.live m (w+1) 1 i)
      let bad := labels.map fun i => bitSymbol (a := A) (fallbackBit hd proj (physicalLabel m (w+1) i))
      ∃ z n, z.user = u.user ∧ n ≤ (44*labels.length+13*(w+1)+16) +
        3*((6+10*(m*m))*labels.length+4) + (2*(v.beforeRows*v.rows*B)+2) ∧
        Exec body program (mk u S) n (mk z {S with R := Function.update (Function.update (Function.update S.R queue codes) mask live) mode bad}) := by
  obtain ⟨writer,write⟩ := recordControls_exec body hd request table rs size queue mask mode (r 5) saved apart mq bq (by
    intro i hi; simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl <;> assumption)
  refine ⟨((parentCounter m r).seq writer).seq (bclear (r 5)),?_⟩
  intro v w B proj reduction positive shape u S radix scratch br rows bh clock fresh freeQueue freeMask freeMode labels codes live bad
  obtain ⟨y,n,user,time,prepare⟩ := parentCounter_exec body m r v positive w B shape u S br rows bh clock fresh
  let parents := List.replicate (v.beforeRows*v.rows*B) (Node.tick (A := A))
  let E := {S with R := Function.update S.R (r 5) parents}
  have outside := maskRegs.notMem
  have pq : r 5 ≠ queue := fun eq => queueRegs.notMem (by simp [eq])
  have pm : r 5 ≠ mask := fun eq => outside (by simp [eq])
  have pb : r 5 ≠ mode := fun eq => modeRegs.notMem (by simp [eq])
  have keep (i) (hi : i ∈ slots rs) : E.R i = S.R i :=
    Function.update_of_ne (fun (eq : i = r 5) => outside (by simp [eq ▸ hi])) _ _
  have radix' : ready (prime^w) E.R rs := by
    intro pair h
    rw [keep _ (List.mem_flatMap.mpr ⟨pair,h,by simp⟩),keep _ (List.mem_flatMap.mpr ⟨pair,h,by simp⟩)]
    exact radix pair h
  obtain ⟨x,t,hx,ht,emit⟩ := write v w B proj reduction shape y E radix'
    ((Function.update_of_ne (fun (eq : saved = r 5) => outside (by simp [eq])) _ _).trans scratch)
    (by simp [E,parents]) ((Function.update_of_ne pq.symm _ _).trans freeQueue) ((Function.update_of_ne pm.symm _ _).trans freeMask)
    ((Function.update_of_ne pb.symm _ _).trans freeMode)
  let D := {E with R := Function.update (Function.update (Function.update E.R queue codes) mask live) mode bad}
  obtain ⟨z,hz,_,clear⟩ := bclear_exec body (r 5) x D
  have len : (D.R (r 5)).length = v.beforeRows*v.rows*B := by simp [D,E,parents,pm,pb,pq]
  rw [len] at clear
  have frame : Function.update D.R (r 5) [] = Function.update (Function.update (Function.update S.R queue codes) mask live) mode bad := by
    funext i
    by_cases p : i = r 5
    · subst i; simp [pm,pb,pq,fresh 5 (by decide)]
    · by_cases a : i = mode <;> by_cases b : i = mask <;> by_cases q : i = queue <;> simp [D,E,Function.update_apply,p,a,b,q,apart,mq,bq,pm.symm,pb.symm,pq.symm]
  refine ⟨z,_,hz.trans (hx.trans user),Nat.add_le_add_right (Nat.add_le_add (by simpa [labels] using time) ht) _,
    Exec.seq (Exec.seq prepare emit) ?_⟩
  simpa only [frame] using clear

/-- Clear the traversal workspace before the record loop borrows it. The two
generated words are the only changes to the cleaned bank. -/
theorem clearAfterMasks_exec {T Q A : ℕ} {P U : Type} (body : P → Pr P T Q A U)
    (mask mode : Fin T) (is : List (Fin T)) (unique : is.Nodup) (hm : mask ∉ is) (hb : mode ∉ is)
    (live bad : List (Fin (A+4))) (u : HS T Q A U) (S : Stacks T A) :
    let setBits := fun (D : Stacks T A) => {D with R := Function.update (Function.update D.R mask live) mode bad}
    let clean := {S with L := fun i => if i ∈ is then [] else S.L i,
                         R := fun i => if i ∈ is then [] else S.R i}
    ∃ z, z.user = u.user ∧ Exec body (clearWorkTapes is) (mk u (setBits S))
      ((is.map fun i => 4*(S.L i).length+2*(S.R i).length+4).sum+1) (mk z (setBits clean)) := by
  intro setBits clean
  obtain ⟨z,user,run⟩ := clearWorkTapes_exec body is unique u (setBits S)
  have frame (i) (h : i ∈ is) : (setBits S).R i = S.R i := by
    have m : i ≠ mask := fun eq => hm (eq ▸ h)
    have b : i ≠ mode := fun eq => hb (eq ▸ h)
    simp [setBits,Function.update_of_ne,m,b]
  have cost := List.map_congr_left (l := is) (fun i hi => congrArg
    (fun xs : List (Fin (A+4)) => 4*(S.L i).length+2*xs.length+4) (frame i hi))
  rw [cost] at run
  refine ⟨z,user,?_⟩
  convert run using 2
  apply Stacks.ext <;> try rfl
  funext i
  by_cases h : i ∈ is
  · have m : i ≠ mask := fun eq => hm (eq ▸ h)
    have b : i ≠ mode := fun eq => hb (eq ▸ h)
    simp [setBits,clean,h,m,b]
  · by_cases b : i = mode
    · subst i; simp [setBits,clean,hb]
    · simp only [setBits,Function.update_of_ne b,clean,ite_eq_right h]
      by_cases m : i = mask <;> simp [m,h]

end IntegerMultBounds.MathlibTM2.Cover.Fallback
