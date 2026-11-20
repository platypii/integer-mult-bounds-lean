module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackPivotStream

/-! Scan the residual record queue in physical order, using one live bit per record. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
variable {T Q A : ℕ} {P U ι : Type}

def maskedScan (mask : Fin T) (live padding : Pr P T Q A U) : Pr P T Q A U :=
  let peek := Prog.act (peekR mask)
  let record := Prog.seq (.act (nextPivotBit mask)) (.cond (·.flag) live padding)
  .seq peek (.loop (·.flag) (.seq record peek))

theorem maskedScan_exec (body : P → Pr P T Q A U) (mask : Fin T)
    (live padding : Pr P T Q A U) (active : ι → Bool) (cost : ι → ℕ)
    (ready : List ι → Stacks T A → Prop)
    (step : ∀ i is (v : HS T Q A U) (S : Stacks T A), ready (i :: is) S →
      S.R mask = ((i :: is).map fun j => bitSymbol (active j)) →
      ∃ z F n, z.user = v.user ∧ ready is F ∧ F.R mask = (is.map fun j => bitSymbol (active j)) ∧
        n ≤ cost i ∧ Exec body (if active i then live else padding)
          (mk {v with flag := active i} {S with R := Function.update S.R mask (is.map fun j => bitSymbol (active j))})
          n (mk z F))
    (is : List ι) (v : HS T Q A U) (S : Stacks T A) (start : ready is S)
    (bits : S.R mask = is.map fun i => bitSymbol (active i)) :
    ∃ z F n, z.user = v.user ∧ ready [] F ∧ F.R mask = [] ∧
      n ≤ (is.map fun i => cost i + 4).sum + 2 ∧ Exec body (maskedScan mask live padding) (mk v S) n (mk z F) := by
  let record : Pr P T Q A U := .seq (.act (nextPivotBit mask)) (.cond (·.flag) live padding)
  let loop : Pr P T Q A U := .loop (·.flag) (.seq record (.act (peekR mask)))
  have run (u : HS T Q A U) (flag : u.flag = is.head?.isSome) :
      ∃ z F n, z.user = u.user ∧ ready [] F ∧ F.R mask = [] ∧
        n ≤ (is.map fun i => cost i + 4).sum + 1 ∧ Exec body loop (mk u S) n (mk z F) := by
    induction is generalizing S u with
    | nil => exact ⟨u,S,1,rfl,start,by simpa using bits,by simp,.loop_false (by simpa using flag)⟩
    | cons i is ih =>
      obtain ⟨y,D,l,hy,next,tail,hl,branch⟩ := step i is u S start bits
      have pop := Exec.act (body := body) (nextPivotBit mask) (mk u S)
      have one : Exec body record (mk u S) (1+(l+1)) (mk y D) := by
        cases h : active i <;> simp [nextPivotBit,Action.run,bits,h,update_rt] at pop <;> simp [h] at branch
        · exact .seq pop (.cond_false rfl branch)
        · exact .seq pop (.cond_true rfl branch)
      have peek := Exec.act (body := body) (peekR mask) (mk y D)
      rw [peekR_run,tail] at peek
      obtain ⟨z,F,n,hz,done,empty,hn,more⟩ := ih D next tail {y with flag := (is.map fun j => bitSymbol (a := A) (active j)).head?.isSome} (by cases is <;> rfl)
      exact ⟨z,F,_,hz.trans hy,done,empty,by simp only [List.map_cons,List.sum_cons]; omega,
        .loop_true (by simpa using flag) (.seq one peek) more⟩
  have peek := Exec.act (body := body) (peekR mask) (mk v S)
  rw [peekR_run,bits] at peek
  obtain ⟨z,F,n,hz,done,empty,hn,more⟩ := run {v with flag := (is.map fun i => bitSymbol (a := A) (active i)).head?.isSome}
    (by cases is <;> rfl)
  exact ⟨z,F,_,hz,done,empty,by omega,.seq peek more⟩

/-- Run the record branches on one payload, composing their mathematical effects in directory
order. The mask pop preserves the directory and payload representations. -/
theorem maskedPayloadScan_exec {W : Type} (body : P → Pr P T Q A U) (mask : Fin T)
    (live fallback : Pr P T Q A U) (active : ι → Bool) (cost : ι → ℕ)
    (ready : List ι → Stacks T A → Prop) (payload : W → Stacks T A → Prop)
    (effect : ι → W → W → Prop)
    (release : ∀ is word (S : Stacks T A) xs, ready is S → payload word S →
      let D := {S with R := Function.update S.R mask xs}
      ready is D ∧ payload word D)
    (step : ∀ i is word (v : HS T Q A U) (S : Stacks T A), ready (i :: is) S → payload word S →
      ∃ z D n next, z.user = v.user ∧ n ≤ cost i ∧
        Exec body (if active i then live else fallback) (mk v S) n (mk z D) ∧
        ready is D ∧ effect i word next ∧ payload next D ∧ D.R mask = S.R mask)
    (is : List ι) (word : W) (v : HS T Q A U) (S : Stacks T A)
    (start : ready is S) (input : payload word S)
    (bits : S.R mask = is.map fun i => bitSymbol (active i)) :
    ∃ z D n next, z.user = v.user ∧ n ≤ (is.map fun i => cost i + 4).sum + 2 ∧
      Exec body (maskedScan mask live fallback) (mk v S) n (mk z D) ∧
      ready [] D ∧ D.R mask = [] ∧ payload next D ∧
      is.foldr (fun i rest x => ∃ y, effect i x y ∧ rest y) (· = next) word := by
  let chain := fun (js : List ι) (x y : W) =>
    js.foldr (fun i rest a => ∃ b, effect i a b ∧ rest b) (· = y) x
  let inv := fun remaining (B : Stacks T A) => ready remaining B ∧
    ∃ current : W, payload current B ∧ ∀ final, chain remaining current final → chain is word final
  obtain ⟨z,D,n,user,done,empty,time,run⟩ := maskedScan_exec body mask live fallback active cost inv
    (by
      intro i js u B h _
      obtain ⟨r,x,px,cont⟩ := h
      let xs := js.map fun j => bitSymbol (a := A) (active j)
      obtain ⟨rr,pp⟩ := release _ x B xs r px
      obtain ⟨y,E,t,b,uy,ht,exec,re,eb,pb,maskFrame⟩ := step i js x {u with flag := active i} _ rr pp
      exact ⟨y,E,t,uy,⟨re,b,pb,fun final suffix => cont final ⟨b,eb,suffix⟩⟩,
        maskFrame.trans (Function.update_self ..),ht,exec⟩)
    is v S ⟨start,word,input,fun _ h => h⟩ bits
  obtain ⟨r,x,px,cont⟩ := done
  exact ⟨z,D,n,x,user,time,run,r,empty,px,cont x rfl⟩

/-- Index the tape invariant by the number of records already consumed. The branch
sees the remaining mask after dispatch and must retain it for the next iteration. -/
theorem maskedRange_exec (body : P → Pr P T Q A U) (mask : Fin T) (live padding : Pr P T Q A U)
    (records : ℕ) (active : ℕ → Bool) (cost : ℕ → ℕ) (ready : ℕ → Stacks T A → Prop)
    (release : ∀ j S bits, ready j S → ready j {S with R := Function.update S.R mask bits})
    (step : ∀ j, j < records → ∀ (v : HS T Q A U) (S : Stacks T A), ready j S →
      ∃ z F n, z.user = v.user ∧ ready (j+1) F ∧ F.R mask = S.R mask ∧ n ≤ cost j ∧
        Exec body (if active j then live else padding) (mk v S) n (mk z F))
    (v : HS T Q A U) (S : Stacks T A) (start : ready 0 S)
    (bits : S.R mask = (List.range records).map fun j => bitSymbol (active j)) :
    ∃ z F n, z.user = v.user ∧ ready records F ∧ F.R mask = [] ∧
      n ≤ ((List.range records).map fun j => cost j + 4).sum + 2 ∧
      Exec body (maskedScan mask live padding) (mk v S) n (mk z F) := by
  let inv := fun (is : List ℕ) (D : Stacks T A) =>
    ∃ j ≤ records, is = (List.range records).drop j ∧ ready j D
  have advance (i : ℕ) (is : List ℕ) (u : HS T Q A U) (D : Stacks T A) (h : inv (i :: is) D)
      (_ : D.R mask = ((i :: is).map fun j => bitSymbol (active j))) :
      ∃ z F n, z.user = u.user ∧ inv is F ∧ F.R mask = (is.map fun j => bitSymbol (active j)) ∧ n ≤ cost i ∧
        Exec body (if active i then live else padding)
          (mk {u with flag := active i} {D with R := Function.update D.R mask (is.map fun j => bitSymbol (active j))})
          n (mk z F) := by
    obtain ⟨j,hj,eq,current⟩ := h
    have len := congrArg List.length eq
    simp only [List.length_cons,List.length_drop,List.length_range] at len
    have inside : j < records := by omega
    have lo : j < (List.range records).length := by simpa using inside
    have split := eq.trans (List.getElem_cons_drop lo).symm
    simp only [List.getElem_range,List.cons.injEq] at split
    obtain ⟨rfl,suffix⟩ := split
    let tail := is.map fun k => bitSymbol (a := A) (active k)
    obtain ⟨z,F,n,hz,next,keep,hn,run⟩ := step i inside {u with flag := active i}
      {D with R := Function.update D.R mask tail} (release i D tail current)
    have done : inv is F := ⟨i+1,inside,suffix,next⟩
    exact ⟨z,F,n,hz,done,keep.trans (Function.update_self ..),hn,run⟩
  obtain ⟨z,F,n,hz,⟨j,hj,eq,done⟩,empty,hn,run⟩ :=
    maskedScan_exec body mask live padding active cost inv advance (List.range records) v S
      ⟨0,Nat.zero_le _,by simp,start⟩ bits
  have len := congrArg List.length eq
  simp only [List.length_nil,List.length_drop,List.length_range] at len
  obtain rfl : j = records := by omega
  exact ⟨z,F,n,hz,done,empty,hn,run⟩

/-- Consume one fallback bit even on padding, so both selector tapes advance
in physical record order. -/
def classifiedScan (liveMask fallbackMask : Fin T) (good fallback padding : Pr P T Q A U) :
    Pr P T Q A U :=
  maskedScan liveMask (.seq (.act (nextPivotBit fallbackMask)) (.cond (·.flag) fallback good))
    (.seq (.act (nextPivotBit fallbackMask)) padding)

/-- Transport one payload through the three classified branches, consuming both selector streams. -/
theorem classifiedPayloadScan_exec {W : Type} (body : P → Pr P T Q A U) (mask mode : Fin T)
    (apart : mask ≠ mode) (good fallback padding : Pr P T Q A U) (live bad : ι → Bool)
    (cost : ι → ℕ) (ready : List ι → Stacks T A → Prop) (payload : W → Stacks T A → Prop)
    (effect : ι → W → W → Prop)
    (release : ∀ k, k = mask ∨ k = mode → ∀ is word (S : Stacks T A) xs, ready is S → payload word S →
      let B := {S with R := Function.update S.R k xs}
      ready is B ∧ payload word B)
    (step : ∀ i is word (u : HS T Q A U) (S : Stacks T A), ready (i :: is) S → payload word S →
      ∃ z D n next, z.user = u.user ∧ n ≤ cost i ∧
        Exec body (if live i then (if bad i then fallback else good) else padding) (mk u S) n (mk z D) ∧
        ready is D ∧ effect i word next ∧ payload next D ∧ D.R mask = S.R mask ∧ D.R mode = S.R mode)
    (is : List ι) (word : W) (u : HS T Q A U) (S : Stacks T A) (start : ready is S) (input : payload word S)
    (liveBits : S.R mask = is.map fun j => bitSymbol (live j)) (badBits : S.R mode = is.map fun j => bitSymbol (bad j)) :
    ∃ z D n next, z.user = u.user ∧ n ≤ (is.map fun i => cost i+2+4).sum+2 ∧
      Exec body (classifiedScan mask mode good fallback padding) (mk u S) n (mk z D) ∧
      (ready [] D ∧ D.R mode = []) ∧ D.R mask = [] ∧ payload next D ∧
      is.foldr (fun i rest x => ∃ y, effect i x y ∧ rest y) (· = next) word := by
  let modes := fun (js : List ι) => js.map fun i => bitSymbol (a := A) (bad i)
  apply maskedPayloadScan_exec body mask _ _ live (fun i => cost i+2)
    (fun js B => ready js B ∧ B.R mode = modes js) payload effect _ _ is word u S ⟨start,badBits⟩ input liveBits
  · intro js x B xs h p
    obtain ⟨r,q⟩ := release mask (Or.inl rfl) js x B xs h.1 p
    exact ⟨⟨r,(Function.update_of_ne apart.symm xs B.R).trans h.2⟩,q⟩
  · intro i js x v B current px
    let rest := modes js
    let E := {B with R := Function.update B.R mode rest}
    let y := {v with flag := bad i}
    have bit : B.R mode = bitSymbol (bad i) :: rest := current.2
    have pop : Exec body (.act (nextPivotBit mode)) (mk v B) 1 (mk y E) := by
      simpa [nextPivotBit,Action.run,bit,update_rt,y,E] using Exec.act (body := body) (nextPivotBit mode) (mk v B)
    obtain ⟨r,p⟩ := release mode (Or.inr rfl) _ x B rest current.1 px
    obtain ⟨z,D,n,next,user,time,run,rdy,eff,pay,hm,hb⟩ := step i js x y E r p
    have frame : E.R mask = B.R mask := Function.update_of_ne apart rest B.R
    have endMode : D.R mode = rest := hb.trans (Function.update_self mode rest B.R)
    cases hl : live i <;> simp only [hl,Bool.false_eq_true,ite_false,ite_true] at run ⊢
    · exact ⟨z,D,_,next,user,by omega,Exec.seq pop run,⟨rdy,endMode⟩,eff,pay,hm.trans frame⟩
    · cases h : bad i <;> simp only [h,Bool.false_eq_true,ite_false,ite_true] at run
      · exact ⟨z,D,_,next,user,by omega,Exec.seq pop (.cond_false h run),⟨rdy,endMode⟩,eff,pay,hm.trans frame⟩
      · exact ⟨z,D,_,next,user,by omega,Exec.seq pop (.cond_true h run),⟨rdy,endMode⟩,eff,pay,hm.trans frame⟩

/-- The three record programs share a tape invariant. Dispatch adds at most
six steps per record and leaves both selector tapes empty. -/
theorem classifiedScan_exec (body : P → Pr P T Q A U) (liveMask fallbackMask : Fin T)
    (apart : liveMask ≠ fallbackMask) (good fallback padding : Pr P T Q A U)
    (records : ℕ) (live bad : ℕ → Bool) (cost : ℕ → ℕ) (ready : ℕ → Stacks T A → Prop)
    (release : ∀ j S k bits, k = liveMask ∨ k = fallbackMask → ready j S →
      ready j {S with R := Function.update S.R k bits})
    (step : ∀ j, j < records → ∀ (v : HS T Q A U) (S : Stacks T A), ready j S →
      ∃ z F n, z.user = v.user ∧ ready (j+1) F ∧ F.R liveMask = S.R liveMask ∧
        F.R fallbackMask = S.R fallbackMask ∧ n ≤ cost j ∧
        Exec body (if live j then (if bad j then fallback else good) else padding)
          (mk v S) n (mk z F))
    (v : HS T Q A U) (S : Stacks T A) (start : ready 0 S)
    (liveBits : S.R liveMask = (List.range records).map fun j => bitSymbol (live j))
    (badBits : S.R fallbackMask = (List.range records).map fun j => bitSymbol (bad j)) :
    ∃ z F n, z.user = v.user ∧ ready records F ∧ F.R liveMask = [] ∧ F.R fallbackMask = [] ∧
      n ≤ ((List.range records).map fun j => (cost j+2)+4).sum + 2 ∧
      Exec body (classifiedScan liveMask fallbackMask good fallback padding) (mk v S) n (mk z F) := by
  let bits := fun j => ((List.range records).drop j).map fun i => bitSymbol (a := A) (bad i)
  let inv := fun j (D : Stacks T A) => ready j D ∧ D.R fallbackMask = bits j
  have keep j D word (h : inv j D) : inv j {D with R := Function.update D.R liveMask word} :=
    ⟨release j D _ word (Or.inl rfl) h.1, (Function.update_of_ne apart.symm ..).trans h.2⟩
  apply Exists.elim (maskedRange_exec body liveMask _ _ records live (fun j => cost j+2) inv keep ?_
    v S ⟨start, by simpa [bits] using badBits⟩ liveBits)
  · rintro z ⟨F,n,hz,done,empty,time,run⟩
    exact ⟨z,F,n,hz,done.1,empty,by simpa only [bits, List.drop_of_length_le (List.length_range.le), List.map_nil] using done.2,time,run⟩
  intro j hj u D current
  have head : D.R fallbackMask = bitSymbol (bad j) :: bits (j+1) := by
    rw [current.2]
    dsimp only [bits]
    rw [← List.getElem_cons_drop (show j < (List.range records).length by simpa using hj)]
    simp
  let E := {D with R := Function.update D.R fallbackMask (bits (j+1))}
  obtain ⟨z,F,n,hz,next,outer,inner,time,run⟩ := step j hj {u with flag := bad j} E
    (release j D _ _ (Or.inr rfl) current.1)
  have pop := Exec.act (body := body) (nextPivotBit fallbackMask) (mk u D)
  have effects : inv (j+1) F := ⟨next, inner.trans (Function.update_self ..)⟩
  have untouched : F.R liveMask = D.R liveMask := outer.trans (Function.update_of_ne apart ..)
  cases h : live j <;> cases b : bad j <;>
    simp [nextPivotBit,Action.run,head,b,update_rt] at pop <;>
    simp only [h,b,Bool.false_eq_true,ite_false,ite_true,E] at run ⊢ <;>
    first
    | exact ⟨z,F,1+n,hz,effects,untouched,by omega,.seq pop run⟩
    | exact ⟨z,F,1+(n+1),hz,effects,untouched,by omega,.seq pop (.cond_false rfl run)⟩
    | exact ⟨z,F,1+(n+1),hz,effects,untouched,by omega,.seq pop (.cond_true rfl run)⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
