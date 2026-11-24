module

public import IntegerMultBounds.MathlibTM2.M6.BitBorrowedIntervalDirectory
public import IntegerMultBounds.MathlibTM2.M6.BitIdleDispatchSeed

public import IntegerMultBounds.MathlibTM2.M6.BitDirectoryIntervalSplit

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback M8.RevMachine
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout IntervalDescriptor

/-- The ordinary dispatch bank is followed by the six shared role fields,
nine header arithmetic slots and 26 private child-record slots. -/
def idleRolePorts : Fin 6 ↪ Fin 113 := ⟨![72,73,74,75,76,77],by decide⟩
def idleHeaderArithmetic : Fin 12 ↪ Fin 113 := ⟨![5,2,76,78,79,80,81,82,83,84,85,86],by decide⟩

def idleRecordSlot : Fin 34 ↪ Fin 113 :=
  ⟨![72,73,74,78,79,77,6,0,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112],by decide⟩

/-- Slot seven reads the split fan's logical length. Every other child slot
lies on the caller board, disjoint from the split data. -/
def idleCallerRecord {T : ℕ} (board : Fin 113 ↪ Fin T) (splitter : Fin intervalSplitTapes ↪ Fin T)
    (apart : ∀ i k, splitter i ≠ board k) : Fin 34 ↪ Fin T where
  toFun k := if k = 7 then splitter (intervalOwners 142080 ((1 : Fin 2).natAdd 142080)) else board (idleRecordSlot k)
  inj' := by
    intro k l
    by_cases a : k = 7 <;> by_cases b : l = 7
    · exact fun _ => a.trans b.symm
    · simp only [a,b,ite_true,ite_false]
      exact fun eq => (apart _ _ eq).elim
    · simp only [a,b,ite_true,ite_false]
      exact fun eq => (apart _ _ eq.symm).elim
    · simpa only [a,b,ite_false,board.injective.eq_iff,idleRecordSlot.injective.eq_iff] using (id : k = l → k = l)

noncomputable abbrev idlePackPorts := (Fin.castLEEmb (by decide : 35 ≤ 59)).trans (Fin.castLEEmb swapHostFits)

/-- Clear everything outside the ordinary registers and shared role words. -/
noncomputable def idleCallerWork {B : ℕ} (protectedPorts : Fin 78 ↪ Fin B) : List (Fin B) :=
  (List.finRange B).filter fun t => ∀ k, protectedPorts k ≠ t

private theorem inCallerWork {B : ℕ} (protectedPorts : Fin 78 ↪ Fin B) (t : Fin B) :
    t ∈ idleCallerWork protectedPorts ↔ ∀ k, protectedPorts k ≠ t := by simp [idleCallerWork]

/-- The owner word occupies tape 24. The remaining ordinary tapes retain
the seed produced by dispatch. -/
def IdleDispatchReady {T : ℕ} (raw : Fin 72 ↪ Fin T) (w W L cutoff : ℕ) (S : Stacks T prime) : Prop :=
  ∀ k, k ≠ 24 → S.L (raw k) = [] ∧ S.R (raw k) = idleDispatchWord w W L cutoff k.val

/-- The installed active child runs on an interleaved word using the shared
role descriptor and the ordinary dispatch registers. -/
theorem compiledIdleRecord [M8.Machine.Net] {P U Config : Type} {N T Q : ℕ}
    {input : Config → CutoffNodeInput} {body : P → Pr P N Q prime U}
    {dst : Fin (142081+2) ↪ Fin N} {leafRate : ℝ} {childBudget : Config → ℕ → ℕ}
    (family : SplitRecordTreeFamily input body dst leafRate childBudget)
    (swapCap : (@rowSwapBlock BinaryRadixEqualShared.supplierNet).states ≤ Q)
    (capacity : let q := 7+(CyclicRowCycle.states 142080+5)+4; q+q ≤ Q)
    (i : Fin 9) (j : Fin idleCopies.length) (board : Fin 113 ↪ Fin T)
    (splitter : Fin intervalSplitTapes ↪ Fin T) (apart : ∀ r k, splitter r ≠ board k) :
    let raw := (Fin.castLEEmb (by decide : 72 ≤ 113)).trans board
    let fields := idleRolePorts.trans board
    let src := raw 24
    let caller := (Fin.natAddEmb 142082 (m := T)).trans (Fin.castAddEmb N)
    let embed := caller.trans (intervalExtend T N)
    ∃ minimum : ℝ, 0 ≤ minimum ∧ ∀ D : ℝ, minimum ≤ D →
      ∃ table : Option (Empty ⊕ P) → Pr (Option (Empty ⊕ P)) (intervalHostSize T N) Q prime U,
      let work := idleCallerWork (((Fin.castAddEmb 35 (n := 78)).trans board).trans embed)
      ∃ (code : Pr (Option (Empty ⊕ P)) (intervalHostSize T N) Q prime U) (fixed base swaps : ℕ),
      ∀ (p : CutoffNodeInput) x, let c := input x
      c.node = scheduledChild prime p.node (idleDirectoryIndex (i,j)) → c.cutoff < c.node.width →
      (∀ k : Fin nodeChildren5.length, let d := scheduledChild prime c.node k
        c.cutoff < d.width → childBudget x k.val ≤ cutoffTreeBudget D leafRate c.cutoff (c.depth-(c.path.length+1)) d) →
      let budget := cutoffTreeBudget D leafRate c.cutoff (c.depth-c.path.length) c.node
      let e := idleInterval i idleCopies[j.val].2
      let lane := phaseIntervalChild (e.1+1) (e.2+1) (p.w+1) p.idleWidth 64
      let wide := {lane with afterD := lane.afterD*142080}
      ∀ (word : Fin (volume prime wide) → ZMod 2) u S,
        RecordPayload (embed src) (fun _ => blank) 0 word S →
        IdleDispatchReady (raw.trans embed) p.w p.idleWidth c.root.width.size c.cutoff S →
        (∀ t ∈ work, S.L t = [] ∧ S.R t = []) →
        (∀ k, S.R (embed (fields k)) = (Routines.hdr (role p.node 142080) k).map bitSymbol) →
        ∃ z F n, Exec table code (mk u S) n (mk z F) ∧ z.user = u.user ∧
          CleanupBound S F n (fixed*p.cells+
            (base+swaps*(@swapVolumeRate BinaryRadixEqualShared.supplierNet p.w))*c.cells+budget) ∧
          RecordPayload (embed src) (fun _ => blank) 0
            (Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) word) F ∧
          ∀ t, t ≠ embed src → F.L t = S.L t ∧ F.R t = S.R t := by
  intro raw fields src caller embed
  let headers := intervalDirectoryPorts.trans raw
  let record := idleCallerRecord board splitter apart
  let h := idleHeaderArithmetic.trans board
  let tmp := raw 62
  let count := raw 60
  let saved := raw 61
  let width := raw 59
  let small := idlePackPorts
  let live := (intervalOwners 142080).trans splitter
  let ports := intervalRecordBank (live.trans caller) (small 24)
  have recOff k (a : k ≠ (7 : Fin 34)) : record k = board (idleRecordSlot k) := ite_eq_right a
  have workOff r k (member : k ∈ idleRecordWork) : splitter r ≠ record k := by
    have ne : k ≠ 7 := by rintro rfl; revert member; decide
    rw [recOff _ ne]
    apply apart
  obtain ⟨minimum,nonneg,build⟩ := compiledIdleInterval family swapCap i j live headers width record
    (fun r k hk => (workOff _ k (by simp [idleRecordWork,hk])).symm)
    (fun r k => apart _ _) (fun r => apart _ _) (fun r k => by
      by_cases a : k = 7
      · subst k
        apply live.injective.ne
        intro eq
        have bad := congrArg Fin.val eq
        change r.val = 142080+1 at bad
        omega
      · rw [recOff k a]
        apply apart) (by rfl)
  refine ⟨minimum,nonneg,?_⟩
  intro D enough
  obtain ⟨bank,table,worker,rate,frame,execute⟩ := build D enough
  refine ⟨table,?_⟩
  intro work
  let shared := ((Fin.castAddEmb 35 (n := 78)).trans board).trans embed
  have distinct : work.Nodup := (List.nodup_finRange _).filter _
  have splitFree k : embed (splitter k) ∈ work := (inCallerWork shared _).2
    (fun a => embed.injective.ne (apart _ _).symm)
  have outside : embed src ∉ work := fun mem => (inCallerWork shared _).1 mem 24 rfl
  have arg : [count,splitter 0,src,saved,tmp].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,not_false_eq_true,List.nodup_nil,and_true]
    exact ⟨⟨(apart _ _).symm,raw.injective.ne (by decide),raw.injective.ne (by decide),raw.injective.ne (by decide)⟩,
      ⟨apart _ _,apart _ _,apart _ _⟩,⟨raw.injective.ne (by decide),raw.injective.ne (by decide)⟩,raw.injective.ne (by decide)⟩
  obtain ⟨code,fixed,base,swaps,run⟩ := splitDirectoryInterval i j splitter capacity headers width record dst bank frame table worker fields h
    (fun k => by fin_cases k <;> rfl)
    (fun k _ _ => ⟨board.injective.ne ((by decide : ∀ a, idleRolePorts a ≠ idleHeaderArithmetic 3) k),
      board.injective.ne ((by decide : ∀ a, idleRolePorts a ≠ idleHeaderArithmetic 4) k)⟩)
    (fun k => ⟨board.injective.ne ((by decide : ∀ a, (intervalDirectoryPorts a).castLE (show 72 ≤ 113 from Nat.le_add_right 72 41) ≠ idleHeaderArithmetic 3) k),
      board.injective.ne ((by decide : ∀ a, (intervalDirectoryPorts a).castLE (show 72 ≤ 113 from Nat.le_add_right 72 41) ≠ idleHeaderArithmetic 4) k)⟩)
    ⟨board.injective.ne (by decide : (59 : Fin 113) ≠ idleHeaderArithmetic 3),board.injective.ne (by decide : (59 : Fin 113) ≠ idleHeaderArithmetic 4)⟩
    src tmp count saved arg (fun r => ⟨apart _ _,apart _ _,apart _ _,apart _ _⟩)
    (fun r k => apart _ _) (fun r k => apart _ _) (fun r k => apart _ _) (fun r => apart _ _)
    (fun r => by rw [recOff 6 (by decide)]; apply apart) workOff work distinct (splitFree 0) outside
  let regs := raw.trans embed
  obtain ⟨wrapped,enter⟩ := withIntervalDirectory table regs code
  refine ⟨wrapped,fixed+4*work.length+41,rate*base,rate*swaps,?_⟩
  intro p x c scheduled active children budget e lane wide word u S payload ready fresh inherited
  have wordAt (k : Fin 72) (ne : k ≠ 24) := (ready k ne).2
  have blankRegs (k : Fin 72) (lo : 59 ≤ k.val) (hi : k.val ≤ 65) : S.R (regs k) = [] := by
    refine (wordAt k ((by decide : ∀ i : Fin 72, 59 ≤ i.val → i ≠ 24) k lo)).trans ?_
    simp [idleDispatchWord,show k.val ≠ 2 by omega,show k.val ≠ 28 by omega,
      show k.val ≠ 53 by omega,show k.val ≠ 71 by omega,show k.val ≠ 5 by omega,show k.val ≠ 6 by omega]
  have hc := blankRegs 60 (by decide) (by decide)
  have hs := blankRegs 61 (by decide) (by decide)
  have tl := (ready 62 (by decide)).1
  have tr := blankRegs 62 (by decide) (by decide)
  have clock : (S.R (regs 5)).length = p.w := by rw [wordAt 5 (by decide)]; simp [idleDispatchWord]
  have radix : S.R (regs 2) = binSyms (prime^(p.w+1)).size (prime^(p.w+1)) := wordAt 2 (by decide)
  have suffix : S.R (regs 53) = binSyms p.idleWidth.size p.idleWidth := wordAt 53 (by decide)
  have unit : S.R (regs 28) = binSyms 1 1 := wordAt 28 (by decide)
  have markers (k : Fin 3) := (ready (intervalDirectoryPorts (copyRecordSources k))
    ((by decide : ∀ i, intervalDirectoryPorts (copyRecordSources i) ≠ 24) k)).1
  have atom : (S.R (regs 71)).length = p.w+1 := by rw [wordAt 71 (by decide)]; simp [idleDispatchWord]
  have cut : S.R (regs 6) = binSyms c.root.width.size c.cutoff := wordAt 6 (by decide)
  let post := fun (l r : List (Fin (prime+4))) => RecordPayload (embed src) (fun _ => blank) 0
    (Shared50RecursiveNodeRows.transpose (one_dvd wide.rows) word)
    {S with L := fun _ => l, R := fun _ => r}
  let price := (fixed+4*work.length)*p.cells +
    (rate*base+(rate*swaps)*(@swapVolumeRate BinaryRadixEqualShared.supplierNet p.w))*c.cells+budget
  obtain ⟨z,F,n,exec,user,paid,result,off⟩ := enter p.w p.idleWidth u S price post radix suffix unit markers atom blankRegs (by
    intro v A _ dims left right
    have sameL (k : Fin 72) (ne : ∀ i, intervalDirectoryPorts (copyRecordSources i) ≠ k) :
        A.L (regs k) = S.L (regs k) := left _ (fun i => regs.injective.ne (ne i))
    have sameR (k : Fin 72) (ne : (59 : Fin 72) ≠ k) : A.R (regs k) = S.R (regs k) :=
      right _ (regs.injective.ne ne)
    have payload' : RecordPayload (embed src) (fun _ => blank) 0 word A := by
      intro z
      change readAt blank (A.L (regs 24)) (A.R (regs 24)) _ = _
      rw [sameL 24 (by decide),sameR 24 (by decide)]
      exact payload z
    have regOff (t) (mem : t ∈ work) (k : Fin 72) : regs k ≠ t :=
      (inCallerWork shared _).1 mem (k.castAdd 6)
    have fresh' (t) (mem : t ∈ work) : A.L t = [] ∧ A.R t = [] :=
      ⟨(left t (fun _ => regOff t mem _)).trans (fresh t mem).1,
       (right t (regOff t mem 59)).trans (fresh t mem).2⟩
    have fields' k : A.R (embed (fields k)) = _ := (right _ (embed.injective.ne (board.injective.ne
      ((by decide : ∀ k, (59 : Fin 113) ≠ idleRolePorts k) k)))).trans (inherited k)
    have middle := fields' (4 : Fin 6)
    have child := execute p x scheduled active children
    have privateAt k (hi : 78 ≤ k.val) : embed (board k) ∈ work := (inCallerWork shared _).2 (fun a =>
      embed.injective.ne (board.injective.ne (fun eq => by have bad := congrArg Fin.val eq; change a.val = k.val at bad; omega)))
    have empty k (hk : 3 ≤ k.val) := (fresh' _ (privateAt (idleHeaderArithmetic k)
      ((by decide : ∀ k : Fin 12, 3 ≤ k.val → 78 ≤ (idleHeaderArithmetic k).val) k hk))).2
    have scratch r k (ne : k ≠ small 24) := fresh' _ ((inCallerWork shared (ports r k)).2 (fun a =>
      intervalWorkOutside _ _ r k ne (caller (board (a.castAdd 35)))))
    have free k (hk : k ∈ idleRecordWork) : A.L (embed (record k)) = [] ∧ A.R (embed (record k)) = [] := by
      have ne : k ≠ 7 := by rintro rfl; revert hk; decide
      rw [recOff k ne]
      exact fresh' _ (privateAt _ ((by decide : ∀ k ∈ idleRecordWork, 78 ≤ (idleRecordSlot k).val) k hk))
    have bridge (k : Fin 142082) := fresh' _ ((inCallerWork shared (intervalExtend T N ((k.castAdd T).castAdd N))).2 (fun a =>
      (intervalExtend T N).injective.ne ((Fin.castAddEmb N).injective.ne (suffixApart _ _))))
    have vacant (k : Fin N) := fresh' _ ((inCallerWork shared (intervalExtend T N (k.natAdd (142082+T)))).2 (fun a =>
      (intervalExtend T N).injective.ne (suffixApart _ _).symm))
    obtain ⟨z,F,n,exec,user,paid,output,clean,keep⟩ := run p c rate budget scheduled child word v A payload'
      ((sameR 60 (by decide)).trans hc) ((sameR 61 (by decide)).trans hs)
      ((sameL 62 (by decide)).trans tl) ((sameR 62 (by decide)).trans tr)
      (fun k => fresh' _ (splitFree k)) ((congrArg List.length (sameR 5 (by decide))).trans clock)
      ((sameR 2 (by decide)).trans radix) middle empty (fun k _ _ => fields' k) dims scratch ((sameR 6 (by decide)).trans cut) free bridge vacant
    have entry : tapeCharge cleanupWeight work A = 4*work.length := by
      unfold tapeCharge
      rw [List.map_congr_left (g := fun _ => 4) (fun k hk => by simp [cleanupWeight,(fresh' k hk).1,(fresh' k hk).2])]
      simp [List.map_const',Nat.mul_comm]
    refine ⟨z,F,n,exec,user,?_,output,?_⟩
    · have pos : 0 < p.cells := Nat.mul_pos (pow_pos (pow_pos Shared50ModularControl.prime_prime.pos _) _)
          (Nat.mul_pos p.idlePositive (by decide))
      have stock := Nat.mul_le_mul_left (4*work.length) pos
      have combine (a b c d v : ℕ) : a*((b+c*d)*v) = (a*b+(a*c)*d)*v := by ring
      intro js nd
      have bound := paid js nd
      rw [entry,combine rate base swaps] at bound
      change _ ≤ _ + ((fixed+4*work.length)*p.cells+_+budget)
      rw [Nat.add_mul]
      omega
    · intro t ne
      by_cases mem : t ∈ work
      · exact ⟨(clean t mem).1.trans (fresh' t mem).1.symm,(clean t mem).2.trans (fresh' t mem).2.symm⟩
      obtain ⟨a,eq⟩ : ∃ a, shared a = t := by
        by_contra! h
        exact mem ((inCallerWork shared t).2 h)
      subst t
      exact keep (board (a.castAdd 35)) (fun h => ne (congrArg embed h)) mem (fun k => apart _ _))
  refine ⟨z,F,n,exec,user,?_,result,off⟩
  have mass : prime^(p.w+1) ≤ p.cells := (Nat.le_self_pow (by decide : 128 ≠ 0) _).trans
    (Nat.le_mul_of_pos_right _ (Nat.mul_pos p.idlePositive (by decide)))
  have clockBound : p.w+1 ≤ p.cells := (Nat.lt_pow_self Shared50ModularControl.prime_prime.one_lt).le.trans mass
  have sizeBound : (p.w+1).size ≤ p.w+1 := Nat.size_le.mpr Nat.lt_two_pow_self
  intro js distinct
  have bill := paid js distinct
  dsimp only [price] at bill
  rw [Nat.add_mul (fixed+4*work.length) 41]
  omega

end IntegerMultBounds.MathlibTM2.M6.BitNode
