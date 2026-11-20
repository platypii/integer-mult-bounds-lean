module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackDimension
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCanonicalUnaryHeader
public import IntegerMultBounds.Machine.BinaryCanonicalData
public import IntegerMultBounds.Machine.RadixZeroFill
public import IntegerMultBounds.MathlibTM2.Host.WordCopy
import IntegerMultBounds.MathlibTM2.Host.ChunkSwap

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host
variable {T Q A : ℕ} {F U : Type}

/-- A represented descriptor contains its full bit word. The following cell is
blank even when the machine stores explicit blanks on the stack. -/
theorem descriptorRightPrefix (bits : List Bool) (left right : List (Fin (A+4)))
    (rep : ∀ z, readAt blank left right (z-1) = RadixZeroFill.encodedBinary bits z) :
    ∃ tail, right = bits.map bitSymbol ++ tail ∧ tail.head?.getD blank = blank := by
  have cells (i : ℕ) := rep ((i : ℤ)+1)
  simp only [encodedBinary_eq, ← readAt_single, add_sub_cancel_right, readAt_nonneg] at cells
  clear rep
  induction bits generalizing right with
  | nil => exact ⟨right,rfl,by cases right <;> simpa using cells 0⟩
  | cons b bits ih =>
    have head := cells 0
    cases right with
    | nil => cases b <;> simp [bitSymbol,blank] at head
    | cons x xs =>
      have hx : x = bitSymbol b := by simpa using head
      obtain ⟨tail,eq,last⟩ := ih xs (fun i => by simpa using cells (i+1))
      exact ⟨tail,by simp [hx,eq],last⟩

open WordCmd in
def copyDescriptor (src tmp dst : Fin T) : Pr F T Q A U :=
  (moveRL src isBit).seq ((copyLoop src tmp isBit).seq
    ((moveLR tmp isBit).seq (moveR tmp dst id)))

open WordCmd in
theorem copyDescriptor_exec (body : F → Pr F T Q A U) {src tmp dst : Fin T}
    (distinct : [src,tmp,dst].Nodup) (bits : List Bool) (v : HS T Q A U) (S : Stacks T A)
    (rep : ∀ z, readAt blank (S.L src) (S.R src) (z-1) = RadixZeroFill.encodedBinary bits z)
    (left : S.L tmp = []) (right : S.R tmp = []) :
    ∃ u, u.user = v.user ∧ Exec body (copyDescriptor src tmp dst) (mk v S) (8*bits.length+8)
      (mk u {S with R := Function.update S.R dst (bits.map bitSymbol ++ S.R dst)}) := by
  regs_ne distinct
  obtain ⟨tail,word,stop⟩ := descriptorRightPrefix bits _ _ rep
  have endR : (tail.head?.map isBit).getD false = false := by
    cases tail with
    | nil => rfl
    | cons x xs => simp at stop; simp [stop,isBit]; rfl
  have endL : ((S.L src).head?.map isBit).getD false = false := by
    have h := rep 0
    rw [encodedBinary_eq] at h
    simp [readAt,wordTape] at h
    cases eq : S.L src with
    | nil => simp
    | cons x xs => simp [eq] at h; simp [h,isBit]
  let base := fun i => (S.L i,S.R i)
  let xs := bits.map (bitSymbol (a := A))
  let mid := Function.update base src (xs.reverse ++ S.L src,tail)
  let out := Function.update base tmp (xs,S.R tmp)
  have regEq (f : Fin T → LR A) : regs S id f =
      {S with L := fun i => (f i).1, R := fun i => (f i).2} := by
    unfold regs
    congr 1
    · funext i; exact regs_L_at Function.injective_id S f i
    · funext i; exact regs_R_at Function.injective_id S f i
  obtain ⟨u,hu,scan⟩ := moveRL_exec body Function.injective_id S src isBit xs tail base v
    (isBit_bits bits) endR word
  obtain ⟨w,hw,copy⟩ := copyLoop_exec body Function.injective_id S ‹src ≠ tmp› isBit xs.reverse
    (S.L src) mid u (fun x hx => isBit_bits bits x (List.mem_reverse.mp hx)) endL (by simp [mid])
  have frame : Function.update (Function.update mid src (S.L src,xs.reverse.reverse ++ (mid src).2))
      tmp (xs.reverse.reverse ++ (mid tmp).1,(mid tmp).2) = out := by
    funext i
    by_cases hi : i = tmp <;> by_cases hj : i = src <;>
      simp_all [mid,base,out,xs,Function.update_apply]
  rw [frame] at copy
  let D := regs S id out
  obtain ⟨y,hy,turn⟩ := moveLR_exec body tmp isBit xs [] w D (isBit_bits bits) rfl
    (by simp [D,regEq,out])
  let E : Stacks T A := {D with L := Function.update D.L tmp [], R := Function.update D.R tmp (xs.reverse ++ D.R tmp)}
  obtain ⟨z,hz,finish⟩ := moveR_exec body tmp dst ‹tmp ≠ dst› id y E
  have cost : (E.R tmp).length = bits.length := by simp [E,D,regEq,out,right,xs]
  rw [cost] at finish
  have start : regs S id base = S := by rw [regEq]
  rw [start] at scan
  refine ⟨z,hz.trans (hy.trans (hw.trans hu)),Exec.cast (Exec.seq scan (Exec.seq copy (Exec.seq turn finish))) ?_ ?_⟩
  · simp [xs]; omega
  · congr 2
    · funext i; by_cases h : i = tmp <;> simp_all [E,D,regEq,out,base,Function.update_apply]
    · funext i; by_cases h : i = tmp <;> by_cases k : i = dst <;>
        simp_all [E,D,regEq,out,base,movedR,xs,Function.update_apply]

private theorem canonicalSymbols {xs : List Bool} {x : ℕ} (hc : GrowingCounterData.Canonical xs)
    (hv : Counter.value xs = x) : xs.map (bitSymbol (a := A)) = binSyms x.size x := by
  have eq := BinaryCanonicalData.value_injective xs (binBits x.size x) hc
    (Mult.PhaseCellToeplitz.binBits_size_canonical x)
    (hv.trans (Routing.binaryCanonical_value_binBits _ _ (Nat.lt_size_self x)).symm)
  rw [eq,binSyms_eq]

/-- The leaf radix is odd. Clearing its low bit on a copy yields the tail count. -/
def clearLowBit (j : Fin T) : Act T Q A U :=
  .pop (.rt j) (fun v _ => v) (.push (.rt j) (fun _ => bitSymbol false) .done)

theorem negationTailCount_exec (body : F → Pr F T Q A U) (r : Fin 4 ↪ Fin T)
    (M : ℕ) (odd : Odd M) (v : HS T Q A U) (S : Stacks T A)
    (radix : S.R (r 0) = binSyms M.size M) (free : ∀ i : Fin 4, i ≠ 0 → S.R (r i) = []) :
    let prog := (bcopy (r 0) (r 1) (r 2) (r 3)).seq
      (.seq (.act (clearLowBit (r 1))) (Routing.binaryCanonicalProgram (r 1) (r 2)))
    ∃ z, z.user = v.user ∧ Exec body prog (mk v S) ((6*M.size+6)+(1+(4*M.size+6)))
      (mk z {S with R := Function.update S.R (r 1) (binSyms (M-1).size (M-1))}) := by
  intro prog
  obtain ⟨u,hu,copy⟩ := bcopy_exec body (a := r 0) (c := r 1) (t₁ := r 2) (t₂ := r 3)
    (by simp [List.nodup_cons,r.injective.eq_iff]) v S (free 2 (by decide)) (free 3 (by decide))
  rw [radix,free 1 (by decide),List.append_nil,length_binSyms] at copy
  let D : Stacks T A := {S with R := Function.update S.R (r 1) (binSyms M.size M)}
  let E : Stacks T A := {S with R := Function.update S.R (r 1) (binSyms M.size (M-1))}
  have clear := Exec.act (body := body) (clearLowBit (r 1)) (mk u D)
  have fits := Nat.lt_size_self M
  have low : bitSymbol (a := A) false :: (binSyms M.size M).tail = binSyms M.size (M-1) := by
    obtain ⟨k,hk⟩ := odd
    generalize hw : M.size = w at *
    cases w with
    | zero => simp at fits; omega
    | succ w =>
      rw [binSyms_succ,binSyms_succ]
      simp [Nat.testBit_zero,show (M-1)%2 = 0 by omega,show (M-1)/2 = M/2 by omega]
  have step : Exec body (.act (clearLowBit (r 1))) (mk u D) 1 (mk u E) := by
    simpa [clearLowBit,Action.run,D,E,Stacks.get,update_rt,store_mk,low] using clear
  obtain ⟨xs,z,hc,hv,_,hz,trim⟩ := Routing.binaryCanonical_exec body (r 1) (r 2) (r.injective.ne (by decide))
    M.size (M-1) (by omega) u E (Function.update_self ..) (by simp [E,r.injective.eq_iff,free 2 (by decide)])
  rw [canonicalSymbols hc hv] at trim
  exact ⟨z,hz.trans hu,by simpa only [prog,E,Function.update_idem] using Exec.seq copy (Exec.seq step trim)⟩

/-- Form the suffix width for the sign pass using the live gap, modulus and inner width. -/
theorem negationSuffix_exec (body : F → Pr F T Q A U) (r : Fin 11 ↪ Fin T)
    (G M B : ℕ) (hg : 0 < G) (hm : 0 < M) (hb : 0 < B)
    (v : HS T Q A U) (S : Stacks T A) (gap : S.R (r 0) = binSyms G.size G)
    (radix : S.R (r 1) = binSyms M.size M) (width : S.R (r 2) = binSyms B.size B)
    (free : ∀ i : Fin 11, 3 ≤ i → i < 10 → S.R (r i) = []) :
    let suffix := G*(M*B)
    ∃ z n, z.user = v.user ∧ n ≤ 432*suffix ∧ Exec body (middleRowDescriptor r) (mk v S) n
      (mk z {S with R := Function.update S.R (r 4) (binSyms suffix.size suffix)}) := by
  obtain ⟨xs,z,n,hc,hv,hu,hn,run⟩ := middleRowDescriptor_exec body r G M B hg hm hb v S gap radix width free
  rw [canonicalSymbols hc hv,Nat.mul_assoc] at run
  exact ⟨z,n,hu,by simpa only [Nat.mul_assoc] using hn,run⟩

/-- Prepare the prefix product from the first three descriptor headers and a
zero digit of the live modulus width. Gap and suffix headers remain in place. -/
theorem leafPrefixAndZero_exec (body : F → Pr F T Q A U) (r : Fin 13 ↪ Fin T)
    (rowsBefore rows beforeH M : ℕ) (hp : 0 < rowsBefore) (hr : 0 < rows) (hh : 0 < beforeH)
    (u : HS T Q A U) (S : Stacks T A)
    (prefixRows : S.R (r 0) = binSyms rowsBefore.size rowsBefore)
    (rowCount : S.R (r 1) = binSyms rows.size rows)
    (heads : S.R (r 2) = binSyms beforeH.size beforeH)
    (modulus : S.R (r 11) = binSyms M.size M)
    (scratch : ∀ i : Fin 13, (3 ≤ i ∧ i < 10) ∨ i = 12 → S.R (r i) = []) :
    let pre := rowsBefore*rows*beforeH
    let ports := (Fin.castLEEmb (by decide : 11 ≤ 13)).trans r
    let prog := (middleRowDescriptor ports).seq (bzero (r 11) (r 12) (r 5))
    ∃ z n, z.user = u.user ∧ n ≤ 432*pre+(4*M.size+4) ∧
      Exec body prog (mk u S) n (mk z {S with R := Function.update (Function.update S.R (r 4) (binSyms pre.size pre)) (r 12) (binSyms M.size 0)}) := by
  intro pre ports prog
  obtain ⟨v,n,hv,hn,run⟩ := negationSuffix_exec body ports rowsBefore rows beforeH hp hr hh u S
    prefixRows rowCount heads (fun i lo hi => scratch (i.castLE (by decide)) (.inl ⟨lo,hi⟩))
  let D : Stacks T A := {S with R := Function.update S.R (r 4) (binSyms pre.size pre)}
  have entry : Exec body (middleRowDescriptor ports) (mk u S) n (mk v D) := by
    simpa only [D,pre,Nat.mul_assoc,show ports 4 = r 4 from rfl] using run
  have keep (i : Fin 13) (hi : i ≠ 4) : D.R (r i) = S.R (r i) := Function.update_of_ne (r.injective.ne hi) _ _
  obtain ⟨z,hz,zero⟩ := bzero_exec body (wR := r 11) (c := r 12) (t := r 5)
    (by simp [List.nodup_cons,r.injective.eq_iff]) v D ((keep 5 (by decide)).trans (scratch _ (by decide)))
  rw [(keep 11 (by decide)).trans modulus,length_binSyms,(keep 12 (by decide)).trans (scratch _ (by decide)),
    List.append_nil] at zero
  exact ⟨z,_,hz.trans hv,Nat.add_le_add_right (by simpa only [pre,Nat.mul_assoc] using hn) _,Exec.seq entry zero⟩

/-- Borrow the two dimension-header slots for one leaf call, then return
them blank. The cost of erasing each header depends on its actual word width. -/
theorem withLeafDimensions_exec (body : F → Pr F T Q A U) (r : Fin 13 ↪ Fin T)
    (rowsBefore rows beforeH M : ℕ) (hp : 0 < rowsBefore) (hr : 0 < rows) (hh : 0 < beforeH)
    (u : HS T Q A U) (S : Stacks T A)
    (prefixRows : S.R (r 0) = binSyms rowsBefore.size rowsBefore)
    (rowCount : S.R (r 1) = binSyms rows.size rows)
    (heads : S.R (r 2) = binSyms beforeH.size beforeH)
    (modulus : S.R (r 11) = binSyms M.size M)
    (scratch : ∀ i : Fin 13, (3 ≤ i ∧ i < 10) ∨ i = 12 → S.R (r i) = [])
    (leaf : Pr F T Q A U) (budget : ℕ) (post : Stacks T A → Prop) :
    let pre := rowsBefore*rows*beforeH
    let ports := (Fin.castLEEmb (by decide : 11 ≤ 13)).trans r
    let setup := (middleRowDescriptor ports).seq (bzero (r 11) (r 12) (r 5))
    let ready : Stacks T A := {S with R := Function.update (Function.update S.R (r 4) (binSyms pre.size pre)) (r 12) (binSyms M.size 0)}
    (∀ v : HS T Q A U, v.user = u.user → ∃ z D n, z.user = v.user ∧ n ≤ budget ∧
      Exec body leaf (mk v ready) n (mk z D) ∧ D.R (r 4) = ready.R (r 4) ∧ D.R (r 12) = ready.R (r 12) ∧
      post {D with R := Function.update (Function.update D.R (r 4) []) (r 12) []}) →
    ∃ z D n, z.user = u.user ∧ n ≤ 432*pre+(4*M.size+4)+(budget+(2*pre.size+2+(2*M.size+2))) ∧
      Exec body (setup.seq (leaf.seq ((bclear (r 4)).seq (bclear (r 12))))) (mk u S) n (mk z D) ∧
      D.R (r 4) = S.R (r 4) ∧ D.R (r 12) = S.R (r 12) ∧ post D := by
  intro pre ports setup ready run
  obtain ⟨v,k,hv,hk,prepare⟩ := leafPrefixAndZero_exec body r rowsBefore rows beforeH M hp hr hh u S
    prefixRows rowCount heads modulus scratch
  obtain ⟨z,D,n,hz,hn,call,preWord,zeroWord,result⟩ := run v hv
  obtain ⟨a,ha,_,clearPre⟩ := bclear_exec body (r 4) z D
  let E : Stacks T A := {D with R := Function.update D.R (r 4) []}
  obtain ⟨b,hb,_,clearZero⟩ := bclear_exec body (r 12) a E
  have preLength : (D.R (r 4)).length = pre.size := by
    rw [preWord]; simp [ready,r.injective.eq_iff,length_binSyms]
  have zeroLength : (E.R (r 12)).length = M.size := by
    simp [E,r.injective.eq_iff,zeroWord,ready,length_binSyms]
  rw [preLength] at clearPre
  rw [zeroLength] at clearZero
  refine ⟨b,_,_,hb.trans (ha.trans (hz.trans hv)),Nat.add_le_add hk (Nat.add_le_add_right hn _),
    Exec.seq prepare (Exec.seq call (Exec.seq clearPre clearZero)),?_,?_,result⟩
  · simp [E,r.injective.eq_iff,scratch 4 (by decide)]
  · simp [scratch 12 (by decide)]

/-- Multiply the tail block count by the suffix width and remove leading zero padding. -/
theorem negationTailWidth_exec (body : F → Pr F T Q A U) (r : Fin 9 ↪ Fin T)
    (count width : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (blocks : S.R (r 0) = binSyms count.size count) (blockWidth : S.R (r 1) = binSyms width.size width)
    (free : ∀ i : Fin 9, 2 ≤ i → i < 8 → S.R (r i) = []) :
    let L := count.size+width.size
    let prog := (bmul (r 0) (r 1) (r 2) (r 3) (r 4) (r 5) (r 6) (r 7) (r 8)).seq
      (Routing.binaryCanonicalProgram (r 2) (r 3))
    ∃ z n, z.user = v.user ∧ n ≤ count.size*(12*L+20)+16*L+24+(4*L+6) ∧
      Exec body prog (mk v S) n (mk z {S with R := Function.update S.R (r 2) (binSyms (count*width).size (count*width))}) := by
  intro L prog
  obtain ⟨u,n,hu,hn,mul⟩ := bmul_exec body (a := r 0) (b := r 1) (c := r 2)
    (s := r 3) (t := r 4) (tx := r 5) (ty := r 6) (tz := r 7) (cy := r 8)
    (by simp [List.nodup_cons,r.injective.eq_iff]) (r.injective.ne (by decide)) (r.injective.ne (by decide))
    (Nat.lt_size_self count) (Nat.lt_size_self width) v S blocks blockWidth (free 2 (by decide) (by decide))
    (free 3 (by decide) (by decide)) (free 4 (by decide) (by decide)) (free 5 (by decide) (by decide))
    (free 6 (by decide) (by decide)) (free 7 (by decide) (by decide))
  let D := Function.update S.R (r 2) (binSyms L (count*width))
  have fits : count*width < 2^L := by
    rw [show L = count.size+width.size from rfl,pow_add]
    exact Nat.mul_lt_mul_of_lt_of_le (Nat.lt_size_self count) (Nat.lt_size_self width).le (by positivity)
  obtain ⟨xs,z,hc,hv,_,hz,trim⟩ := Routing.binaryCanonical_exec body (r 2) (r 3)
    (r.injective.ne (by decide)) L _ fits u {S with R := D} (Function.update_self ..)
    (by simp [D,r.injective.eq_iff,free 3 (by decide) (by decide)])
  rw [canonicalSymbols hc hv] at trim
  refine ⟨z,_,hz.trans hu,Nat.add_le_add_right hn _,?_⟩
  simpa only [D,Function.update_idem] using Exec.seq mul trim

def negationSuffixPorts : Fin 11 ↪ Fin 17 := ⟨![15,12,16,1,4,2,3,6,9,11,13],by decide⟩
def negationCountPorts : Fin 4 ↪ Fin 17 := ⟨![12,7,1,2],by decide⟩
def negationProductPorts : Fin 9 ↪ Fin 17 := ⟨![7,4,5,1,2,3,6,9,11],by decide⟩

/-- The three computed headers occupy their final sign-loop slots. Gap and
inner width lie outside the sign bank; the modulus stays on its return port. -/
theorem negationDimensions_exec (body : F → Pr F 17 Q A U) (P G M B : ℕ)
    (hg : 0 < G) (hm : 0 < M) (hb : 0 < B) (odd : Odd M)
    (u : HS 17 Q A U) (S : Stacks 17 A)
    (prefixCount : S.R 8 = binSyms P.size P)
    (gap : S.R 15 = binSyms G.size G) (radix : S.R 12 = binSyms M.size M)
    (width : S.R 16 = binSyms B.size B)
    (free : ∀ i : Fin 17, i ∈ [1,2,3,4,5,6,7,9,10,11,14] → S.R i = []) :
    let suffix := G*(M*B)
    let count := M-1
    let L := count.size+suffix.size
    let tail := (bcopy 12 7 1 2).seq (.seq (.act (clearLowBit 7)) (Routing.binaryCanonicalProgram 7 1))
    let product := (bmul 7 4 5 1 2 3 6 9 11).seq (Routing.binaryCanonicalProgram 5 1)
    let prog := (middleRowDescriptor negationSuffixPorts).seq (tail.seq product)
    let publish := (bcopy 4 10 1 2).seq (bcopy 8 14 1 2)
    let headers := Function.update (Function.update (Function.update S.R 4 (binSyms suffix.size suffix))
      7 (binSyms count.size count)) 5 (binSyms (count*suffix).size (count*suffix))
    ∃ z n, z.user = u.user ∧ n ≤ 432*suffix+((6*M.size+6)+(1+(4*M.size+6))+
      (count.size*(12*L+20)+16*L+24+(4*L+6))) + (6*suffix.size+6+(6*P.size+6)) ∧
      Exec body (prog.seq publish) (mk u S) n (mk z {S with R := Function.update (Function.update headers 10 (binSyms suffix.size suffix)) 14 (binSyms P.size P)}) := by
  intro suffix count L tail product prog publish headers
  obtain ⟨v,n,hv,hn,first⟩ := negationSuffix_exec body negationSuffixPorts G M B hg hm hb u S gap radix width
    (fun i lo hi => free _ ((by decide : ∀ j : Fin 11, 3 ≤ j → j < 10 →
      negationSuffixPorts j ∈ [1,2,3,4,5,6,7,9,10,11,14]) i lo hi))
  let D : Stacks 17 A := {S with R := Function.update S.R 4 (binSyms suffix.size suffix)}
  obtain ⟨w,hw,predRun⟩ := negationTailCount_exec body negationCountPorts M odd v D
    (by change D.R 12 = _; simpa [D] using radix)
    (by intro i hi
        have facts := (by decide : ∀ j : Fin 4, j ≠ 0 → negationCountPorts j ≠ 4 ∧
          negationCountPorts j ∈ [1,2,3,4,5,6,7,9,10,11,14]) i hi
        exact (Function.update_of_ne facts.1 _ _).trans (free _ facts.2))
  let E : Stacks 17 A := {D with R := Function.update D.R 7 (binSyms count.size count)}
  obtain ⟨z,m,hz,hmul,last⟩ := negationTailWidth_exec body negationProductPorts count suffix w E
    (by change E.R 7 = _; simp [E]) (by change E.R 4 = _; simp [E,D])
    (by intro i lo hi
        have facts := (by decide : ∀ j : Fin 9, 2 ≤ j → j < 8 → negationProductPorts j ≠ 7 ∧
          negationProductPorts j ≠ 4 ∧ negationProductPorts j ∈ [1,2,3,4,5,6,7,9,10,11,14]) i lo hi
        exact (Function.update_of_ne facts.1 _ D.R).trans
          ((Function.update_of_ne facts.2.1 _ S.R).trans (free _ facts.2.2)))
  let H : Stacks 17 A := {S with R := headers}
  have copyHeader (a c : Fin 17) (regs : [a,c,1,2].Nodup) (x : ℕ)
      (v : HS 17 Q A U) (I : Stacks 17 A) (src : I.R a = binSyms x.size x)
      (dst : I.R c = []) (tmp : I.R 1 = []) (work : I.R 2 = []) :
      ∃ w, w.user = v.user ∧ Exec body (bcopy a c 1 2) (mk v I) (6*x.size+6)
        (mk w {I with R := Function.update I.R c (binSyms x.size x)}) := by
    obtain ⟨w,hu,run⟩ := bcopy_exec body regs v I tmp work
    exact ⟨w,hu,by simpa only [src,dst,length_binSyms,List.append_nil] using run⟩
  obtain ⟨y,hy,copyWidth⟩ := copyHeader 4 10 (by decide) suffix z H
    (by simp [H,headers]) (by simp [H,headers,free 10 (by decide)])
    (by simp [H,headers,free 1 (by decide)]) (by simp [H,headers,free 2 (by decide)])
  let I : Stacks 17 A := {H with R := Function.update H.R 10 (binSyms suffix.size suffix)}
  obtain ⟨f,hf,copyCount⟩ := copyHeader 8 14 (by decide) P y I
    (by simp [I,H,headers,prefixCount]) (by simp [I,H,headers,free 14 (by decide)])
    (by simp [I,H,headers,free 1 (by decide)]) (by simp [I,H,headers,free 2 (by decide)])
  exact ⟨f,_,hf.trans (hy.trans (hz.trans (hw.trans hv))),
    Nat.add_le_add_right (Nat.add_le_add hn (Nat.add_le_add_left hmul _)) _,
    Exec.seq (Exec.seq first (Exec.seq predRun last)) (Exec.seq copyWidth copyCount)⟩

end IntegerMultBounds.MathlibTM2.Cover.Fallback
