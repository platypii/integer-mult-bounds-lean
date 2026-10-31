module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoop
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice
public import IntegerMultBounds.MathlibTM2.StackResources

/-! Reverse packed line order without reversing symbols within a line. The
symbol-volume header is retained; no row count or decoded words are needed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def prependPackedLine (volume src dst line tmp : Fin T) : Pr P T Q A U :=
  .seq (transfer volume src line tmp) (moveR line dst id)

theorem prependPackedLine_exec (volume src dst line tmp : Fin T)
    (hreg : [volume,src,dst,line,tmp].Nodup)
    (xs tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hvolume : (S.R volume).length = xs.length) (hsrc : S.R src = xs++tail)
    (hline : S.R line = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (prependPackedLine volume src dst line tmp) (mk v S) (6*xs.length+6)
        (mk v' {S with R := (Function.update (Function.update S.R src tail) dst (xs++S.R dst))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := transfer_exec (body := body) (count := volume) (src := src) (dst := line) (tmp := tmp) (by regs_nodup) v S xs tail hsrc hvolume htmp
  let M : Stacks T A := {S with R := (Function.update (Function.update S.R src tail) line xs.reverse)}
  have he₁' : Exec body (transfer volume src line tmp) (mk v S) (4*xs.length+4) (mk v₁ M) := by
    simpa only [hline,List.append_nil] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body line dst ‹dst ≠ line›.symm id v₁ M
  refine ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁' he₂).cast ?_ ?_⟩
  · simp only [M,Function.update_self,List.length_reverse]; omega
  · apply congrArg (mk v₂)
    ext1
    · rfl
    · rfl
    · rfl
    · funext k
      by_cases hs : k = src
      · subst k; simp [M,movedR,‹src ≠ line›,‹src ≠ dst›]
      by_cases hd : k = dst
      · subst k; simp [M,movedR,‹dst ≠ line›,‹src ≠ dst›.symm]
      by_cases hl : k = line
      · subst k; simp [M,movedR,hline,‹dst ≠ line›.symm,‹src ≠ line›.symm]
      simp [M,movedR,hs,hd,hl]

def reversePackedLines (clock volume src dst line tmp : Fin T) : Pr P T Q A U :=
  countedLoop clock (prependPackedLine volume src dst line tmp)

/-- Consume a fixed-volume replica bank into the opposite replica order,
preserving each line, both suffixes and every tape except clock/src/dst. -/
theorem reversePackedLines_exec (clock volume src dst line tmp : Fin T)
    (hreg : [clock,volume,src,dst,line,tmp].Nodup)
    (lines : List (List (Fin (A+4)))) (V : ℕ) (hlen : ∀ xs ∈ lines, xs.length = V)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hclock : (S.R clock).length = lines.length) (hvolume : (S.R volume).length = V)
    (hsrc : S.R src = lines.flatten++tail) (hline : S.R line = []) (htmp : S.R tmp = []) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ lines.length*(6*V+9)+2 ∧
      Exec body (reversePackedLines clock volume src dst line tmp) (mk v S) n (mk v' F) ∧
      F.R src = tail ∧ F.R dst = lines.reverse.flatten++S.R dst ∧ F.R clock = [] ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ k, k ≠ src → k ≠ dst → k ≠ clock → F.R k = S.R k := by
  have hr := hreg
  regs_ne hr
  let Inv := fun j (R : Stacks T A) => ∃ done todo : List (List (Fin (A+4))),
    lines = done++todo ∧ done.length = j ∧ R.inp = S.inp ∧ R.out = S.out ∧ R.L = S.L ∧
    (∀ k, k ≠ src → k ≠ dst → k ≠ clock → R.R k = S.R k) ∧
    R.R src = todo.flatten++tail ∧ R.R dst = done.reverse.flatten++S.R dst
  obtain ⟨vf,F,n,hu,hn,he,hc,hI⟩ := countedLoop_exec (body := body) clock
    (prependPackedLine volume src dst line tmp) lines.length (6*V+6) Inv
    (by
      intro j R xs hI
      obtain ⟨done,todo,hrep,hj,hi,ho,hl,hframe,hs,hd⟩ := hI
      refine ⟨done,todo,hrep,hj,hi,ho,hl,?_,?_,?_⟩
      · intro k hks hkd hkc; simpa only [Function.update_of_ne hkc] using hframe k hks hkd hkc
      · simpa only [Function.update_of_ne ‹clock ≠ src›.symm] using hs
      · simpa only [Function.update_of_ne ‹clock ≠ dst›.symm] using hd)
    (by
      intro j hj vi R hI
      obtain ⟨done,todo,hrep,hlenDone,hi,ho,hl,hframe,hs,hd⟩ := hI
      cases todo with
      | nil => simp only [List.append_nil] at hrep; subst lines; omega
      | cons xs todo =>
        have hx : xs ∈ lines := by rw [hrep]; simp
        have hkeep (k : Fin T) (hk : k ∈ [volume,line,tmp]) : R.R k = S.R k := by
          apply hframe
          all_goals
            simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
            rcases hk with rfl | rfl | rfl
            all_goals first | assumption | (apply Ne.symm; assumption)
        obtain ⟨v',hu',hex⟩ := prependPackedLine_exec (body := body)
          volume src dst line tmp (by regs_nodup) xs (todo.flatten++tail) vi R
          (by rw [hkeep volume (by simp),hvolume,hlen xs hx])
          (by simpa only [List.flatten_cons,List.append_assoc] using hs)
          (by rw [hkeep line (by simp)]; exact hline)
          (by rw [hkeep tmp (by simp)]; exact htmp)
        let R' : Stacks T A := {R with R := (Function.update (Function.update R.R src
          (todo.flatten++tail)) dst (xs++R.R dst))}
        refine ⟨v',R',6*xs.length+6,hu',by rw [hlen xs hx],hex,?_,
          done++[xs],todo,?_,?_,hi,ho,hl,?_,?_,?_⟩
        · simp [R',‹clock ≠ src›,‹clock ≠ dst›]
        · simpa only [List.append_assoc,List.singleton_append] using hrep
        · simp [hlenDone]
        · intro k hks hkd hkc
          simpa only [R',Function.update_of_ne hks,Function.update_of_ne hkd] using hframe k hks hkd hkc
        · simp [R',‹src ≠ dst›]
        · simp [R',hd,List.reverse_append,List.append_assoc])
    v S hclock ⟨[],lines,rfl,rfl,rfl,rfl,rfl,(by intros; rfl),hsrc,by simp⟩
  obtain ⟨done,todo,hrep,hlenDone,hi,ho,hl,hframe,hs,hd⟩ := hI
  have ht : todo = [] := by
    have hh := congrArg List.length hrep
    simp only [List.length_append] at hh
    have : todo.length = 0 := by omega
    exact List.eq_nil_of_length_eq_zero this
  subst todo
  simp only [List.append_nil] at hrep
  subst done
  exact ⟨vf,F,n,hu,by simpa only [Nat.add_assoc] using hn,he,
    by simpa using hs,hd,hc,hi,ho,hl,hframe⟩

/-- Borrow the replica count rather than consuming it. -/
def retainedReversePackedLines (count clock volume src dst line tmp : Fin T) : Pr P T Q A U :=
  .seq (copyR count clock tmp (fun _ => tick)) (reversePackedLines clock volume src dst line tmp)

theorem retainedReversePackedLines_exec (count clock volume src dst line tmp : Fin T)
    (hreg : [count,clock,volume,src,dst,line,tmp].Nodup)
    (lines : List (List (Fin (A+4)))) (V : ℕ) (hlen : ∀ xs ∈ lines, xs.length = V)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hcount : (S.R count).length = lines.length) (hvolume : (S.R volume).length = V)
    (hsrc : S.R src = lines.flatten++tail)
    (hclock : S.R clock = []) (hline : S.R line = []) (htmp : S.R tmp = []) :
    ∃ v' F n, v'.user = v.user ∧ n ≤ lines.length*(6*V+13)+6 ∧
      Exec body (retainedReversePackedLines count clock volume src dst line tmp) (mk v S) n (mk v' F) ∧
      F.R src = tail ∧ F.R dst = lines.reverse.flatten++S.R dst ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ k, k ≠ src → k ≠ dst → F.R k = S.R k := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := copyR_exec (body := body) count clock tmp
    ‹count ≠ clock› ‹count ≠ tmp› ‹clock ≠ tmp› (fun _ => tick) v S htmp
  let M : Stacks T A := {S with R := (Function.update S.R clock
    (((S.R count).map (fun _ => tick)).reverse++S.R clock))}
  have hoff (k : Fin T) (hk : k ≠ clock) : M.R k = S.R k := by simp [M,hk]
  obtain ⟨v₂,F,n₂,hu₂,hn₂,he₂,hs,hd,hc,hi,ho,hl,hframe⟩ := reversePackedLines_exec (body := body)
    clock volume src dst line tmp (by regs_nodup) lines V hlen tail v₁ M
    (by simp [M,hclock,hcount])
    (by rw [hoff volume ‹clock ≠ volume›.symm]; exact hvolume)
    (by rw [hoff src ‹clock ≠ src›.symm]; exact hsrc)
    (by rw [hoff line ‹clock ≠ line›.symm]; exact hline)
    (by rw [hoff tmp ‹clock ≠ tmp›.symm]; exact htmp)
  refine ⟨v₂,F,(4*(S.R count).length+4)+n₂,hu₂.trans hu₁,?_,Exec.seq he₁ he₂,hs,?_,hi,ho,hl,?_⟩
  · rw [hcount]; nlinarith only [hn₂]
  · simpa only [hoff dst ‹clock ≠ dst›.symm] using hd
  · intro k hks hkd
    by_cases hkc : k = clock
    · subst k; exact hc.trans hclock.symm
    · exact (hframe k hks hkd hkc).trans (hoff k hkc)

/-- Reordering is linear native traffic, including its intermediate archive. -/
theorem reversePackedLines_pushBound (clock volume src dst line tmp : Fin T) :
    mnNativePushBound 2 (reversePackedLines (P := P) (Q := Q) (A := A) (U := U)
      clock volume src dst line tmp) := by
  simp [reversePackedLines,prependPackedLine,countedLoop,countedLoopBody,
    transfer,moveR,scanR,keepIn,transferAct,drainR,popDo,whileR,moveStep,peekR,
    mnNativePushBound,mnActPush]

theorem retainedReversePackedLines_pushBound (count clock volume src dst line tmp : Fin T) :
    mnNativePushBound 2 (retainedReversePackedLines (P := P) (Q := Q) (A := A) (U := U)
      count clock volume src dst line tmp) := by
  simp only [retainedReversePackedLines,mnNativePushBound]
  constructor
  · simp [copyR,copyStep,moveR,whileR,moveStep,peekR,
      mnNativePushBound,mnActPush]
  · exact reversePackedLines_pushBound _ _ _ _ _ _

theorem reversePackedLines_within_stock
    {clock volume src dst line tmp : Fin T} {v v' : HS T Q A U}
    {S F : Stacks T A} {n N V : ℕ}
    (hex : Exec body (reversePackedLines clock volume src dst line tmp) (mk v S) n (mk v' F))
    (hn : n ≤ N*(6*V+9)+2) (depth : ℕ) :
    ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*(N*(6*V+9)+2))
      depth (reversePackedLines clock volume src dst line tmp) (mk v S) n (mk v' F) := by
  exact mn_native_exec_within hex 2 (reversePackedLines_pushBound _ _ _ _ _ _) depth _ (by omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
