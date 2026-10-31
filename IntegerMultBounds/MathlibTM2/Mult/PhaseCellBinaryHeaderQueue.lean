module

public import IntegerMultBounds.MathlibTM2.Host.BinArithStock
public import IntegerMultBounds.MathlibTM2.Host.OrderedMove
public import IntegerMultBounds.MathlibTM2.StackStockComposition

/-! Generate an ordered fixed-width parameter queue from live unary headers.
Source words are retained and all conversion scratch is restored. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def prependBinaryHeader (src width word saved tmp dst carry : Fin T) : Pr P T Q A U :=
  .seq (toBinary src width word saved tmp carry) (moveRightOrdered word tmp dst)

private theorem orderedMove_within (src tmp dst : Fin T)
    {s f : Store (HΓ (T := T) A) (HS T Q A U)} {n : ℕ}
    (he : Exec body (moveRightOrdered src tmp dst) s n f) (depth B : ℕ) (hb : mnSize s+depth ≤ B) :
    ExecWithin body (fun d z => mnSize z+d ≤ B) depth (moveRightOrdered src tmp dst) s n f := by
  cases he with
  | seq h₁ h₂ =>
    have h₁ := moveR_within src tmp id h₁ depth B hb
    exact .seq h₁ (moveR_within tmp dst id h₂ depth B h₁.final)

theorem prependBinaryHeader_exec (src width word saved tmp dst carry : Fin T)
    (hreg : [src,width,word,saved,tmp,dst].Nodup) (v : HS T Q A U) (S : Stacks T A)
    (hblank : ∀ i ∈ [word,saved,tmp], S.R i = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ (S.R src).length*(4*(S.R width).length+10)+8*(S.R width).length+12 ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2*(4*(S.R width).length+4))
        depth (prependBinaryHeader src width word saved tmp dst carry) (mk v S) n
        (mk v' {S with R := Function.update S.R dst (binSyms (S.R width).length (S.R src).length++S.R dst)}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := toBinary_exec_within (body := body) (u := src) (wR := width)
    (c := word) (saved := saved) (tmp := tmp) (by regs_nodup) carry v S
    (hblank word (by simp)) (hblank saved (by simp)) (hblank tmp (by simp)) depth
  let M : Stacks T A := {S with R := Function.update S.R word (binSyms (S.R width).length (S.R src).length)}
  obtain ⟨v₂,hu₂,he₂⟩ := moveRightOrdered_exec (body := body) word tmp dst
    ‹word ≠ tmp› ‹word ≠ dst› ‹tmp ≠ dst› v₁ M
    (by simp [M,‹word ≠ tmp›.symm,hblank tmp (by simp)])
  have hlen : (M.R word).length = (S.R width).length := by simp [M,binSyms]
  rw [hlen] at he₂
  have hw₂ := orderedMove_within word tmp dst he₂ depth _ he₁.final
  have hwhole := ExecWithin.seq he₁ hw₂
  have hout : (mk v₂ {M with R := Function.update (Function.update M.R word []) dst (M.R word++M.R dst)}) =
      mk v₂ {S with R := Function.update S.R dst (binSyms (S.R width).length (S.R src).length++S.R dst)} := by
    apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hd : i = dst
    · subst i; simp [M,‹word ≠ dst›.symm]
    by_cases hw : i = word
    · subst i; simp [M,hd,hblank word (by simp)]
    · simp [M,hd,hw]
  rw [hout] at hwhole
  exact ⟨v₂,n₁+(4*(S.R width).length+4),hu₂.trans hu₁,by omega,hwhole⟩

def binaryHeaderQueue (width word saved tmp dst carry : Fin T) : List (Fin T) → Pr P T Q A U
  | [] => .act .done
  | src::ports => .seq (binaryHeaderQueue width word saved tmp dst carry ports)
      (prependBinaryHeader src width word saved tmp dst carry)

def binaryHeaderQueueCost (R : Regs T A) (W : ℕ) : List (Fin T) → ℕ
  | [] => 1
  | src::ports => binaryHeaderQueueCost R W ports+(R src).length*(4*W+10)+8*W+12


theorem binaryHeaderQueueCost_eq (R : Regs T A) (W : ℕ) (ports : List (Fin T)) :
    binaryHeaderQueueCost R W ports =
      ((ports.map (fun i => (R i).length)).sum)*(4*W+10)+ports.length*(8*W+12)+1 := by
  induction ports with
  | nil => simp [binaryHeaderQueueCost]
  | cons src ports ih =>
    simp only [binaryHeaderQueueCost,ih,List.map_cons,List.sum_cons,List.length_cons]
    ring

theorem binaryHeaderQueue_exec (width word saved tmp dst carry : Fin T) (ports : List (Fin T))
    (hregs : ∀ src ∈ ports, [src,width,word,saved,tmp,dst].Nodup)
    (v : HS T Q A U) (S : Stacks T A) (hblank : ∀ i ∈ [word,saved,tmp], S.R i = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ binaryHeaderQueueCost S.R (S.R width).length ports ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        ports.length*(2*(4*(S.R width).length+4))) depth (binaryHeaderQueue width word saved tmp dst carry ports)
        (mk v S) n (mk v' {S with R := (Function.update S.R dst
          ((ports.flatMap (fun i => binSyms (S.R width).length (S.R i).length))++S.R dst))}) := by
  induction ports generalizing v S with
  | nil =>
    refine ⟨v,1,rfl,le_rfl,?_⟩
    have he := ExecWithin.act (body := body) (Inv := fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
      ([] : List (Fin T)).length*(2*(4*(S.R width).length+4))) (d := depth) .done (mk v S) (by simp) (by simp [Action.run])
    simpa [binaryHeaderQueue,Function.update_eq_self_iff] using he
  | cons src ports ih =>
    have hr := hregs src (by simp)
    regs_ne hr
    obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := ih (fun i hi => hregs i (by simp [hi])) v S hblank
    let M : Stacks T A := {S with R := (Function.update S.R dst
      ((ports.flatMap (fun i => binSyms (S.R width).length (S.R i).length))++S.R dst))}
    have hframe (i : Fin T) (hi : i ≠ dst) : M.R i = S.R i := Function.update_of_ne hi _ _
    have hblankM : ∀ i ∈ [word,saved,tmp], M.R i = [] := by
      intro i hi
      have hn : i ≠ dst := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl <;> assumption
      rw [hframe i hn,hblank i hi]
    obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := prependBinaryHeader_exec (body := body)
      src width word saved tmp dst carry (hregs src (by simp)) v₁ M hblankM depth
    rw [hframe src ‹src ≠ dst›,hframe width ‹width ≠ dst›] at hn₂ he₂
    have hwhole := mn_seq_within_add he₁ he₂
    have hout : mk v₂ {M with R := (Function.update M.R dst
        (binSyms (S.R width).length (S.R src).length++M.R dst))} =
      mk v₂ {S with R := (Function.update S.R dst
        (((src::ports).flatMap (fun i => binSyms (S.R width).length (S.R i).length))++S.R dst))} := by
      apply congrArg (mk v₂)
      refine Stacks.ext rfl rfl rfl ?_
      funext i
      by_cases hi : i = dst
      · subst i; simp [M,List.flatMap_cons,List.append_assoc]
      · simp [M,hi]
    rw [hout] at hwhole
    refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,?_,hwhole.mono ?_⟩
    · simp only [binaryHeaderQueueCost]
      omega
    · intro d z hz
      simpa only [List.length_cons,Nat.add_mul,Nat.one_mul,Nat.add_assoc] using hz

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
