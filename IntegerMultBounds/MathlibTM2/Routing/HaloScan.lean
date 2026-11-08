module

public import IntegerMultBounds.MathlibTM2.Routing.HaloScanLayout
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoop

/-! A single fixed counted loop emits a monotone list of window pairs. Only
ordinary metadata and the loop counter depend on the number of windows. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloScan
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz HaloWindowPair HaloScanLayout
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def scan (clock width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp : Fin T) : Pr P T Q A U :=
  countedLoop clock (emitPair width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp)

theorem scan_native (clock width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp : Fin T) :
    mnNativePushBound 3 (scan (P := P) (Q := Q) (A := A) (U := U)
      clock width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp) := by
  refine ⟨?_,?_,emitPair_native _ _ _ _ _ _ _ _ _ _ _ _ _,?_⟩ <;>
    simp [peekR,mnNativePushBound,mnActPush]

/-- The loop endpoint, including its consumed clock and carried final overlap. -/
def finish (clock queue src archive overlap : Fin T) (S : Stacks T A)
    (old : List (Fin (A+4))) (xs : List (WindowPair (Fin (A+4)))) (tail queueTail : List (Fin (A+4))) : Stacks T A :=
  {S with R := (Function.update (Function.update (Function.update (Function.update (Function.update S.R
    clock []) queue queueTail) src tail) archive ((output old xs).reverse++S.R archive)) overlap (remainingOverlap old xs))}

theorem scan_exec
    (clock width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp : Fin T)
    (hreg : [clock,width,queue,binary,duplicate,work,bodyCount,keepCount,src,archive,overlap,spare,saved,tmp].Nodup)
    (V : ℕ) (old : List (Fin (A+4))) (xs : List (WindowPair (Fin (A+4))))
    (hfit : ∀ x ∈ xs, x.Fits V) (tail queueTail : List (Fin (A+4)))
    (v : HS T Q A U) (S : Stacks T A)
    (hclock : (S.R clock).length = xs.length) (hwidth : (S.R width).length = V)
    (hqueue : S.R queue = xs.flatMap (WindowPair.metadata V)++queueTail)
    (hsrc : S.R src = xs.flatMap WindowPair.input++tail) (hold : S.R overlap = old)
    (hblank : ∀ i ∈ [binary,duplicate,work,bodyCount,keepCount,spare,saved,tmp], S.R i = []) :
    ∃ vf n, vf.user = v.user ∧
      n ≤ 2*old.length+30*(xs.flatMap WindowPair.input).length+xs.length*(76*V+149)+2 ∧
      Exec body (scan clock width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp)
        (mk v S) n (mk vf (finish clock queue src archive overlap S old xs tail queueTail)) := by
  have hr := hreg
  regs_ne hr
  let p : Pr P T Q A U := emitPair width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp
  have hloop : ∀ (xs : List (WindowPair (Fin (A+4)))) (old : List (Fin (A+4)))
      (vi : HS T Q A U) (F : Stacks T A),
      (∀ x ∈ xs, x.Fits V) → (F.R clock).length = xs.length → (F.R width).length = V →
      F.R queue = xs.flatMap (WindowPair.metadata V)++queueTail →
      F.R src = xs.flatMap WindowPair.input++tail → F.R overlap = old →
      (∀ i ∈ [binary,duplicate,work,bodyCount,keepCount,spare,saved,tmp], F.R i = []) →
      vi.flag = (F.R clock).head?.isSome →
      ∃ vf n, vf.user = vi.user ∧ n ≤ loopCost V old xs ∧
        Exec body (.loop (·.flag) (countedLoopBody clock p)) (mk vi F) n
          (mk vf (finish clock queue src archive overlap F old xs tail queueTail)) := by
    intro xs
    induction xs with
    | nil =>
      intro old vi F _ hc _ hq hs ho _ hf
      have he : F.R clock = [] := List.eq_nil_of_length_eq_zero hc
      refine ⟨vi,1,rfl,by simp [loopCost],(Exec.loop_false (by simpa [he] using hf)).cast rfl ?_⟩
      apply congrArg (mk vi)
      refine Stacks.ext rfl rfl rfl ?_
      funext i
      simp only [List.flatMap_nil,List.nil_append] at hq hs
      simp only [finish,output,remainingOverlap,List.reverse_nil,List.nil_append]
      rw [←ho,←hs,←hq,←he]
      simp
    | cons x xs ih =>
      intro old vi F hfit hc hw hq hs ho hb hf
      obtain ⟨c,cs,hcs⟩ : ∃ c cs, F.R clock = c::cs := List.exists_cons_of_ne_nil (by intro he; simp [he] at hc)
      let M : Stacks T A := {F with R := Function.update F.R clock cs}
      have hp : Exec body (.act (.pop (.rt clock) (fun v _ => v) .done)) (mk vi F) 1 (mk vi M) := by
        simpa [M,Action.run,hcs,update_rt] using
          (Exec.act (body := body) (.pop (.rt clock) (fun v _ => v) .done) (mk vi F))
      have hx := hfit x (by simp)
      obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := emitPair_exec (body := body)
        width queue binary duplicate work bodyCount keepCount src archive overlap spare saved tmp
        (by regs_nodup) V old x.fresh₁ x.kept₁ x.fresh₂ x.kept₂
        (xs.flatMap WindowPair.input++tail) (xs.flatMap (WindowPair.metadata V)++queueTail)
        hx.1 hx.2.1 hx.2.2.1 hx.2.2.2 vi M
        (by simpa [M,‹clock ≠ width›.symm] using hw)
        (by simpa [M,‹clock ≠ queue›.symm,WindowPair.metadata,List.append_assoc] using hq)
        (by simpa [M,‹clock ≠ src›.symm,WindowPair.input,List.append_assoc] using hs)
        (by simpa [M,‹clock ≠ overlap›.symm] using ho) (by
          intro i hi
          have hic : i ≠ clock := by
            simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
            rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact Ne.symm (by assumption)
          simpa [M,hic] using hb i hi)
      let N : Stacks T A := {M with R := (Function.update (Function.update (Function.update
        (Function.update M.R queue (xs.flatMap (WindowPair.metadata V)++queueTail)) src (xs.flatMap WindowPair.input++tail))
        archive ((x.output old).reverse++M.R archive)) overlap x.kept₂)}
      have off (i : Fin T) (hiq : i ≠ queue) (his : i ≠ src) (hia : i ≠ archive) (hio : i ≠ overlap) : N.R i = M.R i := by
        simp [N,hiq,his,hia,hio]
      have hnclock : N.R clock = cs := by simp [N,M,‹clock ≠ overlap›,‹clock ≠ archive›,‹clock ≠ src›,‹clock ≠ queue›]
      have hpeek := Exec.act (body := body) (peekR clock) (mk v₁ N)
      rw [peekR_run] at hpeek
      obtain ⟨vf,n₂,hu₂,hn₂,he₂⟩ := ih x.kept₂ {v₁ with flag := (N.R clock).head?.isSome} N
        (by intro y hy; exact hfit y (by simp [hy]))
        (by rw [hnclock]; simp only [hcs,List.length_cons] at hc; omega)
        (by rw [off width ‹width ≠ queue› ‹width ≠ src› ‹width ≠ archive› ‹width ≠ overlap›]; simpa [M,‹clock ≠ width›.symm] using hw)
        (by simp [N,‹queue ≠ overlap›,‹queue ≠ archive›,‹queue ≠ src›])
        (by simp [N,‹src ≠ overlap›,‹src ≠ archive›]) (by simp [N]) (by
          intro i hi
          have hbi := hb i hi
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
          rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            rw [off _ (by first | assumption | exact Ne.symm (by assumption))
              (by first | assumption | exact Ne.symm (by assumption))
              (by first | assumption | exact Ne.symm (by assumption))
              (by first | assumption | exact Ne.symm (by assumption))] <;>
            simpa [M,Ne.symm (show clock ≠ _ from by assumption)] using hbi) rfl
      refine ⟨vf,1+(n₁+1)+n₂+1,hu₂.trans hu₁,by simp only [loopCost]; omega,
        (Exec.loop_true (by simpa [hcs] using hf) (Exec.seq hp (Exec.seq he₁ hpeek)) he₂).cast rfl ?_⟩
      apply congrArg (mk vf)
      refine Stacks.ext rfl rfl rfl ?_
      funext i
      by_cases hio : i = overlap
      · subst i; simp [finish,remainingOverlap]
      by_cases hia : i = archive
      · subst i
        simp [finish,N,M,output,‹archive ≠ overlap›,‹clock ≠ archive›.symm,List.reverse_append,List.append_assoc]
      by_cases his : i = src
      · subst i; simp [finish,‹src ≠ overlap›,‹src ≠ archive›]
      by_cases hiq : i = queue
      · subst i; simp [finish,‹queue ≠ overlap›,‹queue ≠ archive›,‹queue ≠ src›]
      by_cases hic : i = clock
      · subst i; simp [finish,‹clock ≠ overlap›,‹clock ≠ archive›,‹clock ≠ src›,‹clock ≠ queue›]
      · simp [finish,N,M,hio,hia,his,hiq,hic]
  have hpeek := Exec.act (body := body) (peekR clock) (mk v S)
  rw [peekR_run] at hpeek
  obtain ⟨vf,n,hu,hn,he⟩ := hloop xs old {v with flag := (S.R clock).head?.isSome} S
    hfit hclock hwidth hqueue hsrc hold hblank rfl
  exact ⟨vf,1+n,hu,by have h := loopCost_le V old xs; omega,Exec.seq hpeek he⟩

end IntegerMultBounds.MathlibTM2.Routing.HaloScan
