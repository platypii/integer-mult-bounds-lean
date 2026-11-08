module

public import IntegerMultBounds.MathlibTM2.Routing.FiberScan
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoopBoundedStock
public import IntegerMultBounds.MathlibTM2.Host.StackStock

/-! Ordered fiber scans share one stage reserve. A partial source and growing
archive are bounded by initial stock plus the exact total output volume. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.FiberScanStock
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz FiberScan
variable {T Q A : ℕ} {P U α : Type} {body : P → Pr P T Q A U}

theorem scanFibers_exec_within (clock src archive : Fin T) (hreg : [clock,src,archive].Nodup)
    (p : Pr P T Q A U) (fibers : List α) (input output : α → List (Fin (A+4))) (c reserve : ℕ)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hstep : ∀ x ∈ fibers, ∀ (vi : HS T Q A U) (F : Stacks T A) rest,
      (∀ i, i ≠ src → i ≠ archive → i ≠ clock → F.R i = S.R i) → F.R src = input x++rest →
      ∃ v' n, v'.user = vi.user ∧ n ≤ c ∧
        (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk vi F)+depth+reserve) depth p
          (mk vi F) n (mk v' {F with R := (Function.update (Function.update F.R src rest)
            archive ((output x).reverse++F.R archive))})))
    (hclock : (S.R clock).length = fibers.length)
    (hsrc : S.R src = fibers.flatMap input++tail) (harchive : S.R archive = []) :
    ∃ vf n, vf.user = v.user ∧ n ≤ fibers.length*(c+3)+2*(fibers.flatMap output).length+4 ∧
      Exec body (scanFibers clock src archive p) (mk v S) n
        (mk vf {S with R := (Function.update (Function.update S.R src (fibers.flatMap output++tail)) clock [])}) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (3*(fibers.flatMap output).length+reserve+2)) depth (scanFibers clock src archive p) (mk v S) n
        (mk vf {S with R := (Function.update (Function.update S.R src (fibers.flatMap output++tail)) clock [])})) := by
  have hr := hreg
  regs_ne hr
  let Inv := fun j (F : Stacks T A) => ∃ done todo : List α,
    fibers = done++todo ∧ done.length = j ∧ F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
    (∀ i, i ≠ src → i ≠ archive → i ≠ clock → F.R i = S.R i) ∧
    F.R src = todo.flatMap input++tail ∧
    F.R archive = (done.flatMap output).reverse
  let boundary := mnSize (mk v S)+(fibers.flatMap output).length
  have hbound : ∀ j (vi : HS T Q A U) F, Inv j F → (F.R clock).length ≤ fibers.length →
      mnSize (mk vi F) ≤ boundary := by
    intro j vi F hI hc
    obtain ⟨done,todo,hd,hj,hi,ho,hl,hframe,hs,ha⟩ := hI
    have hinput : (F.R src).length ≤ (S.R src).length := by
      rw [hs,hsrc,hd,List.flatMap_append]
      simp only [List.length_append]
      omega
    have houtput : (F.R archive).length ≤ (fibers.flatMap output).length := by
      rw [ha,hd,List.flatMap_append]
      simp only [List.length_reverse,List.length_append]
      omega
    apply mnSize_mk_le_archive v vi S F archive (fibers.flatMap output).length
    · exact (hostFrameStock_congr hi ho hl).le
    · omega
    · intro i hia
      by_cases his : i = src
      · subst i; exact hinput
      by_cases hic : i = clock
      · subst i; omega
      · rw [hframe i his hia hic]
  obtain ⟨v₁,F,n,hu₁,hn,he,hc,hI⟩ := countedLoop_exec_bounded_stock (body := body) clock p fibers.length c boundary reserve Inv
    (by
      intro j F xs hI
      obtain ⟨done,todo,hd,hj,hi,ho,hl,hframe,hs,ha⟩ := hI
      refine ⟨done,todo,hd,hj,hi,ho,hl,?_,?_,?_⟩
      · intro i his hia hic
        simpa only [Function.update_of_ne hic] using hframe i his hia hic
      · simpa only [Function.update_of_ne ‹clock ≠ src›.symm] using hs
      · simpa only [Function.update_of_ne ‹clock ≠ archive›.symm] using ha)
    hbound
    (by
      intro j hj vi F hI hclockRemaining
      have hb := hbound j vi F hI (by omega)
      obtain ⟨done,todo,hd,hj',hi,ho,hl,hframe,hs,ha⟩ := hI
      cases todo with
      | nil => simp only [List.append_nil] at hd; subst fibers; omega
      | cons x todo =>
        have hx : x ∈ fibers := by rw [hd]; simp
        obtain ⟨v',m,hu,hm,hex⟩ := hstep x hx vi F (todo.flatMap input++tail) hframe
          (by simpa only [List.flatMap_cons,List.append_assoc] using hs)
        let F' : Stacks T A := {F with R := (Function.update (Function.update F.R src
          (todo.flatMap input++tail)) archive ((output x).reverse++F.R archive))}
        refine ⟨v',F',m,hu,hm,?_,?_,done++[x],todo,?_,?_,hi,ho,hl,?_,?_,?_⟩
        · intro depth
          exact (hex depth).mono (by intro d z hz; omega)
        · simp [F',‹clock ≠ src›,‹clock ≠ archive›]
        · simpa only [List.append_assoc,List.singleton_append] using hd
        · simp [hj']
        · intro i his hia hic
          simpa only [F',Function.update_of_ne his,Function.update_of_ne hia] using hframe i his hia hic
        · simp [F',‹src ≠ archive›]
        · simp [F',ha,List.flatMap_append,List.reverse_append])
    v S hclock ⟨[],fibers,rfl,rfl,rfl,rfl,rfl,(by intros; rfl),hsrc,by simpa using harchive⟩
  have hstock := hbound fibers.length v₁ F hI (by rw [hc]; simp)
  obtain ⟨done,todo,hd,hj,hi,ho,hl,hframe,hs,ha⟩ := hI
  have ht : todo = [] := by
    have hh := congrArg List.length hd
    simp only [List.length_append] at hh
    exact List.eq_nil_of_length_eq_zero (by omega)
  subst todo
  simp only [List.append_nil] at hd
  subst done
  simp only [List.flatMap_nil,List.nil_append] at hs
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body archive src ‹src ≠ archive›.symm id v₁ F
  have hfinal : {F with R := movedR F.R archive src id (F.R archive)} =
      {S with R := (Function.update (Function.update S.R src (fibers.flatMap output++tail)) clock [])} := by
    refine Stacks.ext hi ho hl ?_
    funext i
    by_cases his : i = src
    · subst i; simp [movedR,ha,hs,‹clock ≠ src›.symm]
    by_cases hia : i = archive
    · subst i; simp [movedR,‹src ≠ archive›.symm,‹clock ≠ archive›.symm,harchive]
    by_cases hic : i = clock
    · subst i; simp [movedR,‹clock ≠ src›,‹clock ≠ archive›,hc]
    · simp [movedR,his,hia,hic,hframe i his hia hic]
  refine ⟨v₂,n+(2*(F.R archive).length+2),hu₂.trans hu₁,?_,
    (Exec.seq (he 0).toExec he₂).cast rfl (congrArg (mk v₂) hfinal),?_⟩
  · rw [ha,List.length_reverse]
    omega
  · intro depth
    have hm := mn_native_exec_within he₂ 1 (by simp [moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush])
      depth (boundary+depth+(2*(fibers.flatMap output).length+2)) (by rw [ha,List.length_reverse]; omega)
    let I : ℕ → Store (HΓ (T := T) A) (HS T Q A U) → Prop := fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(3*(fibers.flatMap output).length+reserve+2)
    have hl := (he depth).mono (J := I) (by intro d z hz; dsimp only [I,boundary] at *; omega)
    have hm' := hm.mono (J := I) (by intro d z hz; dsimp only [I,boundary] at *; omega)
    exact (ExecWithin.seq hl hm').cast rfl (congrArg (mk v₂) hfinal)

end IntegerMultBounds.MathlibTM2.Routing.FiberScanStock
