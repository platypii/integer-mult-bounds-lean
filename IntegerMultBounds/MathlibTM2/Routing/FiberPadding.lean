module

public import IntegerMultBounds.MathlibTM2.Routing.FiberScan
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDiscardPrefix

/-! Ordered padding and cropping of one complete field at a time. Row bodies
advance into the common archive; the structural scanner restores row order. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.FiberPadding
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  FiberScan SmallFieldMove
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def padFiber (volume padding src archive tmp : Fin T) (zero : Fin (A+4)) : Pr P T Q A U :=
  .seq (transfer volume src archive tmp) (umulSym 1 zero padding archive tmp)

theorem padFiber_exec (volume padding src archive tmp : Fin T)
    (hreg : [volume,padding,src,archive,tmp].Nodup) (zero : Fin (A+4))
    (xs tail : List (Fin (A+4))) (K : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hvolume : (S.R volume).length = xs.length) (hpadding : (S.R padding).length = K)
    (hsrc : S.R src = xs++tail) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧ Exec body (padFiber volume padding src archive tmp zero) (mk v S)
      (4*(xs.length+K)+8)
      (mk v' {S with R := (Function.update (Function.update S.R src tail)
        archive ((xs++List.replicate K zero).reverse++S.R archive))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := transfer_exec (body := body) (count := volume) (src := src)
    (dst := archive) (tmp := tmp) (by regs_nodup) v S xs tail hsrc hvolume htmp
  let M : Stacks T A := {S with R := (Function.update (Function.update S.R src tail)
    archive (xs.reverse++S.R archive))}
  obtain ⟨v₂,hu₂,he₂⟩ := umulSym_exec (body := body) 1 zero (a := padding) (b := archive) (t := tmp)
    ‹padding ≠ archive› ‹padding ≠ tmp› ‹archive ≠ tmp› v₁ M
    (by simp [M,‹src ≠ tmp›.symm,‹archive ≠ tmp›.symm,htmp])
  refine ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁ he₂).cast ?_ ?_⟩
  · simp only [M,Function.update_of_ne ‹padding ≠ src›,Function.update_of_ne ‹padding ≠ archive›,hpadding]
    omega
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases his : i = src <;> by_cases hia : i = archive <;>
      simp_all [M,List.reverse_append,List.append_assoc]

def cropFiber (volume padding src archive trash tmp : Fin T) : Pr P T Q A U :=
  .seq (transfer volume src archive tmp) (discardPrefix padding src trash tmp)

/-- Cropping removes only the current field's trailing extension. The discarded
symbols need not be zero, so the same program also handles ordered core crops. -/
theorem cropFiber_exec (volume padding src archive trash tmp : Fin T)
    (hreg : [volume,padding,src,archive,trash,tmp].Nodup)
    (xs extra tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hvolume : (S.R volume).length = xs.length) (hpadding : (S.R padding).length = extra.length)
    (hsrc : S.R src = xs++extra++tail) (htrash : S.R trash = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧ Exec body (cropFiber volume padding src archive trash tmp) (mk v S)
      ((4*xs.length+4)+(6*extra.length+6))
      (mk v' {S with R := (Function.update (Function.update S.R src tail)
        archive (xs.reverse++S.R archive))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := transfer_exec (body := body) (count := volume) (src := src)
    (dst := archive) (tmp := tmp) (by regs_nodup) v S xs (extra++tail)
    (by simpa only [List.append_assoc] using hsrc) hvolume htmp
  let M : Stacks T A := {S with R := (Function.update (Function.update S.R src (extra++tail))
    archive (xs.reverse++S.R archive))}
  obtain ⟨v₂,hu₂,he₂⟩ := discardPrefix_exec (body := body) (count := padding) (src := src)
    (trash := trash) (tmp := tmp) (by regs_nodup) extra tail v₁ M
    (by simp [M,‹src ≠ archive›])
    (by simp [M,‹padding ≠ src›,‹padding ≠ archive›,hpadding])
    (by simp [M,‹src ≠ trash›.symm,‹archive ≠ trash›.symm,htrash])
    (by simp [M,‹src ≠ tmp›.symm,‹archive ≠ tmp›.symm,htmp])
  refine ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁ he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases his : i = src <;> by_cases hia : i = archive <;>
    simp_all [M]

def padFibers (clock volume padding src archive tmp : Fin T) (zero : Fin (A+4)) : Pr P T Q A U :=
  scanFibers clock src archive (padFiber volume padding src archive tmp zero)

theorem padFibers_exec (clock volume padding src archive tmp : Fin T)
    (hreg : [clock,volume,padding,src,archive,tmp].Nodup) (zero : Fin (A+4))
    (rows : List (List (Fin (A+4)))) (V K : ℕ) (hlen : ∀ xs ∈ rows, xs.length = V)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hclock : (S.R clock).length = rows.length) (hvolume : (S.R volume).length = V)
    (hpadding : (S.R padding).length = K) (hsrc : S.R src = rows.flatten++tail)
    (harchive : S.R archive = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ rows.length*(6*(V+K)+11)+4 ∧
      Exec body (padFibers clock volume padding src archive tmp zero) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R src
          (rows.flatMap (fun xs => xs++List.replicate K zero)++tail)) clock [])}) := by
  have hr := hreg
  regs_ne hr
  have houtput : (rows.flatMap (fun xs => xs++List.replicate K zero)).length = rows.length*(V+K) := by
    rw [List.length_flatMap,List.map_eq_replicate_iff.mpr ?_,List.sum_replicate,smul_eq_mul]
    intro xs hm; simp only [List.length_append,List.length_replicate,hlen xs hm]
  obtain ⟨v',n,hu,hn,he⟩ := scanFibers_exec (body := body) clock src archive (by regs_nodup)
    (padFiber volume padding src archive tmp zero) rows id (fun xs => xs++List.replicate K zero)
    (4*(V+K)+8) tail v S
    (by
      intro xs hm vi F rest hframe hs
      have hkeep (i : Fin T) (hi : i ∈ [volume,padding,tmp]) : F.R i = S.R i := by
        apply hframe
        all_goals
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
          rcases hi with rfl | rfl | rfl
          all_goals first | assumption | (apply Ne.symm; assumption)
      obtain ⟨vf,hu,he⟩ := padFiber_exec (body := body) volume padding src archive tmp (by regs_nodup)
        zero xs rest K vi F
        (by rw [hkeep _ (by simp),hvolume,hlen xs hm])
        (by rw [hkeep _ (by simp)]; exact hpadding) hs
        (by rw [hkeep _ (by simp)]; exact htmp)
      exact ⟨vf,_,hu,by rw [hlen xs hm],he⟩)
    hclock (by simpa only [List.flatMap_id] using hsrc) harchive
  refine ⟨v',n,hu,?_,he⟩
  rw [houtput] at hn
  nlinarith only [hn]

def cropFibers (clock volume padding src archive trash tmp : Fin T) : Pr P T Q A U :=
  scanFibers clock src archive (cropFiber volume padding src archive trash tmp)

theorem cropFibers_exec (clock volume padding src archive trash tmp : Fin T)
    (hreg : [clock,volume,padding,src,archive,trash,tmp].Nodup)
    (rows : List (List (Fin (A+4)) × List (Fin (A+4)))) (V K : ℕ)
    (hlen : ∀ r ∈ rows, r.1.length = V ∧ r.2.length = K)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hclock : (S.R clock).length = rows.length) (hvolume : (S.R volume).length = V)
    (hpadding : (S.R padding).length = K) (hsrc : S.R src = pairStream rows++tail)
    (harchive : S.R archive = []) (htrash : S.R trash = []) (htmp : S.R tmp = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ rows.length*(6*(V+K)+13)+4 ∧
      Exec body (cropFibers clock volume padding src archive trash tmp) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R src
          (rows.flatMap Prod.fst++tail)) clock [])}) := by
  have hr := hreg
  regs_ne hr
  have houtput : (rows.flatMap Prod.fst).length = rows.length*V := by
    rw [List.length_flatMap,List.map_eq_replicate_iff.mpr ?_,List.sum_replicate,smul_eq_mul]
    intro r hm; exact (hlen r hm).1
  obtain ⟨v',n,hu,hn,he⟩ := scanFibers_exec (body := body) clock src archive (by regs_nodup)
    (cropFiber volume padding src archive trash tmp) rows (fun r => r.1++r.2) Prod.fst
    (4*V+6*K+10) tail v S
    (by
      intro r hm vi F rest hframe hs
      have hkeep (i : Fin T) (hi : i ∈ [volume,padding,trash,tmp]) : F.R i = S.R i := by
        apply hframe
        all_goals
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
          rcases hi with rfl | rfl | rfl | rfl
          all_goals first | assumption | (apply Ne.symm; assumption)
      obtain ⟨vf,hu,he⟩ := cropFiber_exec (body := body) volume padding src archive trash tmp (by regs_nodup)
        r.1 r.2 rest vi F
        (by rw [hkeep _ (by simp),hvolume,(hlen r hm).1])
        (by rw [hkeep _ (by simp),hpadding,(hlen r hm).2])
        (by simpa only [List.append_assoc] using hs)
        (by rw [hkeep _ (by simp)]; exact htrash)
        (by rw [hkeep _ (by simp)]; exact htmp)
      exact ⟨vf,_,hu,by rw [(hlen r hm).1,(hlen r hm).2]; omega,he⟩)
    hclock hsrc harchive
  refine ⟨v',n,hu,?_,he⟩
  rw [houtput] at hn
  nlinarith only [hn]

theorem padFibers_pushBound (clock volume padding src archive tmp : Fin T) (zero : Fin (A+4)) :
    mnNativePushBound 2 (padFibers (P := P) (Q := Q) (U := U) clock volume padding src archive tmp zero) := by
  apply scanFibers_pushBound
  simp [padFiber,transfer,umulSym,scanR,keepIn,transferAct,drainR,popDo,pushN,
    moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

theorem cropFibers_pushBound (clock volume padding src archive trash tmp : Fin T) :
    mnNativePushBound 2 (cropFibers (P := P) (Q := Q) (A := A) (U := U) clock volume padding src archive trash tmp) := by
  apply scanFibers_pushBound
  simp [cropFiber,discardPrefix,transfer,uclear,scanR,keepIn,transferAct,drainR,popDo,
    moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]

end IntegerMultBounds.MathlibTM2.Routing.FiberPadding
