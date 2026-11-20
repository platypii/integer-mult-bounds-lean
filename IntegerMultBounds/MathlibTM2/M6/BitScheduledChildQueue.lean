module

public import IntegerMultBounds.MathlibTM2.Cover.LabelDirectoryCaller
public import IntegerMultBounds.MathlibTM2.M6.BitDescriptorRecurrence

/-! Transfer the scheduled PR589 child's inherited label directory. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Cover Host Stack
open Shared50ModularControl (prime)

/-- The dispatcher's 21 registers precede the scanner's private registers.
Both branches share the directory, scratch and width. Each has its own count. -/
def childQueuePorts (good : Bool) : Fin 8 ↪ Fin (21+59) :=
  ⟨![2,7,Fin.natAdd 21 58,6,13,if good then 3 else 5,1,Fin.natAdd 21 47],
    by cases good <;> decide⟩

/-- Install the partition's leading queue at a scheduled nonroot child.
The caller supplies its count and extended width. Alignment at the root
pays for every record's prefix at the child's active width. -/
theorem scheduledChildQueue_exec {T Q : ℕ} {P U : Type} (body : P → Pr P T Q prime U)
    (bank : Fin (21+59) ↪ Fin T) (good : Bool) (root : RecursiveInterchangeLayout.Descriptor)
    (depth b cutoff : ℕ) (levels : 0 < depth) (base : 0 < b)
    (rootWidth : root.width = 64^depth*b) (stop : 42^depth*b ≤ cutoff)
    (path : List (Fin nodeChildren5.length)) (i : Fin nodeChildren5.length)
    (selected : List ℕ) (ancestor : ℕ → List (Fin (prime+4)))
    (tail : List (Fin (prime+4))) (u : HS T Q prime U) (S : Stacks T prime) :
    let r := (childQueuePorts good).trans bank
    let v := path.foldl (scheduledChild prime) root
    let a := directoryDigits prime root path
    let w := v.width/64
    let word := fun j : ℕ => LabelDirectory.entry ancestor 64 w (selected[j]?.getD 0)
    let size := selected.length*(a+w*(64*64))
    cutoff ≤ (scheduledChild prime v i).width →
    (∀ j ∈ selected, (ancestor j).length = a) →
    S.R (r 1) = selected.flatMap (LabelDirectory.entry ancestor 64 w) ++ tail →
    (S.R (r 5)).length = selected.length → (S.R (r 6)).length = a+w*(64*64) →
    S.R (r 0) = [] → S.R (r 2) = [] → S.R (r 3) = [] → S.R (r 4) = [] → S.R (r 7) = [] →
    ∃ z t, z.user = u.user ∧ t ≤ 12*size+9*selected.length+4*(a+w*(64*64))+16 ∧
      (S.R (r 6)).length = directoryDigits prime root (path++[i]) ∧
      (S.R (r 6)).length ≤ prime^(scheduledChild prime v i).width ∧
      (∀ j < selected.length, (word j).length = (S.R (r 6)).length) ∧
      Exec body ((((Mult.ShortConv.unaryProduct (r 5) (r 6) (r 0) (r 3) (r 4)).seq
        (Mult.PhaseCellToeplitz.takePrefix (r 0) (r 1) (r 2) (r 3) (r 4))).seq (Node.ucopy (r 6) (r 7) (r 3))).seq (bclear (r 0)))
        (mk u S) t (mk z {S with R := (Function.update (Function.update (Function.update S.R (bank 7) tail)
          (bank (Fin.natAdd 21 58)) ((List.range selected.length).flatMap word)) (bank (Fin.natAdd 21 47))
          (List.replicate (directoryDigits prime root (path++[i])) Node.tick))}) := by
  intro r v a w word size active widths source rows header count dst buf tmp blankWidth
  obtain ⟨z,t,user,paid,words,run⟩ := LabelDirectoryCaller.takeChild_exec (body := body)
    ((Fin.castLEEmb (by decide : 7 ≤ 8)).trans r) selected ancestor 64 w a widths tail u S source rows header count dst buf tmp
  have extended := header.trans (directoryDigits_append_call prime root path i).symm
  have fit := directoryDigits_fit_aligned prime Shared50ModularControl.prime_prime.two_le root
    depth b cutoff levels base rootWidth stop (path++[i]) (by simpa [List.foldl_append,v] using active)
  let F : Stacks T prime := {S with R := (Function.update (Function.update
    (Function.update S.R (r 0) (List.replicate size Node.tick)) (r 1) tail)
    (r 2) ((List.range selected.length).flatMap word))}
  obtain ⟨out,same,copy⟩ := Node.ucopy_exec (body := body) (a := r 6) (b := r 7) (t := r 3)
    (by simp) (by simp) (by simp) z F (by simpa [F] using buf)
  have widthNow : (F.R (r 6)).length = (S.R (r 6)).length := by simp [F]
  rw [widthNow,show F.R (r 7) = [] by simpa [F] using blankWidth,List.append_nil] at copy
  let D : Stacks T prime := {F with R := (Function.update F.R (r 7)
    (List.replicate (S.R (r 6)).length Node.tick))}
  obtain ⟨final,unchanged,_,clear⟩ := bclear_exec (body := body) (r 0) out D
  have len : (D.R (r 0)).length = size := by simp [D,F]
  rw [len] at clear
  refine ⟨final,_,unchanged.trans (same.trans user),?_,extended,extended ▸ (by simpa [List.foldl_append,v] using fit),
    fun j hj => (words j hj).trans header.symm,(Exec.seq (Exec.seq run copy) clear).cast rfl ?_⟩
  · rw [header]
    omega
  · congr 1
    refine Stacks.ext (by rfl) (by rfl) (by rfl) ?_
    funext k
    change Function.update D.R (r 0) [] k = Function.update (Function.update
      (Function.update S.R (r 1) tail) (r 2) ((List.range selected.length).flatMap word)) (r 7)
        (List.replicate (directoryDigits prime root (path++[i])) Node.tick) k
    by_cases eq : k = r 0
    · subst k; simp [count]
    · simp [D,F,Function.update_apply,eq,extended]

/-- The scanner view of the queue transfer on a fresh private bank. -/
theorem childQueue_scanner {T : ℕ} (bank : Fin (21+59) ↪ Fin T) (S : Stacks T prime)
    (tail queue : List (Fin (prime+4))) (width : ℕ)
    (fresh : ∀ j : Fin 59, S.R (bank (Fin.natAdd 21 j)) = []) :
    let R := Function.update (Function.update (Function.update S.R (bank 7) tail)
      (bank (Fin.natAdd 21 58)) queue) (bank (Fin.natAdd 21 47)) (List.replicate width Node.tick)
    ∀ j : Fin 59, R (bank (Fin.natAdd 21 j)) = if j.val = 47 then List.replicate width (bitSymbol true)
      else if j.val = 58 then queue else [] := by
  intro R j
  have off : Fin.natAdd 21 j ≠ (7 : Fin 80) := by intro eq; have := congrArg Fin.val eq; simp at this; omega
  by_cases widthCell : j = 47
  · subst j; simp [R,Node.tick]
  by_cases queueCell : j = 58
  · subst j; simp [R]
  have ne47 := bank.injective.ne (show Fin.natAdd 21 j ≠ Fin.natAdd 21 (47 : Fin 59)
    from fun eq => widthCell ((Fin.natAddEmb 21).injective eq))
  have ne58 := bank.injective.ne (show Fin.natAdd 21 j ≠ Fin.natAdd 21 (58 : Fin 59)
    from fun eq => queueCell ((Fin.natAddEmb 21).injective eq))
  simp only [R,Function.update_of_ne ne47,Function.update_of_ne ne58,
    Function.update_of_ne (bank.injective.ne off),fresh,
    show j.val ≠ 47 from fun eq => widthCell (Fin.ext eq),
    show j.val ≠ 58 from fun eq => queueCell (Fin.ext eq),ite_false]

end IntegerMultBounds.MathlibTM2.M6.BitNode
