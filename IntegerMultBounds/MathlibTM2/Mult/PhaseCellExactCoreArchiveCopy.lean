module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExactCoreRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReverseCopyRows

/-! Feed the physical reverse-core archive to grouped publication. One restoring
row scan recovers increasing core order while preserving each replica block. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem exactCoreArchive_copy_exec {p W coreWidth L : ℕ}
    (ks : List ℕ) (Fs : List (ZMod s → GaussianInt))
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)) (batches : List (List (List GaussianInt)))
    (h : List.Forall₂ (fun k rows => ExactCoreRows (A := A) p W coreWidth k Fs J rows) ks batches)
    (hcore : ∀ k ∈ ks, coreLength s coreWidth k = L)
    (count savedCount width source archive dst saved tmp : Fin T)
    (hreg : [count,savedCount,width,source,archive,dst,saved,tmp].Nodup)
    (borrowed : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hcount : (S.R count).length = ks.length) (hwidth : (S.R width).length = Fs.length*(L*W))
    (hsource : S.R source = (batches.map (fun rows => cstream A W rows.flatten)).reverse.flatten++borrowed)
    (hfresh : ∀ r ∈ [savedCount,archive,saved,tmp], S.R r = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ reverseCopyRowsCost ks.length (Fs.length*(L*W)) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        2*reverseCopyRowsCost ks.length (Fs.length*(L*W))) depth
        (reverseCopyRows count savedCount width source archive dst saved tmp) (mk v S) n
        (mk v' {S with R := (Function.update S.R dst
          ((batches.map (fun rows => cstream A W rows.flatten)).flatten++S.R dst))}) := by
  have hshape : ∀ rows ∈ batches, rows.length = Fs.length ∧ ∀ row ∈ rows, row.length = L := by
    clear hcount hsource
    induction h with
    | nil => simp
    | @cons k rows ks batches hk htail ih =>
      intro rs hrs
      rcases List.mem_cons.mp hrs with rfl | hrs
      · exact ⟨hk.1,fun row hr => (hk.2.1 row hr).trans (hcore k (by simp))⟩
      · exact ih (fun k hk => hcore k (by simp [hk])) rs hrs
  have hlen : ∀ word ∈ (batches.map (fun rows => cstream A W rows.flatten)).reverse,
      word.length = Fs.length*(L*W) := by
    intro word hword
    obtain ⟨rows,hr,rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hword)
    rw [length_cstream,length_flatten_const rows (hshape rows hr).2,(hshape rows hr).1]
    exact Nat.mul_assoc _ _ _
  obtain ⟨v',n,hu,hn,he⟩ := reverseCopyRows_exec_within (body := body)
    count savedCount width source archive dst saved tmp hreg (Fs.length*(L*W))
    (batches.map (fun rows => cstream A W rows.flatten)).reverse hlen borrowed v S
    (by simpa only [List.length_reverse,List.length_map,←h.length_eq] using hcount)
    hwidth hsource hfresh depth
  refine ⟨v',n,hu,?_,?_⟩
  · simpa only [List.length_reverse,List.length_map,←h.length_eq] using hn
  · simpa only [List.length_reverse,List.length_map,←h.length_eq,List.reverse_reverse] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
