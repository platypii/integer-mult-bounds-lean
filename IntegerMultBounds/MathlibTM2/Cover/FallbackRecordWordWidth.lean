module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMovePrefix
public import IntegerMultBounds.MathlibTM2.Fast.Output

/-! Move a padded record coefficient onto a canonical-width archive. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack Host Mult.PhaseCellToeplitz Mult.ShortConv

def narrowRecordWord {T Q A : ℕ} {F U : Type} (r : Fin 7 ↪ Fin T) : Pr F T Q A U :=
  (movePrefix (r 0) (r 1) (r 2) (r 3) (r 4)).seq
    ((transfer (r 5) (r 2) (r 6) (r 4)).seq (Fast.clearR (r 2)))

theorem narrowRecordWord_exec {T Q A : ℕ} {F U : Type} (body : F → Pr F T Q A U)
    (r : Fin 7 ↪ Fin T) (width extra x : ℕ) (fits : x < 2^width) (tail : List (Fin (A+4)))
    (u : HS T Q A U) (S : Stacks T A) (field : S.R (r 1) = binSyms (width+extra) x ++ tail)
    (long : (S.R (r 0)).length = width+extra) (short : (S.R (r 5)).length = width)
    (empty : ∀ i ∈ ([2,3,4] : List (Fin 7)), S.R (r i) = []) :
    ∃ z, z.user = u.user ∧ Exec body (narrowRecordWord r) (mk u S) (10*width+8*extra+12)
      (mk z {S with R := Function.update (Function.update S.R (r 1) tail) (r 6) ((binSyms width x).reverse ++ S.R (r 6))}) := by
  have first := ((by decide : ([0,1,2,3,4] : List (Fin 7)).Nodup).map r.injective)
  have second := ((by decide : ([5,2,6,4] : List (Fin 7)).Nodup).map r.injective)
  obtain ⟨v,hv,load⟩ := movePrefix_exec (body := body) first _ tail u S field
    (long.trans (length_binSyms ..).symm) (empty 3 (by decide)) (empty 4 (by decide))
  rw [empty 2 (by decide),List.append_nil] at load
  let D : Stacks T A := {S with R := Function.update (Function.update S.R (r 1) tail) (r 2) (binSyms (width+extra) x)}
  have parts : D.R (r 2) = binSyms width x ++ binSyms extra 0 := by
    simp [D,binSyms_append width extra x,Nat.div_eq_of_lt fits]
  obtain ⟨v',hv',move⟩ := transfer_exec (body := body) second v D _ _ parts
    (by simp [D,r.injective.eq_iff,short]) (by simp [D,r.injective.eq_iff,empty])
  let E : Stacks T A := {D with R := Function.update (Function.update D.R (r 2) (binSyms extra 0)) (r 6) ((binSyms width x).reverse ++ D.R (r 6))}
  obtain ⟨z,hz,clear⟩ := Fast.clearR_exec body (r 2) v' E
  refine ⟨z,hz.trans (hv'.trans hv),(Exec.seq load (Exec.seq move clear)).cast ?_ ?_⟩
  · simp [E,r.injective.eq_iff,length_binSyms]; omega
  · congr 2
    funext j
    by_cases a : j = r 2 <;> by_cases b : j = r 6 <;>
      simp_all [D,E,Function.update_apply,r.injective.eq_iff]

def narrowRecordWords {T Q A : ℕ} {F U : Type} (r : Fin 7 ↪ Fin T) : ℕ → Pr F T Q A U
  | 0 => .act .done
  | n+1 => (narrowRecordWord r).seq (narrowRecordWords r n)

theorem narrowRecordWords_exec {T Q A : ℕ} {F U : Type} (body : F → Pr F T Q A U)
    (r : Fin 7 ↪ Fin T) (width extra : ℕ) (xs : List ℕ) (fits : ∀ x ∈ xs, x < 2^width)
    (tail : List (Fin (A+4))) (u : HS T Q A U) (S : Stacks T A)
    (input : S.R (r 1) = (xs.map (binSyms (width+extra))).flatten ++ tail)
    (long : (S.R (r 0)).length = width+extra) (short : (S.R (r 5)).length = width)
    (empty : ∀ i ∈ ([2,3,4] : List (Fin 7)), S.R (r i) = []) :
    ∃ z, z.user = u.user ∧ Exec body (narrowRecordWords r xs.length) (mk u S)
      (xs.length*(10*width+8*extra+12)+1)
      (mk z {S with R := Function.update (Function.update S.R (r 1) tail) (r 6) ((xs.map (binSyms width)).flatten.reverse ++ S.R (r 6))}) := by
  induction xs generalizing u S with
  | nil =>
    simp only [List.map_nil,List.flatten_nil,List.nil_append] at input
    refine ⟨u,rfl,?_⟩
    simpa [← input,narrowRecordWords,r.injective.eq_iff] using Exec.act (body := body) (.done : Act T Q A U) (mk u S)
  | cons x xs ih =>
    let rest := (xs.map (binSyms (A := A) (width+extra))).flatten ++ tail
    obtain ⟨v,hv,word⟩ := narrowRecordWord_exec body r width extra x (fits x (by simp)) rest u S
      (by simpa [rest,List.append_assoc] using input) long short empty
    let D : Stacks T A := {S with R := Function.update (Function.update S.R (r 1) rest) (r 6) ((binSyms width x).reverse ++ S.R (r 6))}
    obtain ⟨z,hz,run⟩ := ih (fun y hy => fits y (by simp [hy])) v D
      (by simp [D,rest,r.injective.eq_iff]) (by simpa [D,r.injective.eq_iff] using long)
      (by simpa [D,r.injective.eq_iff] using short) (by
        intro i hi
        have h := (by decide : ∀ i ∈ ([2,3,4] : List (Fin 7)), i ≠ 1 ∧ i ≠ 6) i hi
        simpa [D,r.injective.eq_iff,h.1,h.2] using empty i hi)
    refine ⟨z,hz.trans hv,(Exec.seq word run).cast (by simp [Nat.succ_mul]; omega) ?_⟩
    congr 2
    funext j
    by_cases a : j = r 1 <;> by_cases b : j = r 6 <;>
      simp_all [D,r.injective.eq_iff,List.append_assoc]

/-- Restore the coefficients to their original order on the destination tape. -/
theorem narrowRecordArchive_exec {T Q A : ℕ} {F U : Type} (body : F → Pr F T Q A U)
    (r : Fin 7 ↪ Fin T) (dst : Fin T) (outside : ∀ i, dst ≠ r i)
    (width extra : ℕ) (xs : List ℕ) (fits : ∀ x ∈ xs, x < 2^width)
    (tail : List (Fin (A+4))) (u : HS T Q A U) (S : Stacks T A)
    (input : S.R (r 1) = (xs.map (binSyms (width+extra))).flatten ++ tail)
    (long : (S.R (r 0)).length = width+extra) (short : (S.R (r 5)).length = width)
    (empty : ∀ i ∈ ([2,3,4,6] : List (Fin 7)), S.R (r i) = []) :
    let words := (xs.map (binSyms (A := A) width)).flatten
    ∃ z, z.user = u.user ∧ Exec body ((narrowRecordWords r xs.length).seq (moveR (r 6) dst id))
      (mk u S) (xs.length*(10*width+8*extra+12)+1+(2*words.length+2))
      (mk z {S with R := Function.update (Function.update S.R (r 1) tail) dst (words ++ S.R dst)}) := by
  intro words
  obtain ⟨v,hv,run⟩ := narrowRecordWords_exec body r width extra xs fits tail u S input long short
    (fun i hi => empty i ((by decide : ∀ k ∈ ([2,3,4] : List (Fin 7)), k ∈ ([2,3,4,6] : List (Fin 7))) i hi))
  rw [empty 6 (by decide),List.append_nil] at run
  let D : Stacks T A := {S with R := Function.update (Function.update S.R (r 1) tail) (r 6) words.reverse}
  obtain ⟨z,hz,finish⟩ := moveR_exec body (r 6) dst (outside 6).symm id v D
  refine ⟨z,hz.trans hv,(Exec.seq run finish).cast (by simp [D]) ?_⟩
  congr 2
  funext j
  have distinct := (outside 6).symm
  by_cases a : j = dst <;> by_cases b : j = r 6 <;>
    simp_all [D,movedR,Function.update_apply,r.injective.eq_iff]

end IntegerMultBounds.MathlibTM2.Cover.Fallback
