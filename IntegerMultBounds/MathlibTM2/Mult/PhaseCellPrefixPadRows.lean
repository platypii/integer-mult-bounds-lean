module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice
public import IntegerMultBounds.MathlibTM2.Node.ScanPStock

/-! One linear pass prefixes every fixed-width row with the same padding word.
The runtime row counter and all scratch are restored. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def prefixPadRow (rowSymbols padSymbols src acc saved tmp : Fin T) (fill : Fin (A+4)) : Pr P T Q A U :=
  .seq (umulSym 1 fill padSymbols acc saved) (transfer rowSymbols src acc tmp)

def prefixPadRows (rowSymbols padSymbols src acc saved tmp rows savedRows : Fin T)
    (fill : Fin (A+4)) : Pr P T Q A U :=
  .seq (scanP rows savedRows (prefixPadRow rowSymbols padSymbols src acc saved tmp fill)) (moveR acc src id)

theorem prefixPadRow_native (rowSymbols padSymbols src acc saved tmp : Fin T) (fill : Fin (A+4)) :
    mnNativePushBound 2 (prefixPadRow (P := P) (Q := Q) (A := A) (U := U)
      rowSymbols padSymbols src acc saved tmp fill) := by
  simp [prefixPadRow,umulSym,scanR,drainR,popDo,keepIn,pushN,moveR,moveStep,whileR,peekR,
    transfer,transferAct,mnNativePushBound,mnActPush]

theorem prefixPadRow_exec (rowSymbols padSymbols src acc saved tmp : Fin T)
    (hreg : [rowSymbols,padSymbols,src,acc,saved,tmp].Nodup) (fill : Fin (A+4)) (padding : ℕ)
    (xs tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hrow : (S.R rowSymbols).length = xs.length) (hpad : (S.R padSymbols).length = padding)
    (hsrc : S.R src = xs++tail) (hsaved : S.R saved = []) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧ Exec body (prefixPadRow rowSymbols padSymbols src acc saved tmp fill)
      (Host.mk v S) (4*(xs.length+padding)+8)
      (Host.mk v' {S with R := (Function.update (Function.update S.R src tail) acc
        (xs.reverse++(List.replicate padding fill++S.R acc)))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := umulSym_exec (body := body) 1 fill ‹padSymbols ≠ acc› ‹padSymbols ≠ saved›
    ‹acc ≠ saved› v S hsaved
  let F : Stacks T A := {S with R := Function.update S.R acc (List.replicate padding fill++S.R acc)}
  have he₁' : Exec body (umulSym 1 fill padSymbols acc saved) (Host.mk v S) (4*padding+4) (Host.mk v₁ F) := by
    simpa only [hpad,Nat.one_mul] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := transfer_exec (body := body) (count := rowSymbols) (src := src) (dst := acc)
    (tmp := tmp) (by regs_nodup) v₁ F xs tail
    (by simpa [F,‹src ≠ acc›] using hsrc) (by simpa [F,‹rowSymbols ≠ acc›] using hrow)
    (by simpa [F,‹acc ≠ tmp›.symm] using htmp)
  refine ⟨v₂,hu₂.trans hu₁,(Exec.seq he₁' he₂).cast (by omega) ?_⟩
  apply congrArg (Host.mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hs : k = src <;> by_cases ha : k = acc <;> simp [F,hs,ha,‹src ≠ acc›]

private theorem prefixPadRow_size (src acc : Fin T) (hsa : src ≠ acc)
    (xs tail pad : List (Fin (A+4))) (v w : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = xs++tail) :
    mnSize (Host.mk w {S with R := (Function.update (Function.update S.R src tail) acc
      (xs.reverse++(pad++S.R acc)))}) = mnSize (Host.mk v S)+pad.length := by
  let F : Stacks T A := {S with R := Function.update S.R src tail}
  have h₁ : mnSize (Host.mk v F)+(S.R src).length = mnSize (Host.mk v S)+tail.length := by
    simpa only [F,Host.mk,update_rt,get_rt] using mn_size_update (Host.mk v S) v (.rt src) tail
  have h₂ : mnSize (Host.mk w {F with R := Function.update F.R acc (xs.reverse++(pad++S.R acc))})+(F.R acc).length =
      mnSize (Host.mk v F)+(xs.reverse++(pad++S.R acc)).length := by
    simpa only [Host.mk,update_rt,get_rt] using
      mn_size_update (Host.mk v F) w (.rt acc) (xs.reverse++(pad++S.R acc))
  have ha : F.R acc = S.R acc := Function.update_of_ne hsa.symm _ _
  rw [ha,List.length_append,List.length_reverse,List.length_append] at h₂
  rw [hsrc,List.length_append] at h₁
  change mnSize (Host.mk w {F with R := Function.update F.R acc (xs.reverse++(pad++S.R acc))}) = _
  omega

/-- Per-row padding uses one forward source pass and one final reversal. -/
theorem prefixPadRows_exec_within (rowSymbols padSymbols src acc saved tmp rows savedRows : Fin T)
    (hreg : [rowSymbols,padSymbols,src,acc,saved,tmp,rows,savedRows].Nodup) (fill : Fin (A+4))
    (width padding : ℕ) (xs : List (List (Fin (A+4)))) (hlen : ∀ x ∈ xs, x.length = width)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hrow : (S.R rowSymbols).length = width) (hpad : (S.R padSymbols).length = padding)
    (hsrc : S.R src = xs.flatten++tail) (hacc : S.R acc = [])
    (hrows : (S.R rows).length = xs.length) (hsavedRows : S.R savedRows = [])
    (hsaved : S.R saved = []) (htmp : S.R tmp = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ xs.length*(6*(width+padding)+13)+6 ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        (xs.length*padding+2*(4*(width+padding)+10))) depth
        (prefixPadRows rowSymbols padSymbols src acc saved tmp rows savedRows fill) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R src
          (xs.flatMap (fun x => List.replicate padding fill++x)++tail))}) := by
  have hr := hreg
  regs_ne hr
  let pad := List.replicate padding fill
  let padded := fun x : List (Fin (A+4)) => pad++x
  let Ψ := fun j => Function.update (Function.update S.R src ((xs.drop j).flatten++tail))
    acc ((xs.take j).flatMap padded).reverse
  have hp : IterStockSpec body (prefixPadRow rowSymbols padSymbols src acc saved tmp fill)
      rows savedRows Ψ (4*(width+padding)+8) xs.length := by
    intro j hj u F hF
    have hbase (k : Fin T) (hkSrc : k ≠ src) (hkAcc : k ≠ acc) (hkRows : k ≠ rows)
        (hkSaved : k ≠ savedRows) : F.R k = S.R k := by
      rw [hF k hkRows hkSaved]
      simp [Ψ,hkSrc,hkAcc]
    have hscalar (k : Fin T) (hk : k ∈ [rowSymbols,padSymbols,saved,tmp]) : F.R k = S.R k := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl
      all_goals apply hbase <;> first | assumption | (apply Ne.symm; assumption)
    have hjlen : xs[j].length = width := hlen _ (List.getElem_mem hj)
    have hsource : F.R src = xs[j]++((xs.drop (j+1)).flatten++tail) := by
      rw [hF src ‹src ≠ rows› ‹src ≠ savedRows›]
      simp only [Ψ,Function.update_of_ne ‹src ≠ acc›,Function.update_self]
      rw [List.drop_eq_getElem_cons hj,List.flatten_cons,List.append_assoc]
    have harchive : F.R acc = ((xs.take j).flatMap padded).reverse := by
      rw [hF acc ‹acc ≠ rows› ‹acc ≠ savedRows›]
      simp [Ψ]
    obtain ⟨u',hu,he⟩ := prefixPadRow_exec rowSymbols padSymbols src acc saved tmp (by regs_nodup)
      fill padding xs[j] ((xs.drop (j+1)).flatten++tail) u F
      (by rw [hscalar rowSymbols (by simp),hrow,hjlen])
      (by rw [hscalar padSymbols (by simp)]; exact hpad) hsource
      (by rw [hscalar saved (by simp)]; exact hsaved) (by rw [hscalar tmp (by simp)]; exact htmp)
    let R := Function.update (Function.update F.R src ((xs.drop (j+1)).flatten++tail))
      acc (xs[j].reverse++(pad++F.R acc))
    refine ⟨u',R,4*(xs[j].length+padding)+8,hu,by rw [hjlen],he,?_,?_,?_,?_⟩
    · simp [R,‹src ≠ rows›.symm,‹acc ≠ rows›.symm]
    · simp [R,‹src ≠ savedRows›.symm,‹acc ≠ savedRows›.symm]
    · intro k hkRows hkSaved
      by_cases hkAcc : k = acc
      · subst k
        simp only [R,Ψ,Function.update_self]
        rw [harchive,List.take_succ_eq_append_getElem hj]
        simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
          padded,pad,List.reverse_append,List.reverse_replicate,List.append_assoc]
      by_cases hkSrc : k = src
      · subst k
        simp [R,Ψ,‹src ≠ acc›]
      simp only [R,Ψ,Function.update_of_ne hkSrc,Function.update_of_ne hkAcc]
      exact hbase k hkSrc hkAcc hkRows hkSaved
    · have hsize : mnSize (Host.mk u' {F with R := R}) = mnSize (Host.mk u F)+pad.length :=
        prefixPadRow_size src acc ‹src ≠ acc› xs[j] _ pad u u' F hsource
      rw [hsize]
      exact Nat.le_add_right _ _
  have hzero : Ψ 0 = S.R := by
    simp only [Ψ,List.drop_zero,List.take_zero,List.flatMap_nil,List.reverse_nil]
    rw [←hsrc,←hacc]
    simp only [Function.update_eq_self]
  obtain ⟨u,R,n,hu,hn,he,hrows',hsavedRows',hR⟩ := scanP_exec (body := body) ‹rows ≠ savedRows› hp.toIterSpec 0 v S
    (by simpa only [hrows,Nat.zero_add] using Nat.le_refl xs.length) (by intro k _ _; rw [hzero])
  have hw := scanP_within_final_stock ‹rows ≠ savedRows› (by decide : 1 ≤ 2)
    (prefixPadRow_native rowSymbols padSymbols src acc saved tmp fill) hp 0 v S
    (by simpa only [hrows,Nat.zero_add] using Nat.le_refl xs.length) (by intro k _ _; rw [hzero]) he depth
  let F : Stacks T A := {S with R := R}
  have hsource : F.R src = tail := by
    change R src = _
    rw [hR src ‹src ≠ rows› ‹src ≠ savedRows›]
    simp [Ψ,hrows,‹src ≠ acc›]
  have harchive : F.R acc = (xs.flatMap padded).reverse := by
    change R acc = _
    rw [hR acc ‹acc ≠ rows› ‹acc ≠ savedRows›]
    simp [Ψ,hrows]
  obtain ⟨u',hu',he'⟩ := moveR_exec body acc src ‹src ≠ acc›.symm id u F
  have hend : Host.mk u' {F with R := movedR F.R acc src id (F.R acc)} =
      Host.mk u' {S with R := Function.update S.R src (xs.flatMap padded++tail)} := by
    apply congrArg (Host.mk u')
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    change movedR R acc src id (F.R acc) k = _
    by_cases hkSrc : k = src
    · subst k
      simp only [movedR,Function.update_self,List.map_id,harchive,List.reverse_reverse]
      rw [show R src = tail from hsource]
    by_cases hkAcc : k = acc
    · subst k
      simp [movedR,‹src ≠ acc›.symm,hacc]
    by_cases hkRows : k = rows
    · subst k
      simp [movedR,‹src ≠ rows›.symm,‹acc ≠ rows›.symm,hrows',hsavedRows]
    by_cases hkSaved : k = savedRows
    · subst k
      simp [movedR,‹src ≠ savedRows›.symm,‹acc ≠ savedRows›.symm,hsavedRows',hsavedRows]
    simp only [movedR,Function.update_of_ne hkSrc,Function.update_of_ne hkAcc]
    rw [hR k hkRows hkSaved]
    simp [Ψ,hkSrc,hkAcc]
  have hlenFlat : xs.flatten.length = xs.length*width := by
    rw [List.length_flatten]
    have hmap : xs.map List.length = List.replicate xs.length width := List.map_eq_replicate_iff.mpr hlen
    rw [hmap,List.sum_replicate,smul_eq_mul]
  have hlenPad : (xs.flatMap padded).length = xs.length*(padding+width) := by
    rw [List.length_flatMap]
    have hmap : xs.map (fun x => (padded x).length) = List.replicate xs.length (padding+width) := by
      apply List.map_eq_replicate_iff.mpr
      intro x hx
      simp [padded,pad,hlen x hx]
    rw [hmap,List.sum_replicate,smul_eq_mul]
  have hsizeMove := mn_movedR_size src acc ‹src ≠ acc› u u' F
  rw [hend] at hsizeMove
  have hsizeUpdate := mn_size_update (Host.mk v S) u' (.rt src) (xs.flatMap padded++tail)
  have hsizeUpdate' : mnSize (Host.mk u' {S with R := Function.update S.R src (xs.flatMap padded++tail)})+
      (S.R src).length = mnSize (Host.mk v S)+(xs.flatMap padded++tail).length := by
    simpa only [Host.mk,update_rt,get_rt] using hsizeUpdate
  rw [hsrc,List.length_append,hlenFlat,List.length_append,hlenPad] at hsizeUpdate'
  have hsize : mnSize (Host.mk u F) = mnSize (Host.mk v S)+xs.length*padding := by
    rw [Nat.mul_add] at hsizeUpdate'
    omega
  let budget := mnSize (Host.mk v S)+depth+(xs.length*padding+2*(4*(width+padding)+10))
  have hw' := hw.mono (J := fun d z => mnSize z+d ≤ budget) (by
    intro d z hz
    change mnSize z+d ≤ mnSize (Host.mk u F)+depth+2*(4*(width+padding)+8+2) at hz
    rw [hsize] at hz
    dsimp only [budget]
    omega)
  have hm := Host.moveR_within acc src id he' depth budget (by rw [hsize]; dsimp only [budget]; omega)
  refine ⟨u',n+(2*(F.R acc).length+2),hu'.trans hu,?_,hend ▸ ExecWithin.seq hw' hm⟩
  simp only [hrows,hsavedRows,List.length_nil,Nat.add_zero,Nat.mul_zero,
    Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_id] at hn
  rw [harchive,List.length_reverse,hlenPad]
  nlinarith only [hn]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
