module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMaskedTransferWord
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoop

/-! Apply one mask symbol per word with one left-to-right scan. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast

def maskedLine (flags : List Bool) (xs : List GaussianInt) : List GaussianInt :=
  List.zipWith (fun flag x => if flag then x else 0) flags xs

@[simp] theorem maskedLine_length (flags : List Bool) (xs : List GaussianInt)
    (hx : xs.length = flags.length) : (maskedLine flags xs).length = flags.length := by
  simp [maskedLine,hx]

theorem maskedLine_getElem (flags : List Bool) (xs : List GaussianInt)
    (hx : xs.length = flags.length) (j : ℕ) (hj : j < flags.length) :
    (maskedLine flags xs)[j]'(by simp [hx,hj]) = if flags[j] then xs[j]'(by omega) else 0 := by
  simp [maskedLine]

variable {T Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ T Q A U}

def maskedTransferLine (count width mask src dst trash tmp : Fin T) : Pr P₀ T Q A U :=
  countedLoop count (maskedTransferWord width mask src dst trash tmp)

theorem maskedTransferLine_exec {count width mask src dst trash tmp : Fin T}
    (hreg : [count,width,mask,src,dst,trash,tmp].Nodup) (hA : 4 ≤ A)
    (flags : List Bool) (xs : List GaussianInt) (w : ℕ)
    (hxs : xs.length = flags.length)
    (tailX : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hcount : (S.R count).length = flags.length) (hwidth : (S.R width).length = w)
    (hmask : S.R mask = flags.map (fun flag => pairSym A flag flag))
    (hX : S.R src = cstream A w xs++tailX)
    (htrash : S.R trash = []) (htmp : S.R tmp = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ flags.length*(10*w+15)+2 ∧
      Exec body (maskedTransferLine count width mask src dst trash tmp) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update
          (Function.update S.R mask []) src tailX)
          dst ((cstream A w (maskedLine flags xs)).reverse++S.R dst)) count [])}) := by
  have hr := hreg
  regs_ne hr
  let zs := maskedLine flags xs
  let Inv : ℕ → Stacks T A → Prop := fun j B =>
    B.inp = S.inp ∧ B.out = S.out ∧ B.L = S.L ∧
    (∀ k : Fin T, k ≠ count → k ≠ mask → k ≠ src → k ≠ dst → B.R k = S.R k) ∧
    B.R mask = (flags.drop j).map (fun flag => pairSym A flag flag) ∧
    B.R src = cstream A w (xs.drop j)++tailX ∧
    B.R dst = (cstream A w (zs.take j)).reverse++S.R dst
  have hstable : ∀ j B cs, Inv j B → Inv j {B with R := Function.update B.R count cs} := by
    intro j B cs h
    rcases h with ⟨hi,ho,hl,hf,hm,hx,hz⟩
    exact ⟨hi,ho,hl,by intro k hc hm hx hz; simpa [hc] using hf k hc hm hx hz,
      by simpa [‹count ≠ mask›.symm] using hm,
      by simpa [‹count ≠ src›.symm] using hx,
      by simpa [‹count ≠ dst›.symm] using hz⟩
  have hstep : ∀ j < flags.length, ∀ (vi : HS T Q A U) B, Inv j B →
      ∃ v' B' m, v'.user = vi.user ∧ m ≤ 10*w+12 ∧
        Exec body (maskedTransferWord width mask src dst trash tmp) (mk vi B) m (mk v' B') ∧
        B'.R count = B.R count ∧ Inv (j+1) B' := by
    intro j hj vi B h
    rcases h with ⟨hi,ho,hl,hf,hm,hx,hz⟩
    have hjx : j < xs.length := by omega
    have hmask' : B.R mask = pairSym A flags[j] flags[j]::
        ((flags.drop (j+1)).map (fun flag => pairSym A flag flag)) := by
      rw [hm,List.drop_eq_getElem_cons hj]
      rfl
    have hx' : B.R src = csyms A w xs[j]++(cstream A w (xs.drop (j+1))++tailX) := by
      rw [hx,List.drop_eq_getElem_cons hjx,cstream_cons,List.append_assoc]
    have hwidth' : (B.R width).length = w := by
      rw [hf width ‹count ≠ width›.symm ‹width ≠ mask› ‹width ≠ src› ‹width ≠ dst›]
      exact hwidth
    have htrash' : B.R trash = [] := by
      rw [hf trash ‹count ≠ trash›.symm ‹mask ≠ trash›.symm ‹src ≠ trash›.symm ‹dst ≠ trash›.symm]
      exact htrash
    have htmp' : B.R tmp = [] := by
      rw [hf tmp ‹count ≠ tmp›.symm ‹mask ≠ tmp›.symm ‹src ≠ tmp›.symm ‹dst ≠ tmp›.symm]
      exact htmp
    obtain ⟨v',m,hu,hmCost,he⟩ := maskedTransferWord_exec (body := body)
      (width := width) (mask := mask) (src := src) (dst := dst) (trash := trash) (tmp := tmp)
      (by regs_nodup) hA flags[j] w xs[j] (cstream A w (xs.drop (j+1))++tailX)
      ((flags.drop (j+1)).map (fun flag => pairSym A flag flag)) vi B hmask' hx' hwidth' htrash' htmp'
    let B' : Stacks T A := {B with R := (Function.update (Function.update (Function.update B.R
      mask ((flags.drop (j+1)).map (fun flag => pairSym A flag flag)))
      src (cstream A w (xs.drop (j+1))++tailX))
      dst ((csyms A w (if flags[j] then xs[j] else 0)).reverse++B.R dst))}
    have hzlen : j < zs.length := by simpa [zs,maskedLine_length flags xs hxs] using hj
    have hzget : zs[j] = if flags[j] then xs[j] else 0 := maskedLine_getElem flags xs hxs j hj
    have hnext : (cstream A w (zs.take (j+1))).reverse =
        (csyms A w (if flags[j] then xs[j] else 0)).reverse++(cstream A w (zs.take j)).reverse := by
      rw [List.take_succ_eq_append_getElem hzlen,cstream_append,cstream_cons,cstream_nil,
        List.append_nil,List.reverse_append,hzget]
    refine ⟨v',B',m,hu,hmCost,he,by simp [B',‹count ≠ mask›,‹count ≠ src›,‹count ≠ dst›],
      hi,ho,hl,?_,?_,?_,?_⟩
    · intro k hc hm hx hz
      simpa [B',hm,hx,hz] using hf k hc hm hx hz
    · simp [B',‹mask ≠ src›,‹mask ≠ dst›]
    · simp [B',‹src ≠ dst›]
    · simp [B',hz,hnext,List.append_assoc]
  have hInv : Inv 0 S := ⟨rfl,rfl,rfl,by intros; rfl,by simpa using hmask,
    by simpa using hX,by simp⟩
  obtain ⟨v',S',m,hu,hm,he,hcount',hI⟩ := countedLoop_exec (body := body)
    count (maskedTransferWord width mask src dst trash tmp) flags.length (10*w+12)
    Inv hstable hstep v S hcount hInv
  rcases hI with ⟨hi,ho,hl,hf,hm',hx',hz'⟩
  refine ⟨v',m,hu,?_,he.cast rfl ?_⟩
  · simpa only [maskedTransferLine] using hm
  · apply congrArg (mk v')
    refine Stacks.ext hi ho hl ?_
    funext k
    by_cases hc : k = count
    · subst k; simpa using hcount'
    by_cases hmask' : k = mask
    · subst k; simpa [‹count ≠ mask›.symm,‹mask ≠ src›,‹mask ≠ dst›] using hm'
    by_cases hx'' : k = src
    · subst k; simpa [‹count ≠ src›.symm,‹src ≠ dst›,← hxs] using hx'
    by_cases hd : k = dst
    · subst k
      have hzlen : zs.length = flags.length := maskedLine_length flags xs hxs
      simpa [‹count ≠ dst›.symm,← hzlen] using hz'
    · simpa [hc,hmask',hx'',hd] using hf k hc hmask' hx'' hd

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
