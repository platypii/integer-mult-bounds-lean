module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationSelectWord
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoop

/-! Select two aligned streams with one left-to-right scan. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

def publicationWords {α : Type} (flags : List Bool) (xs ys : List α) : List α :=
  List.zipWith (fun flag xy => if flag then xy.1 else xy.2) flags (xs.zip ys)

theorem publicationWords_length {α : Type} (flags : List Bool) (xs ys : List α)
    (hx : xs.length = flags.length) (hy : ys.length = flags.length) :
    (publicationWords flags xs ys).length = flags.length := by
  simp [publicationWords,hx,hy]

theorem publicationWords_getElem {α : Type} (flags : List Bool) (xs ys : List α)
    (hx : xs.length = flags.length) (hy : ys.length = flags.length) (i : ℕ) (hi : i < flags.length) :
    (publicationWords flags xs ys)[i]'(by rw [publicationWords_length flags xs ys hx hy]; exact hi) =
      if flags[i] then xs[i]'(by omega) else ys[i]'(by omega) := by
  simp [publicationWords, List.getElem_zipWith, List.getElem_zip]

variable {T Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ T Q A U}

def publicationSelectLoop (count width mask x y dst trash tmp : Fin T) : Pr P₀ T Q A U :=
  countedLoop count (publicationSelectWord width mask x y dst trash tmp)

theorem publicationSelectLoop_exec {count width mask x y dst trash tmp : Fin T}
    (hreg : [count,width,mask,x,y,dst,trash,tmp].Nodup) (hA : 4 ≤ A)
    (flags : List Bool) (xs ys : List (List (Fin (A+4)))) (w : ℕ)
    (hxs : xs.length = flags.length) (hys : ys.length = flags.length)
    (hwordX : ∀ z ∈ xs, z.length = w) (hwordY : ∀ z ∈ ys, z.length = w)
    (tailX tailY : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hcount : (S.R count).length = flags.length) (hwidth : (S.R width).length = w)
    (hmask : S.R mask = flags.map (fun flag => pairSym A flag flag))
    (hX : S.R x = xs.flatten++tailX) (hY : S.R y = ys.flatten++tailY)
    (htrash : S.R trash = []) (htmp : S.R tmp = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ flags.length*(10*w+15)+2 ∧
      Exec body (publicationSelectLoop count width mask x y dst trash tmp) (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update
          (Function.update S.R mask []) x tailX) y tailY)
          dst ((publicationWords flags xs ys).flatten.reverse++S.R dst)) count [])}) := by
  have hr := hreg
  regs_ne hr
  let zs := publicationWords flags xs ys
  let Inv : ℕ → Stacks T A → Prop := fun j B =>
    B.inp = S.inp ∧ B.out = S.out ∧ B.L = S.L ∧
    (∀ k : Fin T, k ≠ count → k ≠ mask → k ≠ x → k ≠ y → k ≠ dst → B.R k = S.R k) ∧
    B.R mask = (flags.drop j).map (fun flag => pairSym A flag flag) ∧
    B.R x = (xs.drop j).flatten++tailX ∧ B.R y = (ys.drop j).flatten++tailY ∧
    B.R dst = (zs.take j).flatten.reverse++S.R dst
  have hstable : ∀ j B cs, Inv j B → Inv j {B with R := Function.update B.R count cs} := by
    intro j B cs h
    rcases h with ⟨hi,ho,hl,hf,hm,hx,hy,hz⟩
    exact ⟨hi,ho,hl,by intro k hc hm hx hy hz; simpa [hc] using hf k hc hm hx hy hz,
      by simpa [‹count ≠ mask›.symm] using hm,
      by simpa [‹count ≠ x›.symm] using hx,
      by simpa [‹count ≠ y›.symm] using hy,
      by simpa [‹count ≠ dst›.symm] using hz⟩
  have hstep : ∀ j < flags.length, ∀ (vi : HS T Q A U) B, Inv j B →
      ∃ v' B' m, v'.user = vi.user ∧ m ≤ 10*w+12 ∧
        Exec body (publicationSelectWord width mask x y dst trash tmp) (mk vi B) m (mk v' B') ∧
        B'.R count = B.R count ∧ Inv (j+1) B' := by
    intro j hj vi B h
    rcases h with ⟨hi,ho,hl,hf,hm,hx,hy,hz⟩
    have hjx : j < xs.length := by omega
    have hjy : j < ys.length := by omega
    have hwX : (xs[j]).length = w := hwordX _ (List.getElem_mem hjx)
    have hwY : (ys[j]).length = w := hwordY _ (List.getElem_mem hjy)
    have hmask' : B.R mask = pairSym A flags[j] flags[j]::
        ((flags.drop (j+1)).map (fun flag => pairSym A flag flag)) := by
      rw [hm,List.drop_eq_getElem_cons hj]
      rfl
    have hx' : B.R x = xs[j]++((xs.drop (j+1)).flatten++tailX) := by
      have hdrop := List.drop_eq_getElem_cons hjx
      simpa only [hdrop,List.flatten_cons,List.append_assoc] using hx
    have hy' : B.R y = ys[j]++((ys.drop (j+1)).flatten++tailY) := by
      have hdrop := List.drop_eq_getElem_cons hjy
      simpa only [hdrop,List.flatten_cons,List.append_assoc] using hy
    have hwidth' : (B.R width).length = w := by
      rw [hf width ‹count ≠ width›.symm ‹width ≠ mask› ‹width ≠ x› ‹width ≠ y› ‹width ≠ dst›]
      exact hwidth
    have htrash' : B.R trash = [] := by
      rw [hf trash ‹count ≠ trash›.symm ‹mask ≠ trash›.symm ‹x ≠ trash›.symm ‹y ≠ trash›.symm ‹dst ≠ trash›.symm]
      exact htrash
    have htmp' : B.R tmp = [] := by
      rw [hf tmp ‹count ≠ tmp›.symm ‹mask ≠ tmp›.symm ‹x ≠ tmp›.symm ‹y ≠ tmp›.symm ‹dst ≠ tmp›.symm]
      exact htmp
    obtain ⟨v',hu,he⟩ := publicationSelectWord_exec (body := body)
      (width := width) (mask := mask) (x := x) (y := y) (dst := dst) (trash := trash) (tmp := tmp)
      (by regs_nodup) hA flags[j] xs[j] ys[j]
      ((xs.drop (j+1)).flatten++tailX) ((ys.drop (j+1)).flatten++tailY)
      ((flags.drop (j+1)).map (fun flag => pairSym A flag flag)) vi B hmask' hx' hy'
      (by rw [hwidth',hwX]) (by rw [hwX,hwY]) htrash' htmp'
    let B' : Stacks T A := {B with R := (Function.update (Function.update (Function.update (Function.update B.R
      mask ((flags.drop (j+1)).map (fun flag => pairSym A flag flag)))
      x ((xs.drop (j+1)).flatten++tailX)) y ((ys.drop (j+1)).flatten++tailY))
      dst ((if flags[j] then xs[j] else ys[j]).reverse++B.R dst))}
    have hzlen : j < zs.length := by simpa [zs,publicationWords_length flags xs ys hxs hys] using hj
    have hzget : zs[j] = if flags[j] then xs[j] else ys[j] :=
      publicationWords_getElem flags xs ys hxs hys j hj
    have hnext : (zs.take (j+1)).flatten.reverse =
        (if flags[j] then xs[j] else ys[j]).reverse++(zs.take j).flatten.reverse := by
      rw [List.take_succ_eq_append_getElem hzlen,List.flatten_append,List.flatten_cons,List.flatten_nil,
        List.append_nil,List.reverse_append,hzget]
    refine ⟨v',B',10*w+12,hu,le_rfl,?_,by simp [B',‹count ≠ mask›,‹count ≠ x›,‹count ≠ y›,‹count ≠ dst›],hi,ho,hl,?_,?_,?_,?_,?_⟩
    · simpa only [hwX] using he
    · intro k hc hm hx hy hz
      simpa [B',hm,hx,hy,hz] using hf k hc hm hx hy hz
    · simp [B',‹mask ≠ x›,‹mask ≠ y›,‹mask ≠ dst›]
    · simp [B',‹x ≠ y›,‹x ≠ dst›]
    · simp [B',‹y ≠ dst›]
    · simp [B',hz,hnext,List.append_assoc]
  have hInv : Inv 0 S := ⟨rfl,rfl,rfl,by intros; rfl,by simpa using hmask,
    by simpa using hX,by simpa using hY,by simp⟩
  obtain ⟨v',S',m,hu,hm,he,hcount',hI⟩ := countedLoop_exec (body := body)
    count (publicationSelectWord width mask x y dst trash tmp) flags.length (10*w+12)
    Inv hstable hstep v S hcount hInv
  rcases hI with ⟨hi,ho,hl,hf,hm',hx',hy',hz'⟩
  refine ⟨v',m,hu,?_,he.cast rfl ?_⟩
  · simpa only [publicationSelectLoop] using hm
  · apply congrArg (mk v')
    refine Stacks.ext hi ho hl ?_
    funext k
    by_cases hc : k = count
    · subst k; simpa using hcount'
    by_cases hmask' : k = mask
    · subst k; simpa [‹count ≠ mask›.symm,‹mask ≠ x›,‹mask ≠ y›,‹mask ≠ dst›] using hm'
    by_cases hx'' : k = x
    · subst k; simpa [‹count ≠ x›.symm,‹x ≠ y›,‹x ≠ dst›,← hxs] using hx'
    by_cases hy'' : k = y
    · subst k; simpa [‹count ≠ y›.symm,‹y ≠ dst›,← hys] using hy'
    by_cases hd : k = dst
    · subst k
      have hzlen : zs.length = flags.length := publicationWords_length flags xs ys hxs hys
      simpa [‹count ≠ dst›.symm,← hzlen] using hz'
    · simpa [hc,hmask',hx'',hy'',hd] using hf k hc hmask' hx'' hy'' hd

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
