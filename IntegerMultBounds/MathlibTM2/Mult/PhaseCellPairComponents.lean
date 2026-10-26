module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoop
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvDecode

/-! Assemble two real-component symbol streams in one sequential pass. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ T Q A U}

def pairComponentSymbol (x y : Fin (A+4)) : Fin (A+4) := pairSym A (pairRe x) (pairRe y)

def pairComponentStep (x y dst : Fin T) : Act T Q A U :=
  .pop (.rt x) (fun v o => {v with scan := Function.update v.scan x (o.getD blank)})
    (.pop (.rt y) (fun v o => {v with scan := Function.update v.scan y (o.getD blank)})
      (.push (.rt dst) (fun v => pairComponentSymbol (v.scan x) (v.scan y)) .done))

def pairComponents (count x y dst : Fin T) : Pr P₀ T Q A U :=
  countedLoop count (.act (pairComponentStep x y dst))

theorem pairComponentStep_run {x y dst : Fin T} (hreg : [x,y,dst].Nodup)
    (a b : Fin (A+4)) (xs ys : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hx : S.R x = a::xs) (hy : S.R y = b::ys) :
    (pairComponentStep x y dst : Act T Q A U).run (mk v S) =
      mk {v with scan := Function.update (Function.update v.scan x a) y b}
        {S with R := (Function.update (Function.update (Function.update S.R x xs) y ys)
          dst (pairComponentSymbol a b::S.R dst))} := by
  regs_ne hreg
  simp [pairComponentStep,Action.run,update_rt,hx,hy,Function.update_of_ne, *, Ne.symm,ne_comm]

theorem pairComponents_exec {count x y dst : Fin T} (hreg : [count,x,y,dst].Nodup)
    (xs ys tailX tailY : List (Fin (A+4))) (hlen : xs.length = ys.length)
    (v : HS T Q A U) (S : Stacks T A)
    (hc : (S.R count).length = xs.length) (hx : S.R x = xs++tailX) (hy : S.R y = ys++tailY) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 4*xs.length+2 ∧
      Exec body (pairComponents count x y dst) (mk v S) m
        (mk v' {S with R := Function.update (Function.update (Function.update (Function.update
          S.R x tailX) y tailY) dst ((List.zipWith pairComponentSymbol xs ys).reverse++S.R dst)) count []}) := by
  have hr := hreg
  regs_ne hr
  let zs := List.zipWith pairComponentSymbol xs ys
  have hzlen : zs.length = xs.length := by simp [zs,hlen]
  let Inv : ℕ → Stacks T A → Prop := fun j B =>
    B.inp = S.inp ∧ B.out = S.out ∧ B.L = S.L ∧
    (∀ k : Fin T, k ≠ count → k ≠ x → k ≠ y → k ≠ dst → B.R k = S.R k) ∧
    B.R x = xs.drop j++tailX ∧ B.R y = ys.drop j++tailY ∧
    B.R dst = (zs.take j).reverse++S.R dst
  have hstable : ∀ j B cs, Inv j B → Inv j {B with R := Function.update B.R count cs} := by
    intro j B cs h
    rcases h with ⟨hi,ho,hl,hf,hx,hy,hz⟩
    exact ⟨hi,ho,hl,by intro k hc hx hy hz; simpa [hc] using hf k hc hx hy hz,
      by simpa [‹count ≠ x›.symm] using hx,
      by simpa [‹count ≠ y›.symm] using hy,
      by simpa [‹count ≠ dst›.symm] using hz⟩
  have hstep : ∀ j < xs.length, ∀ (vi : HS T Q A U) B, Inv j B →
      ∃ v' B' m, v'.user = vi.user ∧ m ≤ 1 ∧
        Exec body (.act (pairComponentStep x y dst)) (mk vi B) m (mk v' B') ∧
        B'.R count = B.R count ∧ Inv (j+1) B' := by
    intro j hj vi B h
    rcases h with ⟨hi,ho,hl,hf,hx,hy,hz⟩
    have hjy : j < ys.length := by omega
    have hx' : B.R x = xs[j]::(xs.drop (j+1)++tailX) := by rw [hx,List.drop_eq_getElem_cons hj]; rfl
    have hy' : B.R y = ys[j]::(ys.drop (j+1)++tailY) := by rw [hy,List.drop_eq_getElem_cons hjy]; rfl
    let B' : Stacks T A := {B with R := Function.update (Function.update (Function.update B.R
      x (xs.drop (j+1)++tailX)) y (ys.drop (j+1)++tailY)) dst (pairComponentSymbol xs[j] ys[j]::B.R dst)}
    let v' : HS T Q A U := {vi with scan := Function.update (Function.update vi.scan x xs[j]) y ys[j]}
    have he : Exec body (.act (pairComponentStep x y dst)) (mk vi B) 1 (mk v' B') := by
      have hrun := pairComponentStep_run (show [x,y,dst].Nodup by regs_nodup) xs[j] ys[j]
        (xs.drop (j+1)++tailX) (ys.drop (j+1)++tailY) vi B hx' hy'
      simpa only [hrun] using (Exec.act (body := body) (pairComponentStep x y dst) (mk vi B))
    have hzget : zs[j]'(by omega) = pairComponentSymbol xs[j] ys[j] := by simp [zs,List.getElem_zipWith]
    have hnext : (zs.take (j+1)).reverse = pairComponentSymbol xs[j] ys[j]::(zs.take j).reverse := by
      rw [List.take_succ_eq_append_getElem (by omega),List.reverse_append,hzget]
      simp
    refine ⟨v',B',1,rfl,le_rfl,he,by simp [B',‹count ≠ x›,‹count ≠ y›,‹count ≠ dst›],hi,ho,hl,?_,?_,?_,?_⟩
    · intro k hc hx hy hz
      simpa [B',hx,hy,hz] using hf k hc hx hy hz
    · simp [B',‹x ≠ y›,‹x ≠ dst›]
    · simp [B',‹y ≠ dst›]
    · simp [B',hz,hnext]
  have hInv : Inv 0 S := ⟨rfl,rfl,rfl,by intros; rfl,by simpa using hx,by simpa using hy,by simp⟩
  obtain ⟨v',S',m,hu,hm,he,hcount,hI⟩ := countedLoop_exec (body := body)
    count (.act (pairComponentStep x y dst)) xs.length 1 Inv hstable hstep v S hc hInv
  rcases hI with ⟨hi,ho,hl,hf,hx',hy',hz'⟩
  refine ⟨v',m,hu,by simpa [Nat.mul_comm] using hm,he.cast rfl ?_⟩
  apply congrArg (mk v')
  refine Stacks.ext hi ho hl ?_
  funext k
  by_cases hc : k = count
  · subst k; simpa using hcount
  by_cases hxx : k = x
  · subst k; simpa [‹count ≠ x›.symm,‹x ≠ y›,‹x ≠ dst›] using hx'
  by_cases hyy : k = y
  · subst k; simpa [‹count ≠ y›.symm,‹y ≠ dst›,hlen] using hy'
  by_cases hdd : k = dst
  · subst k; simpa [‹count ≠ dst›.symm,← hzlen] using hz'
  · simpa [hc,hxx,hyy,hdd] using hf k hc hxx hyy hdd

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
