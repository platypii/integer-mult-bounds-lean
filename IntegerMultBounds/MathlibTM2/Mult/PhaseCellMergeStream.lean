module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMergeWord

/-! # Branch subtraction through the existing Gaussian word-stream executor -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Layer

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

/-- The stream executor resets the subtraction carry at each word boundary. -/
def mergeStream (a b dst width tmp : Fin T) : Pr P T Q A U :=
  autoWords ![a, b] ![dst] dst width tmp (gaussAuto A rsbSubG 2 false)

/-- Subtract two finite coefficient streams. Both inputs are consumed, their
exact difference is accumulated in reverse symbol order, and all other stacks
are restored. The existing Gaussian stream loop supplies the execution proof. -/
theorem mergeStream_exec {a b dst width tmp : Fin T}
    (hlay : AutoLayout ![a, b] ![dst] dst width tmp) (hA : 96 ≤ A)
    {w n : ℕ} (hw : 1 ≤ w) (X Y : Fin n → GaussianInt)
    (v : HS T Q A U) (S : Stacks T A)
    (hx : S.R a = cstream A w (List.ofFn X)) (hy : S.R b = cstream A w (List.ofFn Y))
    (hwidth : (S.R width).length = w) (htmp : S.R tmp = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ n * (5 * w + 6) + 2 ∧
      Exec body (mergeStream a b dst width tmp) (mk v S) m
        (mk v' { S with R := (Function.update (Function.update (Function.update S.R a []) b []) dst
          ((cstream A w (List.ofFn (fun i => X i - Y i))).reverse ++ S.R dst)) }) := by
  have hstream (F : Fin n → GaussianInt) : cstream A w (List.ofFn F) =
      (List.ofFn fun c => red w (F c)).flatMap (coeffSyms A w) := by
    change (List.ofFn F).flatMap (fun z => coeffSyms A w (red w z)) = _
    rw [← List.flatMap_map (red w) (coeffSyms A w), List.map_ofFn]
    rfl
  let zs : Fin n → Fin 2 → GR w := fun c => ![red w (X c), red w (Y c)]
  obtain ⟨v', m, hu, hm, he⟩ := gaussAuto_exec_gen body hlay
    (g := rsbSubG) (B := 2) (by omega)
    (by intro j; fin_cases j; simp [rsbSubG, Fin.sum_univ_two])
    (by norm_num; omega) false hw hwidth zs v S rfl htmp (by
      intro i
      fin_cases i
      · change S.R a = (List.ofFn fun c => red w (X c)).flatMap (coeffSyms A w)
        rw [hx, hstream]
      · change S.R b = (List.ofFn fun c => red w (Y c)).flatMap (coeffSyms A w)
        rw [hy, hstream])
  have houtput : (fun j : Fin 1 =>
      (List.ofFn fun c : Fin n => glin rsbSubG (fun i => swapGR false (zs c i)) j).flatMap
        (coeffSyms A w)) = fun _ => cstream A w (List.ofFn (fun i => X i - Y i)) := by
    funext j
    fin_cases j
    simp only [zs, swapGR_false]
    change (List.ofFn fun c => glin rsbSubG ![red w (X c), red w (Y c)] 0).flatMap
      (coeffSyms A w) = _
    simp only [glin_rsbSubG]
    exact (hstream (fun i => X i - Y i)).symm
  rw [houtput] at he
  refine ⟨v', m, hu, hm, he.cast rfl ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  have hab : a ≠ b := by
    intro h
    have hh := hlay.ins_inj (show (![a, b] : Fin 2 → Fin T) 0 = ![a, b] 1 by simpa using h)
    exact (by decide : (0 : Fin 2) ≠ 1) hh
  have had : a ≠ dst := hlay.ins_outs 0 0
  have hbd : b ≠ dst := hlay.ins_outs 1 0
  funext k
  change autoRegs S.R ![a, b] ![dst] (fun _ => cstream A w (List.ofFn (fun i => X i - Y i))) k = _
  have hin (i : Fin 2) := autoRegs_ins (R := S.R) (ins := ![a, b]) (outs := ![dst])
    (out := fun _ : Fin 1 => cstream A w (List.ofFn (fun i => X i - Y i))) hlay.ins_inj i
  have hout := autoRegs_outs (R := S.R) (ins := ![a, b]) (outs := ![dst])
    (out := fun _ : Fin 1 => cstream A w (List.ofFn (fun i => X i - Y i)))
    hlay.outs_inj hlay.ins_outs 0
  by_cases ha : k = a
  · subst k
    simpa [had, hab] using hin 0
  · by_cases hb : k = b
    · subst k
      simpa [hbd] using hin 1
    · by_cases hd : k = dst
      · subst k
        simpa using hout
      · rw [autoRegs_of_notMem]
        · simp [ha, hb, hd]
        · rintro ⟨i, hi⟩
          fin_cases i
          · exact ha (by simpa using hi.symm)
          · exact hb (by simpa using hi.symm)
        · rintro ⟨j, hj⟩
          fin_cases j
          exact hd (by simpa using hj.symm)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
