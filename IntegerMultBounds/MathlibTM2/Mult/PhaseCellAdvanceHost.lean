module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAdvanceCode
public import IntegerMultBounds.MathlibTM2.Mult.ChirpControlEmit
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice

/-! Decode one origin packet and emit its computed forward symbol advance.
Consumed binary packets are archived in reverse for one final restoration. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

def advanceReg : TblR 4 → Fin 117
  | .v i => ⟨i.val, by omega⟩
  | .wr => 4 | .wn => 5 | .acc => 6
  | .z i => ⟨7+i.val, by omega⟩

theorem advanceReg_injective : Function.Injective advanceReg := by
  intro x y h
  cases x <;> cases y <;> simp_all [advanceReg, Fin.ext_iff]
  all_goals omega

theorem advanceReg_range (r : TblR 4) : (advanceReg r).val < 19 := by
  cases r <;> simp [advanceReg] <;> omega

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

def originAdvanceNext : Pr P 117 Q A U :=
  .seq (uclear 0) (.seq (copyPrefix 4 109 0 7 8)
    (.seq (transfer 4 109 89 8) (.seq (tblCompile advanceReg originAdvanceCode)
      (chirpControlEmit 3 90 7 8 9))))

theorem originAdvanceNext_exec {W e previous origin w : ℕ} (he : e ≤ W)
    (st : TblSt 4 A) (hp : st.val 1 = previous) (hw : st.val 2 = w)
    (hpo : previous ≤ origin) (hfit : ∀ i, st.val i < 2^W)
    (hoW : origin < 2^W) (hadvance : (origin-previous)*w < 2^W)
    (tail : List (Fin (A+4))) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds advanceReg S (tblRho W (List.replicate W tick) (List.replicate e tick) st))
    (hsrc : S.R 109 = binSyms W origin ++ tail) :
    ∃ st' v' S' n, st'.val 0 = origin ∧ st'.val 1 = origin ∧ st'.val 2 = w ∧
      st'.val 3 = (origin-previous)*w ∧ st'.acc = st.acc ∧ (∀ i, st'.val i < 2^W) ∧
      v'.user = v.user ∧ n ≤ 3*tblC W e+27*W+23+6*((origin-previous)*w) ∧
      Exec body originAdvanceNext (mk v S) n (mk v' S') ∧
      tblHolds advanceReg S' (tblRho W (List.replicate W tick) (List.replicate e tick) st') ∧
      S'.R 109 = tail ∧ S'.R 89 = (binSyms W origin).reverse ++ S.R 89 ∧
      S'.R 90 = blank :: (List.replicate ((origin-previous)*w) tick ++ S.R 90) ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ k, k ≠ 109 → k ≠ 89 → k ≠ 90 → (∀ r, advanceReg r ≠ k) → S'.R k = S.R k := by
  obtain ⟨v₀, hu₀, he₀⟩ := uclear_exec body 0 v S
  let S₀ : Stacks 117 A := { S with R := Function.update S.R 0 [] }
  have hzero : (S.R 0).length = W := by simpa [advanceReg, tblRho, binSyms] using congrArg List.length (hS (.v 0))
  have hwidth : (S.R 4).length = W := by
    simpa [advanceReg, tblRho] using congrArg List.length (hS .wr)
  have he₀' : Exec body (uclear 0) (mk v S) (2*W+2) (mk v₀ S₀) := by simpa [hzero] using he₀
  obtain ⟨v₁, hu₁, he₁⟩ := copyPrefix_exec (body := body) (count := 4) (src := 109) (dst := 0) (saved := 7) (tmp := 8)
    (by decide) v₀ S₀ (binSyms W origin) tail
    (by simpa [S₀] using hsrc)
    (by simp [S₀, hwidth, binSyms])
    (by simpa [S₀, advanceReg, tblRho] using hS (.z 0))
    (by simpa [S₀, advanceReg, tblRho] using hS (.z 1))
  let S₁ : Stacks 117 A := { S₀ with R := Function.update S₀.R 0 (binSyms W origin) }
  have he₁' : Exec body (copyPrefix 4 109 0 7 8) (mk v₀ S₀) (10*W+10) (mk v₁ S₁) := by
    simpa [S₁, S₀, binSyms] using he₁
  obtain ⟨v₂, hu₂, he₂⟩ := transfer_exec (body := body) (count := 4) (src := 109) (dst := 89) (tmp := 8)
    (by decide) v₁ S₁ (binSyms W origin) tail (by simpa [S₁, S₀] using hsrc)
    (by simp [S₁, S₀, hwidth, binSyms])
    (by simpa [S₁, S₀, advanceReg, tblRho] using hS (.z 1))
  let S₂ : Stacks 117 A := { S₁ with R := (Function.update (Function.update S₁.R 109 tail) 89
    ((binSyms W origin).reverse ++ S₁.R 89)) }
  have he₂' : Exec body (transfer 4 109 89 8) (mk v₁ S₁) (4*W+4) (mk v₂ S₂) := by
    simpa [S₂, binSyms] using he₂
  let st₂ : TblSt 4 A := ⟨Function.update st.val 0 origin, st.acc⟩
  have hh₂ : tblHolds advanceReg S₂ (tblRho W (List.replicate W tick) (List.replicate e tick) st₂) := by
    intro r
    have h109 : advanceReg r ≠ (109 : Fin 117) := by intro he; have hh := advanceReg_range r; rw [he] at hh; omega
    have h89 : advanceReg r ≠ (89 : Fin 117) := by intro he; have hh := advanceReg_range r; rw [he] at hh; omega
    by_cases hr : r = .v 0
    · subst r; simp [S₂, S₁, S₀, st₂, advanceReg, tblRho]
    have hn : advanceReg r ≠ (0 : Fin 117) := by simpa [advanceReg] using advanceReg_injective.ne hr
    cases r with
    | v i =>
      have hi : i ≠ 0 := by intro he; apply hr; simp [he]
      simpa [S₂, S₁, S₀, h109, h89, hn, st₂, tblRho, hi] using hS (.v i)
    | wr => simpa [S₂, S₁, S₀, st₂, advanceReg, tblRho] using hS .wr
    | wn => simpa [S₂, S₁, S₀, st₂, advanceReg, tblRho] using hS .wn
    | acc => simpa [S₂, S₁, S₀, st₂, advanceReg, tblRho] using hS .acc
    | z i => simpa [S₂, S₁, S₀, h109, h89, hn, st₂, tblRho] using hS (.z i)
  have hfit₂ : ∀ i, st₂.val i < 2^W := by
    intro i; by_cases hi : i = 0
    · subst i; simpa [st₂] using hoW
    simpa [st₂, hi] using hfit i
  have hc := originAdvanceCode_do (e := e) st₂ (by simp [st₂]) (by simpa [st₂] using hp)
    (by simpa [st₂] using hw) hpo hfit₂ hadvance
  obtain ⟨st₃, ⟨⟨ho₃, hp₃, hw₃, hd₃, ha₃⟩, hb₃⟩, hr⟩ := TblDo.host (body := body) advanceReg_injective
    (List.replicate W tick) (List.replicate e tick) (by simp) (by simp) he (hc.bounded hfit₂) hfit₂
  obtain ⟨v₃, S₃, n₃, hu₃, hn₃, he₃, hh₃, hf₃⟩ := hr v₂ S₂ hh₂
  obtain ⟨v₄, n₄, hu₄, hn₄, he₄⟩ := chirpControlEmit_exec (body := body)
    (a := 3) (dst := 90) (work := 7) (saved := 8) (tmp := 9) (by decide)
    W ((origin-previous)*w) hadvance v₃ S₃
    (by simpa [advanceReg, tblRho, hd₃] using hh₃ (.v 3))
    (by simpa [advanceReg, tblRho] using hh₃ (.z 0))
    (by simpa [advanceReg, tblRho] using hh₃ (.z 1))
    (by simpa [advanceReg, tblRho] using hh₃ (.z 2))
  let S₄ : Stacks 117 A := { S₃ with R := (Function.update S₃.R 90
    (blank :: (List.replicate ((origin-previous)*w) tick ++ S₃.R 90))) }
  have hoff (k : Fin 117) (hk : 19 ≤ k.val) : S₃.R k = S₂.R k :=
    hf₃.2.2.2 k (fun r he => by have hh := advanceReg_range r; rw [he] at hh; omega)
  refine ⟨st₃, v₄, S₄, (2*W+2)+((10*W+10)+((4*W+4)+(n₃+n₄))), ho₃, hp₃, hw₃, hd₃,
    ha₃, hb₃, hu₄.trans (hu₃.trans (hu₂.trans (hu₁.trans hu₀))), by omega,
    Exec.seq he₀' (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ he₄))), ?_, ?_, ?_, ?_,
    hf₃.1, hf₃.2.1, hf₃.2.2.1, ?_⟩
  · intro r
    have hn : advanceReg r ≠ (90 : Fin 117) := by intro he; have hh := advanceReg_range r; rw [he] at hh; omega
    simpa [S₄, hn] using hh₃ r
  · simp [S₄, hoff 109 (by decide), S₂, S₁, S₀]
  · simp [S₄, hoff 89 (by decide), S₂, S₁, S₀]
  · simp [S₄, hoff 90 (by decide), S₂, S₁, S₀]
  · intro k hk109 hk89 hk90 hk
    have hk0 : k ≠ 0 := (hk (.v 0)).symm
    simp [S₄, hk90, hf₃.2.2.2 k hk, S₂, S₁, S₀, hk109, hk89, hk0]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
