module

public import IntegerMultBounds.MathlibTM2.Fast.SubWord

/-! # A structural row accumulator through the shared subtraction automaton

Consume one product stream and subtract it from a single accumulator word.
The proof works over arbitrary lists; no concrete arithmetic certificate is used.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

def subtractRowStep (acc terms saved width tmp : Fin T) : Pr P T Q A U :=
  .seq (rsbSubWord acc terms saved width tmp) (moveR saved acc id)

theorem subtractRowStep_exec {acc terms saved width tmp : Fin T}
    (hreg : [acc, terms, saved, width, tmp].Nodup) (hA : 96 ≤ A) (w : ℕ)
    (v : HS T Q A U) (S : Stacks T A) (x y : GaussianInt) (tail : List (Fin (A + 4)))
    (hx : S.R acc = csyms A w x) (hy : S.R terms = csyms A w y ++ tail)
    (hsaved : S.R saved = []) (hwidth : (S.R width).length = w) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (subtractRowStep acc terms saved width tmp) (mk v S) (7 * w + 8)
        (mk v' { S with R := (Function.update (Function.update S.R terms tail) acc
          (csyms A w (x - y))) }) := by
  have hreg' := hreg
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hreg'
  obtain ⟨⟨hat, has, haw, ham⟩, ⟨hts, htw, htm⟩, ⟨hsw, hsm⟩, hwm, _⟩ := hreg'
  obtain ⟨v₁, hu₁, he₁⟩ := subWord_exec (body := body) hreg hA w v S x y [] tail
    (by simpa using hx) hy hwidth htmp
  let S₁ : Stacks T A := { S with R := (Function.update (Function.update
    (Function.update S.R acc []) terms tail) saved ((csyms A w (x - y)).reverse ++ S.R saved)) }
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body saved acc ‹acc ≠ saved›.symm id v₁ S₁
  have hlen : (S₁.R saved).length = w := by simp [S₁, hsaved, csyms]
  refine ⟨v₂, hu₂.trans hu₁, (Exec.seq he₁ he₂).cast (by rw [hlen]; omega) ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · rfl
  funext k
  by_cases ha : k = acc
  · subst k
    simp [S₁, movedR, ‹acc ≠ saved›, ‹acc ≠ terms›, hsaved]
  by_cases hb : k = terms
  · subst k
    simp [S₁, movedR, ‹acc ≠ terms›.symm, ‹terms ≠ saved›]
  by_cases hs : k = saved
  · subst k
    simp [S₁, movedR, ‹acc ≠ saved›.symm, ‹terms ≠ saved›.symm, hsaved]
  simp [S₁, movedR, ha, hb, hs]

def subtractRow (acc terms saved width tmp : Fin T) : Pr P T Q A U :=
  .seq (.act (peekR terms))
    (.loop (·.flag) (.seq (subtractRowStep acc terms saved width tmp) (.act (peekR terms))))

private theorem subtractRow_loop {acc terms saved width tmp : Fin T}
    (hreg : [acc, terms, saved, width, tmp].Nodup) (hA : 96 ≤ A) {w : ℕ} (hw : 1 ≤ w)
    (ys : List GaussianInt) :
    ∀ (v : HS T Q A U) (S : Stacks T A) (x : GaussianInt),
    S.R acc = csyms A w x → S.R terms = cstream A w ys → S.R saved = [] →
    (S.R width).length = w → S.R tmp = [] → v.flag = (S.R terms).head?.isSome →
    ∃ v', v'.user = v.user ∧
      Exec body (.loop (·.flag)
        (.seq (subtractRowStep acc terms saved width tmp) (.act (peekR terms))))
        (mk v S) (ys.length * (7 * w + 10) + 1)
        (mk v' { S with R := (Function.update (Function.update S.R terms []) acc
          (csyms A w (x - ys.sum))) }) := by
  have hreg' := hreg
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hreg'
  obtain ⟨⟨hat, has, haw, ham⟩, ⟨hts, htw, htm⟩, ⟨hsw, hsm⟩, hwm, _⟩ := hreg'
  induction ys with
  | nil =>
    intro v S x hx hy hs hc ht hf
    refine ⟨v, rfl, ?_⟩
    have hstate : ({ S with R := (Function.update (Function.update S.R terms []) acc
        (csyms A w (x - ([] : List GaussianInt).sum))) } : Stacks T A) = S := by
      simp only [List.sum_nil, sub_zero]
      have hy' : S.R terms = [] := by simpa [cstream] using hy
      rw [← hx, ← hy']
      simp
    rw [hstate]
    simpa only [List.length_nil, Nat.zero_mul, Nat.zero_add] using
      (Exec.loop_false (body := body) (s := mk v S) (f := fun v : HS T Q A U => v.flag)
        (p := .seq (subtractRowStep acc terms saved width tmp) (.act (peekR terms)))
        (by simpa [hy, cstream] using hf))
  | cons y ys ih =>
    intro v S x hx hy hs hc ht hf
    obtain ⟨v₁, hu₁, he₁⟩ := subtractRowStep_exec (body := body) hreg hA w v S x y
      (cstream A w ys) hx (by simpa [cstream] using hy) hs hc ht
    let S₁ : Stacks T A := { S with R := (Function.update (Function.update S.R terms
      (cstream A w ys)) acc (csyms A w (x - y))) }
    have he₂ := Exec.act (body := body) (peekR terms) (mk v₁ S₁)
    rw [peekR_run] at he₂
    obtain ⟨v₂, hu₂, he₃⟩ := ih { v₁ with flag := (S₁.R terms).head?.isSome } S₁ (x - y)
      (by simp [S₁]) (by simp [S₁, ‹acc ≠ terms›.symm])
      (by simpa [S₁, ‹acc ≠ saved›.symm, ‹terms ≠ saved›.symm] using hs)
      (by simpa [S₁, ‹acc ≠ width›.symm, ‹terms ≠ width›.symm] using hc)
      (by simpa [S₁, ‹acc ≠ tmp›.symm, ‹terms ≠ tmp›.symm] using ht) rfl
    have hflag : v.flag = true := by
      rw [hf]
      have hlen : 0 < (S.R terms).length := by
        rw [hy]
        simp only [cstream, List.flatMap_cons, List.length_append]
        have hh : (csyms A w y).length = w := by simp [csyms]
        change 0 < (csyms A w y).length + _
        omega
      cases hlist : S.R terms with
      | nil => simp [hlist] at hlen
      | cons z zs => simp
    refine ⟨v₂, hu₂.trans hu₁,
      (Exec.loop_true hflag (Exec.seq he₁ he₂) he₃).cast (by simp; ring) ?_⟩
    have hsum : x - y - ys.sum = x - (y :: ys).sum := by simp [sub_sub]
    simp only [hsum]
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases ha : k = acc
    · subst k; simp [S₁]
    by_cases hb : k = terms
    · subst k; simp [S₁, ‹acc ≠ terms›.symm]
    simp [S₁, ha, hb]

/-- Every row term is consumed, while the counter, temporary and save tapes
are restored exactly. The result is a signed-word representation of `x - sum ys`. -/
theorem subtractRow_exec {acc terms saved width tmp : Fin T}
    (hreg : [acc, terms, saved, width, tmp].Nodup) (hA : 96 ≤ A) {w : ℕ} (hw : 1 ≤ w)
    (ys : List GaussianInt) (v : HS T Q A U) (S : Stacks T A) (x : GaussianInt)
    (hx : S.R acc = csyms A w x) (hy : S.R terms = cstream A w ys)
    (hsaved : S.R saved = []) (hwidth : (S.R width).length = w) (htmp : S.R tmp = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (subtractRow acc terms saved width tmp) (mk v S) (ys.length * (7 * w + 10) + 2)
        (mk v' { S with R := (Function.update (Function.update S.R terms []) acc
          (csyms A w (x - ys.sum))) }) := by
  obtain ⟨v', hu, he⟩ := subtractRow_loop (body := body) hreg hA hw ys
    { v with flag := (S.R terms).head?.isSome } S x hx hy hsaved hwidth htmp rfl
  refine ⟨v', hu, (Exec.seq (peekR_run terms v S ▸ Exec.act (body := body) (peekR terms) (mk v S)) he).cast
    (by omega) rfl⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
