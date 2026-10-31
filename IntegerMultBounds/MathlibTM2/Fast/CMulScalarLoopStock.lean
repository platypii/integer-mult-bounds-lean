module

public import IntegerMultBounds.MathlibTM2.Fast.CMulScalarBoundary
public import IntegerMultBounds.MathlibTM2.Fast.CMulScalarBlockStock

/-! The actual scalar-table outer loop shares one numerical reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
  {cr : CR → Fin T} {ι : Fin 64 → Fin T}

theorem rmulScalar_loop_exec_within (hcr : Function.Injective cr) (hdisj : ∀ r j, cr r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w p : ℕ} (hw : 1 ≤ w) (hp : p ≤ w) (xs : List GaussianInt) (a : GaussianInt)
    (hxs : ∀ x ∈ xs, Fits w x) (ha : Fits w a) (har : a.im = 0)
    (v : HS T Q A U) (S : Stacks T A) (hc : CClean ι S)
    (hr : Ready (fun r => S.R (cr r)) w p)
    (hsrc : S.R (cr .xs) = cstream A w xs) (hscalar : S.R (cr .ys) = csyms A w a)
    (hysv : S.R (cr .ysv) = [])
    (C : ℕ) (hpush : mnProgPush (cmulBlock cr
      (rmulOne (P := P) (Q := Q) (A := A) (U := U) ι hι hT hQ cr)) ≤ C) (depth : ℕ) :
    ∃ vf n, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+xs.length*w+depth+
      C*(rmulCost w+2*w+6)) depth
      (cwhileP (cr .xs) (cmulBlock cr (rmulOne ι hι hT hQ cr))) (mk v S) n
      (mk vf (scalarBoundary cr S w (fun x => tdivN p (x*a)) [] xs)) := by
  let g := fun x => tdivN p (x*a)
  let B := fun rem done => scalarBoundary cr S w g rem done
  let ρ := fun r => S.R (cr r)
  let H := mnSize (mk v S)+xs.length*w
  let reserve := C*(rmulCost w+2*w+6)
  let Inv := fun (d : ℕ) (z : Store (HΓ (T := T) A) (HS T Q A U)) => mnSize z+d ≤ H+depth+reserve
  have hstock (rem done : List GaussianInt) (hparts : done++rem = xs) (vi : HS T Q A U) :
      mnSize (mk vi (B rem done)) ≤ H := by
    have hs := scalarBoundary_size hcr v vi S w g xs rem done hsrc hparts
    have hl : done.length ≤ xs.length := by
      have := congrArg List.length hparts
      simp only [List.length_append] at this
      omega
    exact hs.le.trans (Nat.add_le_add_left (Nat.mul_le_mul_right w hl) _)
  have key : ∀ rem done, done++rem = xs → ∀ (vi : HS T Q A U),
      vi.flag = ((B rem done).R (cr .xs)).head?.isSome →
      ∃ vf n, ExecWithin body Inv depth
        (.loop (·.flag) (.seq (cmulBlock cr (rmulOne ι hι hT hQ cr)) (.act (peekR (cr .xs)))))
        (mk vi (B rem done)) n (mk vf (B [] xs)) := by
    intro rem
    induction rem with
    | nil =>
      intro done hparts vi hflag
      have hd : done = xs := by simpa using hparts
      subst done
      refine ⟨vi,1,.loop_false ?_ ?_⟩
      · simpa [B,scalarBoundary,hcr.eq_iff] using hflag
      · have hs := hstock [] xs (by simp) vi
        change mnSize (mk vi (B [] xs))+depth ≤ H+depth+reserve
        omega
    | cons x rem ih =>
      intro done hparts vi hflag
      have hx : Fits w x := hxs x (by rw [← hparts]; simp)
      have hholds := scalarBoundary_holds hcr S w g (x::rem) done
      have hfr := scalarBoundary_fr (cr := cr) S w g (x::rem) done
      have hready : Ready (scalarLoopSt ρ w g (x::rem) done) w p :=
        ((hr.update .xs (by simp) _).update .xsv (by simp) _).update .acc (by simp) _
      obtain ⟨v₁,S₁,n₁,hu₁,hn₁,hh,hf,ht⟩ := rmulBlock_one_exec_within (rx := cstream A w rem) hcr hdisj hι hT hQ hA
        hready hw hp hx ha har
        (by simp [scalarLoopSt]) (by simp [scalarLoopSt,ρ,hscalar])
        (by simp [scalarLoopSt,ρ,hysv]) C hpush vi (B (x::rem) done)
        (hc.of_fr hdisj hfr) hholds
      have heq : blockSt (scalarLoopSt ρ w g (x::rem) done) w
          (fun x y => tdivN p (x*y)) (cstream A w rem) [(x,a)] =
          scalarLoopSt ρ w g rem (done++[x]) := by
        funext r
        cases r <;> simp [blockSt,scalarLoopSt,g,List.reverse_append,List.append_assoc]
      have hs₁ : S₁ = B rem (done++[x]) := (hfr.trans hf).eq_of_holds
        (scalarBoundary_fr (cr := cr) S w g rem (done++[x])) (by
          intro r
          rw [hh r]
          rw [heq]
          exact (scalarBoundary_holds hcr S w g rem (done++[x]) r).symm)
      have ht₁ := ht depth
      rw [hs₁] at ht₁
      have hparts' : (done++[x])++rem = xs := by simpa [List.append_assoc] using hparts
      have hs₀ := hstock (x::rem) done hparts vi
      have hs₂ := hstock rem (done++[x]) hparts' v₁
      have hp₁ : ExecWithin body Inv depth (cmulBlock cr (rmulOne ι hι hT hQ cr))
          (mk vi (B (x::rem) done)) n₁ (mk v₁ (B rem (done++[x]))) := ht₁.mono (by
            intro d z hz
            change mnSize z+d ≤ H+depth+reserve
            change mnSize z+d ≤ mnSize (mk vi (B (x::rem) done))+depth+reserve at hz
            omega)
      have epeek := peekR_run (cr .xs) v₁ (B rem (done++[x])) ▸
        Exec.act (body := body) (peekR (cr .xs)) (mk v₁ (B rem (done++[x])))
      have hpeek : ExecWithin body Inv depth (.act (peekR (cr .xs)))
          (mk v₁ (B rem (done++[x]))) 1
          (mk {v₁ with flag := ((B rem (done++[x])).R (cr .xs)).head?.isSome} (B rem (done++[x]))) :=
        mn_native_exec_within epeek 0 (by simp [peekR,mnNativePushBound,mnActPush]) depth _ (by
          simp only [Nat.zero_mul,Nat.add_zero]
          omega)
      obtain ⟨vf,n₂,ht₂⟩ := ih (done++[x]) hparts'
        {v₁ with flag := ((B rem (done++[x])).R (cr .xs)).head?.isSome} rfl
      have hft : vi.flag = true := by
        rw [hflag]
        have hne : (B (x::rem) done).R (cr .xs) ≠ [] := by
          simpa [B,scalarBoundary,hcr.eq_iff] using (cstream_ne_nil (A := A) hw (x := x) (l := rem))
        cases he : (B (x::rem) done).R (cr .xs) with
        | nil => exact False.elim (hne he)
        | cons c cs => rfl
      exact ⟨vf,_,.loop_true (by simpa using hft) (.seq hp₁ hpeek) ht₂⟩
  have hB₀ : B xs [] = S := by simp [B,scalarBoundary,← hsrc]
  obtain ⟨vf,n,ht⟩ := key xs [] (by simp)
    {v with flag := (S.R (cr .xs)).head?.isSome} (by rw [hB₀])
  rw [hB₀] at ht
  have epeek := peekR_run (cr .xs) v S ▸ Exec.act (body := body) (peekR (cr .xs)) (mk v S)
  have hpeek := mn_native_exec_within epeek 0
    (by simp [peekR,mnNativePushBound,mnActPush]) depth (H+depth+reserve) (by
      simp only [Nat.zero_mul,Nat.add_zero]
      dsimp only [H]
      omega)
  exact ⟨vf,_,.seq hpeek ht⟩

end IntegerMultBounds.MathlibTM2.Fast
