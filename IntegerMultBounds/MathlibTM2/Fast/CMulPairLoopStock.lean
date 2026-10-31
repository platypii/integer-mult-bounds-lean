module

public import IntegerMultBounds.MathlibTM2.Fast.CMulPairBoundary
public import IntegerMultBounds.MathlibTM2.Fast.CMulStock

/-! The actual pointwise-product loop shares one numerical reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
  {cr : CR → Fin T} {ι : Fin 64 → Fin T}

theorem rmulPair_loop_exec_within (hcr : Function.Injective cr) (hdisj : ∀ r j, cr r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w p : ℕ} (hw : 1 ≤ w) (hp : p ≤ w) (zs : List (GaussianInt × GaussianInt))
    (hzs : ∀ z ∈ zs, Fits w z.1 ∧ Fits w z.2 ∧ z.2.im = 0)
    (v : HS T Q A U) (S : Stacks T A) (hc : CClean ι S)
    (hr : Ready (fun r => S.R (cr r)) w p)
    (hsrc : S.R (cr .xs) = cstream A w (zs.map Prod.fst))
    (hscalar : S.R (cr .ys) = cstream A w (zs.map Prod.snd))
    (C : ℕ) (hpush : mnProgPush (rmulOne (P := P) (Q := Q) (A := A) (U := U) ι hι hT hQ cr) ≤ C) (depth : ℕ) :
    ∃ vf n, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+zs.length*w+depth+
      C*rmulCost w) depth
      (cwhileP (cr .ys) (rmulOne ι hι hT hQ cr)) (mk v S) n
      (mk vf (pairBoundary cr S w (fun x y => tdivN p (x*y)) [] zs)) := by
  let g := fun x y => tdivN p (x*y)
  let B := fun rem done => pairBoundary cr S w g rem done
  let ρ := fun r => S.R (cr r)
  let H := mnSize (mk v S)+zs.length*w
  let reserve := C*rmulCost w
  let Inv := fun (d : ℕ) (z : Store (HΓ (T := T) A) (HS T Q A U)) => mnSize z+d ≤ H+depth+reserve
  have hstock (rem done : List (GaussianInt × GaussianInt)) (hparts : done++rem = zs) (vi : HS T Q A U) :
      mnSize (mk vi (B rem done)) ≤ H := by
    have hs := pairBoundary_size hcr v vi S w g zs rem done hsrc hscalar hparts
    have hl : done.length ≤ zs.length := by
      have := congrArg List.length hparts
      simp only [List.length_append] at this
      omega
    exact hs.le.trans (Nat.add_le_add_left (Nat.mul_le_mul_right w hl) _)
  have key : ∀ rem done, done++rem = zs → ∀ (vi : HS T Q A U),
      vi.flag = ((B rem done).R (cr .ys)).head?.isSome →
      ∃ vf n, ExecWithin body Inv depth
        (.loop (·.flag) (.seq (rmulOne ι hι hT hQ cr) (.act (peekR (cr .ys)))))
        (mk vi (B rem done)) n (mk vf (B [] zs)) := by
    intro rem
    induction rem with
    | nil =>
      intro done hparts vi hflag
      have hd : done = zs := by simpa using hparts
      subst done
      refine ⟨vi,1,.loop_false ?_ ?_⟩
      · simpa [B,pairBoundary,hcr.eq_iff] using hflag
      · have hs := hstock [] zs (by simp) vi
        change mnSize (mk vi (B [] zs))+depth ≤ H+depth+reserve
        omega
    | cons x rem ih =>
      intro done hparts vi hflag
      have hx := hzs x (by rw [← hparts]; simp)
      have hholds := pairBoundary_holds hcr S w g (x::rem) done
      have hfr := pairBoundary_fr (cr := cr) S w g (x::rem) done
      have hready : Ready (blockLoopSt ρ w g [] (x::rem) done) w p :=
        ((((hr.update .xs (by simp) _).update .ys (by simp) _).update .xsv
          (by simp) _).update .ysv (by simp) _).update .acc (by simp) _
      have hrun := rmulOne_runs (body := body) hcr hdisj hι hT hQ hA hready hw hp
        hx.1 hx.2.1 hx.2.2
        (rx := cstream A w (rem.map Prod.fst)) (ry := cstream A w (rem.map Prod.snd))
        (by simp [blockLoopSt]) (by simp [blockLoopSt])
      obtain ⟨v₁,S₁,n₁,hu₁,hn₁,hh,hf,ht⟩ := hrun.exec_within_native
        (WordCmd.native_of_noCalls (rmulOne_noCalls hι hT hQ) hpush)
        vi (B (x::rem) done) (hc.of_fr hdisj hfr) hholds
      have heq : oneSt (blockLoopSt ρ w g [] (x::rem) done) w x.1 x.2
          (cstream A w (rem.map Prod.fst)) (cstream A w (rem.map Prod.snd)) (g x.1 x.2) =
          blockLoopSt ρ w g [] rem (done++[x]) := by
        funext r
        cases r <;> simp [oneSt,opSt,blockLoopSt,g,List.reverse_append,List.append_assoc]
      have hs₁ : S₁ = B rem (done++[x]) := (hfr.trans hf).eq_of_holds
        (pairBoundary_fr (cr := cr) S w g rem (done++[x])) (by
          intro r
          rw [hh r]
          rw [heq]
          exact (pairBoundary_holds hcr S w g rem (done++[x]) r).symm)
      have ht₁ := ht depth
      rw [hs₁] at ht₁
      have hparts' : (done++[x])++rem = zs := by simpa [List.append_assoc] using hparts
      have hs₀ := hstock (x::rem) done hparts vi
      have hs₂ := hstock rem (done++[x]) hparts' v₁
      have hp₁ : ExecWithin body Inv depth (rmulOne ι hι hT hQ cr)
          (mk vi (B (x::rem) done)) n₁ (mk v₁ (B rem (done++[x]))) := ht₁.mono (by
            intro d z hz
            change mnSize z+d ≤ H+depth+reserve
            change mnSize z+d ≤ mnSize (mk vi (B (x::rem) done))+depth+reserve at hz
            omega)
      have epeek := peekR_run (cr .ys) v₁ (B rem (done++[x])) ▸
        Exec.act (body := body) (peekR (cr .ys)) (mk v₁ (B rem (done++[x])))
      have hpeek : ExecWithin body Inv depth (.act (peekR (cr .ys)))
          (mk v₁ (B rem (done++[x]))) 1
          (mk {v₁ with flag := ((B rem (done++[x])).R (cr .ys)).head?.isSome} (B rem (done++[x]))) :=
        mn_native_exec_within epeek 0 (by simp [peekR,mnNativePushBound,mnActPush]) depth _ (by
          simp only [Nat.zero_mul,Nat.add_zero]
          omega)
      obtain ⟨vf,n₂,ht₂⟩ := ih (done++[x]) hparts'
        {v₁ with flag := ((B rem (done++[x])).R (cr .ys)).head?.isSome} rfl
      have hft : vi.flag = true := by
        rw [hflag]
        have hne : (B (x::rem) done).R (cr .ys) ≠ [] := by
          simpa [B,pairBoundary,hcr.eq_iff] using (cstream_ne_nil (A := A) hw (x := x.2) (l := rem.map Prod.snd))
        cases he : (B (x::rem) done).R (cr .ys) with
        | nil => exact False.elim (hne he)
        | cons c cs => rfl
      exact ⟨vf,_,.loop_true (by simpa using hft) (.seq hp₁ hpeek) ht₂⟩
  have hB₀ : B zs [] = S := by simp [B,pairBoundary,← hsrc,← hscalar]
  obtain ⟨vf,n,ht⟩ := key zs [] (by simp)
    {v with flag := (S.R (cr .ys)).head?.isSome} (by rw [hB₀])
  rw [hB₀] at ht
  have epeek := peekR_run (cr .ys) v S ▸ Exec.act (body := body) (peekR (cr .ys)) (mk v S)
  have hpeek := mn_native_exec_within epeek 0
    (by simp [peekR,mnNativePushBound,mnActPush]) depth (H+depth+reserve) (by
      simp only [Nat.zero_mul,Nat.add_zero]
      dsimp only [H]
      omega)
  exact ⟨vf,_,.seq hpeek ht⟩

end IntegerMultBounds.MathlibTM2.Fast
