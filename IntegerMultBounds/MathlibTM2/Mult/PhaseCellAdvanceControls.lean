module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAdvanceLoop

/-! Generate the complete delimited sweep controls, restoring the binary
origin stream and unary batch count. Only the control destination and bounded
table state change; all conversion scratch is released. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

def originAdvanceControls : Pr P 117 Q A U :=
  .seq (.act (peekR 116)) (.seq (.loop (·.flag) originAdvanceLoopBody)
    (.seq (.act (.push (.rt 90) (fun _ => blank) .done))
      (.seq (moveR 90 91 id) (.seq (moveR 89 109 id) (moveR 88 116 id)))))

theorem originAdvanceControls_exec {W e previous w : ℕ} (he : e ≤ W)
    (origins : List ℕ) (hsorted : (previous::origins).Pairwise (· ≤ ·))
    (hcoords : ∀ origin ∈ origins, origin < 2^W) (hunits : ∀ origin ∈ origins, origin*w < 2^W)
    (st : TblSt 4 A) (hp : st.val 1 = previous) (hw : st.val 2 = w) (hfit : ∀ i, st.val i < 2^W)
    (cs suffix : List (Fin (A+4))) (hlen : cs.length = origins.length)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds advanceReg S (tblRho W (List.replicate W tick) (List.replicate e tick) st))
    (hc : S.R 116 = cs) (hsrc : S.R 109 = origins.flatMap (binSyms W) ++ suffix)
    (h88 : S.R 88 = []) (h89 : S.R 89 = []) (h90 : S.R 90 = []) :
    ∃ st' v' S' n, st'.val 2 = w ∧ st'.acc = st.acc ∧ (∀ i, st'.val i < 2^W) ∧
      v'.user = v.user ∧
      n ≤ origins.length*(3*tblC W e+29*W+30)+8*(originAdvances w previous origins).sum+11 ∧
      Exec body originAdvanceControls (mk v S) n (mk v' S') ∧
      tblHolds advanceReg S' (tblRho W (List.replicate W tick) (List.replicate e tick) st') ∧
      S'.R 91 = gatherControls A (originAdvances w previous origins ++ [0]) ++ S.R 91 ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ k, k ≠ 91 → (∀ r, advanceReg r ≠ k) → S'.R k = S.R k := by
  have hpeek := Exec.act (body := body) (peekR 116) (mk v S)
  rw [peekR_run, hc] at hpeek
  obtain ⟨st₁, v₁, S₁, n₁, hw₁, ha₁, hb₁, hu₁, hn₁, he₁, hh₁, hc₁, h88₁, hs₁, h89₁,
    h90₁, hi₁, ho₁, hl₁, hf₁⟩ := originAdvanceLoop_exec (body := body) he origins hsorted hcoords hunits
    st hp hw hfit cs suffix hlen { v with flag := cs.head?.isSome } S hS hc hsrc rfl
  let ds := originAdvances w previous origins
  let packets := origins.flatMap (binSyms (A := A) W)
  have h88' : S₁.R 88 = cs.reverse := by simpa [h88] using h88₁
  have h89' : S₁.R 89 = packets.reverse := by simpa [packets, h89] using h89₁
  have h90' : S₁.R 90 = (gatherControls A ds).reverse := by simpa [ds, h90] using h90₁
  have h91' : S₁.R 91 = S.R 91 := hf₁ 91 (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun r he => by have hh := advanceReg_range r; rw [he] at hh; omega)
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 90 (blank::S₁.R 90) }
  have hpPush := Exec.act (body := body) (.push (.rt 90) (fun _ => blank) .done) (mk v₁ S₁)
  have hpPush' : Exec body (.act (.push (.rt 90) (fun _ => blank) .done)) (mk v₁ S₁) 1 (mk v₁ S₂) := by
    simpa [S₂, Action.run, update_rt] using hpPush
  obtain ⟨v₂, hu₂, he₂⟩ := moveR_exec body 90 91 (by decide) id v₁ S₂
  let S₃ : Stacks 117 A := { S₂ with R := movedR S₂.R 90 91 id (S₂.R 90) }
  obtain ⟨v₃, hu₃, he₃⟩ := moveR_exec body 89 109 (by decide) id v₂ S₃
  let S₄ : Stacks 117 A := { S₃ with R := movedR S₃.R 89 109 id (S₃.R 89) }
  obtain ⟨v₄, hu₄, he₄⟩ := moveR_exec body 88 116 (by decide) id v₃ S₄
  let S₅ : Stacks 117 A := { S₄ with R := movedR S₄.R 88 116 id (S₄.R 88) }
  have hlength : packets.length = origins.length*W := by simp [packets, List.length_flatMap, binSyms]
  have h89len : (S₃.R 89).length = origins.length*W := by simp [S₃, S₂, movedR, h89', hlength]
  have h88len : (S₄.R 88).length = origins.length := by simp [S₄, S₃, S₂, movedR, h88', hlen]
  have h90len : (S₂.R 90).length = ds.sum+origins.length+1 := by simp [S₂, h90', ds]
  have hadd (xs : List ℕ) : gatherControls A (xs++[0]) = gatherControls A xs ++ [blank] := by
    induction xs with
    | nil => simp [gatherControls]
    | cons x xs ih => simp [gatherControls, ih, List.append_assoc]
  refine ⟨st₁, v₄, S₅, 1+(n₁+(1+((2*(S₂.R 90).length+2)+((2*(S₃.R 89).length+2)+(2*(S₄.R 88).length+2))))),
    hw₁, ha₁, hb₁, hu₄.trans (hu₃.trans (hu₂.trans hu₁)), ?_,
    Exec.seq hpeek (Exec.seq he₁ (Exec.seq hpPush' (Exec.seq he₂ (Exec.seq he₃ he₄)))), ?_, ?_,
    hi₁, ho₁, hl₁, ?_⟩
  · rw [h90len, h89len, h88len]
    unfold originAdvanceLoopCost at hn₁
    dsimp only [ds] at *
    nlinarith only [hn₁]
  · intro r
    have hr := advanceReg_range r
    have hfar (k : ℕ) (hk : 19 ≤ k) : (advanceReg r).val ≠ k := by omega
    simpa [S₅, S₄, S₃, S₂, movedR, Function.update_apply, Fin.ext_iff,
      hfar 88 (by decide), hfar 89 (by decide), hfar 90 (by decide), hfar 91 (by decide),
      hfar 109 (by decide), hfar 116 (by decide)] using hh₁ r
  · simp [S₅, S₄, S₃, S₂, movedR, h90', h91', hadd, ds, List.reverse_cons, List.append_assoc]
  · intro k hk91 hk
    by_cases hk116 : k = 116
    · subst k; simp [S₅, S₄, S₃, S₂, movedR, hc₁, h88', hc]
    by_cases hk88 : k = 88
    · subst k; simp [S₅, movedR, h88]
    by_cases hk109 : k = 109
    · subst k; simp [S₅, S₄, S₃, S₂, movedR, h89', hs₁, packets, hsrc]
    by_cases hk89 : k = 89
    · subst k; simp [S₅, S₄, movedR, h89]
    by_cases hk90 : k = 90
    · subst k; simp [S₅, S₄, S₃, movedR, h90]
    simp [S₅, S₄, S₃, S₂, movedR, hk91, hk116, hk88, hk109, hk89, hk90,
      hf₁ k hk116 hk88 hk109 hk89 hk90 hk]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
