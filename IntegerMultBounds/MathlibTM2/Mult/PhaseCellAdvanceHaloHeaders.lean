module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAdvanceHaloMasters
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakePrefix

/-! Consume the next ordered origin and advance retained coordinate headers.
Unary work is proportional to movement, while binary packet work is proportional
to word width. All temporary stacks are restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def advanceHaloHeaders (width src word next delta a b count work saved tmp borrow : Fin T) : Pr P T Q A U :=
  .seq (takePrefix width src next work saved)
    (.seq (advanceHaloMasters word next delta a b work saved tmp borrow)
      (.seq (uclear word)
        (.seq (takePrefix width next word work saved) (.act (dropTop count .done)))))

def advanceHaloHeadersCost (V d : ℕ) : ℕ := 12*d+46*V+37

theorem advanceHaloHeaders_exec {width src word next delta a b count work saved tmp borrow : Fin T}
    (hreg : [width,src,word,next,delta,a,b,count,work,saved,tmp,borrow].Nodup)
    {V x y : ℕ} (hxy : x ≤ y) (hy : y < 2^V)
    (tail cs : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hwidth : (S.R width).length = V) (hword : S.R word = binSyms V x)
    (hsrc : S.R src = binSyms V y++tail) (hcount : S.R count = tick::cs)
    (hfresh : ∀ k ∈ [next,delta,work,saved,tmp], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ advanceHaloHeadersCost V (y-x) ∧
      Exec body (advanceHaloHeaders width src word next delta a b count work saved tmp borrow)
        (mk v S) n (mk v' {S with R := (Function.update
          (Function.update (Function.update (Function.update
            (Function.update S.R a (List.replicate (y-x) tick++S.R a))
            b (List.replicate (y-x) tick++S.R b)) word (binSyms V y)) src tail) count cs)}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := takePrefix_exec (body := body)
    (count := width) (src := src) (dst := next) (buf := work) (tmp := saved)
    (by regs_nodup) v S (binSyms V y) tail hsrc
    (by simpa only [length_binSyms] using hwidth)
    (hfresh work (by simp)) (hfresh saved (by simp))
  let H : Stacks T A := {S with R := Function.update (Function.update S.R src tail) next (binSyms V y)}
  have he₁' : Exec body (takePrefix width src next work saved) (mk v S) (6*V+6) (mk v₁ H) := by
    simpa only [H,hfresh next (by simp),List.append_nil,length_binSyms] using he₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := advanceHaloMasters_exec (body := body)
    (old := word) (next := next) (delta := delta) (a := a) (b := b)
    (work := work) (saved := saved) (tmp := tmp) (borrow := borrow)
    (by regs_nodup) hxy hy v₁ H
    (by simpa [H,‹word ≠ next›,‹src ≠ word›.symm] using hword)
    (by simp [H]) (by
      intro k hk
      have hn : k ≠ next ∧ k ≠ src := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl <;> constructor <;>
          first | assumption | exact Ne.symm (by assumption)
      simpa only [H,Function.update_of_ne hn.1,Function.update_of_ne hn.2] using
        hfresh k (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢; tauto))
  let J : Stacks T A := {H with R := (Function.update
    (Function.update H.R a (List.replicate (y-x) tick++H.R a))
    b (List.replicate (y-x) tick++H.R b))}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body word v₂ J
  have hwordJ : J.R word = binSyms V x := by
    simpa [J,H,‹word ≠ b›,‹word ≠ a›,‹word ≠ next›,‹src ≠ word›.symm] using hword
  have hlen : (J.R word).length = V := by rw [hwordJ,length_binSyms]
  let K : Stacks T A := {J with R := Function.update J.R word []}
  obtain ⟨v₄,hu₄,he₄⟩ := takePrefix_exec (body := body)
    (count := width) (src := next) (dst := word) (buf := work) (tmp := saved)
    (by regs_nodup) v₃ K (binSyms V y) []
    (by simp [K,J,H,‹word ≠ next›.symm,‹next ≠ b›,‹next ≠ a›])
    (by simpa [K,J,H,‹width ≠ word›,‹width ≠ b›,‹width ≠ a›,‹width ≠ next›,
      ‹width ≠ src›,length_binSyms] using hwidth)
    (by simpa [K,J,H,‹word ≠ work›.symm,‹b ≠ work›.symm,‹a ≠ work›.symm,
      ‹next ≠ work›.symm,‹src ≠ work›.symm] using hfresh work (by simp))
    (by simpa [K,J,H,‹word ≠ saved›.symm,‹b ≠ saved›.symm,‹a ≠ saved›.symm,
      ‹next ≠ saved›.symm,‹src ≠ saved›.symm] using hfresh saved (by simp))
  let M : Stacks T A := {K with R := Function.update (Function.update K.R next []) word (binSyms V y)}
  have he₄' : Exec body (takePrefix width next word work saved) (mk v₃ K) (6*V+6) (mk v₄ M) := by
    simpa only [M,K,Function.update_self,List.append_nil,length_binSyms] using he₄
  have hc : M.R count = tick::cs := by
    simpa [M,K,J,H,‹word ≠ count›.symm,‹next ≠ count›.symm,
      ‹b ≠ count›.symm,‹a ≠ count›.symm,‹src ≠ count›.symm] using hcount
  have he₅ : Exec body (.act (dropTop count .done)) (mk v₄ M) 1
      (mk v₄ {M with R := Function.update M.R count cs}) := by
    simpa [dropTop,Action.run,update_rt,hc] using Exec.act (body := body) (dropTop count .done) (mk v₄ M)
  refine ⟨v₄,(6*V+6)+(n₂+((2*V+2)+((6*V+6)+1))),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)),?_,
    (Exec.seq he₁' (Exec.seq he₂ (Exec.seq (he₃.cast (by rw [hlen]) rfl)
      (Exec.seq he₄' he₅)))).cast rfl ?_⟩
  · unfold advanceHaloHeadersCost advanceHaloMastersCost at *
    omega
  · apply congrArg (mk v₄)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hc : k = count
    · subst k
      simp [M,K,J,H]
    by_cases hw : k = word
    · subst k
      simp [M,K,J,H,hc,‹src ≠ word›.symm]
    by_cases hs : k = src
    · subst k
      simp [M,K,J,H,hc,hw,‹src ≠ next›,‹src ≠ a›,‹src ≠ b›]
    by_cases ha : k = a
    · subst k
      simp [M,K,J,H,hc,hw,hs,‹a ≠ b›,‹next ≠ a›.symm]
    by_cases hb : k = b
    · subst k
      simp [M,K,J,H,hc,hw,hs,‹next ≠ b›.symm]
    by_cases hn : k = next
    · subst k
      simp [M,K,J,H,hc,hw,hs,ha,hb,hfresh next (by simp)]
    simp [M,K,J,H,hc,hw,hs,ha,hb,hn]


/-- Cost of following an ordered sequence of generated origins. -/
def haloHeaderSweepCost (V x : ℕ) : List ℕ → ℕ
  | [] => 0
  | y::ys => advanceHaloHeadersCost V (y-x)+haloHeaderSweepCost V y ys

/-- Unary movement telescopes; only binary packet work is paid per origin. -/
theorem haloHeaderSweepCost_le (V s x : ℕ) (ys : List ℕ)
    (hordered : (x::ys).Pairwise (· ≤ ·)) (hx : x ≤ s)
    (hfit : ∀ y ∈ ys, y ≤ s) :
    haloHeaderSweepCost V x ys ≤ 12*(s-x)+ys.length*(46*V+37) := by
  induction ys generalizing x with
  | nil => simp [haloHeaderSweepCost]
  | cons y ys ih =>
    have hxy : x ≤ y := (List.pairwise_cons.mp hordered).1 y (by simp)
    have hy : y ≤ s := hfit y (by simp)
    have htail := ih y (List.pairwise_cons.mp hordered).2 hy
      (fun z hz => hfit z (by simp only [List.mem_cons]; exact Or.inr hz))
    simp only [haloHeaderSweepCost,List.length_cons,Nat.succ_mul] at *
    unfold advanceHaloHeadersCost
    have htel : 12*(y-x)+12*(s-y) = 12*(s-x) := by omega
    omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
