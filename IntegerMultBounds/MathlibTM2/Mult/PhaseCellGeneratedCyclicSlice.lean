module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicSliceControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicSlice
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicIntervalRead

/-! Crop the published principal stream using only retained ordinary endpoint rulers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Fast
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

def generatedCyclicSlice : Pr P 224 Q A U :=
  .seq cyclicSliceControls (.seq (cyclicSlice 138 2 0 1 132 147 5 6 7) (clearWords [0,1,2]))

def generatedCyclicSliceCost (s a n w : ℕ) : ℕ :=
  cyclicSliceControlsCost a (min n (s-a)) (n-min n (s-a)) w+
    ((6*(a*w)+10*(n*w)+32)+(2*((a+n)*w)+7))

theorem generatedCyclicSlice_exec {s : ℕ} [NeZero s] (a n w : ℕ) (ha : a < s) (hn : n ≤ s)
    (G : ZMod s → GaussianInt) (tail : List (Fin (A+4))) (v : HS 224 Q A U) (S : Stacks 224 A)
    (haSrc : (S.R 144).length = a) (hleftEnd : (S.R 145).length = a+min n (s-a))
    (hrightEnd : (S.R 146).length = n-min n (s-a)) (hwidth : (S.R 94).length = w)
    (hfresh : ∀ k ∈ ([(0 : Fin 224),1,2,3,4,5,6,7,138,141,143]), S.R k = [])
    (hsource : S.R 132 = cstream A w (chirpLine s G)++tail) :
    ∃ v' m, v'.user = v.user ∧ m ≤ generatedCyclicSliceCost s a n w ∧
      Exec body generatedCyclicSlice (mk v S) m
        (mk v' {S with R := Function.update S.R 147 (cstream A w (cyclicInterval a n G)++S.R 147)}) := by
  obtain ⟨v₁,m₁,hv₁,hm₁,he₁⟩ := cyclicSliceControls_exec (body := body) a (min n (s-a)) (n-min n (s-a)) w v S
    haSrc hleftEnd hrightEnd hwidth (by
      intro k hk
      apply hfresh k
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
  let S₁ : Stacks 224 A := {S with R := (Function.update (Function.update (Function.update S.R
    0 (List.replicate (a*w) tick)) 1 (List.replicate (min n (s-a)*w) tick))
    2 (List.replicate ((n-min n (s-a))*w) tick))}
  obtain ⟨v₂,hv₂,he₂⟩ := cyclicSlice_exec (body := body) 138 2 0 1 132 147 5 6 7 (by decide)
    a n w ha hn G tail v₁ S₁ (by simpa [S₁] using hsource)
    (by simpa [S₁] using hfresh 138 (by simp)) (by simp [S₁]) (by simp [S₁]) (by simp [S₁])
    (by simpa [S₁] using hfresh 5 (by simp)) (by simpa [S₁] using hfresh 6 (by simp))
    (by simpa [S₁] using hfresh 7 (by simp))
  let S₂ : Stacks 224 A := {S₁ with R := Function.update S₁.R 147 (cstream A w (cyclicInterval a n G)++S₁.R 147)}
  obtain ⟨v₃,hv₃,he₃⟩ := clearWords_exec (body := body) [(0 : Fin 224),1,2] (by decide) v₂ S₂
  have hvolume : a*w+min n (s-a)*w+(n-min n (s-a))*w = (a+n)*w := by
    rw [← Nat.add_mul,← Nat.add_mul]
    congr 1
    omega
  have hsum : ([(0 : Fin 224),1,2].map (fun k => (S₂.R k).length)).sum = (a+n)*w := by
    simpa [S₂,S₁,Nat.add_assoc] using hvolume
  refine ⟨v₃,m₁+((6*(a*w)+10*(n*w)+32)+(2*((a+n)*w)+7)),
    hv₃.trans (hv₂.trans hv₁),Nat.add_le_add_right hm₁ _,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast (by rw [hsum]; rfl) ?_⟩
  apply congrArg (mk v₃)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases h0 : k = 0 <;> by_cases h1 : k = 1 <;> by_cases h2 : k = 2 <;> by_cases h147 : k = 147 <;>
    simp [S₂,S₁,h0,h1,h2,h147,hfresh 0 (by simp),hfresh 1 (by simp),hfresh 2 (by simp)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
