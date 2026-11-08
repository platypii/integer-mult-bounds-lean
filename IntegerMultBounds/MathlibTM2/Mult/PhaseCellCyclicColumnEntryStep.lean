module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSelectedCyclicColumnEntry

/-! A restoring cyclic entry step advances the retained folded-row cursor. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 151 Q A U}

def cyclicColumnEntryStep : Pr P 151 Q A U :=
  .seq (ucopy 137 0 136) (.seq selectedCyclicColumnEntry (.act (.push (.rt 137) (fun _ => tick) .done)))

def cyclicColumnEntryStepCost (q V s a b n i : ℕ) : ℕ :=
  (4*n+4)+(selectedCyclicColumnEntryCost q V s a b n i+1)

theorem cyclicColumnEntryStep_exec {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (q V a b n : ℕ)
    (hA : 4 ≤ A) (hwide : s+s ≤ 2^V) (ha : a ≤ s) (hb : b ≤ s) (hn : n < B.card)
    (C D : ZMod s → GaussianInt) (pageTail tail : List (Fin (A+4))) (v : HS 151 Q A U) (S : Stacks 151 A)
    (hcursor : (S.R 137).length = n) (hwidth : (S.R 115).length = V)
    (hpage : S.R 109 = cstream A V ((bFoldOrder s B).map
      (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++pageTail)
    (hq : (S.R 119).length = q) (hs : (S.R 121).length = s)
    (haSrc : (S.R 144).length = a) (hbSrc : (S.R 145).length = b)
    (hsource : S.R 132 = cstream A (2*q+8) (chirpLine s D)++(cstream A (2*q+8) (chirpLine s C)++tail))
    (h0 : S.R 0 = []) (h94 : S.R 94 = []) (h106 : S.R 106 = [])
    (h135 : S.R 135 = []) (h136 : S.R 136 = []) (h139 : S.R 139 = [])
    (hblank : ∀ k : Fin 151, k.val < 31 → k ≠ 0 → S.R k = []) :
    let i := bFoldAt s B n
    ∃ v' m, v'.user = v.user ∧ m ≤ cyclicColumnEntryStepCost q V s a b n i.val ∧
      Exec body cyclicColumnEntryStep (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 150
          (csyms A (2*q+8) (if a ≤ i.val ∧ i.val < b then C i else D i)++S.R 150)) 137 (tick::S.R 137))}) := by
  dsimp only
  obtain ⟨v₁,hv₁,he₁⟩ := ucopy_exec body (a := 137) (b := 0) (t := 136) (by decide) (by decide) (by decide) v S h136
  let S₁ : Stacks 151 A := {S with R := Function.update S.R 0 (List.replicate n tick)}
  have he₁' : Exec body (ucopy 137 0 136) (mk v S) (4*n+4) (mk v₁ S₁) := by simpa [S₁,hcursor,h0] using he₁
  obtain ⟨v₂,m₂,hv₂,hm₂,he₂,_,_⟩ := selectedCyclicColumnEntry_exec (body := body)
    B q V a b n hA hwide ha hb hn C D pageTail tail v₁ S₁ (by simp [S₁])
    (by simpa [S₁] using hwidth) (by simpa [S₁] using hpage) (by simpa [S₁] using hq)
    (by simpa [S₁] using hs) (by simpa [S₁] using haSrc) (by simpa [S₁] using hbSrc)
    (by simpa [S₁] using hsource) (by simpa [S₁] using h94) (by simpa [S₁] using h106)
    (by simpa [S₁] using h135) (by simpa [S₁] using h139)
    (by intro k hk hk0; simpa [S₁,hk0] using hblank k hk hk0)
  let output := csyms A (2*q+8) (if a ≤ (bFoldAt s B n).val ∧ (bFoldAt s B n).val < b
    then C (bFoldAt s B n) else D (bFoldAt s B n))++S.R 150
  let S₂ : Stacks 151 A := {S with R := Function.update S.R 150 output}
  have he₂' : Exec body selectedCyclicColumnEntry (mk v₁ S₁) m₂ (mk v₂ S₂) := by
    convert he₂ using 1
    apply congrArg (mk v₂)
    ext1
    · rfl
    · rfl
    · rfl
    · funext k
      by_cases h0' : k = 0 <;> by_cases h150 : k = 150 <;> simp [S₂,S₁,output,h0',h150,h0]
  have he₃ := Exec.act (body := body) (.push (.rt 137) (fun _ => tick) .done) (mk v₂ S₂)
  refine ⟨v₂,(4*n+4)+(m₂+1),hv₂.trans hv₁,Nat.add_le_add_left (Nat.add_le_add_right hm₂ _) _,
    (Exec.seq he₁' (Exec.seq he₂' he₃)).cast rfl ?_⟩
  simp [S₂,output,Action.run,update_rt]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
