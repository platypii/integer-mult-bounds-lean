module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCollectCyclicColumnEntries
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicColumnEntryLoopStock

/-! Retire collection controls without adding to the shared row reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 151 Q A U}

theorem collectCyclicColumnEntries_exec_within {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (q V a b start L : ℕ)
    (cap depth : ℕ)
    (hcost : ∀ j < L,
      cyclicColumnEntryStepCost q V s a b (start+j) (bFoldAt s B (start+j)).val ≤ cap)
    (hA : 4 ≤ A) (hwide : s+s ≤ 2^V) (ha : a ≤ s) (hb : b ≤ s) (hfit : start+L ≤ B.card)
    (C D : ZMod s → GaussianInt) (pageTail tail : List (Fin (A+4))) (v : HS 151 Q A U) (S : Stacks 151 A)
    (hcursor : (S.R 137).length = start) (hcount : (S.R 138).length = L)
    (hwidth : (S.R 115).length = V)
    (hpage : S.R 109 = cstream A V ((bFoldOrder s B).map
      (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++pageTail)
    (hq : (S.R 119).length = q) (hs : (S.R 121).length = s)
    (haSrc : (S.R 144).length = a) (hbSrc : (S.R 145).length = b)
    (hsource : S.R 132 = cstream A (2*q+8) (chirpLine s D)++(cstream A (2*q+8) (chirpLine s C)++tail))
    (h0 : S.R 0 = []) (h94 : S.R 94 = []) (h106 : S.R 106 = [])
    (h135 : S.R 135 = []) (h136 : S.R 136 = []) (h139 : S.R 139 = []) (h140 : S.R 140 = [])
    (hblank : ∀ k : Fin 151, k.val < 31 → k ≠ 0 → S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ collectCyclicColumnEntriesCost B q V a b start L ∧
      ExecWithin body (fun d z => mnSize z+d ≤
        mnSize (mk v S)+depth+L*((2*q+8)+1)+8*(cap+2)) depth collectCyclicColumnEntries (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 138 []) 150
          (cstream A (2*q+8) ((List.range L).reverse.map (fun j =>
            let i := bFoldAt s B (start+j)
            if a ≤ i.val ∧ i.val < b then C i else D i))++S.R 150))
          137 [])}) := by
  obtain ⟨v₁,m₁,hv₁,hm₁,he₁⟩ := cyclicColumnEntryLoop_exec_within (body := body)
    B q V a b start L cap depth hcost hA hwide ha hb hfit C D pageTail tail v S hcursor hcount hwidth hpage
    hq hs haSrc hbSrc hsource h0 h94 h106 h135 h136 h139 h140 hblank
  let output := cstream A (2*q+8) ((List.range L).reverse.map (fun j =>
    let i := bFoldAt s B (start+j)
    if a ≤ i.val ∧ i.val < b then C i else D i))++S.R 150
  let S₁ : Stacks 151 A := {S with R := (Function.update (Function.update S.R 150 output)
    137 (List.replicate L tick++S.R 137))}
  obtain ⟨v₂,hv₂,he₂⟩ := uclear_exec body 137 v₁ S₁
  let S₂ : Stacks 151 A := {S₁ with R := Function.update S₁.R 137 []}
  obtain ⟨v₃,hv₃,he₃⟩ := uclear_exec body 138 v₂ S₂
  have hlen137 : (S₁.R 137).length = L+start := by simp [S₁,hcursor]
  have hlen138 : (S₂.R 138).length = L := by simpa [S₂,S₁] using hcount
  let D₁ : Stacks 151 A := {S with R := Function.update S.R 150 output}
  have hd : mnSize (mk v D₁)+(S.R 150).length = mnSize (mk v S)+output.length := by
    simpa only [D₁,mk,update_rt,get_rt] using mn_size_update (mk v S) v (.rt 150) output
  have hc : mnSize (mk v₁ S₁)+(D₁.R 137).length =
      mnSize (mk v D₁)+(List.replicate L tick++S.R 137).length := by
    simpa only [S₁,D₁,mk,update_rt,get_rt] using
      mn_size_update (mk v D₁) v₁ (.rt 137) (List.replicate L tick++S.R 137)
  have hsize : mnSize (mk v₁ S₁) ≤ mnSize (mk v S)+L*((2*q+8)+1) := by
    have hout : output.length = L*(2*q+8)+(S.R 150).length := by simp [output]
    have hc' : (D₁.R 137).length = (S.R 137).length := by simp [D₁]
    rw [hc',List.length_append,List.length_replicate] at hc
    rw [hout] at hd
    rw [Nat.mul_add,Nat.mul_one]
    omega
  let bound := mnSize (mk v S)+depth+L*((2*q+8)+1)+8*(cap+2)
  have ht₁ := he₁.mono (J := fun d z => mnSize z+d ≤ bound) (by
    intro d z hz
    change mnSize z+d ≤ mnSize (mk v₁ S₁)+depth+8*(cap+2) at hz
    dsimp only [bound]
    omega)
  have ht₂ := mn_native_exec_within he₂ 0
    (by simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush])
    depth bound (by simpa only [Nat.zero_mul,Nat.add_zero] using ht₁.final)
  have ht₃ := mn_native_exec_within he₃ 0
    (by simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush])
    depth bound (by simpa only [Nat.zero_mul,Nat.add_zero] using ht₂.final)
  refine ⟨v₃,m₁+((2*(L+start)+2)+(2*L+2)),hv₃.trans (hv₂.trans hv₁),
    Nat.add_le_add_right hm₁ _,(ExecWithin.seq ht₁ (ExecWithin.seq ht₂ ht₃)).cast (by rw [hlen137,hlen138]) ?_⟩
  apply congrArg (mk v₃)
  ext1
  · rfl
  · rfl
  · rfl
  · funext k
    by_cases h150 : k = 150 <;> by_cases h137 : k = 137 <;> by_cases h138 : k = 138 <;>
      simp [S₂,S₁,output,h150,h137,h138]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
