module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScaledBandControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCollectCyclicColumnEntries
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFoldedBandSchedule

/-! Construct the joint cyclic band range, collect its selected entries, and retire controls. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 151 Q A U}

def preparedCyclicBandCollection : Pr P 151 Q A U :=
  .seq (scaledBandControls 24) collectCyclicColumnEntries

noncomputable def preparedCyclicBandCollectionCost {s : ℕ} [NeZero s]
    (B : Finset (ZMod s)) (q V band a b n : ℕ) : ℕ :=
  let W := 24*band+1
  scaledBandControlsCost 24 n band B.card+
    collectCyclicColumnEntriesCost B q V a b (n-W) (min B.card (n+W+1)-(n-W))

theorem preparedCyclicBandCollection_exec {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (q V band a b n : ℕ)
    (hA : 4 ≤ A) (hwide : s+s ≤ 2^V) (ha : a ≤ s) (hb : b ≤ s) (hn : n < B.card)
    (C D : ZMod s → GaussianInt) (pageTail tail : List (Fin (A+4))) (v : HS 151 Q A U) (S : Stacks 151 A)
    (hindex : (S.R 0).length = n) (hwidth : (S.R 115).length = V)
    (hband : (S.R 124).length = band) (hrows : (S.R 116).length = B.card)
    (hpage : S.R 109 = cstream A V ((bFoldOrder s B).map
      (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++pageTail)
    (hq : (S.R 119).length = q) (hs : (S.R 121).length = s)
    (haSrc : (S.R 144).length = a) (hbSrc : (S.R 145).length = b)
    (hsource : S.R 132 = cstream A (2*q+8) (chirpLine s D)++(cstream A (2*q+8) (chirpLine s C)++tail))
    (hfresh : ∀ k ∈ [(94 : Fin 151),106,135,136,137,138,139,140], S.R k = [])
    (hblank : ∀ k : Fin 151, k.val < 31 → k ≠ 0 → S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ preparedCyclicBandCollectionCost B q V band a b n ∧
      Exec body preparedCyclicBandCollection (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 0 []) 150
          (cstream A (2*q+8) ((foldedBandRows B (24*band+1) n).reverse.map
            (fun i => if a ≤ i.val ∧ i.val < b then C i else D i))++S.R 150))}) := by
  let W := 24*band+1
  let start := n-W
  let L := min B.card (n+W+1)-start
  have hstart : start ≤ min B.card (n+W+1) := by dsimp [start]; omega
  have hfit : start+L ≤ B.card := by dsimp [L]; omega
  obtain ⟨v₁,hv₁,he₁⟩ := scaledBandControls_exec (body := body) 24 n band B.card v S hindex hband hrows
    (by intro k hk; exact hfresh k (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢; tauto))
  let S₁ : Stacks 151 A := {S with R := (Function.update (Function.update (Function.update S.R 0 [])
    137 (List.replicate start tick)) 138 (List.replicate L tick))}
  obtain ⟨v₂,m₂,hv₂,hm₂,he₂⟩ := collectCyclicColumnEntries_exec (body := body) B q V a b start L
    hA hwide ha hb hfit C D pageTail tail v₁ S₁ (by simp [S₁]) (by simp [S₁])
    (by simpa [S₁] using hwidth) (by simpa [S₁] using hpage) (by simpa [S₁] using hq)
    (by simpa [S₁] using hs) (by simpa [S₁] using haSrc) (by simpa [S₁] using hbSrc)
    (by simpa [S₁] using hsource) (by simp [S₁]) (by simpa [S₁] using hfresh 94 (by simp))
    (by simpa [S₁] using hfresh 106 (by simp)) (by simpa [S₁] using hfresh 135 (by simp))
    (by simpa [S₁] using hfresh 136 (by simp)) (by simpa [S₁] using hfresh 139 (by simp))
    (by simpa [S₁] using hfresh 140 (by simp))
    (by intro k hk hk0
        have h137 : k ≠ 137 := by intro he; subst k; norm_num at hk
        have h138 : k ≠ 138 := by intro he; subst k; norm_num at hk
        simpa [S₁,hk0,h137,h138] using hblank k hk hk0)
  have hindices : List.range' start L = (List.range L).map (fun j => start+j) := by
    apply List.ext_getElem <;> simp
  have hwords : (foldedBandRows B W n).reverse.map (fun i => if a ≤ i.val ∧ i.val < b then C i else D i) =
      (List.range L).reverse.map (fun j => let i := bFoldAt s B (start+j); if a ≤ i.val ∧ i.val < b then C i else D i) := by
    change ((List.range' start L).map (bFoldAt s B)).reverse.map _ = _
    rw [hindices]
    simp [List.map_reverse,List.map_map,Function.comp_def]
  refine ⟨v₂,scaledBandControlsCost 24 n band B.card+m₂,hv₂.trans hv₁,Nat.add_le_add_left hm₂ _,
    (Exec.seq he₁ he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  rw [← hwords]
  ext1
  · rfl
  · rfl
  · rfl
  · funext k
    by_cases h0 : k = 0 <;> by_cases h150 : k = 150 <;> by_cases h137 : k = 137 <;> by_cases h138 : k = 138 <;>
      simp [S₁,W,h0,h150,h137,h138,hfresh 137 (by simp),hfresh 138 (by simp)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
