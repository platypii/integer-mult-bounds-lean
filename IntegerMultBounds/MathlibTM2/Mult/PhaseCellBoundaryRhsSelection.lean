module

public import IntegerMultBounds.MathlibTM2.Host.GatherRecords
public import IntegerMultBounds.MathlibTM2.Mult.ChirpCyclicMath
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFoldData

/-! A single masked scan produces ordered boundary RHS values; the existing fold gives solver order. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.BandFactor

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def boundaryRhsFlags (s : ℕ) (B : Finset (ZMod s)) : List Bool :=
  (physOrder s).map (fun x => decide (x ∈ B))

theorem boundaryRhsFlags_length (s : ℕ) (B : Finset (ZMod s)) : (boundaryRhsFlags s B).length = s := by
  simp [boundaryRhsFlags,physOrder]

theorem boundaryRhs_select_ordered (s : ℕ) [NeZero s] (B : Finset (ZMod s)) (C : ZMod s → GaussianInt) :
    gatherSymbols (chirpLine s C) (boundaryRhsFlags s B) = (bOrder s B).map C := by
  simpa [chirpLine,boundaryRhsFlags,bOrder,physOrder,List.map_map,Function.comp_def] using
    gatherSymbols_filter C (fun x => decide (x ∈ B)) (physOrder s)

theorem boundaryRhs_select_folded (s : ℕ) [NeZero s] (B : Finset (ZMod s)) (C : ZMod s → GaussianInt) :
    foldList (gatherSymbols (chirpLine s C) (boundaryRhsFlags s B)) = (bFoldOrder s B).map C := by
  rw [boundaryRhs_select_ordered,foldList_map,foldList_bOrder]

theorem boundaryRhsOrderedGather_exec {src mask width symbols ts tm acc out cs : Fin T}
    (hreg : [src,mask,width,symbols,ts,tm,acc,out].Nodup)
    (s : ℕ) [NeZero s] (B : Finset (ZMod s)) (C : ZMod s → GaussianInt) (w : ℕ)
    (ms : List (Fin (A+4))) (f : Fin (A+4) → Bool) (hflags : ms.map f = boundaryRhsFlags s B)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = cstream A w (chirpLine s C)++tail)
    (hmask : S.R mask = ms) (hw : (S.R width).length = w)
    (hfresh : ∀ k ∈ [symbols,ts,tm,acc], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ s*(16*w+10)+16 ∧
      Exec body (gatherRecords src mask width symbols ts tm acc out cs f) (mk v S) m
        (mk v' {S with R := Function.update S.R out (cstream A w ((bOrder s B).map C)++S.R out)}) := by
  let words := (chirpLine s C).map (csyms A w)
  have hlenMs : ms.length = s := by
    have hh := congrArg List.length hflags
    simpa only [List.length_map,boundaryRhsFlags_length] using hh
  have hlen : words.length = ms.length := by simp [words,hlenMs]
  have hwidth : ∀ x ∈ words, x.length = w := by
    intro x hx
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hx
    simp
  have hsem : (gatherSymbols words (ms.map f)).flatten = cstream A w ((bOrder s B).map C) := by
    rw [hflags]
    change (gatherSymbols ((chirpLine s C).map (csyms A w)) (boundaryRhsFlags s B)).flatten = _
    rw [gatherSymbols_map,boundaryRhs_select_ordered]
    rfl
  obtain ⟨v',m,hu,hm,he⟩ := gatherRecords_exec (body := body) hreg ms words w f
    hlen hwidth tail v S (by simpa only [words,cstream,List.flatMap_def] using hsrc) hmask hw hfresh
  exact ⟨v',m,hu,by simpa only [hlenMs] using hm,by simpa only [hsem] using he⟩

theorem boundaryRhsFold_runs {rg : RsbR → Fin T} {ι : Fin 64 → Fin T}
    (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (s : ℕ) [NeZero s] (B : Finset (ZMod s)) (C : ZMod s → GaussianInt) (w : ℕ)
    (σ : RsbR → List (Fin (A+4)))
    (hsel : σ .sel = cstream A w ((bOrder s B).map C))
    (htswn : (σ .tswn).length = (B.card+1)/2*w) (hm2wn : (σ .m2wn).length = B.card/2)
    (hkn : (σ .kn).length = (B.card+1)/2-B.card/2) (hsn : (σ .sn).length = B.card)
    (hwn : (σ (.cm .wn)).length = w) (hvk : σ .vk = []) (hya : σ .ya = []) (hxs : σ .xs = [])
    (hnv : σ .nv = []) (htK : σ .tK = []) (htC : σ .tC = []) (hac2 : σ .ac2 = []) :
    RsbRuns body rg ι (bandFoldLineP rg) σ
      (Function.update (Function.update σ .sel []) .vk (cstream A w ((bFoldOrder s B).map C)))
      (60*(B.card+1)*w+60*B.card+60) := by
  have hlen : ((bOrder s B).map C).length = B.card := by
    rw [List.length_map,← List.toFinset_card_of_nodup (bOrder_nodup s B),bOrder_toFinset]
  have he := band_foldLine_runs (body := body) hrg hdisj σ ((bOrder s B).map C) hsel
    (by simpa only [hlen] using htswn) (by simpa only [hlen] using hm2wn)
    (by simpa only [hlen] using hkn) (by simpa only [hlen] using hsn)
    hwn hvk hya hxs hnv htK htC hac2
  simpa only [hlen,foldList_map,foldList_bOrder] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
