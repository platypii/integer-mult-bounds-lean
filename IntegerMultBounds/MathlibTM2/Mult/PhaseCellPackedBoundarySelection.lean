module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryRhsSelection
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedInterval
public import IntegerMultBounds.ListFilterInterval

/-! Boundary extraction scans only the packed interval containing the boundary.
The resulting order is the existing ambient boundary order, so its fold and
boundary solver can be reused unchanged. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.BandFactor

def packedBoundaryRhsFlags {s : ℕ} (a N : ℕ) (B : Finset (ZMod s)) : List Bool :=
  (((physOrder s).drop a).take N).map (fun x => decide (x ∈ B))

@[simp] theorem packedBoundaryRhsFlags_length {s a N : ℕ} (B : Finset (ZMod s))
    (hfit : a+N ≤ s) : (packedBoundaryRhsFlags a N B).length = N := by
  simp only [packedBoundaryRhsFlags,List.length_map,List.length_take,List.length_drop,
    physOrder,List.length_map,List.length_range]
  exact min_eq_left (by omega)

theorem packedBoundary_order {s a N : ℕ} [NeZero s] (B : Finset (ZMod s))
    (hB : ∀ i ∈ B, a ≤ i.val ∧ i.val < a+N) :
    ((((physOrder s).drop a).take N).filter (fun x => decide (x ∈ B))) = bOrder s B := by
  apply List.filter_take_drop_of_support
  intro j hj hp
  have hjs : j < s := by simpa only [physOrder,List.length_map,List.length_range] using hj
  have hm : (j : ZMod s) ∈ B := by
    simpa only [physOrder,List.getElem_map,List.getElem_range,decide_eq_true_eq] using hp
  simpa only [ZMod.val_natCast,Nat.mod_eq_of_lt hjs] using hB _ hm

theorem packedBoundaryRhs_select_ordered {s a N : ℕ} [NeZero s]
    (B : Finset (ZMod s)) (C : ZMod s → GaussianInt)
    (hB : ∀ i ∈ B, a ≤ i.val ∧ i.val < a+N) :
    gatherSymbols (packedInterval a N C) (packedBoundaryRhsFlags a N B) =
      (bOrder s B).map C := by
  have hline : packedInterval a N C = (((physOrder s).drop a).take N).map C := by
    simp only [packedInterval,chirpLine,physOrder,List.map_drop,List.map_take,List.map_map,
      Function.comp_def]
  rw [hline,packedBoundaryRhsFlags,gatherSymbols_filter,packedBoundary_order B hB]

theorem packedBoundaryRhs_select_folded {s a N : ℕ} [NeZero s]
    (B : Finset (ZMod s)) (C : ZMod s → GaussianInt)
    (hB : ∀ i ∈ B, a ≤ i.val ∧ i.val < a+N) :
    foldList (gatherSymbols (packedInterval a N C) (packedBoundaryRhsFlags a N B)) =
      (bFoldOrder s B).map C := by
  rw [packedBoundaryRhs_select_ordered B C hB,foldList_map,foldList_bOrder]

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem packedBoundaryRhsOrderedGather_exec {src mask width symbols ts tm acc out cs : Fin T}
    (hreg : [src,mask,width,symbols,ts,tm,acc,out].Nodup)
    (s a N : ℕ) [NeZero s] (B : Finset (ZMod s)) (C : ZMod s → GaussianInt) (w : ℕ)
    (hfit : a+N ≤ s) (hB : ∀ i ∈ B, a ≤ i.val ∧ i.val < a+N)
    (ms : List (Fin (A+4))) (f : Fin (A+4) → Bool) (hflags : ms.map f = packedBoundaryRhsFlags a N B)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = cstream A w (packedInterval a N C)++tail)
    (hmask : S.R mask = ms) (hw : (S.R width).length = w)
    (hfresh : ∀ k ∈ [symbols,ts,tm,acc], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ N*(16*w+10)+16 ∧
      Exec body (gatherRecords src mask width symbols ts tm acc out cs f) (mk v S) m
        (mk v' {S with R := Function.update S.R out (cstream A w ((bOrder s B).map C)++S.R out)}) := by
  let words := (packedInterval a N C).map (csyms A w)
  have hlenMs : ms.length = N := by
    have hh := congrArg List.length hflags
    simpa only [List.length_map,packedBoundaryRhsFlags_length B hfit] using hh
  have hlen : words.length = ms.length := by simp [words,hlenMs,packedInterval_length C hfit]
  have hwidth : ∀ x ∈ words, x.length = w := by
    intro x hx
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hx
    simp
  have hsem : (gatherSymbols words (ms.map f)).flatten = cstream A w ((bOrder s B).map C) := by
    rw [hflags]
    change (gatherSymbols ((packedInterval a N C).map (csyms A w)) (packedBoundaryRhsFlags a N B)).flatten = _
    rw [gatherSymbols_map,packedBoundaryRhs_select_ordered B C hB]
    rfl
  obtain ⟨v',m,hu,hm,he⟩ := gatherRecords_exec (body := body) hreg ms words w f
    hlen hwidth tail v S (by simpa only [words,cstream,List.flatMap_def] using hsrc) hmask hw hfresh
  exact ⟨v',m,hu,by simpa only [hlenMs] using hm,by simpa only [hsem] using he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
