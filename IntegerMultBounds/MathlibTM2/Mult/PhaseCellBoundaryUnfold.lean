module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySolutionField
public import IntegerMultBounds.MathlibTM2.Fast.BandFold
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryNormalizePhysical

/-! Execute inverse folding of the computed boundary solution in its physical bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.BandFactor IntegerMultBounds.NLogN.PhaseCellMatrix

/-- Natural boundary order agrees with the ambient recovery field after real projection. -/
theorem boundary_unfold_field {s : ℕ} [NeZero s] (B : Finset (ZMod s))
    (solution : List GaussianInt) (hlen : solution.length = B.card) :
    (unfoldList solution).map realPartWord = (bOrder s B).map (boundarySolutionField B solution) := by
  apply List.ext_getElem (by simp [length_unfoldList,hlen,bOrder_length])
  intro i hi hj
  have hiN : i < B.card := by simpa [length_unfoldList,hlen] using hi
  have hiB : i < (bOrder s B).length := by simpa [bOrder_length] using hiN
  have hmem : (bOrder s B)[i] ∈ B := by
    have h := List.mem_toFinset.mpr (List.getElem_mem hiB)
    simpa only [bOrder_toFinset] using h
  have hpos : bFoldPos s B (bOrder s B)[i] = foldPosN solution.length i := by
    simp only [bFoldPos,hmem,ite_true,bRank_getElem s B i hiB,foldPosN,hlen]
  have hg := getD_unfoldList (0 : GaussianInt) solution i (by omega)
  rw [List.getD_eq_getElem _ _ (by simpa [length_unfoldList,hlen] using hiN)] at hg
  simp only [List.getElem_map]
  rw [boundarySolutionField,ite_eq_left hmem,hpos,← hg]

theorem boundaryFactorFr_two_updates {A : ℕ} {S S' : Stacks 224 A}
    (r t : RsbR) (xs ys : List (Fin (A+4))) (hframe : RsbFr boundaryFactorReg S S')
    (hholds : RsbHolds boundaryFactorReg S'
      (Function.update (Function.update (boundaryFactorState S) r xs) t ys)) :
    S' = {S with R := (Function.update (Function.update S.R (boundaryFactorReg r) xs)
      (boundaryFactorReg t) ys)} := by
  classical
  have h0 : RsbHolds boundaryFactorReg S (boundaryFactorState S) := fun _ => rfl
  have hh := rsb_holds_upd boundaryFactorReg_injective
    (rsb_holds_upd boundaryFactorReg_injective h0 r xs) t ys
  refine Stacks.ext hframe.1 hframe.2.1 hframe.2.2.1 ?_
  funext i
  by_cases hi : ∃ a, boundaryFactorReg a = i
  · obtain ⟨a,rfl⟩ := hi
    exact (hholds a).trans (hh a).symm
  · rw [hframe.2.2.2 i (by simpa using hi)]
    simp only [Function.update_of_ne (fun h => hi ⟨r,h.symm⟩),
      Function.update_of_ne (fun h => hi ⟨t,h.symm⟩)]

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

/-- Inverse fold consumes the folded solution on 217 and returns natural order on 204. -/
theorem boundary_unfold_physical_exec (w : ℕ) (solution : List GaussianInt)
    (v : HS 224 Q A U) (S : Stacks 224 A)
    (hleft : ∀ i, S.L i = []) (hmul : ∀ i : Fin 64, S.R (boundaryFactorMulReg i) = [])
    (hsrc : S.R 217 = cstream A w solution)
    (hfloor : (S.R 189).length = solution.length/2)
    (hparity : (S.R 191).length = (solution.length+1)/2-solution.length/2)
    (hw : (S.R 160).length = w)
    (hclean : ∀ i ∈ ([204,208,211,198,201,215] : List (Fin 224)), S.R i = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ 60*(solution.length+1)*w+60*solution.length+60 ∧
      Exec body (bandUnfoldLineP boundaryFactorReg) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 217 []) 204
          (cstream A w (unfoldList solution)))}) := by
  have hrun := band_unfoldLine_runs (body := body) boundaryFactorReg_injective
    boundaryFactorReg_disjoint (w := w) (boundaryFactorState S) solution hsrc hfloor hparity hw
    (hclean 204 (by simp)) (hclean 208 (by simp)) (hclean 211 (by simp))
    (hclean 198 (by simp)) (hclean 201 (by simp)) (hclean 215 (by simp))
  obtain ⟨v',S',n,hu,hn,he,hh,hfr⟩ := hrun v S ⟨hleft,hmul⟩ (fun _ => rfl)
  have hS := boundaryFactorFr_two_updates .dout .sel [] _ hfr hh
  rw [hS] at he
  exact ⟨v',n,hu,hn,he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
