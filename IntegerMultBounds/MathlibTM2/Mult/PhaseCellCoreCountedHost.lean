module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedOriginHost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreGatherCode

/-! Execute the core controller and publish its origins with their derived count. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Fast.TableVM

open IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

/-- The generated scan supplies both the origin stream and its unary count. -/
def generatedCoreCountedHost : Pr P₀ 117 Q A U := countedOriginHost generatedCoreGatherCode

theorem generatedCoreCountedHost_exec {W V s width radius L : ℕ} (st : TblSt 16 A)
    (hs : st.val 0 = s) (hwidth' : st.val 1 = width)
    (hr : st.val 2 = radius) (hL : st.val 3 = L)
    (hwidth : 0 < width) (hwide : s+width+2*radius < 2^W)
    (hpacket : s ≤ 2^V) (hw : V ≤ W) (hA : 4 ≤ A)
    (hV : 0 < V) (hbound : ∀ j, st.val j < 2^W) (hacc : st.acc = [])
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho W (List.replicate W tick) (List.replicate V tick) st))
    (h104 : S.R 104 = []) (h106 : S.R 106 = []) (h116 : S.R 116 = []) :
    ∃ v' S' m, ∃ st' : TblSt 16 A, v'.user = v.user ∧
      m ≤ (18*((s+width-1)/width)+9)*tblC W V + (coreGatherIndices s width radius L).length*(8*V+6)+6 ∧
      Exec body generatedCoreCountedHost (mk v S) m (mk v' S') ∧
      S'.R 109 = (coreGatherIndices s width radius L).flatMap (fun k => binSyms V (coreStart width k-radius)) ++ S.R 109 ∧
      S'.R 116 = List.replicate (coreGatherIndices s width radius L).length tick ∧
      tblHolds originReg S' (tblRho W (List.replicate W tick) (List.replicate V tick) ⟨st'.val, []⟩) ∧
      (∀ j, st'.val j < 2^W) ∧ S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ k, k ≠ 109 → k ≠ 116 → (∀ r, originReg r ≠ k) → S'.R k = S.R k := by
  let xs := (coreGatherIndices s width radius L).map (fun k => coreStart width k-radius)
  have hx : ∀ x ∈ xs, x < 2^V := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    have hk' : k ∈ coreIndices s width := (List.mem_filter.mp hk).1
    exact (Nat.sub_le _ _).trans_lt
      ((coreIndex_start_lt s width k hwidth hk').trans_le hpacket)
  have hc := generatedCoreGatherCode_do (w := V) st hs hwidth' hr hL hwidth hwide
  have hc' : TblDo A W V generatedCoreGatherCode st (fun st' =>
      st'.acc = (xs.flatMap (fun x => tblPairs A V x 0)).reverse ++ st.acc)
      (18*((s+width-1)/width)+9) := by
    simpa only [xs, List.flatMap_map] using hc
  simpa only [xs, List.length_map, List.flatMap_map, generatedCoreCountedHost] using
    countedOriginListHost_exec xs generatedCoreGatherCode st hc' hx hw hA hV hbound hacc
      v S hS h104 h106 h116

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
