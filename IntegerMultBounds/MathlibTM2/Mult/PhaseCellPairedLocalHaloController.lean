module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedPairedOriginHost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPairedLocalHaloClassCode
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloGroups

/-! One local phase scan generates both coordinate pages and their common count. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  ScalarPlacement
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

def pairedLocalHaloController : Pr P 117 Q A U := countedPairedOriginHost pairedLocalHaloClassCode

def pairedLocalHaloControllerCost (V s t band a b L : ℕ) :=
  (37*haloPhaseCount s t a b+16)*tblC V V+
    (haloLengthGroup s t band a b L).length*(12*V+6)+10

theorem pairedLocalHaloController_exec_within {V s t band a b L : ℕ}
    (hs : 0 < s) (hst : s < t) (hband : band ≤ s) (hab : a ≤ b) (hbs : b ≤ s)
    (hL : 0 < L) (hLs : L ≤ s) (hwide : 8*(t+1)^2+2*band+8 < 2^V) (hA : 4 ≤ A)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho V (List.replicate V tick) (List.replicate V tick)
      (haloClassRawState A s t band a b L)))
    (h104 : S.R 104 = []) (h106 : S.R 106 = []) (h116 : S.R 116 = []) (depth : ℕ) :
    ∃ v' F m, ∃ st' : TblSt 16 A, v'.user = v.user ∧
      m ≤ pairedLocalHaloControllerCost V s t band a b L ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        3*pairedLocalHaloControllerCost V s t band a b L) depth pairedLocalHaloController
        (mk v S) m (mk v' F) ∧
      F.R 113 = haloOriginPackets A V s t band a b L++S.R 113 ∧
      F.R 109 = (haloPackedOffsets s t band a b L).flatMap (binSyms V)++S.R 109 ∧
      F.R 116 = List.replicate (haloLengthGroup s t band a b L).length tick ∧
      tblHolds originReg F (tblRho V (List.replicate V tick) (List.replicate V tick) ⟨st'.val,[]⟩) ∧
      (∀ j, st'.val j < 2^V) ∧ F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ k, k ≠ 109 → k ≠ 113 → k ≠ 116 → (∀ r, originReg r ≠ k) → F.R k = S.R k := by
  let : NeZero s := ⟨by omega⟩
  let xs := (haloOrigins s t band a b L).map (fun p => (p,p-a))
  have hfit : ∀ x ∈ xs, x.1 < 2^V ∧ x.2 < 2^V := by
    intro x hx
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hx
    have hb := haloOrigins_bounds s t band a b L p hp
    have hsV : s < 2^V := by nlinarith only [hwide,hst]
    constructor <;> omega
  have hV : 0 < V := by
    by_contra h
    have he : V = 0 := by omega
    simp [he] at hwide
  have hc := pairedLocalHaloClassCode_do (A := A) hst hab hbs hL hwide
  have hc' : TblDo A V V pairedLocalHaloClassCode (haloClassRawState A s t band a b L)
      (fun st' => st'.acc = (xs.flatMap (fun x => tblPairs A V x.1 x.2)).reverse++[])
      (37*haloPhaseCount s t a b+16) := by
    simpa only [xs,haloOrigins,List.flatMap_map,Function.comp_def,List.map_map] using hc
  obtain ⟨v',F,m,st',hu,hm,he,hambient,hlocal,hcount,hh,hbound,hi,ho,hl,hframe⟩ :=
    countedPairedOriginHost_exec (body := body) xs pairedLocalHaloClassCode
      (haloClassRawState A s t band a b L) hc' hfit le_rfl hA hV
      (haloClassRawState_bounded (hab.trans hbs) hbs hLs hst hband hwide) rfl v S hS h104 h106 h116
  have hcost : m ≤ pairedLocalHaloControllerCost V s t band a b L := by
    simpa [pairedLocalHaloControllerCost,xs] using hm
  refine ⟨v',F,m,st',hu,hcost,?_,?_,?_,?_,hh,hbound,hi,ho,hl,hframe⟩
  · exact mn_native_exec_within he 3 (countedPairedOriginHost_native _) depth _
      (Nat.add_le_add_left (Nat.mul_le_mul_left 3 hcost) _)
  · simpa [xs,haloOrigins,haloOriginPackets,List.flatMap_map] using hambient
  · simpa [xs,haloPackedOffsets,List.flatMap_map] using hlocal
  · simpa [xs] using hcount

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
