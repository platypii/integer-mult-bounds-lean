module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellHaloGatheredStock
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedGatheredStock
public import IntegerMultBounds.MathlibTM2.Mult.Sizes

/-! Aggregate the actual gathered-interior stock envelope over all halo length
classes. Shared charges remain explicit; repeated traffic is local, including
short endpoint cells. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {U : Type}

theorem selectedHaloGatheredStock_le_local (hQ : SS.states ≤ Q)
    (R K ct ce N V u target rhsExp band a b : ℕ) {n : ℕ} (h : Sizes.Big n)
    (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
    (hu : u ≤ Sizes.p n) (ht : target ≤ ct*Sizes.p n) (he : rhsExp ≤ ce*Sizes.p n)
    (hab : a ≤ b) :
    let p := Sizes.p n
    let s := Sizes.s n i
    let t := Sizes.t n i
    let cV := 2*(16*20+8*ct+8*ce+128)+426009
    let l := haloInverseRingLog s t
    let w := executionWidth p l target rhsExp
    let count := fun L => (haloLengthGroup s t band a b L).length
    ((haloLengthKeys s t band a b).map (fun L =>
      if count L = 0 then 0 else
        gatheredInteriorWorkspace (A := A) (U := U) hQ R K p l N (count L) V (b-a) L s t u target rhsExp)).sum ≤
      ((haloLengthKeys s t band a b).map (fun L =>
        cachedOriginsWorkspace (P₀ := Empty) (A := A) (U := U) hQ R K p l 0 L s t u target rhsExp+
          3*(preparedOriginAdvanceCost V (b-a) w (count L)+2*((b-a)*w)+2*count L+10)+
          1500*(count L*L*w)+38)).sum+
      (1872+cachedOriginsTrafficFactor (P₀ := Empty) (A := A) (U := U) hQ R cV)*N*
        (((haloInterior s t band a b).card+8*(b-a)+8*(s/(t-s)+1))*w+6*((b-a)*w+1)) := by
  dsimp only
  obtain ⟨hl,hr,hw,hV⟩ := selectedHaloGatheredWidths ct ce h i u target rhsExp hu ht he
  have hclasses := List.sum_le_sum (l := haloLengthKeys (Sizes.s n i) (Sizes.t n i) band a b)
    (f := fun L => if (haloLengthGroup (Sizes.s n i) (Sizes.t n i) band a b L).length = 0 then 0 else
      gatheredInteriorWorkspace (A := A) (U := U) hQ R K (Sizes.p n)
        (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) N
        (haloLengthGroup (Sizes.s n i) (Sizes.t n i) band a b L).length V (b-a) L
        (Sizes.s n i) (Sizes.t n i) u target rhsExp)
    (g := fun L => gatheredInteriorLinearWorkspace (A := A) (U := U) hQ R K (Sizes.p n)
        (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) N
        (haloLengthGroup (Sizes.s n i) (Sizes.t n i) band a b L).length V (b-a) L
        (Sizes.s n i) (Sizes.t n i) u target rhsExp (2*(16*20+8*ct+8*ce+128)+426009)) (by
      intro L hL
      have hpos : 0 < L := of_decide_eq_true (List.mem_filter.mp hL).2
      split_ifs with hz
      · exact Nat.zero_le _
      · exact gatheredInteriorWorkspace_le_linear hQ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          (by omega) hpos hV)
  exact hclasses.trans (haloGatheredInteriorStock_le_local (A := A) (U := U) hQ
    R K (Sizes.p n) N V (Sizes.s n i) (Sizes.t n i) u target rhsExp
    (2*(16*20+8*ct+8*ce+128)+426009) band a b (h.good.lt i)
    (selectedAxis_gap_le_source h i) hab)

end IntegerMultBounds.MathlibTM2.Cost
