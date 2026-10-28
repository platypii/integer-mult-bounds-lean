module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellAxisDensity
public import IntegerMultBounds.MathlibTM2.Mult.Sizes
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloClassCost

/-! The actual selected axis geometry makes quadratic counter work sparse enough. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

/-- The selected precision is at most a constant times the cube of dimension. -/
theorem selectedPrecision_le_dimension_cube {n : ℕ} (h : Sizes.Big n) :
    Sizes.p n ≤ 48*(Sizes.d n)^3 := by
  have hb : Sizes.b n < (Sizes.d n+1)^3 := by
    by_contra hc
    have hp := Nat.pow_le_pow_left (Nat.le_of_not_gt hc) 31
    have hr := Sizes.b_pow_lt_d_succ_pow n
    have hm : (Sizes.d n+1)^64 ≤ (Sizes.d n+1)^93 := Nat.pow_le_pow_right (by omega) (by decide)
    rw [← pow_mul] at hp
    change Sizes.b n^31 < (Sizes.d n+1)^64 at hr
    norm_num only [Nat.mul] at hp
    omega
  have hd := h.one_le_d
  have hc := Nat.pow_le_pow_left (by omega : Sizes.d n+1 ≤ 2*Sizes.d n) 3
  dsimp only [Sizes.p]
  nlinarith only [hb,hc]

theorem selectedAxisLog_sq_le {n : ℕ} (h : Sizes.Big n) :
    (Sizes.ℓ n)^2 ≤ 16*Sizes.d n*Sizes.p n := by
  have hp := selectedPrecision_le_dimension_cube h
  have hl := h.ℓ_bounds.2
  have hd := h.one_le_d
  have hl' : Sizes.ℓ n ≤ 16*(Sizes.d n)^2 := by
    by_contra hc
    have hlt : 16*(Sizes.d n)^2+1 ≤ Sizes.ℓ n := by omega
    have hm := Nat.mul_le_mul_left (3*Sizes.d n) hlt
    nlinarith only [hm,hl,hp,hd]
  have hsq := Nat.mul_le_mul_right (Sizes.ℓ n) hl'
  have hdl : Sizes.d n*Sizes.ℓ n ≤ Sizes.p n := by nlinarith only [hl,Nat.zero_le (Sizes.d n*Sizes.ℓ n)]
  have hm := Nat.mul_le_mul_left (16*Sizes.d n) hdl
  nlinarith only [hsq,hm]

theorem selectedAxisBits_le (n : ℕ) (i : Fin (Sizes.d n)) :
    Nat.size (Sizes.t n i) ≤ Sizes.ℓ n+1 := by
  have ht : Sizes.t n i ≤ 2^Sizes.ℓ n := by
    dsimp only [Sizes.t]
    split_ifs
    · exact Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
    · exact le_rfl
  simpa only [Nat.size_pow] using Nat.size_le_size ht

theorem selectedHaloGeometryWidth_sq_le (cw : ℕ) {n : ℕ} (h : Sizes.Big n)
    (i : Fin (Sizes.d n)) {w : ℕ} (hw : w ≤ cw*Sizes.p n) :
    (haloGeometryWidth (Sizes.t n i) w+1)^2 ≤
      16*(Nat.size cw+13)^2*Sizes.d n*Sizes.p n := by
  have htbits := selectedAxisBits_le n i
  have hlog : Nat.clog 2 (Sizes.p n) ≤ Sizes.d n := by
    have ha := h.alphaU_le_d
    dsimp only [Sizes.alphaU] at ha
    omega
  have hwbits : Nat.size w ≤ Nat.size cw+Nat.clog 2 (Sizes.p n) := by
    apply Nat.size_le.mpr
    have hwp := hw.trans (Nat.mul_le_mul_left cw (Nat.le_pow_clog (by decide : 1 < 2) (Sizes.p n)))
    have hstrict := Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self cw) (Nat.two_pow_pos (Nat.clog 2 (Sizes.p n)))
    rw [← pow_add] at hstrict
    exact hwp.trans_lt hstrict
  have hdl : Sizes.d n ≤ Sizes.ℓ n := by have := h.two_d_lt_ℓ; omega
  have hl : 1 ≤ Sizes.ℓ n := by have := h.two_le_ℓ; omega
  have hconst : Nat.size cw+10 ≤ (Nat.size cw+10)*Sizes.ℓ n := Nat.le_mul_of_pos_right _ hl
  have hwidth : haloGeometryWidth (Sizes.t n i) w+1 ≤ (Nat.size cw+13)*Sizes.ℓ n := by
    dsimp only [haloGeometryWidth]
    nlinarith only [htbits,hwbits,hlog,hdl,hconst]
  have hsq := Nat.pow_le_pow_left hwidth 2
  have hlSq := Nat.mul_le_mul_left ((Nat.size cw+13)^2) (selectedAxisLog_sq_le h)
  nlinarith only [hsq,hlSq]

/-- The exact repeated control bill has only geometry-width quadratic work. -/
theorem haloControlCellCost_le (P q w t u : ℕ) :
    haloControlCellCost P q w t u+12*weightWorkspaceWidth P q w t u+13 ≤
      2048*((haloGeometryWidth t w+1)^2+weightWorkspaceWidth P q w t u+1) := by
  let G := haloGeometryWidth t w
  let V := weightWorkspaceWidth P q w t u
  change 3*(32*(G+4)^2+8*G)+47*G+10*V+59+12*V+13 ≤ 2048*((G+1)^2+V+1)
  nlinarith only [Nat.zero_le G,Nat.zero_le V]

/-- Actual selected geometry and density pay all repeated cell controls in O(t*p). -/
theorem selectedHaloControlCells_le (cw cV : ℕ) {n : ℕ} (h : Sizes.Big n)
    (i : Fin (Sizes.d n)) (P q w u : ℕ) (hw : w ≤ cw*Sizes.p n)
    (hV : weightWorkspaceWidth P q w (Sizes.t n i) u ≤ cV*Sizes.p n) :
    (Sizes.t n i-Sizes.s n i+1)*
      (haloControlCellCost P q w (Sizes.t n i) u+12*weightWorkspaceWidth P q w (Sizes.t n i) u+13) ≤
        (4096*(16*(Nat.size cw+13)^2+cV+1))*Sizes.t n i*Sizes.p n := by
  let g := Sizes.t n i-Sizes.s n i
  let G := haloGeometryWidth (Sizes.t n i) w
  let V := weightWorkspaceWidth P q w (Sizes.t n i) u
  let K := 16*(Nat.size cw+13)^2
  have hgap : Sizes.d n*g ≤ Sizes.t n i := axisGap_mul_dimension_le (h.good.lt i).le (h.good.bounds i)
  have hwidth := selectedHaloGeometryWidth_sq_le cw h i hw
  change (G+1)^2 ≤ K*Sizes.d n*Sizes.p n at hwidth
  have hgeom := Nat.mul_le_mul_left g hwidth
  have hdensity := Nat.mul_le_mul_left (K*Sizes.p n) hgap
  have hgeomWork : g*(G+1)^2 ≤ K*Sizes.t n i*Sizes.p n := by
    nlinarith only [hgeom,hdensity]
  have hsmall : g ≤ Sizes.t n i := Nat.sub_le _ _
  have hword := Nat.mul_le_mul hsmall hV
  have hone : g ≤ Sizes.t n i*Sizes.p n :=
    hsmall.trans (Nat.le_mul_of_pos_right _ (by have := h.thirteen_le_p; omega))
  have hcount : g+1 ≤ 2*g := by have := h.good.lt i; dsimp only [g]; omega
  have hcell := haloControlCellCost_le P q w (Sizes.t n i) u
  have hwork := Nat.mul_le_mul hcount hcell
  change (g+1)*(haloControlCellCost P q w (Sizes.t n i) u+12*V+13) ≤
    (4096*(K+cV+1))*Sizes.t n i*Sizes.p n
  change (g+1)*(haloControlCellCost P q w (Sizes.t n i) u+12*V+13) ≤
    2*g*(2048*((G+1)^2+V+1)) at hwork
  change g*V ≤ Sizes.t n i*(cV*Sizes.p n) at hword
  nlinarith only [hwork,hgeomWork,hword,hone]

/-- Linear data width bounds the whole numerical workspace on the selected axes. -/
theorem selectedWeightWorkspaceWidth_le (cw : ℕ) {n : ℕ} (h : Sizes.Big n)
    (i : Fin (Sizes.d n)) (q w u : ℕ) (hw : w ≤ cw*Sizes.p n) (hq : q ≤ w) (hu : u ≤ Sizes.p n) :
    weightWorkspaceWidth (2^15*Sizes.p n) q w (Sizes.t n i) u ≤ (2*cw+426009)*Sizes.p n := by
  have hl := h.ℓ_bounds.2
  have hdl : Sizes.ℓ n ≤ Sizes.d n*Sizes.ℓ n := Nat.le_mul_of_pos_left _ h.one_le_d
  have hell : Sizes.ℓ n ≤ Sizes.p n := by nlinarith only [hl,hdl,Nat.zero_le (Sizes.d n*Sizes.ℓ n)]
  have hp := h.thirteen_le_p
  have htbits : Nat.size (Sizes.t n i) ≤ 2*Sizes.p n := by have := selectedAxisBits_le n i; omega
  have hubits : Nat.size u ≤ u := Nat.size_le.mpr Nat.lt_two_pow_self
  dsimp only [weightWorkspaceWidth,coefficientWorkspaceWidth]
  simp only [Nat.size_zero]
  norm_num
  nlinarith only [hw,hq,hu,htbits,hubits,hp]

/-- The repeated controller bill at actual selected widths is O(t*p), uniformly in size. -/
theorem selectedHaloControlCells_fast_le (cw : ℕ) :
    ∃ C : ℕ, ∀ (n : ℕ) (h : Sizes.Big n) (i : Fin (Sizes.d n)) (q w u : ℕ),
      w ≤ cw*Sizes.p n → q ≤ w → u ≤ Sizes.p n →
      (Sizes.t n i-Sizes.s n i+1)*
        (haloControlCellCost (2^15*Sizes.p n) q w (Sizes.t n i) u+
          12*weightWorkspaceWidth (2^15*Sizes.p n) q w (Sizes.t n i) u+13) ≤ C*Sizes.t n i*Sizes.p n := by
  refine ⟨4096*(16*(Nat.size cw+13)^2+(2*cw+426009)+1),?_⟩
  intro n h i q w u hw hq hu
  exact selectedHaloControlCells_le cw (2*cw+426009) h i (2^15*Sizes.p n) q w u hw
    (selectedWeightWorkspaceWidth_le cw h i q w u hw hq hu)

theorem geometryTableCost_le (G : ℕ) : tblC G G ≤ 512*(G+1)^2 := by
  dsimp only [tblC]
  nlinarith only [Nat.zero_le G]

/-- Six candidate scans and all per-cell advances have a uniform linear phase-table allowance. -/
theorem selectedHaloPhaseTables_fast_le (cw : ℕ) :
    ∃ C : ℕ, ∀ (n : ℕ) (h : Sizes.Big n) (i : Fin (Sizes.d n)) (w : ℕ),
      w ≤ cw*Sizes.p n →
      (6*(36*(Sizes.t n i-Sizes.s n i+1)+9)+3*(Sizes.t n i-Sizes.s n i+1))*
        tblC (haloGeometryWidth (Sizes.t n i) w) (haloGeometryWidth (Sizes.t n i) w) ≤
          C*Sizes.t n i*Sizes.p n := by
  let K := 16*(Nat.size cw+13)^2
  refine ⟨273*1024*K,?_⟩
  intro n h i w hw
  let g := Sizes.t n i-Sizes.s n i
  let G := haloGeometryWidth (Sizes.t n i) w
  have hwidth := selectedHaloGeometryWidth_sq_le cw h i hw
  change (G+1)^2 ≤ K*Sizes.d n*Sizes.p n at hwidth
  have hgap : Sizes.d n*g ≤ Sizes.t n i := axisGap_mul_dimension_le (h.good.lt i).le (h.good.bounds i)
  have hgeom := Nat.mul_le_mul_left g hwidth
  have hdensity := Nat.mul_le_mul_left (K*Sizes.p n) hgap
  have hwork : g*(G+1)^2 ≤ K*Sizes.t n i*Sizes.p n := by nlinarith only [hgeom,hdensity]
  have hg : 1 ≤ g := by have := h.good.lt i; dsimp only [g]; omega
  have hcount : 6*(36*(g+1)+9)+3*(g+1) ≤ 546*g := by omega
  have htable := Nat.mul_le_mul hcount (geometryTableCost_le G)
  change (6*(36*(g+1)+9)+3*(g+1))*tblC G G ≤ (273*1024*K)*Sizes.t n i*Sizes.p n
  nlinarith only [htable,hwork]

end IntegerMultBounds.MathlibTM2.Cost
