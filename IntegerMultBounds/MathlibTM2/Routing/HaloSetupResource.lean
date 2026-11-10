module

public import IntegerMultBounds.MathlibTM2.Routing.HaloPrefixResource
public import IntegerMultBounds.MathlibTM2.Routing.HaloCountResource

/-! Ordinary header setup is linear in the row volume plus metadata products
that omit a full local field. Bounds are proved once for arbitrary dimensions. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.HaloSetupResource
open HaloPassContext RetainedHaloTensor RetainedTensorEnumeration HaloAxisSchedule HaloMixedOrder HaloMixedVolume
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

structure Bounds (p : Parameters) (T Q : ℕ) : Prop where
  rowVolume : p.N*p.L*p.B ≤ 2*T
  coreProduct : p.L*p.B ≤ Q
  count : p.N ≤ Q
  length : p.L ≤ Q
  doubleHalo : 2*p.H ≤ Q
  forwardExponent : p.k ≤ 2*Q
  returnExponent : p.r ≤ 4*Q

theorem self_le_two_pow (n : ℕ) : n ≤ 2^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; have hp := Nat.two_pow_pos n; omega

variable {ι : Type} [DecidableEq ι] [Fintype ι]

theorem bounds_global (axis : ι → Axis) (retained : Finset ι) (s : Stage ι)
    (hn : (s.left++s.i::s.right).Nodup) (hall : ∀ j, j ∈ s.left++s.i::s.right)
    (hr : Ready axis retained s) (L H : ℕ) (hL : ∀ j, (axis j).L = L) (hH : ∀ j, (axis j).H = H)
    (hLpos : 0 < L) (hlarge : 64*Fintype.card ι*H ≤ L) (hcoarse : s.params.L ≤ s.params.N)
    (hk : 2^s.params.k ≤ 2*s.params.L) (hrpad : 2^s.params.r ≤ 2*(s.params.L+2*s.params.H)) :
    Bounds s.params (volume axis ∅) ((2*volume axis ∅)/L) := by
  have hM : localLength axis retained s.i = s.params.L := by
    simp [localLength,hr.fresh,hr.axis_eq,HaloAxisTensorInvariant.axisOf]
  have hPL : s.params.L = L := by simpa only [hr.axis_eq,HaloAxisTensorInvariant.axisOf] using hL s.i
  have hN : (axis s.i).N = s.params.N := by simp only [hr.axis_eq,HaloAxisTensorInvariant.axisOf]
  have hf := halo_factorization axis retained s.left s.i s.right hn hall
  rw [hM,hN,hr.spectator] at hf
  have hp := product_pos axis retained (haloBefore s.left)
  have hrow : s.params.N*s.params.L*s.params.B ≤ volume axis retained := by
    rw [←hf]
    have hh := Nat.le_mul_of_pos_left (s.params.N*s.params.L*s.params.B) hp
    convert hh using 1; ring
  have hv := RetainedHaloVolume.volume_lt_two_of_large_core axis retained L H hL hH hLpos hlarge
  have hq : volume axis retained/L ≤ (2*volume axis ∅)/L := Nat.div_le_div_right hv.le
  have hpage := page_count_le axis retained s.left s.i s.right hn hall
  rw [hN,hM,hPL] at hpage
  have hcount : s.params.N ≤ (2*volume axis ∅)/L :=
    (Nat.le_mul_of_pos_left _ hp).trans (hpage.trans hq)
  have hcore : s.params.L*s.params.B ≤ (2*volume axis ∅)/L := by
    apply le_trans ((Nat.le_div_iff_mul_le hLpos).mpr ?_) hq
    have hh := Nat.mul_le_mul_right (s.params.L*s.params.B) hcoarse
    calc
      _ = s.params.L*(s.params.L*s.params.B) := by rw [←hPL]; ring
      _ ≤ s.params.N*(s.params.L*s.params.B) := hh
      _ = s.params.N*s.params.L*s.params.B := by ring
      _ ≤ _ := hrow
  have hlength := hcoarse.trans hcount
  have hk' := (self_le_two_pow s.params.k).trans hk
  have hr' := (self_le_two_pow s.params.r).trans hrpad
  refine ⟨hrow.trans hv.le,hcore,hcount,hlength,?_,?_,?_⟩
  · exact s.params.gap.trans hlength
  · omega
  · have hh := s.params.gap; omega

section Bills
variable (p : Parameters) (T Q : ℕ) (h : Bounds p T Q)
include h

private theorem Q_pos : 0 < Q := lt_of_lt_of_le p.N_pos h.count
omit h in
private theorem Q_le_bytes : Q ≤ Q*p.w := Nat.le_mul_of_pos_right Q p.w_pos
private theorem width_le_bytes : p.w ≤ Q*p.w := Nat.le_mul_of_pos_left p.w (Q_pos p T Q h)
private theorem rows_le : p.B ≤ Q := (Nat.le_mul_of_pos_left p.B p.L_pos).trans h.coreProduct

theorem unary_cost_le : HaloUnaryHeaders.cost p.N p.L p.H p.B ≤ 82*T+20 := by
  have hNL := Nat.le_mul_of_pos_right (p.N*p.L) p.B_pos
  have hN := (Nat.le_mul_of_pos_right p.N p.L_pos).trans hNL
  have hL := (Nat.le_mul_of_pos_left p.L p.N_pos).trans hNL
  have hHL : p.H ≤ p.L := by have hh := p.gap; omega
  have hH := hHL.trans hL
  have hLB := Nat.mul_le_mul_right p.B (Nat.le_mul_of_pos_left p.L p.N_pos)
  have hHB := (Nat.mul_le_mul_right p.B hHL).trans hLB
  dsimp only [HaloUnaryHeaders.cost]
  nlinarith only [hNL,hN,hH,hHB,h.rowVolume]

private theorem products_le :
    p.B*p.w ≤ Q*p.w ∧ p.L*(p.B*p.w) ≤ Q*p.w ∧ (2*p.H)*(p.B*p.w) ≤ Q*p.w := by
  have hb := Nat.mul_le_mul_right p.w (rows_le p T Q h)
  have hcore := Nat.mul_le_mul_right p.w h.coreProduct
  have hhalo := (Nat.mul_le_mul_right (p.B*p.w) p.gap).trans (by simpa only [Nat.mul_assoc] using hcore)
  exact ⟨hb,by simpa only [Nat.mul_assoc] using hcore,hhalo⟩

omit h in
private theorem product_cost_le (a b : ℕ) (ha : a ≤ Q) (hab : a*b ≤ Q*p.w) :
    ProductBinaryHeader.cost a b p.V ≤ (Q*p.w)*(4*p.V+16)+9*(Q*p.w)+4*p.V+16 := by
  have h1 := Nat.mul_le_mul_right (4*p.V+16) hab
  have h2 := Nat.mul_le_mul_left 9 (ha.trans (Q_le_bytes p Q))
  dsimp only [ProductBinaryHeader.cost]; omega

omit h in
private theorem product_stock_le (a b : ℕ) (ha : a ≤ Q) (hab : a*b ≤ Q*p.w) :
    ProductBinaryHeader.reserve a b p.V ≤ 26*(Q*p.w)+8*p.V+20 := by
  have h1 := Nat.mul_le_mul_left 8 hab
  have h2 := Nat.mul_le_mul_left 18 (ha.trans (Q_le_bytes p Q))
  dsimp only [ProductBinaryHeader.reserve]; nlinarith only [h1,h2]

theorem binary_cost_le : HaloBinaryHeaders.cost p.N p.L p.H p.B p.w p.V ≤
    (Q*p.w)*(12*p.V+85)+12*p.V+61 := by
  obtain ⟨hb,hcore,hhalo⟩ := products_le p T Q h
  have hqw := Q_le_bytes p Q
  have hb' := (rows_le p T Q h).trans hqw
  have hB : p.B*(4*p.w+9) ≤ 13*(Q*p.w) := by nlinarith only [hb,hb']
  have hN := Nat.mul_le_mul_right (4*p.V+10) (h.count.trans hqw)
  have hx := product_cost_le p Q p.L (p.B*p.w) h.length hcore
  have hy := product_cost_le p Q (2*p.H) (p.B*p.w) h.doubleHalo hhalo
  have hH : p.H ≤ Q*p.w := by have hh := h.doubleHalo; omega
  have h2H := h.doubleHalo.trans hqw
  dsimp only [HaloBinaryHeaders.cost]
  nlinarith only [hB,hN,hx,hy,hH,h2H,hb]

theorem binary_stock_le : HaloBinaryHeaders.reserve p.L p.H p.B p.w p.V ≤ 86*(Q*p.w)+24*p.V+80 := by
  obtain ⟨hb,hcore,hhalo⟩ := products_le p T Q h
  have hqw := Q_le_bytes p Q
  have hb' := (rows_le p T Q h).trans hqw
  have hB : p.B*(4*p.w+9) ≤ 13*(Q*p.w) := by nlinarith only [hb,hb']
  have hx := product_stock_le p Q p.L (p.B*p.w) h.length hcore
  have hy := product_stock_le p Q (2*p.H) (p.B*p.w) h.doubleHalo hhalo
  have h2H := h.doubleHalo.trans hqw
  dsimp only [HaloBinaryHeaders.reserve]
  nlinarith only [hB,hx,hy,h2H]

theorem width_cost_le : HaloWidthHeaders.cost p.w p.L p.H ≤ 12*(Q*p.w)+20 := by
  have h1 := width_le_bytes p T Q h
  have h2 := h.length.trans (Q_le_bytes p Q)
  have h3 := h.doubleHalo.trans (Q_le_bytes p Q)
  dsimp only [HaloWidthHeaders.cost]; omega

theorem header_cost_le : HaloPassHeaderSetup.cost p ≤ 82*T+(Q*p.w)*(12*p.V+97)+12*p.V+101 := by
  have h1 := unary_cost_le p T Q h
  have h2 := binary_cost_le p T Q h
  have h3 := width_cost_le p T Q h
  dsimp only [HaloPassHeaderSetup.cost]; nlinarith only [h1,h2,h3]

theorem header_stock_le : HaloPassHeaderSetup.reserve p ≤ 164*T+110*(Q*p.w)+24*p.V+160 := by
  have h1 := unary_cost_le p T Q h
  have h2 := binary_stock_le p T Q h
  have h3 := width_cost_le p T Q h
  dsimp only [HaloPassHeaderSetup.reserve]; omega

theorem header_size_le : HaloAxisFromDimensions.headerSize p ≤ 2*T+4*(Q*p.w)+3*p.V := by
  have hqw := Q_le_bytes p Q
  have hLB : p.H*p.B ≤ p.L*p.B := Nat.mul_le_mul_right p.B (by have hh := p.gap; omega)
  have hHB := hLB.trans (h.coreProduct.trans hqw)
  have hw := width_le_bytes p T Q h
  have hL := h.length.trans hqw
  have hH := h.doubleHalo.trans hqw
  have hrow := h.rowVolume
  dsimp only [HaloAxisFromDimensions.headerSize]; omega

theorem master_size_le : HaloMetadataAxis.masterSize p ≤ 11*(Q*p.w) := by
  have hqw := Q_le_bytes p Q
  have hN := h.count.trans hqw
  have hB := (rows_le p T Q h).trans hqw
  have hL := h.length.trans hqw
  have hH := h.doubleHalo.trans hqw
  have hw := width_le_bytes p T Q h
  have hk := h.forwardExponent
  have hr := h.returnExponent
  dsimp only [HaloMetadataAxis.masterSize]; omega

theorem master_cost_le : HaloAxisMasterSetup.cost p ≤ 132*(Q*p.w)+133*p.V+169 := by
  have hh := master_size_le p T Q h
  have he : HaloAxisMasterSetup.cost p = 12*HaloMetadataAxis.masterSize p+133*p.V+169 := by
    rw [HaloAxisMasterSetup.cost,UnaryHeaderList.cost_eq]
    simp only [HaloAxisMasterSetup.entries,List.length_cons,List.length_nil,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,HaloMetadataAxis.masterSize]
    ring
  rw [he]; omega

end Bills
end IntegerMultBounds.MathlibTM2.Routing.HaloSetupResource
