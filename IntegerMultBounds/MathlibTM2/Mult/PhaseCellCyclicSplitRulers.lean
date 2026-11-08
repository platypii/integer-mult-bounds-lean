module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicSplitFromUnary
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseScalarBank
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarHeaderStock
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupStock

/-! Export cyclic endpoints to unary rulers and retire the temporary scalar bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def cyclicEndpointCopies (end1 end2 : Fin T) : List (Fin 7 × Fin T) := [(5,end1),(6,end2)]

def cyclicEndpointValues (s a n : ℕ) (i : Fin 7) : ℕ :=
  if i = 5 then a+min n (s-a) else n-min n (s-a)

def cyclicEndpointR (s a n : ℕ) (end1 end2 : Fin T) (R : Regs T A) : Regs T A :=
  unaryCopiesR (cyclicEndpointValues s a n) R (cyclicEndpointCopies end1 end2)

theorem cyclicEndpointR_end1 (s a n : ℕ) (end1 end2 : Fin T) (R : Regs T A)
    (hne : end1 ≠ end2) :
    cyclicEndpointR s a n end1 end2 R end1 =
      List.replicate (a+min n (s-a)) tick ++ R end1 := by
  simp [cyclicEndpointR, cyclicEndpointCopies, unaryCopiesR, cyclicEndpointValues, hne]

theorem cyclicEndpointR_end2 (s a n : ℕ) (end1 end2 : Fin T) (R : Regs T A)
    (hne : end1 ≠ end2) :
    cyclicEndpointR s a n end1 end2 R end2 =
      List.replicate (n-min n (s-a)) tick ++ R end2 := by
  simp [cyclicEndpointR, cyclicEndpointCopies, unaryCopiesR, cyclicEndpointValues, hne.symm]

theorem cyclicEndpointR_off (s a n : ℕ) (end1 end2 : Fin T) (R : Regs T A)
    (k : Fin T) (h1 : end1 ≠ k) (h2 : end2 ≠ k) :
    cyclicEndpointR s a n end1 end2 R k = R k := by
  apply unaryCopiesR_off
  simp only [cyclicEndpointCopies, List.mem_cons, List.not_mem_nil, or_false]
  intro p hp
  rcases hp with rfl | rfl
  · exact h1
  · exact h2

def cyclicSplitRulers (rg : TblR 7 → Fin T) (header word saved tmp carry sPort aPort nPort end1 end2 : Fin T) : Pr P T Q A U :=
  .seq (cyclicSplitFromUnary rg header word saved tmp carry sPort aPort nPort)
    (.seq (tblUnaryCopies rg (cyclicEndpointCopies end1 end2)) (releaseScalarBank rg))

def cyclicSplitRulersCost (R : Regs T A) (W a n : ℕ) (sPort aPort nPort : Fin T) : ℕ :=
  (binaryHeaderQueueCost R W [sPort,aPort,nPort]+7*(4*W+4)+3*(8*W+8)+2+5*tblC W 0)+
    (6*(a+n)+22*W+13)+(2*(7*W)+15)

theorem cyclicSplitRulers_native (rg : TblR 7 → Fin T) (header word saved tmp carry sPort aPort nPort end1 end2 : Fin T) :
    mnNativePushBound 3 (cyclicSplitRulers (P := P) (Q := Q) (A := A) (U := U)
      rg header word saved tmp carry sPort aPort nPort end1 end2) :=
  ⟨⟨installUnaryScalarInputs_native ..,tblCompile_native ..⟩,
    mnNativePushBound_mono (by decide) (tblUnaryCopies_native ..),
    mnNativePushBound_mono (by decide : 0 ≤ 3) (clearWords_native _)⟩

theorem cyclicSplitRulers_exec (rg : TblR 7 → Fin T) (hrg : Function.Injective rg)
    (header word saved tmp carry sPort aPort nPort : Fin T) (hheader : ∀ r, rg r ≠ header)
    (hregs : ∀ src ∈ [sPort,aPort,nPort], [src,rg .wr,word,saved,tmp,header].Nodup)
    (end1 end2 : Fin T) (hoff : ∀ r, rg r ≠ end1 ∧ rg r ≠ end2)
    (W s a n : ℕ) (has : a ≤ s) (hns : n ≤ s) (hwide : s < 2^W)
    (wl : List (Fin (A+4))) (hwl : wl.length = W) (v : HS T Q A U) (S : Stacks T A)
    (hs : (S.R sPort).length = s) (ha : (S.R aPort).length = a) (hn : (S.R nPort).length = n)
    (hwidth : S.R (rg .wr) = wl) (hblank : ∀ r, r ≠ .wr → S.R (rg r) = [])
    (hwork : ∀ k ∈ [word,saved,tmp], S.R k = []) :
    ∃ v' steps, v'.user = v.user ∧ steps ≤ cyclicSplitRulersCost S.R W a n sPort aPort nPort ∧
      ∀ depth, ExecWithin body (fun j z => mnSize z+j ≤ mnSize (mk v S)+depth+
        3*cyclicSplitRulersCost S.R W a n sPort aPort nPort) depth
        (cyclicSplitRulers rg header word saved tmp carry sPort aPort nPort end1 end2)
        (mk v S) steps (mk v' {S with R := cyclicEndpointR s a n end1 end2 S.R}) := by
  obtain ⟨v₁,M,m₁,st,hv₁,hm₁,he₁,hh,hend,hrest,_,_,_,hacc,hfit,hin,hout,hL,hframe⟩ :=
    cyclicSplitFromUnary_exec (body := body) rg hrg header word saved tmp carry sPort aPort nPort hheader hregs
      W s a n has hns hwide wl hwl v S hs ha hn hwidth hblank hwork
  have hcopies : ∀ p ∈ cyclicEndpointCopies end1 end2, ∀ r, rg r ≠ p.2 := by
    intro p hp r
    simp only [cyclicEndpointCopies,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl
    · exact (hoff r).1
    · exact (hoff r).2
  have hvalues : ∀ p ∈ cyclicEndpointCopies end1 end2, st.val p.1 = cyclicEndpointValues s a n p.1 := by
    intro p hp
    simp only [cyclicEndpointCopies,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl
    · simpa [cyclicEndpointValues] using hend
    · simpa [cyclicEndpointValues] using hrest
  obtain ⟨v₂,m₂,hv₂,hm₂,he₂⟩ := tblUnaryCopies_exec (body := body) hrg wl [] st hfit
    (cyclicEndpointCopies end1 end2) hcopies v₁ M hh
  have hcopyR := unaryCopiesR_congr st.val (cyclicEndpointValues s a n) M.R (cyclicEndpointCopies end1 end2) hvalues
  let F : Stacks T A := {M with R := cyclicEndpointR s a n end1 end2 M.R}
  let G : Stacks T A := {S with R := cyclicEndpointR s a n end1 end2 S.R}
  have he₂' : Exec body (tblUnaryCopies rg (cyclicEndpointCopies end1 end2)) (mk v₁ M) m₂ (mk v₂ F) := by
    simpa only [F, cyclicEndpointR, hcopyR] using he₂
  have htable (R : Regs T A) (r : TblR 7) : cyclicEndpointR s a n end1 end2 R (rg r) = R (rg r) :=
    unaryCopiesR_off _ _ _ _ (fun p hp => (hcopies p hp r).symm)
  have hhF : tblHolds rg F (tblRho W wl [] st) := fun r => (htable M.R r).trans (hh r)
  have hbase (k : Fin T) (hk : ∀ r, rg r ≠ k) : F.R k = G.R k := by
    apply unaryCopiesR_congr_base
    · intro p hp
      exact hframe p.2 (fun r => hcopies p hp r)
    · exact hframe k hk
  obtain ⟨v₃,hv₃,he₃⟩ := releaseScalarBank_to_state_exec (body := body) rg hrg W wl st hacc v₂ F G hhF
    ((htable S.R .wr).trans hwidth) (fun r hr => (htable S.R r).trans (hblank r hr)) hin hout hL hbase
  have hconvert : m₂ ≤ 6*(a+n)+22*W+13 := by
    simp only [unaryCopiesCost,cyclicEndpointCopies,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,hend,hrest] at hm₂
    have hsum : (a+min n (s-a))+(n-min n (s-a)) = a+n := by omega
    omega
  have hex : Exec body (cyclicSplitRulers rg header word saved tmp carry sPort aPort nPort end1 end2)
      (mk v S) (m₁+(m₂+(2*(7*W)+15))) (mk v₃ G) :=
    (Exec.seq he₁ (Exec.seq he₂' he₃)).cast (by omega) rfl
  have hcost : m₁+(m₂+(2*(7*W)+15)) ≤ cyclicSplitRulersCost S.R W a n sPort aPort nPort := by
    dsimp [cyclicSplitRulersCost]
    omega
  exact ⟨v₃,_,hv₃.trans (hv₂.trans hv₁),hcost,fun depth =>
    mn_native_exec_within hex 3 (cyclicSplitRulers_native ..) depth
      (mnSize (mk v S)+depth+3*cyclicSplitRulersCost S.R W a n sPort aPort nPort) (by omega)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
