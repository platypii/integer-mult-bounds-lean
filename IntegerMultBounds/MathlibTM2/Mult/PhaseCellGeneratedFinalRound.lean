module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedRoundList
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFinalRoundTape
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFinalRoundCost
public import IntegerMultBounds.MathlibTM2.StackLifecycleResources

/-! Generate, execute and release final-rounding controls from binary dimensions. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.Main

variable {T Q A s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem generatedFinalRound_exec (hA : 4 ≤ A) (rg : TblR 8 → Fin T) (hrg : Function.Injective rg)
    (ports : Fin 4 → Fin T) (hports : Function.Injective ports) (hsep : ∀ i r, rg r ≠ ports i)
    {src dst tmp sp sg cy : Fin T}
    (hreg : [src,dst,tmp,ports 0,ports 1,ports 2,ports 3,sp,sg,cy].Nodup)
    {W w q p j E : ℕ} (wl : List (Fin (A+4))) (hwl : wl.length = W)
    (st : TblSt 8 A) (h0 : st.val 0 = w) (h1 : st.val 1 = q) (h2 : st.val 2 = p)
    (h3 : st.val 3 = j) (h4 : st.val 4 = E)
    (h5 : st.val 5 = 0) (h6 : st.val 6 = 0) (h7 : st.val 7 = 0)
    (hp : p ≤ q) (hw : q+E+5 ≤ w) (hsize : q-p+j+(p+E+5) ≤ w) (hroom : w < 2^W)
    (hfit : ∀ i, st.val i < 2^W) (G : ZMod s → GaussianInt)
    (hG : ∀ i : ZMod s, ‖pairedCellRead q w (cstream A w (chirpLine s G)) i‖ ≤ 8*(2 : ℝ)^E)
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds rg S (tblRho W wl [] st))
    (hsrc : S.R src = cstream A w (chirpLine s G))
    (hblank : ∀ r ∈ [dst,tmp,sp,sg,cy], S.R r = []) (hheaders : ∀ i, S.R (ports i) = []) :
    ∃ v' n, ∃ H : ZMod s → GaussianInt, v'.user = v.user ∧
      n ≤ 13*tblC W 0+16*w+44*W+38+s*(14*w+23) ∧
      Exec body (generatedFinalRound rg ports src dst tmp sp sg cy) (mk v S) n
        (mk v' {S with R := (Function.update S.R src (cstream A (p+E+5) (chirpLine s H)))}) ∧
      (∀ i : ZMod s, pairedCellRead p (p+E+5) (cstream A (p+E+5) (chirpLine s H)) i =
        rhoC p (((2 : ℂ)^j)⁻¹*pairedCellRead q w (cstream A w (chirpLine s G)) i)) ∧
      ∀ C, mnProgPush (generatedFinalRound (P := P) (U := U) (A := A) (Q := Q) rg ports src dst tmp sp sg cy) ≤ C →
        (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          (C+1)*(13*tblC W 0+16*w+44*W+38+s*(14*w+23))) depth
          (generatedFinalRound rg ports src dst tmp sp sg cy) (mk v S) n
          (mk v' {S with R := (Function.update S.R src (cstream A (p+E+5) (chirpLine s H)))}) := by
  have hread (i : ZMod s) : pairedCellRead q w (cstream A w (chirpLine s G)) i =
      value q (IntegerMultBounds.MathlibTM2.LayerMachine.symZ w (G i)) := by
    simpa only [List.append_nil] using pairedCellRead_signed (q := q) hA (show 1 ≤ w by omega) G [] i
  obtain ⟨v',n,hu,hn,he,hd,ht⟩ := generatedFinalRound_list_exec (body := body) hA rg hrg ports hports
    hsep hreg wl hwl st h0 h1 h2 h3 h4 h5 h6 h7 hp (by omega : 1 ≤ w) hsize hroom hfit (chirpLine s G)
    v S hS hsrc hblank hheaders
  let H : ZMod s → GaussianInt := fun i => finalRoundWord w q p j (G i)
  have hmap : (chirpLine s G).map (finalRoundWord w q p j) = chirpLine s H := by
    simp only [chirpLine,List.map_map,Function.comp_def,H]
  rw [hmap] at he ht
  refine ⟨v',n,H,hu,?_,he,?_,?_⟩
  · simpa only [chirpLine,List.length_map,List.length_range] using hn
  · intro i
    have hmem : G i ∈ chirpLine s G := List.mem_map.mpr ⟨i.val,List.mem_range.mpr i.val_lt,by simp⟩
    have hb : ‖value q (IntegerMultBounds.MathlibTM2.LayerMachine.symZ w (G i))‖ ≤ 8*(2 : ℝ)^E := by
      rw [←hread i]
      exact hG i
    have hf := finalRound_fits q p j E (p+E+5) hp le_rfl _ hb
    have hv := pairedCellRead_encodedField (q := p) hA (show 0 < p+E+5 by omega) H [] i hf
    rw [List.append_nil] at hv
    rw [hv,hread i]
    exact hd (G i) hmem
  · simpa only [chirpLine,List.length_map,List.length_range] using ht

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
