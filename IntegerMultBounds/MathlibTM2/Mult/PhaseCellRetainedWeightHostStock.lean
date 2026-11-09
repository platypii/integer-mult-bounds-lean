module

public import IntegerMultBounds.MathlibTM2.Fast.TableHostStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedWeightHost

/-! Retained weight rows share table arithmetic workspace across the complete stream. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem retainedWeightRows_exec_within {V w q P s t u L lo : ℕ} (st : TblSt 48 A)
    (hready : WeightReady A V P q s t u L st) (hlo' : st.val 47 = lo)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u) (hlo : lo < s) (hL : L ≤ s)
    (hV : V = weightWorkspaceWidth P q w t u) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds coefficientReg S (tblRho V (List.replicate V tick) (List.replicate w tick) st)) :
    ∃ v' S' m st', v'.user = v.user ∧ m ≤ retainedWeightRowsCost V w P L ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+6*L*w+3*tblC V w+2)
        depth retainedWeightRows (mk v S) m (mk v' S')) ∧
      WeightReady A V P q s t u L st' ∧
      tblHolds coefficientReg S' (tblRho V (List.replicate V tick) (List.replicate w tick) st') ∧
      S'.R 110 = (List.range L).flatMap (weightPairSymbols A w q P s t u lo) ++ S.R 110 ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ k, k.val ≥ 63 → k ≠ 110 → S'.R k = S.R k := by
  obtain ⟨hw, hPV, hqV, hloV, hLV, hsV, _, hsq, huV, _, hargs⟩ :=
    weightWorkspaceWidth_facts (q := q) (w := w) hP hs hst hu hlo hL
  rw [← hV] at hw hPV hqV hloV hLV hsV hsq huV hargs
  rcases hready.initialized with ⟨hp, hn, hd, hden, hq, hpowP, hqp⟩
  have hc := weightStreamCode_do (A := A) (V := V) (w := w) st hp hready.precision hn hready.modulus
    hready.period hready.scale hd hden hq hpowP hqp hready.rows hlo'
    hP hs hst hloV hLV hsV hsq huV hPV hqV hargs
  have hoff : ∀ r, coefficientReg r ≠ (110 : Fin 117) := by
    intro r he; have hr := coefficientReg_range r; rw [he] at hr; omega
  obtain ⟨v', S', m, st', ⟨⟨ha, hf⟩, hb⟩, hv, hm, he, ho, hh, hin, hout, hleft, hframe⟩ :=
    tblHost_runs_within (body := body) coefficientReg_injective hoff (List.replicate V tick) (List.replicate w tick)
      (by simp) (by simp) hw (hc.bounded hready.bounded) hready.bounded v S hS
  rw [ha, hready.acc, List.append_nil, List.length_reverse] at hm he
  rw [ha, hready.acc, List.append_nil, List.reverse_reverse] at ho
  have hlen : ((List.range L).flatMap (weightPairSymbols A w q P s t u lo)).length = 2*L*w := by
    simp [List.length_flatMap, weightPairSymbols]
    ring
  rw [hlen] at he
  have hvolume : 3*(2*L*w) = 6*L*w := by ring
  rw [hvolume] at he
  refine ⟨v', S', m, ⟨st'.val, []⟩, hv, ?_, ?_,
    hready.frame hb rfl hf, hh, ho, hin, hout, hleft, ?_⟩
  · dsimp only [retainedWeightRowsCost]
    rw [hlen] at hm
    nlinarith only [hm]
  · intro depth
    exact he depth
  · intro k hk hk110
    exact hframe k hk110 (fun r he => by have hr := coefficientReg_range r; rw [he] at hr; omega)

theorem retainedWeightInit_exec_within {V w P q s t u L : ℕ} (st : TblSt 48 A)
    (hP' : st.val 19 = P) (hq : st.val 45 = q) (hs' : st.val 34 = s)
    (ht : st.val 35 = t) (hu' : st.val 36 = u) (hL' : st.val 46 = L)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u) (hL : L ≤ s)
    (hV : V = weightWorkspaceWidth P q w t u) (hbound : ∀ k, st.val k < 2^V) (hacc : st.acc = [])
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds coefficientReg S (tblRho V (List.replicate V tick) (List.replicate w tick) st)) :
    ∃ v' S' m st', v'.user = v.user ∧ m ≤ (158*P+8*q+424)*tblC V w ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+3*tblC V w)
        depth retainedWeightInit (mk v S) m (mk v' S')) ∧
      WeightReady A V P q s t u L st' ∧
      tblHolds coefficientReg S' (tblRho V (List.replicate V tick) (List.replicate w tick) st') ∧
      tblFr coefficientReg S S' := by
  obtain ⟨hw, hPV, hqV, _, _, hsV, htV, _, _, hdV, _⟩ :=
    weightWorkspaceWidth_facts (q := q) (w := w) hP hs hst hu (show 0 < s from hs) hL
  rw [← hV] at hw hPV hqV hsV htV hdV
  have hc := weightInitCode_do (A := A) (V := V) (w := w) st hP' hq hs' ht hst.le hP hPV hqV hsV htV hdV
  obtain ⟨st', k, hbig, ⟨⟨hinit, ha, hf⟩, hb⟩, hk⟩ := hc.bounded hbound
  obtain ⟨v', S', m, hv, hm, he, hh, hframe⟩ := tblCompile_runs_within (body := body)
    coefficientReg_injective (List.replicate V tick) (List.replicate w tick)
    (by simp) (by simp) hw hbig hbound v S hS
  have hm := hm.trans (Nat.mul_le_mul_right (tblC V w) hk)
  simp only [ha, Nat.sub_self, Nat.add_zero] at he
  refine ⟨v', S', m, st', hv, hm, he, ?_, hh, hframe⟩
  exact ⟨hb, ha.trans hacc, (hf 19 (by decide) (by simp)).trans hP',
    (hf 34 (by decide) (by simp)).trans hs', (hf 35 (by decide) (by simp)).trans ht,
    (hf 36 (by decide) (by simp)).trans hu', (hf 46 (by decide) (by simp)).trans hL', hinit⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
