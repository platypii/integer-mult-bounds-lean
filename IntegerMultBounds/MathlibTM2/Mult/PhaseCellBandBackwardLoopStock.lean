module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBandBackwardStepStock
public import IntegerMultBounds.MathlibTM2.Fast.ResampBScanStock
public import IntegerMultBounds.MathlibTM2.Host.ReplaceFourStock

/-! One complete forward column shares a numerical reserve and pays only linear
native traffic around it. Numerical correctness remains the existing band contract. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
  {rg : RsbR → Fin T} {ι : Fin 64 → Fin T}

theorem band_bwdLoop_runs_within (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w p B s : ℕ} (σ : RsbR → List (Fin (A + 4))) (hready : RsbReady σ w p) (hw : 1 ≤ w)
    (hp : p ≤ w) (cs : List (List ℤ)) (hcs : cs.length = s) (hcl : ∀ c ∈ cs, c.length = B)
    (rcs : List ℤ) (hrcs : rcs.length = s) (hfr : ∀ x ∈ rcs, Fits w (⟨x, 0⟩ : GaussianInt))
    (pend : List GaussianInt) (hpl : pend.length = s + B)
    (hfit : ∀ j < s, Fits w ((Mult.BandList.bandPendB p cs rcs pend j).headD 0))
    (hfx : ∀ j < s, Fits w (tdivN p ((Mult.BandList.bandPendB p cs rcs pend j).headD 0 *
      ⟨rcs.getD j 0, 0⟩)))
    (hfc : ∀ c ∈ cs, ∀ x ∈ c, Fits w (⟨x, 0⟩ : GaussianInt)) (D : List (Fin (A + 4)))
    (hvk : σ .vk = cstream A w pend) (hef : σ .ef = cstream A w (cs.map colC).flatten)
    (hdout : σ .dout = D) (hhv : σ .hv = []) (hya : σ .ya = []) (hxs : σ .xs = [])
    (hpr : σ .pr = []) (hnv : σ .nv = []) (hac : σ .ac = []) (hac2 : σ .ac2 = [])
    (htC : σ .tC = []) (htA : σ .tA = []) (htJ : σ .tJ = []) (hb1 : σ .b1 = [])
    (htL : σ .tL = []) (hsn : (σ .sn).length = s) (hxa : σ .xa = []) (hhc : σ .hc = [])
    (htb : σ .tb = cstream A w (rcs.map fun x => (⟨x, 0⟩ : GaussianInt)))
    (hm2n : (σ .m2n).length = B) (hmwn : (σ .mwn).length = B * w)
    (K L : ℕ)
    (hpushK : mnProgPush (rmulOne (P := P) (Q := Q) (A := A) (U := U)
      ι hι hT hQ (rsbCr rg .hv .xa .hc)) ≤ K)
    (hpushL : mnProgPush (rmulOne (P := P) (Q := Q) (A := A) (U := U)
      ι hι hT hQ (rsbCr rg .ya .xs .pr)) ≤ L) :
    RsbRunsWithin (body := body) (rg := rg) (ι := ι) (bandBwdLoopP rg hι hT hQ) σ
      (Function.update (Function.update (Function.update (Function.update σ .vk
        (cstream A w (Mult.BandList.bandPendB p cs rcs pend s))) .tb []) .ef []) .dout
        (cstream A w (Mult.BandList.bandOutB p cs rcs pend s) ++ D))
      (s * (rmulCost w + 30 * w + 40 + bandFwdStepCost w B + 6) + 4) ((realWeightWorkspace K w 1+1000*(w+1))+(realWeightWorkspace L w B+1000*(B+1)*(w+1))) := by
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → RsbR → List (Fin (A + 4)), Ψ = fun j =>
      Function.update (Function.update (Function.update (Function.update σ .vk
        (cstream A w (Mult.BandList.bandPendB p cs rcs pend j))) .tb
        (cstream A w ((rcs.map fun x => (⟨x, 0⟩ : GaussianInt)).drop j))) .ef
        (cstream A w ((cs.map colC).drop j).flatten)) .dout
        (cstream A w (Mult.BandList.bandOutB p cs rcs pend j) ++ D) := ⟨_, rfl⟩
  have hbody : ∀ j < (σ .sn).length, ∀ X Y, RsbRunsWithin (body := body) (rg := rg) (ι := ι) (bandBwdStepP rg hι hT hQ)
      (rsbUpd2 (Ψ j) .sn X .tL Y) (rsbUpd2 (Ψ (j + 1)) .sn X .tL Y)
      (rmulCost w + 30 * w + 40 + bandFwdStepCost w B) ((realWeightWorkspace K w 1+1000*(w+1))+(realWeightWorkspace L w B+1000*(B+1)*(w+1))) := by
    intro j hj X Y
    rw [hsn] at hj
    have hlenj := Mult.BandList.length_bandPendB p cs rcs pend j (by omega)
    obtain ⟨y, rest, hyr⟩ : ∃ y rest, Mult.BandList.bandPendB p cs rcs pend j = y :: rest := by
      cases h : Mult.BandList.bandPendB p cs rcs pend j with
      | nil => rw [h] at hlenj; simp at hlenj; omega
      | cons y rest => exact ⟨y, rest, rfl⟩
    have hrl : rest.length = s + B - j - 1 := by rw [hyr] at hlenj; simp at hlenj; omega
    have hjc : j < cs.length := by omega
    have hcj := hcl (cs[j]'hjc) (List.getElem_mem hjc)
    have hready' : RsbReady (rsbUpd2 (Ψ j) .sn X .tL Y) w p := by
      simp only [rsbUpd2, hΨ]
      exact (((((hready.update .vk (fun c => by simp) _).update .tb (fun c => by simp) _).update
        .ef (fun c => by simp) _).update
        .dout (fun c => by simp) _).update .sn (fun c => by simp) _).update .tL
        (fun c => by simp) _
    have hjr : j < rcs.length := by omega
    have hstep := band_bwdStep_runs_within (body := body) (ι := ι) (w := w) (B := B) hrg hdisj
      hι hT hQ hA
      (rsbUpd2 (Ψ j) .sn X .tL Y) hready' hw hp y (rcs[j]'hjr) (rest.take B) (rest.drop B)
      (colC (cs[j]'hjc))
      ((cs.map colC).drop (j + 1)).flatten (by simp only [List.length_take]; omega) (by simp [colC, hcj])
      (by have := hfit j hj; rwa [hyr] at this) (hfr _ (List.getElem_mem hjr))
      (by have := hfx j hj; rwa [hyr, List.getD_eq_getElem _ _ hjr] at this)
      (by intro a ha; simp only [colC, List.mem_map] at ha; obtain ⟨x, hx, rfl⟩ := ha
          exact ⟨hfc _ (List.getElem_mem hjc) x hx, rfl⟩)
      (cstream A w (Mult.BandList.bandOutB p cs rcs pend j) ++ D)
      (cstream A w ((rcs.map fun x => (⟨x, 0⟩ : GaussianInt)).drop (j + 1)))
      (by simp [hΨ, hyr]) (by
        have hjm : j < (rcs.map fun x => (⟨x, 0⟩ : GaussianInt)).length := by simpa using hjr
        simp [hΨ]; rw [List.drop_eq_getElem_cons hjm]; simp) (by
        have hjm : j < (cs.map colC).length := by simpa using hjc
        simp [hΨ]; rw [List.drop_eq_getElem_cons hjm]; simp)
      (by simp [hΨ]) (by simp [hΨ, hhv]) (by simp [hΨ, hya]) (by simp [hΨ, hxs])
      (by simp [hΨ, hpr]) (by simp [hΨ, hnv]) (by simp [hΨ, hac]) (by simp [hΨ, hac2])
      (by simp [hΨ, htC]) (by simp [hΨ, htA]) (by simp [hΨ, htJ]) (by simp [hΨ, hb1])
      (by simp [hΨ, hxa]) (by simp [hΨ, hhc]) (by simp [hΨ, hm2n]) (by simp [hΨ, hmwn]) K L hpushK hpushL
    refine hstep.congr ?_
    have hnext : Mult.BandList.bandPendB p cs rcs pend (j + 1) =
        List.zipWith (· - ·) (rest.take B)
          (List.zipWith (fun a b => tdivN p (a * b))
            (List.replicate B (tdivN p (y * ⟨rcs[j]'hjr, 0⟩))) (colC (cs[j]'hjc))) ++
          rest.drop B := by
      have e1 : (cs[j]'hjc).take B = cs[j]'hjc := List.take_of_length_le (le_of_eq hcj)
      rw [machine_sub_eq, e1]
      simp only [Mult.BandList.bandPendB, hyr, List.getD_eq_getElem _ _ hjc,
        List.getD_eq_getElem _ _ hjr]
      rw [subColC_split p _ (cs[j]'hjc) rest (by omega), hcj]
    have hout : Mult.BandList.bandOutB p cs rcs pend (j + 1) =
        tdivN p (y * ⟨rcs[j]'hjr, 0⟩) :: Mult.BandList.bandOutB p cs rcs pend j := by
      simp [Mult.BandList.bandOutB, hyr, List.getElem?_eq_getElem hjr]
    funext r; cases r <;> simp [hΨ, hnext, hout]
  have hstock : ∀ j < (σ .sn).length, ∀ X Y (v v' : HS T Q A U) S F,
      RsbHolds rg S (rsbUpd2 (Ψ j) .sn X .tL Y) →
      RsbHolds rg F (rsbUpd2 (Ψ (j+1)) .sn X .tL Y) → RsbFr rg S F →
      mnSize (mk v' F) ≤ mnSize (mk v S) := by
    intro j hj X Y v v' S F hS hF hf
    have hj' : j < s := by omega
    have hlenj := Mult.BandList.length_bandPendB p cs rcs pend j (by omega)
    have hlenj' := Mult.BandList.length_bandPendB p cs rcs pend (j+1) (by omega)
    have hnonempty : Mult.BandList.bandPendB p cs rcs pend j ≠ [] := by
      intro he; rw [he] at hlenj; simp at hlenj; omega
    obtain ⟨y,rest,hyr⟩ : ∃ y rest, Mult.BandList.bandPendB p cs rcs pend j = y::rest := by
      cases he : Mult.BandList.bandPendB p cs rcs pend j with
      | nil => exact False.elim (hnonempty he)
      | cons y rest => exact ⟨y,rest,rfl⟩
    have hstate : F = {S with R := (Function.update (Function.update (Function.update (Function.update S.R
        (rg .vk) (F.R (rg .vk))) (rg .ef) (F.R (rg .ef))) (rg .dout) (F.R (rg .dout))) (rg .tb) (F.R (rg .tb)))} := by
      refine Stacks.ext hf.1 hf.2.1 hf.2.2.1 ?_
      funext k
      dsimp only
      by_cases hk : ∃ r, rg r = k
      · obtain ⟨r,rfl⟩ := hk
        by_cases hr : r = .vk
        · subst r; simp [hrg.eq_iff]
        by_cases he : r = .ef
        · subst r; simp [hrg.eq_iff]
        by_cases hd : r = .dout
        · subst r; simp [hrg.eq_iff]
        by_cases ht : r = .tb
        · subst r; simp [hrg.eq_iff]
        rw [Function.update_of_ne (hrg.ne ht),Function.update_of_ne (hrg.ne hd),Function.update_of_ne (hrg.ne he),
          Function.update_of_ne (hrg.ne hr),hF r,hS r]
        simp [rsbUpd2,hΨ,Function.update_apply,hr,he,hd,ht]
      · have hnot : ∀ r, rg r ≠ k := by simpa using hk
        simp only [Function.update_of_ne (hnot .tb).symm,Function.update_of_ne (hnot .dout).symm,
          Function.update_of_ne (hnot .ef).symm,Function.update_of_ne (hnot .vk).symm]
        exact hf.2.2.2 k hnot
    have hvklen : (F.R (rg .vk)).length+w = (S.R (rg .vk)).length := by
      rw [hF .vk,hS .vk]
      simp only [rsbUpd2,hΨ]
      simp only [Function.update_apply]
      simp only [reduceCtorEq,ite_false,ite_true,length_cstream]
      have hl : (Mult.BandList.bandPendB p cs rcs pend j).length =
          (Mult.BandList.bandPendB p cs rcs pend (j+1)).length+1 := by omega
      rw [hl,Nat.add_mul,Nat.one_mul]
    have hdlen : (F.R (rg .dout)).length = (S.R (rg .dout)).length+w := by
      rw [hF .dout,hS .dout]
      simp [rsbUpd2,hΨ,Mult.BandList.bandOutB,hyr,Nat.add_comm]
    have heflen : (F.R (rg .ef)).length ≤ (S.R (rg .ef)).length := by
      have hjm : j < (cs.map colC).length := by simp; omega
      rw [hF .ef,hS .ef]
      simp only [rsbUpd2,hΨ]
      simp only [Function.update_apply]
      simp only [reduceCtorEq,ite_false,ite_true,length_cstream]
      rw [List.drop_eq_getElem_cons hjm]
      simp only [List.flatten_cons,List.length_append,Nat.add_mul]
      omega
    have htblen : (F.R (rg .tb)).length ≤ (S.R (rg .tb)).length := by
      rw [hF .tb,hS .tb]
      simp only [rsbUpd2,hΨ,Function.update_apply]
      simp only [reduceCtorEq,ite_false,ite_true,length_cstream,List.length_drop,List.length_map]
      exact Nat.mul_le_mul_right w (by omega)
    have hh := mn_replace_four_size (rg .vk) (rg .ef) (rg .dout) (rg .tb)
      (hrg.ne (by decide)) (hrg.ne (by decide)) (hrg.ne (by decide))
      (hrg.ne (by decide)) (hrg.ne (by decide)) (hrg.ne (by decide)) v v' S
      (F.R (rg .vk)) (F.R (rg .ef)) (F.R (rg .dout)) (F.R (rg .tb))
    rw [←hstate] at hh
    omega
  have h := rsb_rep_runs_within hrg hdisj (ra := .sn) (rt := .tL) (by decide) (bandBwdStepP rg hι hT hQ)
    (σ .sn) Ψ _ _ hbody hstock
  refine (h.congr_pre ?_ |>.congr ?_).mono ?_ (le_refl _)
  · funext r; cases r <;> simp [hΨ, hvk, hef, hdout, htL, htb, Mult.BandList.bandPendB,
      Mult.BandList.bandOutB]
  · rw [hsn]
    have hd : (cs.map colC).drop s = [] := List.drop_of_length_le (by simp [hcs])
    have hdr : (rcs.map fun x => (⟨x, 0⟩ : GaussianInt)).drop s = [] :=
      List.drop_of_length_le (by simp [hrcs])
    funext r; cases r <;> simp [hΨ, htL, hd, hdr]
  · rw [hsn]


end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
