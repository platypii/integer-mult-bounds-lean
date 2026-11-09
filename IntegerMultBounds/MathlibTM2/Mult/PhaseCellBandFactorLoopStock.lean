module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBandFactorStepStock
public import IntegerMultBounds.MathlibTM2.Fast.ResampBScanGrowthStock

/-! The factor axis retains its factor archives and shares one window reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {Proc U : Type} {body : Proc → Pr Proc T Q A U}
  {rg : RsbR → Fin T} {ι : Fin 64 → Fin T}

theorem band_facLoop_runs_within (hrg : Function.Injective rg) (hdisj : ∀ r j, rg r ≠ ι j)
    (hι : Function.Injective ι) (hT : 64 ≤ T) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {w P B K s : ℕ} (σ : RsbR → List (Fin (A + 4))) (hready : RsbReady σ w P) (hw : 1 ≤ w)
    (hp : P ≤ w) (rows inputs : List (List ℤ)) (hrows : rows.length = B + 1)
    (hrl : ∀ row ∈ rows, row.length = 2 * B + 1) (hin : ∀ row ∈ inputs, row.length = 2 * B + 1)
    (hs : inputs.length = s) (hfit : ∀ m < s, FacFits w P K (facState P K rows inputs m))
    (hr0 : ∀ m < s, σ .bx = csyms A w ⟨Mult.BandFactor.newtonZ P (facPiv (facState P K rows inputs m)) 0, 0⟩)
    (SRC HF DF D : List (Fin (A + 4)))
    (hvk : σ .vk = cstream A w (rows.map colC).flatten)
    (hsrc : σ .src = cstream A w (inputs.map colC).flatten ++ SRC)
    (hhf : σ .hf = HF) (hdf : σ .df = DF) (hdout : σ .dout = D) (hmsk : σ .msk = csyms A w 0)
    (hef : σ .ef = []) (htb : σ .tb = []) (hsr : σ .sr = []) (hbo : σ .bo = [])
    (hhv : σ .hv = []) (hxa : σ .xa = []) (hhc : σ .hc = []) (hya : σ .ya = []) (hxs : σ .xs = [])
    (hpr : σ .pr = []) (hac : σ .ac = []) (hac2 : σ .ac2 = []) (hnv : σ .nv = [])
    (hb1 : σ .b1 = []) (htC : σ .tC = []) (htA : σ .tA = []) (htJ : σ .tJ = [])
    (htK : σ .tK = []) (htL : σ .tL = []) (hsel : σ .sel = []) (hsn : (σ .sn).length = s)
    (hkn : (σ .kn).length = K) (hms : (σ .ms).length = B) (hm2n : (σ .m2n).length = 2 * B)
    (hmwn : (σ .mwn).length = 2 * B * w) (hsmwn : (σ .smwn).length = (2 * B + 1) * w)
    (J L : ℕ)
    (hpushJ : mnProgPush (rmulOne (P := Proc) (Q := Q) (A := A) (U := U)
      ι hι hT hQ (rsbCr rg .hv .xa .hc)) ≤ J)
    (hpushL : mnProgPush (rmulOne (P := Proc) (Q := Q) (A := A) (U := U)
      ι hι hT hQ (rsbCr rg .ya .xs .pr)) ≤ L) :
    RsbRunsWithin (body := body) (rg := rg) (ι := ι) (bandFacLoopP rg hι hT hQ) σ
      (Function.update (Function.update (Function.update (Function.update (Function.update σ .vk
        (cstream A w ((facState P K rows inputs s).map colC).flatten)) .src SRC)
        .hf (cstream A w ((List.range s).reverse.map fun j =>
          colC ((facState P K rows inputs j).headD [])).flatten ++ HF))
        .df (cstream A w ((List.range s).reverse.map fun j =>
          (⟨Mult.BandFactor.newtonZ P (facPiv (facState P K rows inputs j)) K, 0⟩ : GaussianInt)) ++ DF))
        .dout (cstream A w (((List.range s).map fun j =>
          colC (Mult.BandFactor.lcolZ P K (facState P K rows inputs j))).flatten.reverse) ++ D))
      (s * (bandFacStepCost w B K + 6) + 4)
      (s*((B+1)*w)+(1000*(B+1)*(B+1)*(w+1) +
       bandNewtonStepPush (P := Proc) (A := A) (U := U) rg hι hT hQ*bandNewtonStepCost w +
       ((realWeightWorkspace J w 1+1000*(w+1))+
        (realWeightWorkspace L w (2*B)+1000*(2*B+1)*(w+1))))) := by
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → RsbR → List (Fin (A + 4)), Ψ = fun m =>
      Function.update (Function.update (Function.update (Function.update (Function.update σ .vk
        (cstream A w ((facState P K rows inputs m).map colC).flatten))
        .src (cstream A w ((inputs.drop m).map colC).flatten ++ SRC))
        .hf (cstream A w ((List.range m).reverse.map fun j =>
          colC ((facState P K rows inputs j).headD [])).flatten ++ HF))
        .df (cstream A w ((List.range m).reverse.map fun j =>
          (⟨Mult.BandFactor.newtonZ P (facPiv (facState P K rows inputs j)) K, 0⟩ : GaussianInt)) ++ DF))
        .dout (cstream A w (((List.range m).map fun j =>
          colC (Mult.BandFactor.lcolZ P K (facState P K rows inputs j))).flatten.reverse) ++ D) := ⟨_, rfl⟩
  have hbody : ∀ j < (σ .sn).length, ∀ X Y, RsbRunsWithin (body := body) (rg := rg) (ι := ι) (bandFacStepP rg hι hT hQ)
      (rsbUpd2 (Ψ j) .sn X .sel Y) (rsbUpd2 (Ψ (j + 1)) .sn X .sel Y) (bandFacStepCost w B K) (1000*(B+1)*(B+1)*(w+1) +
       bandNewtonStepPush (P := Proc) (A := A) (U := U) rg hι hT hQ*bandNewtonStepCost w +
       ((realWeightWorkspace J w 1+1000*(w+1))+
        (realWeightWorkspace L w (2*B)+1000*(2*B+1)*(w+1)))) := by
    intro j hj X Y
    rw [hsn] at hj
    obtain ⟨hlen, hrlen⟩ := facState_shape P K B rows inputs hrows hrl hin j (by omega)
    obtain ⟨row0, rest, hr⟩ : ∃ row0 rest, facState P K rows inputs j=row0 :: rest := by
      cases h : facState P K rows inputs j with
      | nil => rw [h] at hlen; simp at hlen
      | cons a l => exact ⟨a, l, rfl⟩
    have hr0l := hrlen row0 (by rw [hr]; simp)
    obtain ⟨c, tail0, hc⟩ : ∃ c tail0, row0=c :: tail0 := by
      cases row0 with
      | nil => simp at hr0l
      | cons a l => exact ⟨a, l, rfl⟩
    subst hc
    have hfj := hfit j hj
    rw [hr] at hfj
    obtain ⟨hfc, hfn, hfr, hft, hfh⟩ := hfj
    have htl : tail0.length=2*B := by simp at hr0l; omega
    have hrest : rest.length=B := by rw [hr] at hlen; simp at hlen; omega
    have hjin : j < inputs.length := by omega
    set next := inputs[j]'hjin with hnextdef
    have hnl : next.length=2*B+1 := hin next (List.getElem_mem _)
    have hready' : RsbReady (rsbUpd2 (Ψ j) .sn X .sel Y) w P := by
      simp only [rsbUpd2, hΨ]
      exact ((((((hready.update .vk (fun c => by simp) _).update .src (fun c => by simp) _).update
        .hf (fun c => by simp) _).update .df (fun c => by simp) _).update .dout (fun c => by simp)
        _).update .sn (fun c => by simp) _).update .sel (fun c => by simp) _
    have hpiv : facPiv (facState P K rows inputs j)=c := by simp [facPiv, hr]
    have hstep := band_facStep_runs_within (body := body) (ι := ι) (w := w) (B := B) (K := K) hrg hdisj hι
      hT hQ hA (rsbUpd2 (Ψ j) .sn X .sel Y) hready' hw hp c tail0 next rest htl hnl hrest
      (fun row hrow => hrlen row (by rw [hr]; exact List.mem_cons_of_mem _ hrow))
      hfc hfn hfr hft hfh (cstream A w ((inputs.drop (j+1)).map colC).flatten ++ SRC)
      (cstream A w ((List.range j).reverse.map fun j =>
          colC ((facState P K rows inputs j).headD [])).flatten ++ HF)
      (cstream A w ((List.range j).reverse.map fun j =>
          (⟨Mult.BandFactor.newtonZ P (facPiv (facState P K rows inputs j)) K, 0⟩ : GaussianInt)) ++ DF)
      (cstream A w (((List.range j).map fun j =>
          colC (Mult.BandFactor.lcolZ P K (facState P K rows inputs j))).flatten.reverse) ++ D)
      (by simp [rsbUpd2, hΨ, hr, colC])
      (by
        have hdj : (inputs.map colC).drop j=colC next :: (inputs.map colC).drop (j+1) := by
          rw [List.drop_eq_getElem_cons (by simpa using hjin), List.getElem_map]
        simp [rsbUpd2, hΨ, hdj])
      (by simp [rsbUpd2, hΨ]) (by simp [rsbUpd2, hΨ]) (by simp [rsbUpd2, hΨ])
      (by have := hr0 j hj; rw [hpiv] at this; simp [rsbUpd2, hΨ, this]) (by simp [rsbUpd2, hΨ, hmsk])
      (by simp [rsbUpd2, hΨ, hef]) (by simp [rsbUpd2, hΨ, htb]) (by simp [rsbUpd2, hΨ, hsr])
      (by simp [rsbUpd2, hΨ, hbo]) (by simp [rsbUpd2, hΨ, hhv]) (by simp [rsbUpd2, hΨ, hxa])
      (by simp [rsbUpd2, hΨ, hhc]) (by simp [rsbUpd2, hΨ, hya]) (by simp [rsbUpd2, hΨ, hxs])
      (by simp [rsbUpd2, hΨ, hpr]) (by simp [rsbUpd2, hΨ, hac]) (by simp [rsbUpd2, hΨ, hac2])
      (by simp [rsbUpd2, hΨ, hnv]) (by simp [rsbUpd2, hΨ, hb1]) (by simp [rsbUpd2, hΨ, htC])
      (by simp [rsbUpd2, hΨ, htA]) (by simp [rsbUpd2, hΨ, htJ]) (by simp [rsbUpd2, hΨ, htK])
      (by simp [rsbUpd2, hΨ, htL]) (by simp [rsbUpd2, hΨ, hkn]) (by simp [rsbUpd2, hΨ, hms])
      (by simp [rsbUpd2, hΨ, hm2n]) (by simp [rsbUpd2, hΨ, hmwn]) (by simp [rsbUpd2, hΨ, hsmwn]) J L hpushJ hpushL
    refine hstep.congr ?_
    have hnext' : inputs.getD j []=next := by rw [List.getD_eq_getElem _ _ hjin]
    have hst : facState P K rows inputs (j+1)=
        rest.map (fun row => facRow P (Mult.BandFactor.newtonZ P c K) tail0 row)++[next] := by
      simp only [facState, hr, hnext', stepRowsZ_cons]
    have hlc : Mult.BandFactor.lcolZ P K (facState P K rows inputs j)=
        rest.map (fun row => facMul P (Mult.BandFactor.newtonZ P c K) row) := by
      rw [hr, lcolZ_cons]
    funext x; cases x <;> simp [rsbUpd2, hΨ, hst, List.range_succ, hr, colC,
      List.reverse_append, facPiv, lcolZ_cons, Function.comp_def]
  have hstream (xs : List (List ℤ)) (n : ℕ)
      (hx : ∀ row ∈ xs, row.length = n) :
      (cstream A w (xs.map colC).flatten).length = xs.length*n*w := by
    simp only [length_cstream, List.length_flatten, List.map_map]
    have he : xs.map (List.length ∘ colC) = xs.map (fun _ => n) := by
      apply List.map_congr_left
      intro row hr
      simp [colC, hx row hr]
    rw [he]
    simp [List.map_const', List.sum_replicate, smul_eq_mul]
  have hshape (m : ℕ) (hm : m ≤ s) :=
    facState_shape P K B rows inputs hrows hrl hin m (by omega)
  have hwlen (m : ℕ) (hm : m ≤ s) :
      (cstream A w ((facState P K rows inputs m).map colC).flatten).length =
        (B+1)*(2*B+1)*w := by
    rw [hstream _ _ (hshape m hm).2, (hshape m hm).1]
  have hhead (m : ℕ) (hm : m < s) :
      ((facState P K rows inputs m).headD []).length = 2*B+1 := by
    have hh := hshape m (by omega)
    cases he : facState P K rows inputs m with
    | nil => simp [he] at hh
    | cons row rest => exact hh.2 row (by simp [he])
  have hlcol (m : ℕ) (hm : m < s) :
      (Mult.BandFactor.lcolZ P K (facState P K rows inputs m)).length = B := by
    have hh := hshape m (by omega)
    cases he : facState P K rows inputs m with
    | nil => simp [he] at hh
    | cons row rest =>
      have hr : rest.length = B := by simpa [he] using hh.1
      simp [Mult.BandFactor.lcolZ, hr]
  have hhlen (m : ℕ) (hm : m ≤ s) :
      (cstream A w ((List.range m).reverse.map fun j =>
        colC ((facState P K rows inputs j).headD [])).flatten).length = m*(2*B+1)*w := by
    have he : ((List.range m).reverse.map fun j =>
        colC ((facState P K rows inputs j).headD [])) =
        (((List.range m).reverse.map fun j => (facState P K rows inputs j).headD []).map colC) := by simp
    rw [he, hstream _ (2*B+1) (by
      intro row hr
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hr
      exact hhead j (by simpa using (lt_of_lt_of_le (List.mem_range.mp (List.mem_reverse.mp hj)) hm)))]
    simp
  have hdlen (m : ℕ) (hm : m ≤ s) :
      (cstream A w (((List.range m).map fun j =>
        colC (Mult.BandFactor.lcolZ P K (facState P K rows inputs j))).flatten.reverse)).length = m*B*w := by
    rw [length_cstream, List.length_reverse]
    have he : ((List.range m).map fun j =>
        colC (Mult.BandFactor.lcolZ P K (facState P K rows inputs j))) =
        (((List.range m).map fun j => Mult.BandFactor.lcolZ P K (facState P K rows inputs j)).map colC) := by simp
    rw [he]
    have hh := hstream ((List.range m).map fun j =>
      Mult.BandFactor.lcolZ P K (facState P K rows inputs j)) B (by
        intro row hr
        obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hr
        exact hlcol j (lt_of_lt_of_le (List.mem_range.mp hj) hm))
    simpa only [length_cstream, List.length_map, List.length_range] using hh
  let roles : Fin 5 → RsbR := ![.vk,.src,.hf,.df,.dout]
  have hroles : Function.Injective roles := by decide
  have hstock : ∀ j < (σ .sn).length, ∀ X Y (v v' : HS T Q A U) S F,
      RsbHolds rg S (rsbUpd2 (Ψ j) .sn X .sel Y) →
      RsbHolds rg F (rsbUpd2 (Ψ (j+1)) .sn X .sel Y) → RsbFr rg S F →
      mnSize (mk v' F) ≤ mnSize (mk v S)+(B+1)*w := by
    intro j hj X Y v v' S F hS hF hf
    have hjs : j < s := by simpa only [hsn] using hj
    apply RsbHolds.size_le_of_bank_growth hrg roles hroles hS hF hf _ _ v v'
    · intro x hx
      have h0 : x ≠ .vk := (hx 0).symm
      have h1 : x ≠ .src := (hx 1).symm
      have h2 : x ≠ .hf := (hx 2).symm
      have h3 : x ≠ .df := (hx 3).symm
      have h4 : x ≠ .dout := (hx 4).symm
      simp [rsbUpd2,hΨ,Function.update_apply,h0,h1,h2,h3,h4]
    · have hinlen (m : ℕ) :
          (cstream A w ((inputs.drop m).map colC).flatten).length = (s-m)*(2*B+1)*w := by
        rw [hstream _ _ (fun row hr => hin row (List.mem_of_mem_drop hr))]
        simp [hs]
      simp only [roles, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
        rsbUpd2, hΨ, Function.update_apply, reduceCtorEq, ↓reduceIte,
        List.length_append, Nat.add_zero]
      rw [hwlen j (by omega), hwlen (j+1) (by omega), hinlen j, hinlen (j+1),
        hhlen j (by omega), hhlen (j+1) (by omega), hdlen j (by omega), hdlen (j+1) (by omega)]
      simp only [length_cstream, List.length_map, List.length_reverse, List.length_range]
      rw [show s-j = s-(j+1)+1 by omega]
      nlinarith only []
  have h := rsb_rep_runs_within_growth hrg hdisj (ra := .sn) (rt := .sel) (by decide)
    (bandFacStepP rg hι hT hQ) (σ .sn) Ψ _ (1000*(B+1)*(B+1)*(w+1) +
       bandNewtonStepPush (P := Proc) (A := A) (U := U) rg hι hT hQ*bandNewtonStepCost w +
       ((realWeightWorkspace J w 1+1000*(w+1))+
        (realWeightWorkspace L w (2*B)+1000*(2*B+1)*(w+1)))) ((B+1)*w) hbody hstock
  refine (h.congr_pre ?_ |>.congr ?_).mono ?_ (by rw [hsn])
  · funext x; cases x <;> simp [rsbUpd2, hΨ, hvk, hsrc, hhf, hdf, hdout, hsel, facState]
  · rw [hsn]
    have hd : (inputs.map colC).drop s=[] := List.drop_of_length_le (by simp; omega)
    funext x; cases x <;> simp [rsbUpd2, hΨ, hsel, hd]
  · rw [hsn]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
