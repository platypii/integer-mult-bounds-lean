module

public import IntegerMultBounds.MathlibTM2.Fast.RingRecordLoopStock
public import IntegerMultBounds.MathlibTM2.Fast.RingPointwiseBankStock
public import IntegerMultBounds.MathlibTM2.StackExecutionUnique
public import IntegerMultBounds.MathlibTM2.StackStockComposition

/-! The complete compiled word-level product retains a linear operand/output
bank and one record scratch allowance. Setup/readiness share the correctness
proof; execution uniqueness reuses its established time and final-bank ledger. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Host.WordCmd IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.Schoenhage IntegerMultBounds.Schoenhage.Tp
  IntegerMultBounds.Spec.SignedRingProduct
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

/-- A scalar allowance for all work outside the repeated record loop. -/
def ringCoreWorkspace (p l w H X : ℕ) : ℕ :=
  3*(headerCost p (2^l) w H+1)+3*(constCost p l w+1)+
    3*(60*2^l+60*l+4*(p+l+w)+28*X+401)+
    3*(ringRecordCost (wOf p l w) (2^l) w (p+l) (wOf p l w*2^l)+1)+
    3*(24*(8*X+ringSharedBankStock p l w H)+30*X+81)

/-- Batch size enters workspace only through encoded operand volume. -/
theorem ringCoreWorkspace_affine (p l w H X : ℕ) :
    ringCoreWorkspace p l w H X = ringCoreWorkspace p l w H 0+750*X := by
  unfold ringCoreWorkspace
  ring

private theorem finish_tapes_stock_le (τ : Fin 𝕌 → WTape) :
    (finTapes.map (fun i => clen (τ i).words)).sum ≤ 12*wordBankStock τ := by
  have hcell (i : Fin 𝕌) : clen (τ i).words ≤ wordBankStock τ := by
    simp only [WTape.words,clen_append,clen_reverse]
    exact Finset.single_le_sum (fun j _ => Nat.zero_le (clen (τ j).left+clen (τ j).right))
      (Finset.mem_univ i)
  have hsum : ∀ xs : List (Fin 𝕌), (xs.map (fun i => clen (τ i).words)).sum ≤ xs.length*wordBankStock τ := by
    intro xs
    induction xs with
    | nil => simp
    | cons i xs ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      have hi := hcell i
      nlinarith only [hi,ih]
  simpa only [finTapes,List.length_cons,List.length_nil] using hsum finTapes

private theorem combined_workspace_le (base depth data C a b c d e x y z u v : ℕ)
    (ha : a ≤ C*x) (hb : b ≤ C*y) (hc : c ≤ C*z) (hd : d ≤ C*u) (he : e ≤ C*v) :
    base+depth+(a+(b+(c+(data+d+e)))) ≤ base+data+depth+(C+1)*(x+y+z+u+v) := by
  have hs := Nat.add_le_add ha (Nat.add_le_add hb (Nat.add_le_add hc (Nat.add_le_add hd he)))
  nlinarith only [hs]

/-- Same time and exact output as the existing correctness theorem, with one
record scratch budget. Every preparation and finish execution is derived. -/
theorem ringCore_exec_within (ι : Fin 𝕌 → Fin T) (hι : Function.Injective ι)
    {dec : Cmd 𝕌} {hdr : List Bool} {p l w : ℕ} {fs gs : List (Rec (2^l))}
    (hQ : cmdStates (pwCoreWith dec) ≤ Q) (hdec : HdrDecodes dec hdr p l w)
    (hw : p+2 ≤ w) (hlen : fs.length = gs.length)
    (hf : ∀ f ∈ fs, DiskGrid p f.1 f.2) (hg : ∀ g ∈ gs, DiskGrid p g.1 g.2)
    (v : HS T Q A U) (S : Stacks T A) :
    ∃ v' steps, v'.user = v.user ∧
      steps ≤ 3*(pwCost p 0 l 0 w hdr.length fs.length (array w fs).length+1) ∧
      ∀ C, mnProgPush (tcompile (P := P) (Q := Q) (A := A) (U := U) ι (pwCoreWith dec)) ≤ C → ∀ depth,
      ExecWithin body (fun d z => mnSize z+d ≤
        mnSize (mk v (place S ι (startBank hdr (array w fs) (array w gs))))+
        (array w fs).length+depth+(C+1)*ringCoreWorkspace p l w hdr.length (array w fs).length) depth
        (tcompile ι (pwCoreWith dec)) (mk v (place S ι (startBank hdr (array w fs) (array w gs)))) steps
        (mk v' (place S ι (Function.update (startBank hdr (array w fs) (array w gs))
          zO (reg (array w (List.zipWith (prodRec p) fs gs)))))) := by
  obtain ⟨τf,hτf,vf,n,huf,hnf,hef⟩ := tcompile_runs (body := body) hι
    (runs_pwCoreWith hdec hw hlen hf hg) hQ v S
  subst τf
  refine ⟨vf,n,huf,hnf,?_⟩
  intro C hpush depth
  change max (mnProgPush (tcompile ι dec)) (max (mnProgPush (tcompile ι constAll))
    (max (mnProgPush (tcompile ι pwPrep)) (max (mnProgPush (tcompile ι recLoop))
      (mnProgPush (tcompile ι pwFinish))))) ≤ C at hpush
  obtain ⟨hD,hpush⟩ := max_le_iff.mp hpush
  obtain ⟨hC,hpush⟩ := max_le_iff.mp hpush
  obtain ⟨hP,hpush⟩ := max_le_iff.mp hpush
  obtain ⟨hLoop,hF⟩ := max_le_iff.mp hpush
  have hRec : mnProgPush (tcompile (P := P) (Q := Q) (A := A) (U := U) ι recStep) ≤ C := by
    simpa only [recLoop,tcompile,mnProgPush,peekW,mnActPush,Nat.zero_max,Nat.max_zero] using hLoop
  have hQ' : max (cmdStates dec) (max (cmdStates constAll) (max (cmdStates pwPrep)
      (max (cmdStates recStep) (cmdStates pwFinish)))) ≤ Q := hQ
  obtain ⟨hQD,hQ'⟩ := max_le_iff.mp hQ'
  obtain ⟨hQC,hQ'⟩ := max_le_iff.mp hQ'
  obtain ⟨hQP,hQ'⟩ := max_le_iff.mp hQ'
  obtain ⟨hQR,hQF⟩ := max_le_iff.mp hQ'
  have hw1 : 1 ≤ w := by omega
  let F := array w fs
  let G := array w gs
  let τ₀ := startBank hdr F G
  let τ₁ := Function.update (Function.update (Function.update τ₀ iP (reg (ones p))) iL (reg (ones l))) iW (reg (ones w))
  let τ₂ := constBank p l w τ₁
  let τ₃ := pwPreparedBank p l w hdr F G
  obtain ⟨s1,s2,s3,hR⟩ := pwPreparation_spec hdec hw1 F G
  obtain ⟨σ₁,hσ₁,v₁,n₁,hu₁,hn₁,ht₁⟩ := tcompile_runs_within (body := body) hι s1 hQD v S depth
  subst σ₁
  obtain ⟨σ₂,hσ₂,v₂,n₂,hu₂,hn₂,ht₂⟩ := tcompile_runs_within (body := body) hι s2 hQC v₁ S depth
  subst σ₂
  have hFG : G.length = F.length := by simp only [F,G,length_array,hlen]
  have hprep : 60*2^l+60*l+4*(p+l+w)+10*(F.length+G.length)+400+
      2*(clen (cut w F)+clen (cut w G)) ≤ 60*2^l+60*l+4*(p+l+w)+28*F.length+400 := by
    have hF := clen_cut_le w hw1 _ F le_rfl
    have hG := clen_cut_le w hw1 _ G le_rfl
    omega
  have s3' := s3.mono (fun _ h => h) hprep
  obtain ⟨σ₃,hσ₃,v₃,n₃,hu₃,hn₃,ht₃⟩ := tcompile_runs_within (body := body) hι s3' hQP v₂ S depth
  subst σ₃
  let ps := List.zip (fs.map (lsbPairs w)) (gs.map (lsbPairs w))
  have hpf : ps.map Prod.fst = fs.map (lsbPairs w) := by rw [List.map_fst_zip]; simp [hlen]
  have hpg : ps.map Prod.snd = gs.map (lsbPairs w) := by rw [List.map_snd_zip]; simp [hlen]
  have hq : ∀ q ∈ ps, q.1.length = 2^l ∧ q.2.length = 2^l ∧
      (∀ x ∈ q.1, x.1.length = w ∧ x.2.length = w) ∧ (∀ x ∈ q.2, x.1.length = w ∧ x.2.length = w) := by
    intro q hq
    have hm := List.of_mem_zip hq
    obtain ⟨f,_,hf1⟩ := List.mem_map.mp hm.1
    obtain ⟨g,_,hg1⟩ := List.mem_map.mp hm.2
    rw [←hf1,←hg1]
    exact ⟨by simp [lsbPairs],by simp [lsbPairs],lsbPairs_widths w f,lsbPairs_widths w g⟩
  have hp₃ : τ₃ iP = ⟨[],opWords (ps.map Prod.fst)⟩ := by
    rw [hpf,←cut_array hw1]
    rfl
  have hl₃ : τ₃ iL = ⟨[],opWords (ps.map Prod.snd)⟩ := by
    rw [hpg,←cut_array hw1]
    rfl
  have hz₃ : τ₃ zO = ⟨[[]],[]⟩ := rfl
  have hw₃ : τ₃ iW = reg (ones (2*2^l)) := rfl
  obtain ⟨v₄,n₄,hu₄,hn₄,ht₄⟩ := ringRecordLoop_exec_within (body := body) ι hι hQR
    Nat.one_le_two_pow ps τ₃ [] [] [] hq hR hw₃ hp₃ hl₃ hz₃ v₃ S depth
  let output := ps.flatMap (fun q =>
    ((ringWords (wOf p l w) (2^l) w (p+l) (wOf p l w*2^l) q.1 q.2).map List.reverse).flatten)
  let τ₄ := Function.update (Function.update (Function.update τ₃
    iP ⟨(opWords (ps.map Prod.fst)).reverse++[],[]⟩)
    iL ⟨(opWords (ps.map Prod.snd)).reverse++[],[]⟩) zO ⟨[[]++output],[]⟩
  have hps : ps.length = fs.length := by simp [ps,hlen]
  have hvolume : 2*ps.length*2^l*w = F.length := by simp only [F,length_array,hps]; ring
  have hout : output.length ≤ F.length := by
    have h := ringRecordOutput_length_le (wOf p l w) (2^l) w (p+l) (wOf p l w*2^l) ps
    change output.length ≤ ps.length*(2*2^l*w) at h
    nlinarith only [h,hvolume]
  have hbank : wordBankStock τ₄ = wordBankStock τ₃+output.length := by
    have h := ringRecord_boundary_stock τ₃ (opWords (ps.map Prod.fst)) [] []
      (opWords (ps.map Prod.snd)) [] [] [] output
      (by simpa only [List.append_nil] using hp₃) (by simpa only [List.append_nil] using hl₃) hz₃
    simpa only [τ₄,List.nil_append] using h
  have hprepared : wordBankStock τ₃ ≤ 8*F.length+ringSharedBankStock p l w hdr.length := by
    have h := pwPreparedBank_stock_le p l w hw1 hdr F G
    rw [hFG] at h
    convert h using 1
    ring
  have s5 := runs_pwFinish τ₄ (out := output) (F := F) (G := G) (by simp [τ₄])
    (by rfl)
    (by rfl)
  have hfinish : 2*(finTapes.map (fun i => clen (τ₄ i).words)).sum+
      2*(output.length+F.length+G.length)+80 ≤ 24*(8*F.length+ringSharedBankStock p l w hdr.length)+30*F.length+80 := by
    have h := finish_tapes_stock_le τ₄
    omega
  have s5' := s5.mono (fun _ h => h) hfinish
  obtain ⟨σ₅,hσ₅,v₅,n₅,hu₅,hn₅,ht₅⟩ := tcompile_runs_within (body := body) hι s5' hQF v₄ S depth
  have ht₄' : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v₃ (place S ι τ₃))+depth+
      (F.length+mnProgPush (tcompile (P := P) (Q := Q) (A := A) (U := U) ι recStep)*
        (3*(ringRecordCost (wOf p l w) (2^l) w (p+l) (wOf p l w*2^l)+1)))) depth
      (tcompile ι recLoop) (mk v₃ (place S ι τ₃)) n₄ (mk v₄ (place S ι τ₄)) := by
    apply ht₄.mono
    intro d z hz
    rw [hvolume] at hz
    omega
  have ht := mn_seq_within_add ht₁ (mn_seq_within_add ht₂ (mn_seq_within_add ht₃ (mn_seq_within_add ht₄' ht₅)))
  have ht' : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v (place S ι τ₀))+F.length+depth+
      (C+1)*ringCoreWorkspace p l w hdr.length F.length) depth
      (tcompile ι (pwCoreWith dec)) (mk v (place S ι τ₀)) (n₁+(n₂+(n₃+(n₄+n₅))))
      (mk v₅ (place S ι σ₅)) := by
    apply ht.mono
    intro d z hz
    have hd := Nat.mul_le_mul_right (3*(headerCost p (2^l) w hdr.length+1)) hD
    have hc := Nat.mul_le_mul_right (3*(constCost p l w+1)) hC
    have hp := Nat.mul_le_mul_right (3*(60*2^l+60*l+4*(p+l+w)+28*F.length+401)) hP
    have hr := Nat.mul_le_mul_right (3*(ringRecordCost (wOf p l w) (2^l) w (p+l) (wOf p l w*2^l)+1)) hRec
    have hf := Nat.mul_le_mul_right (3*(24*(8*F.length+ringSharedBankStock p l w hdr.length)+30*F.length+81)) hF
    have hb := combined_workspace_le (mnSize (mk v (place S ι τ₀))) depth F.length C
      _ _ _ _ _ _ _ _ _ _ hd hc hp hr hf
    have hb' := hz.trans hb
    dsimp only [τ₀] at hb' ⊢
    unfold ringCoreWorkspace
    exact hb'
  obtain ⟨heqn,heqF⟩ := ht'.toExec.unique hef
  rw [heqn,heqF] at ht'
  exact ht'

end IntegerMultBounds.MathlibTM2.Fast
