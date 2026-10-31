module

public import IntegerMultBounds.MathlibTM2.Fast.RingFormatStock
public import IntegerMultBounds.MathlibTM2.Fast.RingHostStock
public import IntegerMultBounds.MathlibTM2.Fast.RingProdTrace

/-! The full ring-product primitive, including coefficient encoding/decoding,
has shared workspace plus linear encoded-data stock. Repeated arithmetic time
is never used as a batch workspace allowance. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.Spec.SignedRingProduct
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}
  {rg : RpReg → Fin T} {ι : Fin 91 → Fin T}

private theorem rp_placed_runs_within (h : RpLayout rg ι) (hQ : rpStates ≤ Q)
    (C : ℕ) (hpush : mnProgPush (rpHost (P := P) (Q := Q) (A := A) (U := U) ι) ≤ C)
    {p l w : ℕ} {fs gs : List (Rec (2^l))} (hp : 1 ≤ p) (hw : p+2 ≤ w)
    (hlen : fs.length = gs.length) (hf : ∀ f ∈ fs, DiskGrid p f.1 f.2)
    (hg : ∀ g ∈ gs, DiskGrid p g.1 g.2) {ρ : RpReg → List (Fin (A+4))}
    (h0 : ρ .d0 = (header p (2^l) w).map bitSymbol)
    (h1 : ρ .d1 = (array w fs).map bitSymbol) (h2 : ρ .d2 = (array w gs).map bitSymbol)
    (h3 : ρ .d3 = []) :
    RpRunsWithin body rg ι (rpHost ι) ρ
      (Function.update ρ .d3 ((array w (List.zipWith (prodRec p) fs gs)).map bitSymbol))
      (3*rpTime p l w fs.length) ((C+1)*rpHostWorkspace p l w fs.length) := by
  intro v S hc hS
  obtain ⟨v',S',n,hu,hn,he,hS',hfr⟩ := rp_placed_runs (body := body) h hQ hp hw hlen hf hg
    h0 h1 h2 h3 v S hc hS
  obtain ⟨vf,m,_,_,ht⟩ := rpHost_exec_within (body := body) h.ι_inj hQ hp hw hlen hf hg v S hc.1
    (by rw [←h.d0,hS,h0]) (by rw [←h.d1,hS,h1]) (by rw [←h.d2,hS,h2])
    (by rw [←h.d3,hS,h3]) hc.2
  refine ⟨v',S',n,hu,hn,hS',hfr,?_⟩
  intro depth
  have ht' := ht C hpush depth
  obtain ⟨heqn,heqF⟩ := ht'.toExec.unique he
  rw [heqn,heqF] at ht'
  exact ht'

def rpWorkspace (p l w M : ℕ) : ℕ :=
  rpHostWorkspace p l w M+300*(M*2^l*w)+100

/-- The complete primitive retains one shared workspace plus linear batch data. -/
theorem rpWorkspace_affine (p l w M : ℕ) :
    rpWorkspace p l w M = rpWorkspace p l w 0+1842*(M*2^l*w) := by
  unfold rpWorkspace
  rw [rpHostWorkspace_affine p l w M]
  simp only [Nat.zero_mul]
  ring

private theorem format_allowance_le (K w : ℕ) (hw : 3 ≤ w) :
    3*(K*(15*w+12)+6)+3*(K*(15*w+12)+6)+3*(K*(17*w+20)+4) ≤ 300*(K*w)+100 := by
  have hs := Nat.mul_le_mul_left K hw
  nlinarith only [hs]

private theorem primitive_allowance_le (C W K w : ℕ) (hw : 3 ≤ w) :
    3*(K*(15*w+12)+6)+(3*(K*(15*w+12)+6)+((C+1)*W+
      (0+(0+3*(K*(17*w+20)+4))))) ≤ (C+1)*(W+300*(K*w)+100) := by
  have hf := format_allowance_le K w hw
  have hs : 300*(K*w)+100 ≤ (C+1)*(300*(K*w)+100) := Nat.le_mul_of_pos_left _ (by omega)
  nlinarith only [hf,hs]

/-- Full ring primitive on the ordinary pair-symbol streams, with its original
runtime and exact restored frame, and a bound on every intermediate store. -/
theorem rpProg_exec_within (h : RpLayout rg ι) (hT : 91 ≤ T) (hQ : rpStates ≤ Q) (hA : 4 ≤ A)
    {p l w M : ℕ} (hp : 1 ≤ p) (hw : p+2 ≤ w) (X Y : ℕ → Fin (2^l) → GaussianInt)
    (hX : ∀ n < M, DiskGrid p (rpRec X n).1 (rpRec X n).2)
    (hY : ∀ n < M, DiskGrid p (rpRec Y n).1 (rpRec Y n).2)
    (v : HS T Q A U) (S : Stacks T A) (hc : RpClean ι S)
    (hxs : S.R (rg .xs) = cstream A w (rpStream M X))
    (hys : S.R (rg .ys) = cstream A w (rpStream M Y)) (hwn : (S.R (rg .wn)).length = w)
    (hsv : S.R (rg .sv) = []) (hta : S.R (rg .ta) = []) (htb : S.R (rg .tb) = [])
    (hacc : S.R (rg .acc) = []) (htmp : S.R (rg .tmp) = [])
    (hd0 : S.R (rg .d0) = (header p (2^l) w).map bitSymbol) (hd1 : S.R (rg .d1) = [])
    (hd2 : S.R (rg .d2) = []) (hd3 : S.R (rg .d3) = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ rpCost p l w M ∧
      ∀ C, mnProgPush (rpProg (P := P) (Q := Q) (A := A) (U := U) rg ι h.ι_inj hT hQ) ≤ C → ∀ depth,
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(C+1)*rpWorkspace p l w M)
        depth (rpProg rg ι h.ι_inj hT hQ) (mk v S) n
        (mk v' {S with R := (Function.update S.R (rg .out)
          (cstream A w (rpStream M (rpOut p X Y))++S.R (rg .out)))}) := by
  obtain ⟨vf,n,huf,hnf,hef⟩ := rpProg_exec (body := body) h hT hQ hA hp hw X Y hX hY v S hc
    hxs hys hwn hsv hta htb hacc htmp hd0 hd1 hd2 hd3
  refine ⟨vf,n,huf,hnf,?_⟩
  intro C hpush depth
  have hhost : mnProgPush (rpHost (P := P) (Q := Q) (A := A) (U := U) ι) ≤ C := by
    change max (mnProgPush (rpEnc rg .xs .d1)) (max (mnProgPush (rpEnc rg .ys .d2))
      (max (mnProgPush (rpHost ι)) (max (mnProgPush (uclear (rg .d1)))
        (max (mnProgPush (uclear (rg .d2))) (mnProgPush (rpDec rg)))))) ≤ C at hpush
    exact (max_le_iff.mp (max_le_iff.mp (max_le_iff.mp hpush).2).2).1
  let ρ := fun r => S.R (rg r)
  let fs := (List.range M).map (rpRec X)
  let gs := (List.range M).map (rpRec Y)
  have hw1 : 1 ≤ w := by omega
  have hfl : fs.length = M := by simp [fs]
  have hF : array w fs = (rpStream M X).flatMap (rpChunk w) := by
    rw [rp_array_eq_chunks,rpCoeffs_rpRec]
  have hG : array w gs = (rpStream M Y).flatMap (rpChunk w) := by
    rw [rp_array_eq_chunks,rpCoeffs_rpRec]
  have hO : array w (List.zipWith (prodRec p) fs gs) = (rpStream M (rpOut p X Y)).flatMap (rpChunk w) := by
    rw [show fs = (List.range M).map (rpRec X) from rfl,show gs = (List.range M).map (rpRec Y) from rfl,
      rp_zipWith_rpRec,rp_array_eq_chunks,rpCoeffs_rpRec]
  have hdf : ∀ f ∈ fs, DiskGrid p f.1 f.2 := by
    intro f hf
    obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hf
    exact hX n (List.mem_range.mp hn)
  have hdg : ∀ g ∈ gs, DiskGrid p g.1 g.2 := by
    intro g hg
    obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hg
    exact hY n (List.mem_range.mp hn)
  have s1 := (rp_enc_runs (body := body) h hA (src := .xs) (dst := .d1) (Or.inl ⟨rfl,rfl⟩) hw1
    (rpStream M X) (ρ := ρ) hxs hwn hsv hta htb hacc htmp).within_native (rpEnc_native rg .xs .d1)
  let ρ₁ := Function.update ρ .d1 (((rpStream M X).flatMap (rpChunk w)).map bitSymbol++ρ .d1)
  have s2 := (rp_enc_runs (body := body) h hA (src := .ys) (dst := .d2) (Or.inr ⟨rfl,rfl⟩) hw1
    (rpStream M Y) (ρ := ρ₁) (by simp [ρ₁,ρ,hys]) (by simp [ρ₁,ρ,hwn]) (by simp [ρ₁,ρ,hsv])
    (by simp [ρ₁,ρ,hta]) (by simp [ρ₁,ρ,htb]) (by simp [ρ₁,ρ,hacc]) (by simp [ρ₁,ρ,htmp])).within_native
      (rpEnc_native rg .ys .d2)
  let ρ₂ := Function.update ρ₁ .d2 (((rpStream M Y).flatMap (rpChunk w)).map bitSymbol++ρ₁ .d2)
  have s3 := rp_placed_runs_within (body := body) h hQ C hhost (fs := fs) (gs := gs) hp hw
    (by simp [fs,gs]) hdf hdg (ρ := ρ₂) (by simp [ρ₂,ρ₁,ρ,hd0]) (by simp [ρ₂,ρ₁,ρ,hd1,hF])
    (by simp [ρ₂,ρ₁,ρ,hd2,hG]) (by simp [ρ₂,ρ₁,ρ,hd3])
  let ρ₃ := Function.update ρ₂ .d3 ((array w (List.zipWith (prodRec p) fs gs)).map bitSymbol)
  have s4 := (rp_uclear_runs (body := body) h .d1 (ρ := ρ₃) (n := 2*2^l*w*M)
    (by simp [ρ₃,ρ₂,ρ₁,ρ,hd1]; ring)).within_native (c := 0)
      (by simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush])
  have s5 := (rp_uclear_runs (body := body) h .d2 (ρ := Function.update ρ₃ .d1 [])
    (n := 2*2^l*w*M) (by simp [ρ₃,ρ₂,ρ₁,ρ,hd2]; ring)).within_native (c := 0)
      (by simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush])
  have s6 := (rp_dec_runs (body := body) h hw1 (rpStream M (rpOut p X Y))
    (ρ := Function.update (Function.update ρ₃ .d1 []) .d2 [])
    (by simp [ρ₃,hO]) (by simp [ρ₃,ρ₂,ρ₁,ρ,hwn]) (by simp [ρ₃,ρ₂,ρ₁,ρ,hta])
    (by simp [ρ₃,ρ₂,ρ₁,ρ,htb]) (by simp [ρ₃,ρ₂,ρ₁,ρ,hacc]) (by simp [ρ₃,ρ₂,ρ₁,ρ,htmp])).within_native
      (rpDec_native rg)
  obtain ⟨vr,R,m,_,_,_,_,ht⟩ := (s1.seq h (s2.seq h (s3.seq h (s4.seq h (s5.seq h s6))))) v S hc (fun _ => rfl)
  have ht' : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(C+1)*rpWorkspace p l w M)
      depth (rpProg rg ι h.ι_inj hT hQ) (mk v S) m (mk vr R) := by
    apply (ht depth).mono
    intro d z hz
    simp only [length_rpStream,hfl,Nat.zero_mul,Nat.zero_add] at hz
    have hb := primitive_allowance_le C (rpHostWorkspace p l w M) (M*2^l) w (by omega)
    simp only [Nat.zero_add] at hb
    have hh := hz.trans (Nat.add_le_add_left hb (mnSize (mk v S)+depth))
    simpa only [rpWorkspace,Nat.mul_assoc] using hh
  obtain ⟨heqn,heqF⟩ := ht'.toExec.unique hef
  rw [heqn,heqF] at ht'
  exact ht'

end IntegerMultBounds.MathlibTM2.Fast
