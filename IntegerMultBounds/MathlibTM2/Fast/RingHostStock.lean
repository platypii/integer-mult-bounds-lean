module

public import IntegerMultBounds.MathlibTM2.Fast.RingProdBase
public import IntegerMultBounds.MathlibTM2.Fast.RingPointwiseStock

/-! Seal, run the certified pointwise core and unseal, charging all format work
as linear traffic. The original host time and exact frame are reused. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Host.WordCmd IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.Schoenhage IntegerMultBounds.Schoenhage.Tp
  IntegerMultBounds.Spec.SignedRingProduct
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

private theorem rpSeal_native (r : Fin T) :
    mnNativePushBound 1 (rpSeal (P := P) (Q := Q) (A := A) (U := U) r) := by
  simp [rpSeal,moveRL,moveLR,peekRp,rlStep,mv1,actThen,WordCmd.peekL,lrStep,pushL,
    mnNativePushBound,mnActPush]

private theorem rpUnseal_native (r : Fin T) :
    mnNativePushBound 1 (rpUnseal (P := P) (Q := Q) (A := A) (U := U) r) := by
  simp [rpUnseal,moveRL,moveLR,peekRp,rlStep,mv1,actThen,WordCmd.peekL,lrStep,
    mnNativePushBound,mnActPush]

private theorem seal_within (r : Fin T) {z z' : Store (HΓ (T := T) A) (HS T Q A U)} {n : ℕ}
    (he : Exec body (rpSeal r) z n z') (depth : ℕ) :
    ExecWithin body (fun d state => mnSize state+d ≤ mnSize z+depth+n) depth (rpSeal r) z n z' := by
  exact mn_native_exec_within he 1 (rpSeal_native r) depth _ (by omega)

private theorem unseal_within (r : Fin T) {z z' : Store (HΓ (T := T) A) (HS T Q A U)} {n : ℕ}
    (he : Exec body (rpUnseal r) z n z') (depth : ℕ) :
    ExecWithin body (fun d state => mnSize state+d ≤ mnSize z+depth+n) depth (rpUnseal r) z n z' := by
  exact mn_native_exec_within he 1 (rpUnseal_native r) depth _ (by omega)

def rpHostWorkspace (p l w M : ℕ) : ℕ :=
  let H := (header p (2^l) w).length
  let X := 2*2^l*w*M
  ringCoreWorkspace p l w H X+8*H+21*X+41

/-- The host wrapper preserves the core's shared-plus-linear workspace form. -/
theorem rpHostWorkspace_affine (p l w M : ℕ) :
    rpHostWorkspace p l w M = rpHostWorkspace p l w 0+771*(2*2^l*w*M) := by
  dsimp only [rpHostWorkspace]
  rw [ringCoreWorkspace_affine p l w (header p (2^l) w).length (2*2^l*w*M)]
  simp only [Nat.mul_zero]
  ring

private theorem host_allowance_le (C H X W : ℕ) :
    (4*H+7)+((4*X+7)+((4*X+7)+((X+(C+1)*W)+
      ((4*X+5)+((4*H+5)+((4*X+5)+(4*X+5))))))) ≤ (C+1)*(W+8*H+21*X+41) := by
  have h : 8*H+21*X+41 ≤ (C+1)*(8*H+21*X+41) := Nat.le_mul_of_pos_left _ (by omega)
  nlinarith only [h]

/-- The original ring host execution has a complete simultaneous stock bound.
The pointwise scratch appears once, while every seal/unseal pass is charged. -/
theorem rpHost_exec_within {ι : Fin 91 → Fin T} (hι : Function.Injective ι) (hQ : rpStates ≤ Q)
    {p l w : ℕ} {fs gs : List (Rec (2^l))} (hp : 1 ≤ p) (hw : p+2 ≤ w)
    (hlen : fs.length = gs.length) (hf : ∀ f ∈ fs, DiskGrid p f.1 f.2)
    (hg : ∀ g ∈ gs, DiskGrid p g.1 g.2) (v : HS T Q A U) (S : Stacks T A)
    (hL : ∀ j, S.L (ι j) = []) (h0 : S.R (ι 0) = (header p (2^l) w).map bitSymbol)
    (h1 : S.R (ι 1) = (array w fs).map bitSymbol) (h2 : S.R (ι 2) = (array w gs).map bitSymbol)
    (h3 : S.R (ι 3) = []) (hpriv : ∀ j : Fin 91, 4 ≤ j.val → S.R (ι j) = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 3*rpTime p l w fs.length ∧
      ∀ C, mnProgPush (rpHost (P := P) (Q := Q) (A := A) (U := U) ι) ≤ C → ∀ depth,
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(C+1)*rpHostWorkspace p l w fs.length)
        depth (rpHost ι) (mk v S) n (mk v' {S with R := (Function.update S.R (ι 3)
          ((array w (List.zipWith (prodRec p) fs gs)).map bitSymbol))}) := by
  obtain ⟨vf,n,huf,hnf,hef⟩ := rpHost_exec body hι hQ hp hw hlen hf hg v S hL h0 h1 h2 h3 hpriv
  refine ⟨vf,n,huf,hnf,?_⟩
  intro C hpush depth
  have hcore : mnProgPush (tcompile (P := P) (Q := Q) (A := A) (U := U)
      (ι ∘ dataSwap) (pwCoreWith decodeHeader3)) ≤ C := by
    change max (mnProgPush (rpSeal (ι 0))) (max (mnProgPush (rpSeal (ι 1)))
      (max (mnProgPush (rpSeal (ι 2))) (max (mnProgPush (tcompile (ι ∘ dataSwap) (pwCoreWith decodeHeader3)))
        (max (mnProgPush (rpUnseal (ι 3))) (max (mnProgPush (rpUnseal (ι 0)))
          (max (mnProgPush (rpUnseal (ι 1))) (mnProgPush (rpUnseal (ι 2))))))))) ≤ C at hpush
    exact (max_le_iff.mp (max_le_iff.mp (max_le_iff.mp (max_le_iff.mp hpush).2).2).2).1
  let hdr := header p (2^l) w
  let F := array w fs
  let G := array w gs
  let output := array w (List.zipWith (prodRec p) fs gs)
  have n01 : ι 0 ≠ ι 1 := hι.ne (by decide)
  have n02 : ι 0 ≠ ι 2 := hι.ne (by decide)
  have n03 : ι 0 ≠ ι 3 := hι.ne (by decide)
  have n12 : ι 1 ≠ ι 2 := hι.ne (by decide)
  have n13 : ι 1 ≠ ι 3 := hι.ne (by decide)
  have n23 : ι 2 ≠ ι 3 := hι.ne (by decide)
  obtain ⟨v₁,_,he₁⟩ := rpSeal_exec body (ι 0) hdr v S (hL 0) h0
  let S₁ : Stacks T A := {S with R := Function.update S.R (ι 0) (cells [hdr])}
  obtain ⟨v₂,_,he₂⟩ := rpSeal_exec body (ι 1) F v₁ S₁ (hL 1) (by simp [S₁,n01.symm,h1,F])
  let S₂ : Stacks T A := {S₁ with R := Function.update S₁.R (ι 1) (cells [F])}
  obtain ⟨v₃,_,he₃⟩ := rpSeal_exec body (ι 2) G v₂ S₂ (hL 2) (by simp [S₂,S₁,n02.symm,n12.symm,h2,G])
  let S₃ : Stacks T A := {S₂ with R := Function.update S₂.R (ι 2) (cells [G])}
  have hS₃ : place S₃ (ι ∘ dataSwap) (startBank hdr F G) = S₃ := by
    apply rp_place_start hι S₃ hdr F G hL
    · simp [S₃,S₂,S₁,n02,n01]
    · simp [S₃,S₂,S₁,n12]
    · simp [S₃]
    · simpa [S₃,S₂,S₁,n03.symm,n13.symm,n23.symm] using h3
    · intro j hj
      have nj0 : ι j ≠ ι 0 := hι.ne (by intro e; subst j; norm_num at hj)
      have nj1 : ι j ≠ ι 1 := hι.ne (by intro e; subst j; norm_num at hj)
      have nj2 : ι j ≠ ι 2 := hι.ne (by intro e; subst j; norm_num at hj)
      simpa [S₃,S₂,S₁,nj0,nj1,nj2] using hpriv j hj
  have hι' : Function.Injective (ι ∘ dataSwap) := hι.comp dataSwap.injective
  obtain ⟨v₄,m₄,_,_,htrace⟩ := ringCore_exec_within (body := body) (ι ∘ dataSwap) hι' hQ
    (hdrDecodes_decodeHeader3 (l := l) hp (by omega)) hw hlen hf hg v₃ S₃
  have ht₄ := htrace C hcore depth
  have hS₄ : place S₃ (ι ∘ dataSwap) (Function.update (startBank hdr F G) zO (Schoenhage.reg output)) =
      {S₃ with R := Function.update S₃.R (ι 3) (cells [output])} := by
    rw [rp_place_update hι',hS₃]
    simp only [Schoenhage.reg,lcells,show (ι ∘ dataSwap) zO = ι 3 from rfl]
    rw [show Function.update S₃.L (ι 3) [] = S₃.L from Function.update_eq_self_iff.mpr (hL 3).symm]
  rw [hS₃,hS₄] at ht₄
  let S₄ : Stacks T A := {S₃ with R := Function.update S₃.R (ι 3) (cells [output])}
  obtain ⟨v₅,_,he₅⟩ := rpUnseal_exec body (ι 3) output v₄ S₄ (hL 3) (by simp [S₄])
  let S₅ : Stacks T A := {S₄ with R := Function.update S₄.R (ι 3) (output.map bitSymbol)}
  obtain ⟨v₆,_,he₆⟩ := rpUnseal_exec body (ι 0) hdr v₅ S₅ (hL 0) (by simp [S₅,S₄,S₃,S₂,S₁,n03,n02,n01])
  let S₆ : Stacks T A := {S₅ with R := Function.update S₅.R (ι 0) (hdr.map bitSymbol)}
  obtain ⟨v₇,_,he₇⟩ := rpUnseal_exec body (ι 1) F v₆ S₆ (hL 1) (by simp [S₆,S₅,S₄,S₃,S₂,S₁,n01.symm,n13,n12])
  let S₇ : Stacks T A := {S₆ with R := Function.update S₆.R (ι 1) (F.map bitSymbol)}
  obtain ⟨v₈,_,he₈⟩ := rpUnseal_exec body (ι 2) G v₇ S₇ (hL 2) (by simp [S₇,S₆,S₅,S₄,S₃,S₂,S₁,n02.symm,n12.symm,n23])
  have ht₄' : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v₃ S₃)+depth+
      (F.length+(C+1)*ringCoreWorkspace p l w hdr.length F.length)) depth
      (tcompile (ι ∘ dataSwap) (pwCoreWith decodeHeader3)) (mk v₃ S₃) m₄ (mk v₄ S₄) := by
    apply ht₄.mono
    intro d z hz
    dsimp only [hdr,F] at *
    omega
  have ht := mn_seq_within_add (seal_within _ he₁ depth)
    (mn_seq_within_add (seal_within _ he₂ depth) (mn_seq_within_add (seal_within _ he₃ depth)
      (mn_seq_within_add ht₄' (mn_seq_within_add (unseal_within _ he₅ depth)
        (mn_seq_within_add (unseal_within _ he₆ depth)
          (mn_seq_within_add (unseal_within _ he₇ depth) (unseal_within _ he₈ depth)))))))
  have hFG : G.length = F.length := by simp only [F,G,length_array,hlen]
  have hO : output.length = F.length := by simp only [output,F,length_array,List.length_zipWith,hlen,min_self]
  have hworkspace : rpHostWorkspace p l w fs.length =
      ringCoreWorkspace p l w hdr.length F.length+8*hdr.length+21*F.length+41 := by
    simp only [rpHostWorkspace,hdr,F,length_array]
  let S₈ : Stacks T A := {S₇ with R := Function.update S₇.R (ι 2) (G.map bitSymbol)}
  let steps := (4*hdr.length+7)+((4*F.length+7)+((4*G.length+7)+
    (m₄+((4*output.length+5)+((4*hdr.length+5)+((4*F.length+5)+(4*G.length+5)))))))
  have ht' : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
      (C+1)*rpHostWorkspace p l w fs.length) depth (rpHost ι) (mk v S) steps (mk v₈ S₈) := by
    apply ht.mono
    intro d z hz
    rw [hFG,hO] at hz
    rw [hworkspace]
    exact hz.trans (Nat.add_le_add_left (host_allowance_le C hdr.length F.length
      (ringCoreWorkspace p l w hdr.length F.length)) _)
  obtain ⟨heqn,heqF⟩ := ht'.toExec.unique hef
  rw [heqn,heqF] at ht'
  exact ht'

end IntegerMultBounds.MathlibTM2.Fast
