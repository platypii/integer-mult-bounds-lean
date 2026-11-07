module

public import IntegerMultBounds.MathlibTM2.Routing.MixedRadixReturn
public import IntegerMultBounds.MathlibTM2.StackStockComposition

/-! Execute the complete non-dyadic return at the current field length. Every
control producer and retirement is actual code, and all work tapes restore. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing.MixedRadixReturnRun
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main
  MixedRadixReturn PaddedFieldInverseMove PaddedFieldLayout MixedRadixReturnFinish PaddedFieldInverseLayout
variable {T Q A : ℕ} {P U β : Type} {body : P → Pr P T Q A U}

theorem returnField_exec
    (exponent prefixCount count realLength blockWidth bits prefixWork prefixClock clock volume fiberVolume src archive zeroBank oneBank tmp : Fin T)
    (hreg : [exponent,prefixCount,count,realLength,blockWidth,bits,prefixWork,prefixClock,clock,volume,fiberVolume,src,archive,zeroBank,oneBank,tmp].Nodup)
    (encode : β → List (Fin (A+4))) (R B M k : ℕ) (hR : 0 < R) (hB : 0 < B)
    (hencode : ∀ x, (encode x).length = R) (fill : β) (zero : Fin (A+4))
    (hfill : encode fill = List.replicate R zero)
    (matrices : List (List (List β))) (hpositive : 0 < matrices.length)
    (hrows : ∀ rows ∈ matrices, rows.length = B)
    (hlen : ∀ rows ∈ matrices, ∀ xs ∈ rows, xs.length = M) (hfit : M ≤ 2^k)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hk : (S.R exponent).length = k) (hp : (S.R prefixCount).length = matrices.length)
    (hb : (S.R count).length = B) (hm : (S.R realLength).length = M) (hw : (S.R blockWidth).length = R)
    (hsrc : S.R src = (columnRows encode M fill matrices).flatten++tail)
    (hfresh : ∀ i ∈ [bits,prefixWork,prefixClock,clock,volume,fiberVolume,archive,zeroBank,oneBank,tmp], S.R i = []) :
    let V := matrices.length*(B*(2^k*R))
    let output := (sourceRows encode matrices).flatten++tail
    ∃ vf n, vf.user = v.user ∧ n ≤ k*(64*V+3)+384*V+2 ∧
      Exec body (returnField exponent prefixCount count realLength blockWidth bits prefixWork prefixClock clock
        volume fiberVolume src archive zeroBank oneBank tmp zero) (mk v S) n
        (mk vf {S with R := Function.update S.R src output}) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+1000*V)
        depth (returnField exponent prefixCount count realLength blockWidth bits prefixWork prefixClock clock
          volume fiberVolume src archive zeroBank oneBank tmp zero) (mk v S) n
          (mk vf {S with R := Function.update S.R src output})) := by
  dsimp only
  have hr := hreg
  regs_ne hr
  let V := matrices.length*(B*(2^k*R))
  let padded := (columnRows encode M fill matrices).flatMap
    (fun xs => xs++List.replicate (2^k*(B*R)-M*(B*R)) zero)++tail
  let output := (sourceRows encode matrices).flatten++tail
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := prepareReturn_exec (body := body)
    exponent prefixCount count realLength blockWidth bits prefixWork prefixClock volume fiberVolume src archive zeroBank tmp
    (by regs_nodup) encode R B M k hR hB hencode fill zero matrices hpositive hrows hfit tail v S
    hk hp hb hm hw hsrc (by
      intro i hi
      apply hfresh i
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
  let S₁ : Stacks T A := {S with R := (Function.update (Function.update (Function.update (Function.update (Function.update S.R
    bits (List.replicate k tick)) prefixWork (List.replicate (matrices.length*2^k) tick))
    volume (List.replicate R tick)) fiberVolume (List.replicate (B*R) tick)) src padded)}
  have hdisjoint (i : Fin T)
      (hi : i ∈ [exponent,prefixCount,count,realLength,blockWidth,prefixClock,clock,archive,zeroBank,oneBank,tmp]) :
      i ∉ [bits,prefixWork,volume,fiberVolume,src] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    all_goals repeat' apply And.intro
    all_goals first | assumption | (apply Ne.symm; assumption)
  have off₁ (i : Fin T) (hi : i ∉ [bits,prefixWork,volume,fiberVolume,src]) : S₁.R i = S.R i := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hi
    obtain ⟨hib,hip,hiv,hif,his⟩ := hi
    simp only [S₁,Function.update_of_ne his,Function.update_of_ne hif,Function.update_of_ne hiv,
      Function.update_of_ne hip,Function.update_of_ne hib]
  have keep₁ (i : Fin T)
      (hi : i ∈ [exponent,prefixCount,count,realLength,blockWidth,prefixClock,clock,archive,zeroBank,oneBank,tmp]) :
      S₁.R i = S.R i := off₁ i (hdisjoint i hi)
  have fresh₁ (i : Fin T) (hi : i ∈ [prefixClock,clock,archive,zeroBank,oneBank,tmp]) : S₁.R i = [] := by
    have hkeep := hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hkeep
    rcases hkeep with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rw [keep₁ _ (by simp)]; exact hfresh _ (by simp)
  obtain ⟨v₂,F,n₂,hu₂,hn₂,he₂,hw₂,hs₂,hp₂,hv₂,hf₂,hbits₂,hframe₂⟩ := returnPaddedRows_exec (body := body)
    bits prefixWork prefixClock count clock volume fiberVolume src archive zeroBank oneBank tmp (by regs_nodup)
    encode R B M k hR hB hencode fill zero hfill matrices hpositive hrows hlen hfit tail v₁ S₁
    (by simp [S₁,‹bits ≠ src›,‹bits ≠ fiberVolume›,‹bits ≠ volume›,‹bits ≠ prefixWork›])
    (by simp [S₁,‹prefixWork ≠ src›,‹prefixWork ≠ fiberVolume›,‹prefixWork ≠ volume›])
    (by rw [keep₁ count (by simp)]; exact hb)
    (by simp [S₁,‹volume ≠ src›,‹volume ≠ fiberVolume›])
    (by simp [S₁,‹fiberVolume ≠ src›]) (by simp [S₁,padded])
    (fresh₁ _ (by simp)) (fresh₁ _ (by simp)) (fresh₁ _ (by simp))
    (fresh₁ _ (by simp)) (fresh₁ _ (by simp)) (fresh₁ _ (by simp))
  obtain ⟨hi₂,ho₂,hl₂,hframe₂⟩ := hframe₂
  have keep₂ (i : Fin T)
      (hi : i ∈ [exponent,prefixCount,count,realLength,blockWidth,prefixClock,clock,archive,zeroBank,oneBank,tmp]) :
      F.R i = S.R i := (hframe₂ i (hdisjoint i hi)).trans (keep₁ i hi)
  have fresh₂ (i : Fin T) (hi : i ∈ [prefixClock,clock,archive,zeroBank,oneBank,tmp]) : F.R i = [] := by
    have hkeep := hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hkeep
    rcases hkeep with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rw [keep₂ _ (by simp)]; exact hfresh _ (by simp)
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := finishReturn_exec (body := body)
    exponent prefixCount count realLength blockWidth bits prefixWork prefixClock clock volume fiberVolume src archive zeroBank oneBank tmp
    hreg encode R B M k hR hB hencode zero matrices hpositive hrows hlen hfit tail v₂ F
    (by rw [keep₂ exponent (by simp)]; exact hk)
    (by rw [keep₂ realLength (by simp)]; exact hm)
    (by rw [keep₂ prefixCount (by simp)]; exact hp)
    (by rw [keep₂ count (by simp)]; exact hb)
    (by rw [keep₂ blockWidth (by simp)]; exact hw) hp₂ hv₂ hf₂ hs₂
    (by
      intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact hbits₂ | exact fresh₂ _ (by simp))
  let F₃ : Stacks T A := {F with R := fun i => if i ∈ [volume,fiberVolume,prefixWork] then [] else Function.update F.R src output i}
  have hfinal : F₃ = {S with R := Function.update S.R src output} := by
    refine Stacks.ext hi₂ ho₂ hl₂ ?_
    funext i
    by_cases his : i = src
    · subst i; simp [F₃,‹volume ≠ src›.symm,‹fiberVolume ≠ src›.symm,‹prefixWork ≠ src›.symm]
    by_cases hc : i ∈ [volume,fiberVolume,prefixWork]
    · have hs : S.R i = [] := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
        rcases hc with rfl | rfl | rfl <;> exact hfresh _ (by simp)
      simp only [F₃,ite_eq_left hc,Function.update_of_ne his,hs]
    by_cases hib : i = bits
    · subst i
      simp [F₃,‹bits ≠ volume›,‹bits ≠ fiberVolume›,‹bits ≠ prefixWork›,‹bits ≠ src›,hbits₂,hfresh bits (by simp)]
    · have hp' : i ≠ volume ∧ i ≠ fiberVolume ∧ i ≠ prefixWork := by
        simpa only [List.mem_cons,List.not_mem_nil,or_false,not_or] using hc
      have hni : i ∉ [bits,prefixWork,volume,fiberVolume,src] := by
        simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
        exact ⟨hib,hp'.2.2,hp'.1,hp'.2.1,his⟩
      simp only [F₃,ite_eq_right hc,Function.update_of_ne his,hframe₂ i hni,off₁ i hni]
  refine ⟨v₃,n₁+(n₂+n₃),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast rfl (congrArg (mk v₃) hfinal),?_⟩
  · change n₁ ≤ 256*V at hn₁
    change n₂ ≤ k*(64*V+3)+2 at hn₂
    change n₃ ≤ 128*V at hn₃
    change n₁+(n₂+n₃) ≤ k*(64*V+3)+384*V+2
    omega
  · intro depth
    have hw₁ := mn_native_exec_within he₁ 2 (prepareReturn_pushBound _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
      depth (mnSize (mk v S)+depth+512*V) (by change n₁ ≤ 256*V at hn₁; omega)
    have hw₃ := finishReturn_within_stock he₃ hn₃ depth
    have hw := mn_seq_within_add hw₁ (mn_seq_within_add (hw₂ depth) hw₃)
    refine (hw.mono ?_).cast rfl (congrArg (mk v₃) hfinal)
    intro d z hz
    change mnSize z+d ≤ mnSize (mk v S)+depth+(512*V+(200*V+256*V)) at hz
    change mnSize z+d ≤ mnSize (mk v S)+depth+1000*V
    omega

/-- The least-dyadic specialization has bounds in the real tensor volume.
The exponent is ordinary retained metadata; all transient controls are generated
and retired by the concrete controller, with an exact source-only endpoint. -/
theorem returnField_least_exec
    (exponent prefixCount count realLength blockWidth bits prefixWork prefixClock clock volume fiberVolume src archive zeroBank oneBank tmp : Fin T)
    (hreg : [exponent,prefixCount,count,realLength,blockWidth,bits,prefixWork,prefixClock,clock,volume,fiberVolume,src,archive,zeroBank,oneBank,tmp].Nodup)
    (encode : β → List (Fin (A+4))) (R B M : ℕ) (hR : 0 < R) (hB : 0 < B) (hM : 0 < M)
    (hencode : ∀ x, (encode x).length = R) (fill : β) (zero : Fin (A+4))
    (hfill : encode fill = List.replicate R zero)
    (matrices : List (List (List β))) (hpositive : 0 < matrices.length)
    (hrows : ∀ rows ∈ matrices, rows.length = B)
    (hlen : ∀ rows ∈ matrices, ∀ xs ∈ rows, xs.length = M)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hk : (S.R exponent).length = Nat.clog 2 M) (hp : (S.R prefixCount).length = matrices.length)
    (hb : (S.R count).length = B) (hm : (S.R realLength).length = M) (hw : (S.R blockWidth).length = R)
    (hsrc : S.R src = (columnRows encode M fill matrices).flatten++tail)
    (hfresh : ∀ i ∈ [bits,prefixWork,prefixClock,clock,volume,fiberVolume,archive,zeroBank,oneBank,tmp], S.R i = []) :
    let V := matrices.length*(B*(M*R))
    let output := (sourceRows encode matrices).flatten++tail
    ∃ vf n, vf.user = v.user ∧ n ≤ (Nat.clog 2 M)*(128*V+3)+768*V+2 ∧
      Exec body (returnField exponent prefixCount count realLength blockWidth bits prefixWork prefixClock clock
        volume fiberVolume src archive zeroBank oneBank tmp zero) (mk v S) n
        (mk vf {S with R := Function.update S.R src output}) ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+2000*V)
        depth (returnField exponent prefixCount count realLength blockWidth bits prefixWork prefixClock clock
          volume fiberVolume src archive zeroBank oneBank tmp zero) (mk v S) n
          (mk vf {S with R := Function.update S.R src output})) := by
  dsimp only
  obtain ⟨vf,n,hu,hn,he,ht⟩ := returnField_exec (body := body)
    exponent prefixCount count realLength blockWidth bits prefixWork prefixClock clock volume fiberVolume src archive zeroBank oneBank tmp
    hreg encode R B M (Nat.clog 2 M) hR hB hencode fill zero hfill matrices hpositive hrows hlen
    (GeneratedFiberPadding.dyadic_capacity_bounds M hM).1 tail v S hk hp hb hm hw hsrc hfresh
  have hvolume : matrices.length*(B*(2^(Nat.clog 2 M)*R)) ≤ 2*(matrices.length*(B*(M*R))) := by
    have h := GeneratedFiberPadding.padded_volume_lt_twice (matrices.length*B) M R (Nat.mul_pos hpositive hB) hM hR
    exact le_of_lt (by simpa only [Nat.mul_assoc] using h)
  refine ⟨vf,n,hu,?_,he,?_⟩
  · have hkV := Nat.mul_le_mul_left (60*(Nat.clog 2 M)) hvolume
    have hcV := Nat.mul_le_mul_left 384 hvolume
    nlinarith only [hn,hkV,hcV]
  · intro depth
    exact (ht depth).mono (by
      intro d z hz
      have hV := Nat.mul_le_mul_left 1000 hvolume
      omega)

end IntegerMultBounds.MathlibTM2.Routing.MixedRadixReturnRun
