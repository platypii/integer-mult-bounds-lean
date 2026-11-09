module

public import IntegerMultBounds.MathlibTM2.Mult.SignedRoundExec
public import IntegerMultBounds.MathlibTM2.Node.TopWordStock

/-! Truncating a stream reuses the scratch of one signed word, independently
of the number of coefficients in the stream. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem signedRound_within (hA : 4 ≤ A) {src dst tmp cW cS cE cD sp sg cy : Fin T}
    (hreg : [src,dst,tmp,cW,cS,cE,cD,sp,sg,cy].Nodup)
    (w d k : ℕ) (hw : 1 ≤ w) (hdk : d+k ≤ w)
    (xs : List GaussianInt) (hxs : ∀ x ∈ xs, TopFitsZ w x)
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R src = cstream A w xs)
    (hg : topShiftG tmp cW cS cE cD sp sg cy w d k S.R)
    {n : ℕ} {t : Store (HΓ (T := T) A) (HS T Q A U)}
    (he : Exec body (topPass src dst (topShiftWord src dst tmp cW cS cE cD sp sg cy)) (mk v S) n t)
    (depth : ℕ) :
    ExecWithin body (fun callDepth z => mnSize z+callDepth ≤ mnSize (mk v S)+depth+13*topShiftWordCost w d k) depth
      (topPass src dst (topShiftWord src dst tmp cW cS cE cD sp sg cy)) (mk v S) n t := by
  have hr := hreg
  regs_ne hr
  have hframe : TopWordFrame src dst (topShiftG tmp cW cS cE cD sp sg cy (A := A) w d k) := by
    intro R l l' ⟨hW,hS,hE,hD,hsp,hsg,hcy,htmp⟩
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> simp_all [ne_comm]
  apply topPass_within ‹src ≠ dst› hframe (topShiftWord_spec body hA hreg hw hdk)
    (topShiftWord_native ..) (xs.map (csyms A w)) v S ?_ ?_ ?_ hg he depth
  · intro x hx
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hx
    simp [csyms]
  · intro x hx
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hx
    rw [topShiftF_coeffSyms hA hw hdk z (hxs z hz)]
    simp only [csyms,length_coeffSyms]
    omega
  · simpa only [cstream,List.flatMap_def] using hsrc

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
