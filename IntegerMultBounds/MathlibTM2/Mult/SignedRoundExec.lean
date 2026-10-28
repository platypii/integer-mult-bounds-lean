module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpOutputBounds
public import IntegerMultBounds.MathlibTM2.Node.TopWord

/-! Signed word execution needs representability, including the negative endpoint. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Fast
variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U}

theorem signedRound_exec (hA : 4 ≤ A) {src dst tmp cW cS cE cD sp sg cy : Fin T}
    (hreg : [src, dst, tmp, cW, cS, cE, cD, sp, sg, cy].Nodup)
    (w d k : ℕ) (hw : 1 ≤ w) (hdk : d + k ≤ w)
    (xs : List GaussianInt) (hxs : ∀ x ∈ xs, TopFitsZ w x)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = cstream A w xs) (hdst : S.R dst = [])
    (hg : topShiftG tmp cW cS cE cD sp sg cy w d k S.R) :
    ∃ v', v'.user = v.user ∧
      Exec body (topPass src dst (topShiftWord src dst tmp cW cS cE cD sp sg cy))
        (mk v S) (1 + (xs.length * (topShiftWordCost w d k + 1) + 1) +
          (2 * (xs.length * k) + 2))
        (mk v' { S with R := (Function.update S.R src
          (cstream A k (xs.map (tdivN d)))) }) := by
  have hreg' := hreg
  regs_ne hreg'
  have hframe : TopWordFrame src dst (topShiftG tmp cW cS cE cD sp sg cy (A := A) w d k) := by
    intro R l l' ⟨hW, hS, hE, hD, hsp, hsg, hcy, htmp⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp_all [ne_comm]
  have hmap : (xs.map (csyms A w)).map (topShiftF A d k) =
      (xs.map (tdivN d)).map (csyms A k) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro x hx
    have hf := hxs x hx
    exact topShiftF_coeffSyms hA hw hdk x
      hf
  obtain ⟨v', hu, he⟩ := topPass_exec body ‹src ≠ dst› hframe hw
    (topShiftWord_spec body hA hreg hw hdk) (xs.map (csyms A w)) v S
    (by intro x hx; obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hx; simp [csyms])
    (by simpa only [cstream, List.flatMap_def] using hsrc) hdst hg
  rw [hmap] at he
  refine ⟨v', hu, he.cast ?_ ?_⟩
  · simp only [List.length_map]
    change 1 + (xs.length * (topShiftWordCost w d k + 1) + 1) +
      (2 * (cstream A k (xs.map (tdivN d))).length + 2) = _
    simp
  · rfl


end IntegerMultBounds.MathlibTM2.Mult.ShortConv
