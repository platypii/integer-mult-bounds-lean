module

public import IntegerMultBounds.MathlibTM2.Mult.SignedRoundExec

/-! Sign extension of an arbitrary word list restores its surrounding frame. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Fast
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem signedWiden_exec {src dst c₁ c₂ sp : Fin T} (hreg : [src,dst,c₁,c₂,sp].Nodup)
    (w w' : ℕ) (hw : 1 ≤ w) (hww : w ≤ w') (xs : List GaussianInt)
    (hxs : ∀ z ∈ xs, TopFitsZ w z) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = cstream A w xs) (hdst : S.R dst = [])
    (hg : topWidenG c₁ c₂ sp w w' S.R) :
    ∃ v', v'.user = v.user ∧
      Exec body (topPass src dst (topWidenWord src dst c₁ c₂ sp)) (mk v S)
        (1+(xs.length*((4*w+4)+((4*(w'-w)+4)+1)+1)+1)+(2*(xs.length*w')+2))
        (mk v' {S with R := (Function.update S.R src (cstream A w' xs))}) := by
  have hr := hreg
  regs_ne hr
  have hframe : TopWordFrame src dst (topWidenG c₁ c₂ sp (A := A) w w') := by
    intro R l l' ⟨h₁,h₂,hsp⟩
    refine ⟨?_,?_,?_⟩ <;> simp_all [ne_comm]
  have hmap : (xs.map (csyms A w)).map (topWidenF w w') = xs.map (csyms A w') := by
    simp only [List.map_map]
    exact List.map_congr_left (fun z hz => topWidenF_coeffSyms hw hww z (hxs z hz))
  obtain ⟨v',hu,he⟩ := topPass_exec body ‹src ≠ dst› hframe hw (topWidenWord_spec body hreg hw)
    (xs.map (csyms A w)) v S
    (by intro x hx; obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hx; simp [csyms])
    (by simpa only [cstream,List.flatMap_def] using hsrc) hdst hg
  rw [hmap] at he
  refine ⟨v',hu,he.cast ?_ ?_⟩
  · simp only [List.length_map]
    change 1+(xs.length*((4*w+4)+((4*(w'-w)+4)+1)+1)+1)+(2*(cstream A w' xs).length+2) = _
    rw [length_cstream]
  · rfl

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
