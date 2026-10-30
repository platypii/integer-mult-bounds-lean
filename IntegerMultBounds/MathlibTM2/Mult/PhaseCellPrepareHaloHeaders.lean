module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakeUnaryKey
public import IntegerMultBounds.MathlibTM2.Host.ExtendStacks

/-! Initialize the first halo's coordinate headers from its generated binary
origin and retained binary length. Later iterations must advance these masters. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

variable {T T' Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def haloHeaderR (aMaster bMaster word : Fin T) (V a b : ℕ)
    (R : Fin T → List (Fin (A+4))) : Fin T → List (Fin (A+4)) :=
  Function.update (Function.update (Function.update R word (binSyms V a))
    aMaster (List.replicate a tick)) bMaster (List.replicate b tick)

/-- The setup frame with its three owned coordinate slots materialized. -/
def haloHeaderBank (V a b : ℕ) (S : Stacks 242 A) : Stacks 242 A :=
  {S with R := haloHeaderR 141 142 155 V a b S.R}

theorem embStk_haloHeaderR {e : Fin T → Fin T'} (he : Function.Injective e)
    (S : Stacks T' A) (aMaster bMaster word : Fin T) (V a b : ℕ) :
    embStk e {S with R := haloHeaderR (e aMaster) (e bMaster) (e word) V a b S.R} =
      {embStk e S with R := haloHeaderR aMaster bMaster word V a b (embStk e S).R} := by
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  simp only [embStk,Function.comp_apply,haloHeaderR,Function.update_apply,he.eq_iff]

theorem extendStacks_haloHeaderR (h : T ≤ T') (S : Stacks T A)
    (aMaster bMaster word : Fin T) (V a b : ℕ) :
    extendStacks h {S with R := haloHeaderR aMaster bMaster word V a b S.R} =
      {extendStacks h S with R := (haloHeaderR (Fin.castLE h aMaster)
        (Fin.castLE h bMaster) (Fin.castLE h word) V a b (extendStacks h S).R)} := by
  have hinj : Function.Injective (Fin.castLE h) := by
    intro i j he
    exact Fin.ext (congrArg (fun k : Fin T' => k.val) he)
  symm
  apply eq_extendStacks h
  · rw [embStk_haloHeaderR hinj,embStk_extendStacks]
  · intro i hi
    have hn (j : Fin T) : i ≠ Fin.castLE h j := by
      intro he
      have hv := congrArg (fun k : Fin T' => k.val) he
      have hj := j.isLt
      simp only [Fin.val_castLE] at hv
      omega
    have hf := extendStacks_fresh h S i hi
    exact ⟨hf.1,by simpa only [haloHeaderR,Function.update_of_ne (hn _)] using hf.2⟩

def prepareHaloHeaders (width src lengthWord aMaster bMaster word count work saved tmp : Fin T) : Pr P T Q A U :=
  .seq (takeBinaryUnaryKey width src aMaster word work saved tmp)
    (.seq (ucopy aMaster bMaster work)
      (.seq (toUnary lengthWord bMaster work saved tmp) (.act (dropTop count .done))))

def prepareHaloHeadersCost (V a L : ℕ) : ℕ := 10*a+6*L+28*V+23

theorem prepareHaloHeaders_exec {width src lengthWord aMaster bMaster word count work saved tmp : Fin T}
    (hreg : [width,src,lengthWord,aMaster,bMaster,word,count,work,saved,tmp].Nodup)
    (V a L : ℕ) (ha : a < 2^V) (hL : L < 2^V)
    (tail cs : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hwidth : (S.R width).length = V) (hsrc : S.R src = binSyms V a++tail)
    (hlength : S.R lengthWord = binSyms V L) (hcount : S.R count = tick::cs)
    (hfresh : ∀ k ∈ [aMaster,bMaster,word,work,saved,tmp], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ prepareHaloHeadersCost V a L ∧
      Exec body (prepareHaloHeaders width src lengthWord aMaster bMaster word count work saved tmp)
        (mk v S) n (mk v' {S with R := (Function.update
          (Function.update (haloHeaderR aMaster bMaster word V a (a+L) S.R) src tail) count cs)}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := takeBinaryUnaryKey_exec (body := body)
    (width := width) (src := src) (dst := aMaster) (word := word) (work := work) (saved := saved) (tmp := tmp)
    (by regs_nodup) V a ha tail v S hwidth hsrc
    (by intro k hk; exact hfresh k (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢; tauto))
  let S₁ : Stacks T A := {S with R := (Function.update
    (Function.update (Function.update S.R src tail) word (binSyms V a)) aMaster (List.replicate a tick))}
  obtain ⟨v₂,hu₂,he₂⟩ := ucopy_exec body (a := aMaster) (b := bMaster) (t := work)
    ‹aMaster ≠ bMaster› ‹aMaster ≠ work› ‹bMaster ≠ work› v₁ S₁
    (by simp [S₁,‹aMaster ≠ work›.symm,‹word ≠ work›.symm,‹src ≠ work›.symm,hfresh work (by simp)])
  let S₂ : Stacks T A := {S₁ with R := Function.update S₁.R bMaster (List.replicate a tick)}
  have he₂' : Exec body (ucopy aMaster bMaster work) (mk v₁ S₁) (4*a+4) (mk v₂ S₂) := by
    simpa [S₂,S₁,‹aMaster ≠ bMaster›.symm,‹bMaster ≠ word›,‹src ≠ bMaster›.symm,
      hfresh bMaster (by simp)] using he₂
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := toUnary_exec_linear body
    (a := lengthWord) (z := bMaster) (w := work) (t := saved) (t₂ := tmp)
    (by regs_nodup) hL v₂ S₂
    (by simp [S₂,S₁,‹lengthWord ≠ bMaster›,‹lengthWord ≠ aMaster›,‹lengthWord ≠ word›,
      ‹src ≠ lengthWord›.symm,hlength])
    (by simp [S₂,S₁,‹bMaster ≠ work›.symm,‹aMaster ≠ work›.symm,‹word ≠ work›.symm,
      ‹src ≠ work›.symm,hfresh work (by simp)])
    (by simp [S₂,S₁,‹bMaster ≠ saved›.symm,‹aMaster ≠ saved›.symm,‹word ≠ saved›.symm,
      ‹src ≠ saved›.symm,hfresh saved (by simp)])
    (by simp [S₂,S₁,‹bMaster ≠ tmp›.symm,‹aMaster ≠ tmp›.symm,‹word ≠ tmp›.symm,
      ‹src ≠ tmp›.symm,hfresh tmp (by simp)])
  let S₃ : Stacks T A := {S₂ with R := Function.update S₂.R bMaster (List.replicate (a+L) tick)}
  have he₃' : Exec body (toUnary lengthWord bMaster work saved tmp) (mk v₂ S₂) n₃ (mk v₃ S₃) := by
    simpa [S₃,S₂,List.replicate_append_replicate,Nat.add_comm] using he₃
  have hc : S₃.R count = tick::cs := by
    simp [S₃,S₂,S₁,‹bMaster ≠ count›.symm,‹aMaster ≠ count›.symm,‹word ≠ count›.symm,
      ‹src ≠ count›.symm,hcount]
  have he₄ : Exec body (.act (dropTop count .done)) (mk v₃ S₃) 1
      (mk v₃ {S₃ with R := Function.update S₃.R count cs}) := by
    simpa [dropTop,Action.run,update_rt,hc] using Exec.act (body := body) (dropTop count .done) (mk v₃ S₃)
  refine ⟨v₃,n₁+((4*a+4)+(n₃+1)),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁ (Exec.seq he₂' (Exec.seq he₃' he₄))).cast rfl ?_⟩
  · unfold prepareHaloHeadersCost
    omega
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    simp only [S₃,S₂,S₁,haloHeaderR,Function.update_idem]
    rw [Function.update_comm ‹src ≠ word›,Function.update_comm ‹src ≠ aMaster›,
      Function.update_comm ‹src ≠ bMaster›]


end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
