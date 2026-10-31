module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakePrefixStock
public import IntegerMultBounds.MathlibTM2.Host.BinArith

/-! Read one generated binary origin and create the changing unary endpoints.
The queue advances once and all conversion workspace is retired. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def readSupplierEndpoints (width halo queue binary a b work saved tmp : Fin T) : Pr P T Q A U :=
  .seq (takePrefix width queue binary saved tmp)
    (.seq (toUnary binary a work saved tmp)
      (.seq (uclear binary) (.seq (ucopy a b saved) (ucopy halo b saved))))

def readSupplierEndpointsCost (width origin halo : ℕ) : ℕ := 19*width+10*origin+4*halo+22

theorem readSupplierEndpoints_native (width halo queue binary a b work saved tmp : Fin T) :
    mnNativePushBound 3 (readSupplierEndpoints (P := P) (Q := Q) (A := A) (U := U)
      width halo queue binary a b work saved tmp) := by
  simp [readSupplierEndpoints,takePrefix,toUnary,eachSym,hornerIter,udbl,transfer,transferAct,
    uclear,ucopy,umulSym,scanR,drainR,popDo,keepIn,pushN,popPush,moveR,moveStep,whileR,peekR,
    mnNativePushBound,mnActPush]

theorem readSupplierEndpoints_exec (width halo queue binary a b work saved tmp : Fin T)
    (hreg : [width,halo,queue,binary,a,b,work,saved,tmp].Nodup) (V x L : ℕ) (hfit : x < 2^V)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hwidth : (S.R width).length = V) (hhalo : (S.R halo).length = L)
    (hqueue : S.R queue = binSyms V x++tail)
    (hblank : ∀ k ∈ [binary,a,b,work,saved,tmp], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ readSupplierEndpointsCost V x L ∧
      Exec body (readSupplierEndpoints width halo queue binary a b work saved tmp) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update (Function.update S.R queue tail)
          a (List.replicate x tick)) b (List.replicate (x+L) tick))}) := by
  have hr := hreg
  regs_ne hr
  obtain ⟨v₁,hu₁,he₁⟩ := takePrefix_exec (body := body)
    (count := width) (src := queue) (dst := binary) (buf := saved) (tmp := tmp)
    (by regs_nodup) v S (binSyms V x) tail hqueue (by simpa only [length_binSyms] using hwidth)
    (hblank saved (by simp)) (hblank tmp (by simp))
  simp only [length_binSyms,hblank binary (by simp),List.append_nil] at he₁
  let F : Stacks T A := {S with R := (Function.update (Function.update S.R queue tail) binary (binSyms V x))}
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := toUnary_exec_linear (body := body)
    (a := binary) (z := a) (w := work) (t := saved) (t₂ := tmp) (by regs_nodup) hfit v₁ F
    (by simp [F]) (by simp [F,‹binary ≠ work›.symm,‹queue ≠ work›.symm,hblank work (by simp)])
    (by simp [F,‹binary ≠ saved›.symm,‹queue ≠ saved›.symm,hblank saved (by simp)])
    (by simp [F,‹binary ≠ tmp›.symm,‹queue ≠ tmp›.symm,hblank tmp (by simp)])
  let G : Stacks T A := {F with R := Function.update F.R a (List.replicate x tick)}
  have he₂' : Exec body (toUnary binary a work saved tmp) (Host.mk v₁ F) n₂ (Host.mk v₂ G) := by
    simpa [F,G,‹binary ≠ a›.symm,‹queue ≠ a›.symm,hblank a (by simp)] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body binary v₂ G
  let H : Stacks T A := {S with R := (Function.update (Function.update S.R queue tail) a (List.replicate x tick))}
  have he₃' : Exec body (uclear binary) (Host.mk v₂ G) (2*V+2) (Host.mk v₃ H) := by
    have hlen : (G.R binary).length = V := by simp [G,F,‹binary ≠ a›]
    rw [hlen] at he₃
    refine he₃.cast rfl ?_
    apply congrArg (Host.mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hb : k = binary <;> by_cases ha : k = a <;> by_cases hq : k = queue <;>
      simp_all [G,F,H]
  obtain ⟨v₄,hu₄,he₄⟩ := ucopy_exec body ‹a ≠ b› ‹a ≠ saved› ‹b ≠ saved› v₃ H
    (by simp [H,‹a ≠ saved›.symm,‹queue ≠ saved›.symm,hblank saved (by simp)])
  let I : Stacks T A := {H with R := Function.update H.R b (List.replicate x tick)}
  have he₄' : Exec body (ucopy a b saved) (Host.mk v₃ H) (4*x+4) (Host.mk v₄ I) := by
    simpa [I,H,‹a ≠ b›.symm,‹queue ≠ b›.symm,hblank b (by simp)] using he₄
  obtain ⟨v₅,hu₅,he₅⟩ := ucopy_exec body ‹halo ≠ b› ‹halo ≠ saved› ‹b ≠ saved› v₄ I
    (by simp [I,H,‹b ≠ saved›.symm,‹a ≠ saved›.symm,‹queue ≠ saved›.symm,hblank saved (by simp)])
  have he₅' : Exec body (ucopy halo b saved) (Host.mk v₄ I) (4*L+4)
      (Host.mk v₅ {S with R := (Function.update (Function.update (Function.update S.R queue tail)
        a (List.replicate x tick)) b (List.replicate (x+L) tick))}) := by
    simpa [I,H,‹halo ≠ b›,‹halo ≠ a›,‹halo ≠ queue›,hhalo,List.replicate_append_replicate,Nat.add_comm] using he₅
  refine ⟨v₅,(6*V+6)+(n₂+((2*V+2)+((4*x+4)+(4*L+4)))),hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))),?_,
    Exec.seq he₁ (Exec.seq he₂' (Exec.seq he₃' (Exec.seq he₄' he₅')))⟩
  unfold readSupplierEndpointsCost
  omega

theorem readSupplierEndpoints_exec_within (width halo queue binary a b work saved tmp : Fin T)
    (hreg : [width,halo,queue,binary,a,b,work,saved,tmp].Nodup) (V x L : ℕ) (hfit : x < 2^V)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hwidth : (S.R width).length = V) (hhalo : (S.R halo).length = L)
    (hqueue : S.R queue = binSyms V x++tail)
    (hblank : ∀ k ∈ [binary,a,b,work,saved,tmp], S.R k = []) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧ n ≤ readSupplierEndpointsCost V x L ∧
      ExecWithin body (fun d state => mnSize state+d ≤ mnSize (Host.mk v S)+depth+
        3*readSupplierEndpointsCost V x L) depth
        (readSupplierEndpoints width halo queue binary a b work saved tmp) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update (Function.update S.R queue tail)
          a (List.replicate x tick)) b (List.replicate (x+L) tick))}) := by
  obtain ⟨v',n,hu,hn,he⟩ := readSupplierEndpoints_exec width halo queue binary a b work saved tmp hreg V x L hfit tail v S
    hwidth hhalo hqueue hblank
  exact ⟨v',n,hu,hn,mn_native_exec_within he 3 (readSupplierEndpoints_native _ _ _ _ _ _ _ _ _) depth _ (by omega)⟩
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
