module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicPublicationReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicGatherHeaders

/-! Publication uses the same three binary dimensions as gather. Generate them
from retained unary masters; the remaining readiness is an independent workspace
invariant, preserved by the exact three-write frame. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open FixedStreamedBank
noncomputable section
variable {T Q K : ℕ} {P U : Type}

def publicationBinaryRegisters : List (Fin PackedTranspose.tapeCount) :=
  [headerReg 97,headerReg 98,headerReg 102]

def publicationHeadersState (a b C V : ℕ) (S : Stacks PackedTranspose.tapeCount (prime+K)) :=
  {S with R := Function.update (Function.update (Function.update S.R
    (headerReg 97) (binSyms V a)) (headerReg 98) (binSyms V b)) (headerReg 102) (binSyms V C)}

theorem PublicationWorkspaceReady.of_header_frame
    {e : Fin PackedTranspose.tapeCount → Fin T}
    {exponent packet pad tmp saved : Fin PackedTranspose.tapeCount} {a b L W V : ℕ}
    {S F : Stacks T (prime+K)}
    (h : PublicationWorkspaceReady e exponent packet pad tmp saved a b L W V S)
    (hpad : ∀ r ∈ [exponent,packet,pad,tmp,saved], r ∉ publicationBinaryRegisters)
    (hR : ∀ i, i ∉ publicationBinaryRegisters → F.R (e i) = S.R (e i))
    (hL : ∀ i, F.L (e i) = S.L (e i)) :
    PublicationWorkspaceReady e exponent packet pad tmp saved a b L W V F := by
  have hp (r) (hr : r ∈ [exponent,packet,pad,tmp,saved]) := hR r (hpad r hr)
  have hg (i : Fin 117) (hi97 : i ≠ 97) (hi98 : i ≠ 98) (hi102 : i ≠ 102) :
      F.R (e (headerReg i)) = S.R (e (headerReg i)) :=
    hR _ (by simp [publicationBinaryRegisters,headerReg_injective.eq_iff,hi97,hi98,hi102])
  have hw (i : Fin FixedStreamedBank.tapeCount) :
      F.R (e (base (callerWorker i))) = S.R (e (base (callerWorker i))) := by
    apply hR
    have hoff (j : Fin 117) (hj : j ≠ 109) : base (callerWorker i) ≠ headerReg j :=
      (base_injective.ne (TransposeRegisterPlacement.generator_off_worker _ j hj i)).symm
    simp [publicationBinaryRegisters,hoff 97 (by decide),hoff 98 (by decide),hoff 102 (by decide)]
  have hx (i : Fin 7) : F.R (e (extra i)) = S.R (e (extra i)) := by
    apply hR
    simp [publicationBinaryRegisters,headerReg,Ne.symm (base_extra _ _)]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hp exponent (by simp)]; exact h.exponent
  · rw [hp packet (by simp)]; exact h.packet
  · rw [hp pad (by simp)]; exact h.pad
  · rw [hp tmp (by simp)]; exact h.tmp
  · rw [hp saved (by simp)]; exact h.saved
  · change F.R (e (headerReg 106)) = []
    rw [hg 106 (by decide) (by decide) (by decide)]; exact h.zero
  · change (F.R (e (headerReg 115))).length = V
    rw [hg 115 (by decide) (by decide) (by decide)]; exact h.width
  · intro r
    have hr := originReg_range r
    rw [show F.R (e (base (callerGenerator (originReg r)))) = S.R (e (base (callerGenerator (originReg r)))) from
      hg _ (by intro he; rw [he] at hr; norm_num at hr)
        (by intro he; rw [he] at hr; norm_num at hr) (by intro he; rw [he] at hr; norm_num at hr)]
    exact h.blank r
  · change F.R (e (headerReg 116)) = []
    rw [hg 116 (by decide) (by decide) (by decide)]; exact h.stages
  · simpa only [hL] using h.left
  · simpa only [hw] using h.fresh
  · rw [hx]; exact h.count
  · intro i hi
    have hread : F.R (e i) = S.R (e i) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hw _
      all_goals exact hx _
    rw [hread]; exact h.codec i hi

theorem publicationHeaders_exec_within
    (body : P → Pr P PackedTranspose.tapeCount Q (prime+K) U)
    (exponent packet pad tmp saved : Fin PackedTranspose.tapeCount) (a b L W V : ℕ)
    (ha : Nat.size a ≤ V) (hb : Nat.size b ≤ V) (hpacket : Nat.size (L*W) ≤ V)
    (depth : ℕ) (v : HS PackedTranspose.tapeCount Q (prime+K) U)
    (S : Stacks PackedTranspose.tapeCount (prime+K))
    (hworkspace : PublicationWorkspaceReady (fun i => i) exponent packet pad tmp saved a b L W V S)
    (hpad : ∀ r ∈ [exponent,packet,pad,tmp,saved], r ∉ publicationBinaryRegisters)
    (hsourceA : (S.R (headerReg 84)).length = a)
    (hsourceB : (S.R (headerReg 85)).length = b)
    (hsourceC : (S.R packetWidth).length = L*W)
    (hblank : ∀ i ∈ [(97 : Fin 117),98,102,40,41,42,43,44,45], S.R (headerReg i) = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 21*(a+b+L*W)+36*V+85 ∧
      PublicationReady (fun i => i) exponent packet pad tmp saved a b L W V (publicationHeadersState a b (L*W) V S) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        2*(21*(a+b+L*W)+36*V+85)) depth gatherHeadersProgram (mk v S) n
        (mk v' (publicationHeadersState a b (L*W) V S)) := by
  obtain ⟨v',n,hu,hn,he⟩ := gatherHeaders_exec_within body a b (L*W) V ha hb hpacket depth v S
    hworkspace.width hsourceA hsourceB hsourceC hblank
  have hread (i : Fin PackedTranspose.tapeCount) (hi : i ∉ publicationBinaryRegisters) :
      (publicationHeadersState a b (L*W) V S).R i = S.R i := by
    simp only [publicationBinaryRegisters,List.mem_cons,List.not_mem_nil,or_false,not_or] at hi
    simp only [publicationHeadersState,Function.update_of_ne hi.2.2,Function.update_of_ne hi.2.1,Function.update_of_ne hi.1]
  have hw := hworkspace.of_header_frame hpad hread (by intro i; rfl)
  refine ⟨v',n,hu,hn,⟨hw,?_,?_,?_⟩,he⟩
  · change (publicationHeadersState a b (L*W) V S).R (headerReg 97) = _
    simp [publicationHeadersState,headerReg_injective.eq_iff]
  · change (publicationHeadersState a b (L*W) V S).R (headerReg 98) = _
    simp [publicationHeadersState,headerReg_injective.eq_iff]
  · change (publicationHeadersState a b (L*W) V S).R (headerReg 102) = _
    simp [publicationHeadersState]

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
