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

theorem PublicationKernelReady.of_generator_frame
    {e : Fin PackedTranspose.tapeCount → Fin T}
    {pad tmp saved : Fin PackedTranspose.tapeCount} {V : ℕ} {S F : Stacks T (prime+K)}
    (h : PublicationKernelReady e pad tmp saved V S)
    (writes : List (Fin 117))
    (hallowed : ∀ j ∈ writes, 31 ≤ j.val ∧ j ≠ 106 ∧ j ≠ 109 ∧ j ≠ 115 ∧ j ≠ 116)
    (hpad : ∀ r ∈ [pad,tmp,saved], ∀ j ∈ writes, r ≠ headerReg j)
    (hR : ∀ i, (∀ j ∈ writes, i ≠ headerReg j) → F.R (e i) = S.R (e i))
    (hL : ∀ i, F.L (e i) = S.L (e i)) :
    PublicationKernelReady e pad tmp saved V F := by
  have hp (r) (hr : r ∈ [pad,tmp,saved]) := hR r (hpad r hr)
  have hg (i : Fin 117) (hi : i.val < 31 ∨ i = 106 ∨ i = 115 ∨ i = 116) :
      F.R (e (headerReg i)) = S.R (e (headerReg i)) := by
    apply hR
    intro j hj heq
    have hij := headerReg_injective heq
    subst j
    have ha := hallowed i hj
    rcases hi with hi | rfl | rfl | rfl
    · omega
    · exact ha.2.1 rfl
    · exact ha.2.2.2.1 rfl
    · exact ha.2.2.2.2 rfl
  have hw (i : Fin FixedStreamedBank.tapeCount) :
      F.R (e (base (callerWorker i))) = S.R (e (base (callerWorker i))) := by
    apply hR
    intro j hj
    exact (base_injective.ne (TransposeRegisterPlacement.generator_off_worker _ j (hallowed j hj).2.2.1 i)).symm
  have hx (i : Fin 7) : F.R (e (extra i)) = S.R (e (extra i)) := by
    apply hR
    intro j _
    exact (base_extra _ _).symm
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hp pad (by simp)]; exact h.pad
  · rw [hp tmp (by simp)]; exact h.tmp
  · rw [hp saved (by simp)]; exact h.saved
  · change F.R (e (headerReg 106)) = []
    rw [hg 106 (by simp)]; exact h.zero
  · change (F.R (e (headerReg 115))).length = V
    rw [hg 115 (by simp)]; exact h.width
  · intro r
    change F.R (e (headerReg (originReg r))) = []
    rw [hg _ (Or.inl (originReg_range r))]
    exact h.blank r
  · change F.R (e (headerReg 116)) = []
    rw [hg 116 (by simp)]; exact h.stages
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

theorem PublicationWorkspaceReady.of_generator_frame
    {e : Fin PackedTranspose.tapeCount → Fin T}
    {exponent packet pad tmp saved : Fin PackedTranspose.tapeCount} {a b L W V : ℕ}
    {S F : Stacks T (prime+K)}
    (h : PublicationWorkspaceReady e exponent packet pad tmp saved a b L W V S)
    (writes : List (Fin 117)) (hallowed : ∀ j ∈ writes, j ∈ [(84 : Fin 117),85,97,98,102])
    (hpad : ∀ r ∈ [exponent,packet,pad,tmp,saved], ∀ j ∈ writes, r ≠ headerReg j)
    (hR : ∀ i, (∀ j ∈ writes, i ≠ headerReg j) → F.R (e i) = S.R (e i))
    (hL : ∀ i, F.L (e i) = S.L (e i)) :
    PublicationWorkspaceReady e exponent packet pad tmp saved a b L W V F := by
  refine ⟨h.toPublicationKernelReady.of_generator_frame writes ?_ ?_ hR hL,?_,?_⟩
  · intro j hj
    have ha := hallowed j hj
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> decide
  · intro r hr
    exact hpad r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))
  · rw [hR exponent (hpad exponent (by simp))]; exact h.exponent
  · rw [hR packet (hpad packet (by simp))]; exact h.packet

theorem PublicationWorkspaceReady.of_header_frame
    {e : Fin PackedTranspose.tapeCount → Fin T}
    {exponent packet pad tmp saved : Fin PackedTranspose.tapeCount} {a b L W V : ℕ}
    {S F : Stacks T (prime+K)}
    (h : PublicationWorkspaceReady e exponent packet pad tmp saved a b L W V S)
    (hpad : ∀ r ∈ [exponent,packet,pad,tmp,saved], r ∉ publicationBinaryRegisters)
    (hR : ∀ i, i ∉ publicationBinaryRegisters → F.R (e i) = S.R (e i))
    (hL : ∀ i, F.L (e i) = S.L (e i)) :
    PublicationWorkspaceReady e exponent packet pad tmp saved a b L W V F := by
  apply h.of_generator_frame [97,98,102] (by intro j hj; simp only [List.mem_cons,List.not_mem_nil,or_false] at hj; rcases hj with rfl | rfl | rfl <;> simp) ?_ ?_ hL
  · intro r hr j hj heq
    apply hpad r hr
    rw [heq]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl | rfl <;> simp [publicationBinaryRegisters]
  · intro i hi
    apply hR
    simp only [publicationBinaryRegisters,List.mem_cons,List.not_mem_nil,or_false,not_or]
    exact ⟨hi 97 (by simp),hi 98 (by simp),hi 102 (by simp)⟩

theorem publicationHeaderSizes (a b C V : ℕ) (hbits : a+b < V) (hfit : C*2^(a+b) < 2^V) :
    Nat.size a ≤ V ∧ Nat.size b ≤ V ∧ Nat.size C ≤ V := by
  have hV : V ≤ 2^V := Nat.lt_two_pow_self.le
  have ha : a < V := (Nat.le_add_right a b).trans_lt hbits
  have hb : b < V := (Nat.le_add_left b a).trans_lt hbits
  have hC : C < 2^V :=
    (Nat.le_mul_of_pos_right C (Nat.two_pow_pos (a+b))).trans_lt hfit
  exact ⟨Nat.size_le.mpr (ha.trans_le hV),Nat.size_le.mpr (hb.trans_le hV),Nat.size_le.mpr hC⟩

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
