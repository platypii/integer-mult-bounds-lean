module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedPackedReplicaGather
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedOriginAdvanceControls
public import IntegerMultBounds.MathlibTM2.Host.Embed

/-! Generate one local control page, reuse it for every packed RHS, then erase
it. The coordinate width depends on one halo, never the complete replica bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 126 Q A U}

private theorem localGatherControls_eq (A w : ℕ) (offsets : List ℕ) (hne : offsets ≠ []) :
    gatherControls A (originAdvances w 0 offsets++[0]) =
      match offsets.map (·*w) with | [] => [] | p::ps => gatherControls A (p::windowAdvances p ps) := by
  rw [originAdvances_symbols]
  cases offsets with
  | nil => exact (hne rfl).elim
  | cons p ps => simp [originAdvances,originAdvances_window]

def sharedPackedReplicaGather : Pr P 126 Q A U :=
  .seq (embProg (Fin.castLE (by decide : 117 ≤ 126)) Empty.elim
    (preparedNaturalAdvanceControls (P₀ := Empty)))
    (.seq (retainedRowGather 121 122 123 124 125 110 91 1 2 0 92 3 4 5 6 7 8 9 102 94) (uclear 91))

def sharedPackedReplicaGatherCost (V N span L w B : ℕ) : ℕ :=
  preparedOriginAdvanceCost V span w B+
    (N*(retainedRowGatherStepCost (span*w) B L w+5)+4+2*(N*(span*w))+2)+
    (2*(span*w+B+1)+2)

/-- Numerical decoding belongs entirely to the one-time setup term. -/
theorem sharedPackedReplicaGatherCost_eq (V N span L w B : ℕ) :
    sharedPackedReplicaGatherCost V N span L w B =
      (preparedOriginAdvanceCost V span w B+2*(span*w)+2*B+10)+
      N*(B*(14*L*w+25)+30*(span*w)+6*L*w+9*L+50) := by
  unfold sharedPackedReplicaGatherCost retainedRowGatherStepCost
  ring

private theorem repeatedGatherBill (X B R L volume : ℕ) (hX : X = B*R)
    (hB : B ≤ X) (hR : R ≤ X) (hL : L ≤ X) :
    B*(14*R+25)+30*volume+6*R+9*L+50 ≤ 100*(X+volume+1) := by
  nlinarith only [hX,hB,hR,hL,Nat.zero_le X,Nat.zero_le volume]

/-- The repeated work is linear in gathered output and packed source volume. -/
theorem sharedPackedReplicaGatherCost_le (V N span L w B : ℕ)
    (hB : 1 ≤ B) (hL : 1 ≤ L) (hw : 1 ≤ w) :
    sharedPackedReplicaGatherCost V N span L w B ≤
      (preparedOriginAdvanceCost V span w B+2*(span*w)+2*B+10)+
      100*N*(B*L*w+span*w+1) := by
  have hR : 1 ≤ L*w := Nat.mul_le_mul hL hw
  have hB' : B ≤ B*L*w := by
    simpa only [Nat.mul_assoc] using Nat.le_mul_of_pos_right B hR
  have hR' : L*w ≤ B*L*w := by
    simpa only [Nat.mul_assoc] using Nat.le_mul_of_pos_left (L*w) hB
  have hL' : L ≤ B*L*w := (Nat.le_mul_of_pos_right L hw).trans hR'
  have hb := repeatedGatherBill (B*L*w) B (L*w) L (span*w) (by ring) hB' hR' hL'
  have hs := Nat.mul_le_mul_left N hb
  rw [sharedPackedReplicaGatherCost_eq]
  nlinarith only [hs]

theorem sharedPackedReplicaGather_exec {s : ℕ} (V origin span L w : ℕ)
    (offsets : List ℕ) (Fs : List (ZMod s → GaussianInt))
    (hne : offsets ≠ []) (hspan : origin+span ≤ s) (hordered : offsets.Pairwise (· ≤ ·))
    (hfit : ∀ j ∈ offsets, j+L ≤ span)
    (hwV : w < 2^V) (hcoords : span < 2^V) (hunits : span*w < 2^V)
    (suffix borrowed : List (Fin (A+4))) (v : HS 126 Q A U) (S : Stacks 126 A)
    (hV : (S.R 115).length = V) (hw : (S.R 94).length = w) (hL : (S.R 102).length = L)
    (hpackets : S.R 109 = offsets.flatMap (binSyms V)++suffix)
    (hcount : S.R 116 = List.replicate offsets.length tick)
    (hreplicas : (S.R 121).length = Fs.length) (hvolume : (S.R 123).length = span*w)
    (hsource : S.R 124 = Fs.flatMap (fun F => cstream A w (packedInterval origin span F))++borrowed)
    (hblank : ∀ k : Fin 126, k.val < 19 → S.R k = [])
    (hfresh : ∀ k ∈ [(88 : Fin 126),89,90,91,92,104,105,106,122,125], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ sharedPackedReplicaGatherCost V Fs.length span L w offsets.length ∧
      Exec body sharedPackedReplicaGather (mk v S) n
        (mk v' {S with R := (Function.update S.R 110
          (Fs.reverse.flatMap (fun F => cstream A w (offsets.flatMap
            (fun j => cellSourceRows L (fun _ => ((origin+j : ℕ) : ZMod s)) (fun _ => F) 0)))++S.R 110))}) := by
  let controls := gatherControls A (originAdvances w 0 offsets++[0])
  let rhs := Fs.reverse.flatMap (fun F => cstream A w (offsets.flatMap
    (fun j => cellSourceRows L (fun _ => ((origin+j : ℕ) : ZMod s)) (fun _ => F) 0)))
  have hb : ∀ j ∈ offsets, j ≤ span := by intro j hj; have := hfit j hj; omega
  have hsum : (originAdvances w 0 offsets).sum ≤ span*w := by
    simpa only [Nat.zero_mul,Nat.zero_add] using originAdvances_sum_le w 0 span offsets
      (List.pairwise_cons.mpr ⟨fun _ _ => Nat.zero_le _,hordered⟩) (Nat.zero_le _) hb
  have hcontrolLength : controls.length ≤ span*w+offsets.length+1 := by
    simp only [controls,length_gatherControls,List.sum_append,List.sum_singleton,List.length_append,
      List.length_singleton,originAdvances_length]
    omega
  let e : Fin 117 → Fin 126 := Fin.castLE (by decide)
  have he : Function.Injective e := Fin.castLE_injective (by decide)
  obtain ⟨vi,M,n₁,hui,hn₁,hei,hI,hO,hleft,hR⟩ := preparedOriginAdvanceControls_exec
    (body := fun p : Empty => nomatch p) V w span offsets hwV hcoords hunits hordered hb
    (embDn e v) (embStk e S) suffix hV hw hpackets hcount (by
      intro k hk
      exact hblank (e k) hk) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl
      · exact hfresh 88 (by simp)
      · exact hfresh 89 (by simp)
      · exact hfresh 90 (by simp)
      · exact hfresh 106 (by simp))
  have hM : M = {embStk e S with R := Function.update (embStk e S).R 91 controls} := by
    refine Stacks.ext hI hO hleft ?_
    simpa [embStk,e,controls,hfresh 91 (by simp)] using hR
  rw [hM] at hei
  obtain ⟨v₁,hv₁,hu₁,he₁⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim) he (fun p => nomatch p) hei v rfl S rfl
  let G : Stacks 126 A := {S with R := Function.update S.R 91 controls}
  have he₁' : Exec body (embProg e Empty.elim (preparedNaturalAdvanceControls (P₀ := Empty)))
      (mk v S) n₁ (mk v₁ G) := by
    refine he₁.cast rfl ?_
    apply congrArg (mk v₁)
    rw [embOvr_updR he,embOvr_stk]
    rfl
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := retainedPackedReplicaGather_exec (body := body)
    (show [(121 : Fin 126),122,124,125,110,123,91,1,2,0,92,3,4,5,6,7,8,9,102,94].Nodup by decide)
    origin span L w offsets Fs hne hspan hordered hfit borrowed v₁ G
    (by
      cases ho : offsets with
      | nil => exact (hne ho).elim
      | cons p ps => simpa [G,controls,ho] using localGatherControls_eq A w offsets hne)
    (by simpa [G] using hsource) (by simp [G,hfresh 125 (by simp)]) (by simpa [G] using hreplicas)
    (by simp [G,hfresh 122 (by simp)]) (by simpa [G] using hvolume) (by simpa [G] using hL)
    (by simpa [G] using hw) (by simp [G,hfresh 92 (by simp)]) (by
      intro k hk
      have hkLow : k.val < 10 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have hk91 : k ≠ 91 := by intro he; subst k; norm_num at hkLow
      simpa [G,hk91] using hblank k (by omega))
  let F : Stacks 126 A := {G with R := Function.update G.R 110 (rhs++G.R 110)}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) 91 v₂ F
  have hclock : (F.R 91).length = controls.length := by simp [F,G]
  refine ⟨v₃,n₁+(n₂+(2*controls.length+2)),hu₃.trans (hu₂.trans (hu₁.trans hui)),?_,
    (Exec.seq he₁' (Exec.seq he₂ he₃)).cast (by rw [hclock]) ?_⟩
  · unfold sharedPackedReplicaGatherCost
    omega
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h91 : k = 91 <;> by_cases h110 : k = 110 <;>
      simp [F,G,rhs,h91,h110,hfresh 91 (by simp)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
