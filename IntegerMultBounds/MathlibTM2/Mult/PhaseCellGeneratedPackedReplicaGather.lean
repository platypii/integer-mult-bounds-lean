module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedReplicaGather
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedOriginAdvanceControls

/-! Generate the sweep controls from retained binary packed coordinates, gather
all replica/cell pairs, and retire the controls. Ambient numerical metadata is untouched. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

private theorem packedReplicaControls_eq (A N span w : ℕ) (offsets : List ℕ)
    (hne : packedReplicaSymbolOrigins N span w offsets ≠ []) :
    gatherControls A (originAdvances w 0 (packedReplicaSymbolOrigins N span 1 offsets)++[0]) =
      match packedReplicaSymbolOrigins N span w offsets with
      | [] => [] | p::ps => gatherControls A (p::windowAdvances p ps) := by
  have hm : (packedReplicaSymbolOrigins N span 1 offsets).map (·*w) =
      packedReplicaSymbolOrigins N span w offsets := by
    simp [packedReplicaSymbolOrigins,List.map_flatMap,List.map_map,Function.comp_def]
  rw [originAdvances_symbols,hm]
  cases he : packedReplicaSymbolOrigins N span w offsets with
  | nil => exact (hne he).elim
  | cons p ps => simp [originAdvances,originAdvances_window]

def generatedPackedReplicaGather : Pr P 117 Q A U :=
  .seq preparedNaturalAdvanceControls
    (.seq (naturalGather 110 91 1 2 0 92 3 4 5 6 7 8 9 102 94) (uclear 91))

def generatedPackedReplicaGatherCost (V N span L w B : ℕ) : ℕ :=
  preparedOriginAdvanceCost V (N*span) w (N*B)+
    ((N*B)*(14*L*w+25)+12*(N*span*w)+6*L*w+9*L+29)+
    (2*(N*span*w+N*B+1)+2)

/-- Decoder work is per packet; all source movement is linear in packed volume. -/
theorem generatedPackedReplicaGatherCost_eq (V N span L w B : ℕ) :
    generatedPackedReplicaGatherCost V N span L w B =
      (N*B)*(3*tblC V V+29*V+14*L*w+57)+22*(N*span*w)+
        w*(4*V+10)+76*V+6*L*w+9*L+134 := by
  unfold generatedPackedReplicaGatherCost preparedOriginAdvanceCost
  ring

theorem generatedPackedReplicaGather_exec {s : ℕ} (V N origin span L w : ℕ)
    (offsets : List ℕ) (C : ℕ → ZMod s → GaussianInt)
    (hN : 0 < N) (hne : offsets ≠ []) (hspan : origin+span ≤ s)
    (hordered : offsets.Pairwise (· ≤ ·)) (hfit : ∀ j ∈ offsets, j+L ≤ span)
    (hwV : w < 2^V) (hcoords : N*span < 2^V) (hunits : N*span*w < 2^V)
    (suffix : List (Fin (A+4))) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hV : (S.R 115).length = V) (hw : (S.R 94).length = w) (hL : (S.R 102).length = L)
    (hpackets : S.R 109 = (packedReplicaSymbolOrigins N span 1 offsets).flatMap (binSyms V)++suffix)
    (hcount : S.R 116 = List.replicate (N*offsets.length) tick)
    (hsource : S.R 92 = cstream A w (packedReplicaWords origin span N C))
    (hblank : ∀ k : Fin 117, k.val < 19 → S.R k = [])
    (hfresh : ∀ k ∈ [(88 : Fin 117),89,90,91,104,105,106], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ generatedPackedReplicaGatherCost V N span L w offsets.length ∧
      Exec body generatedPackedReplicaGather (mk v S) n
        (mk v' {S with R := (Function.update S.R 110
          (cstream A w ((List.range N).flatMap (fun r => offsets.flatMap
            (fun j => cellSourceRows L (fun _ => ((origin+j : ℕ) : ZMod s)) C r)))++S.R 110))}) := by
  let coords := packedReplicaSymbolOrigins N span 1 offsets
  let controls := gatherControls A (originAdvances w 0 coords++[0])
  let rhs := cstream A w ((List.range N).flatMap (fun r => offsets.flatMap
    (fun j => cellSourceRows L (fun _ => ((origin+j : ℕ) : ZMod s)) C r)))
  have ho : coords.Pairwise (· ≤ ·) := packedReplicaSymbolOrigins_ordered N span L 1 offsets hordered hfit
  have hb : ∀ p ∈ coords, p ≤ N*span := by
    intro p hp
    have hh := packedReplicaSymbolOrigins_fit N span L 1 offsets hfit p hp
    simp only [Nat.mul_one] at hh
    omega
  have hlen : coords.length = N*offsets.length := packedReplicaSymbolOrigins_length _ _ _ _
  have hnonempty : packedReplicaSymbolOrigins N span w offsets ≠ [] := by
    apply List.ne_nil_of_length_pos
    simpa only [packedReplicaSymbolOrigins_length] using Nat.mul_pos hN (List.length_pos_iff.mpr hne)
  have hcontrols := packedReplicaControls_eq A N span w offsets hnonempty
  have hsum : (originAdvances w 0 coords).sum ≤ N*span*w := by
    simpa only [Nat.zero_mul,Nat.zero_add] using originAdvances_sum_le w 0 (N*span) coords (List.pairwise_cons.mpr ⟨fun _ _ => Nat.zero_le _,ho⟩) (Nat.zero_le _) hb
  have hcontrolLength : controls.length ≤ N*span*w+N*offsets.length+1 := by
    simp only [controls,length_gatherControls,List.sum_append,List.sum_singleton,List.length_append,
      List.length_singleton,originAdvances_length,hlen]
    omega
  obtain ⟨v₁,M,n₁,hu₁,hn₁,he₁,hI,hO,hleft,hR⟩ := preparedOriginAdvanceControls_exec (body := body)
    V w (N*span) coords hwV hcoords hunits ho hb v S suffix hV hw hpackets
    (by simpa only [hlen] using hcount) hblank (by
      intro k hk
      apply hfresh k
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
      rcases hk with rfl | rfl | rfl | rfl <;> simp)
  have hM : M = {S with R := Function.update S.R 91 controls} := by
    exact Stacks.ext hI hO hleft (by simpa only [hfresh 91 (by simp),List.append_nil] using hR)
  subst M
  let G : Stacks 117 A := {S with R := Function.update S.R 91 controls}
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := packedReplicaGather_exec (body := body)
    (show [(110 : Fin 117),91,1,2,0,92,3,4,5,6,7,8,9,102,94].Nodup by decide)
    N origin span L w offsets C hN hne hspan hordered hfit v₁ G
    (by
      cases hsy : packedReplicaSymbolOrigins N span w offsets with
      | nil => exact (hnonempty hsy).elim
      | cons p ps => simpa [G,controls,coords,hsy] using hcontrols)
    (by simpa [G] using hsource) (by simpa [G] using hL) (by simpa [G] using hw) (by
      intro k hk
      have hkLow : k.val < 10 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have hk91 : k ≠ 91 := by intro he; subst k; norm_num at hkLow
      simpa [G,hk91] using hblank k (by omega))
  let F : Stacks 117 A := {G with R := Function.update G.R 110 (rhs++G.R 110)}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) 91 v₂ F
  have hclock : (F.R 91).length = controls.length := by simp [F,G]
  refine ⟨v₃,n₁+(n₂+(2*controls.length+2)),hu₃.trans (hu₂.trans hu₁),?_,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast (by rw [hclock]) ?_⟩
  · rw [hlen] at hn₁
    unfold generatedPackedReplicaGatherCost
    omega
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases h91 : k = 91 <;> by_cases h110 : k = 110 <;>
      simp [F,G,rhs,h91,h110,hfresh 91 (by simp)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
