module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedLengthKey
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedGroupHeaders

/-! One generated key supplies both length representations and the exact native
input bank. The remaining queue and caller-owned high registers survive. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def keyedPackedHaloInput : Pr P 168 Q A U := .seq packedLengthKey packedHaloGroupInput

theorem keyedPackedHaloInput_exec {V s t band a b origin K L precision stage q l u : ℕ} [NeZero s]
    (hst : s < t) (hband : band ≤ s) (hab : a ≤ b) (hb : b ≤ s)
    (hL : 0 < L) (hLs : L ≤ s) (hkey : L < 2^V) (hA : 4 ≤ A)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V)
    (hVeq : V = weightWorkspaceWidth precision q (2*q+8) t u)
    (borrowed suffix : List (Fin (A+4))) (v : HS 168 Q A U) (S : Stacks 168 A)
    (hmasters : ∀ r ∈ groupHeaderCopies, r.1 ≠ 128 →
      (S.R (packedHeaderReg r.1)).length = groupHeaderValue precision stage q l s t u band L r.1)
    (h133 : S.R 133 = [])
    (hleft : ∀ k : Fin 168, k.val < 117 → S.L k = [])
    (hblank : ∀ k : Fin 168, k.val < 117 → k ≠ 93 → k ≠ 110 → S.R k = [])
    (hsource : S.R 110 = borrowed)
    (hmeta : CouplingIntervalMetadata V s t band a b origin K S)
    (hwidth : (S.R 125).length = V) (hkeys : S.R 126 = binSyms V L++suffix)
    (hfresh : ∀ k ∈ [(134 : Fin 168),135,136], S.R k = []) :
    ∃ v' F m, v'.user = v.user ∧
      m ≤ (2*(S.R 128).length+2*(S.R 157).length+6*L+17*V+16)+
        installGroupHeadersCost precision stage q l s t u band L+binaryHaloClassCost V s t band a b L ∧
      Exec body keyedPackedHaloInput (mk v S) m (mk v' F) ∧
      embStk packedCellCoreReg F = batchInputBank precision stage q l s t u band L
        (haloPackedOffsets s t band a b L).length
        (fun n => (packedCellOrigin (s := s) a (haloPackedOffsets s t band a b L) n).val)
        [] borrowed (S.R 93) S.inp S.out ∧
      F.R 126 = suffix ∧ F.R 128 = List.replicate L tick ∧ F.R 157 = binSyms V L ∧
      (∀ k : Fin 168, 117 ≤ k.val → k ≠ 126 → k ≠ 128 → k ≠ 157 →
        F.L k = S.L k ∧ F.R k = S.R k) ∧ F.L = S.L := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := packedLengthKey_exec (body := body) V L hkey suffix v S hwidth hkeys hfresh
  let B : Stacks 168 A := {S with R := (Function.update (Function.update (Function.update S.R
    126 suffix) 128 (List.replicate L tick)) 157 (binSyms V L))}
  have hoff (k : Fin 168) (h126 : k ≠ 126) (h128 : k ≠ 128) (h157 : k ≠ 157) : B.R k = S.R k := by
    simp [B,h126,h128,h157]
  have hmasterB : ∀ r ∈ groupHeaderCopies, (B.R (packedHeaderReg r.1)).length =
      groupHeaderValue precision stage q l s t u band L r.1 := by
    intro r hr
    by_cases h128 : r.1 = 128
    · simp [B,h128,packedHeaderReg,groupHeaderValue]
    · have h126 : packedHeaderReg r.1 ≠ 126 := by
        simp only [groupHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have h157 : packedHeaderReg r.1 ≠ 157 := by
        intro he; have hv := congrArg (fun k : Fin 168 => k.val) he
        have hh := r.1.isLt
        change r.1.val = 157 at hv
        omega
      rw [hoff _ h126 (fun he => h128 (Fin.ext (congrArg (fun k : Fin 168 => k.val) he))) h157]
      exact hmasters r hr h128
  have hmetaB : CouplingIntervalMetadata V s t band a b origin K B := by
    constructor
    · rw [hoff 163 (by decide) (by decide) (by decide)]; exact hmeta.width
    · intro k hk
      have hn : k ≠ 126 ∧ k ≠ 128 ∧ k ≠ 157 := by
        simp only [couplingIntervalPorts,List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [hoff k hn.1 hn.2.1 hn.2.2]; exact hmeta.encoded k hk
  obtain ⟨v₂,F,m₂,hu₂,hm₂,he₂,hbank,hframe⟩ := packedHaloGroupInput_exec (body := body)
    hst hband hab hb hL hLs hA hwide hVeq borrowed v₁ B hmasterB
    (by simpa [B] using h133) hleft
    (by
      intro k hk h93 h110
      have hn126 : k ≠ 126 := by intro he; subst k; norm_num at hk
      have hn128 : k ≠ 128 := by intro he; subst k; norm_num at hk
      have hn157 : k ≠ 157 := by intro he; subst k; norm_num at hk
      rw [hoff k hn126 hn128 hn157]; exact hblank k hk h93 h110)
    (by simpa [B] using hsource) hmetaB (by simp [B])
  have hleftAll : F.L = S.L := by
    apply packedCell_left_eq
    · intro i
      have hF : F.L (packedCellCoreReg i) = [] := by
        simpa [embStk,batchInputBank] using congrArg (fun B : Stacks 117 A => B.L i) hbank
      exact hF.trans (hleft _ i.isLt).symm
    · intro k hk
      exact (hframe k hk).1
  refine ⟨v₂,F,m₁+m₂,hu₂.trans hu₁,by omega,Exec.seq he₁ he₂,?_,?_,?_,?_,?_,hleftAll⟩
  · simpa [B] using hbank
  · simpa [B] using (hframe 126 (by decide)).2
  · simpa [B] using (hframe 128 (by decide)).2
  · simpa [B] using (hframe 157 (by decide)).2
  · intro k hk h126 h128 h157
    simpa only [B,Function.update_of_ne h126,Function.update_of_ne h128,Function.update_of_ne h157]
      using hframe k hk

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
