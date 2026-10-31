module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreGatherPayload

/-! Generate, execute and retire a whole movement-class sweep. Only the packed
payload archive changes; all geometry, source and controller storage returns. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix
variable {Q A : ℕ} {U P : Type} {body : P → Pr P 168 Q A U}

def restoredCoreGather : Pr P 168 Q A U :=
  .seq initializedCoreGather (clearWords [91,109,116])

def restoredCoreGatherCost (V s width radius L w : ℕ) : ℕ :=
  initializedCoreGatherCost V s width radius L w+
    (2*(s*w+(coreGatherIndices s width radius L).length*(V+2)+1)+7)

theorem restoredCoreGather_exec {V s width radius L w : ℕ}
    (hwidth : 0 < width) (hwide : s+width+2*radius < 2^V) (hLfit : L < 2^V)
    (hwV : w < 2^V) (hvol : s*w < 2^V) (hA : 4 ≤ A) (hVpos : 0 < V)
    (hgroup : 0 < (coreGatherIndices s width radius L).length)
    (C : ZMod s → GaussianInt) (v : HS 168 Q A U) (S : Stacks 168 A)
    (h163 : (S.R 163).length = V) (h115 : S.R 115 = []) (h103 : S.R 103 = []) (h105 : S.R 105 = [])
    (hs : S.R 145 = binSyms V s) (hw : S.R 150 = binSyms V width)
    (hr : S.R 152 = binSyms V radius) (hL : S.R 165 = binSyms V L) (hz : S.R 154 = [])
    (hblank : ∀ k : Fin 168, k.val < 31 → S.R k = [])
    (h104 : S.R 104 = []) (h106 : S.R 106 = []) (h116 : S.R 116 = [])
    (hsource : S.R 110 = cstream A w (chirpLine s C))
    (hword : (S.R 94).length = w) (hcontrol : S.R 91 = []) (horigin : S.R 109 = [])
    (hclean : ∀ k ∈ [(92 : Fin 168),93,95,96,97,98,99,100,101,102], S.R k = [])
    (hfresh : ∀ k ∈ [(88 : Fin 168),89,90], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ restoredCoreGatherCost V s width radius L w ∧
      Exec body restoredCoreGather (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R 108
          (cstream A w (coreGatherPayload width radius L [C]) ++ S.R 108))}) := by
  obtain ⟨v₁,F,n,hu,hn,he,hi,ho,hl,hpayload,hc,horigins,hcount,hframe⟩ :=
    initializedCoreGather_payload_exec (body := body) hwidth hwide hLfit hwV hvol hA hVpos hgroup
      C v S h163 h115 h103 h105 hs hw hr hL hz hblank h104 h106 h116 hsource hword hcontrol hclean hfresh
  obtain ⟨v₂,hu₂,he₂⟩ := clearWords_exec (body := body) [(91 : Fin 168),109,116] (by decide) v₁ F
  have horiginLength : (F.R 109).length = (coreGatherIndices s width radius L).length*V := by
    rw [horigins,horigin,List.append_nil,List.length_flatMap]
    simp only [length_binSyms,List.map_const',List.sum_replicate,smul_eq_mul]
  have hcontrolLength := coreGatherControls_length_le A s width radius L w hgroup
  have hsum : (([(91 : Fin 168),109,116]).map (fun k => (F.R k).length)).sum ≤
      s*w+(coreGatherIndices s width radius L).length*(V+2)+1 := by
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
    rw [hc,horiginLength,hcount,List.length_replicate]
    have heq : (coreGatherIndices s width radius L).length*(V+2) =
        (coreGatherIndices s width radius L).length*V+2*(coreGatherIndices s width radius L).length := by ring
    rw [heq]
    omega
  refine ⟨v₂,n+(2*(([(91 : Fin 168),109,116]).map (fun k => (F.R k).length)).sum+7),
    hu₂.trans hu,?_,(Exec.seq he he₂).cast rfl ?_⟩
  · dsimp only [restoredCoreGatherCost]
    omega
  · apply congrArg (Host.mk v₂)
    refine Stacks.ext hi ho hl ?_
    funext k
    by_cases h108 : k = 108
    · subst k
      simpa using hpayload
    by_cases h91 : k = 91
    · subst k
      simp [hcontrol]
    by_cases h109 : k = 109
    · subst k
      simp [horigin]
    by_cases h116 : k = 116
    · subst k
      simp [h116]
    simp only [List.mem_cons,List.not_mem_nil,h91,h109,h116,or_self,ite_false,
      Function.update_of_ne h108]
    exact hframe k h108 h91 h109 h116

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
