module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedBatchWeightSetup
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaFactoryDimensions
public import IntegerMultBounds.MathlibTM2.Host.ClosedProgramStock

/-! Generate one complete numerical weight page from ordinary headers and binary
origins, then convert its counters for replica-cache installation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def generateReplicaWeightPage : Pr P₀ 117 Q A U :=
  .seq sharedBatchWeightSetup prepareReplicaFactoryDimensions

def generateReplicaWeightPageCost (N P s t u q L w B : ℕ) : ℕ :=
  sharedBatchWeightSetupCost P s t u q L w B+prepareReplicaFactoryDimensionsCost N B L

theorem generateReplicaWeightPage_exec (N P s t u q L w B : ℕ) (lo : ℕ → ℕ)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tail : List (Fin (A+4)))
    (hN : S.R 113 = List.replicate N tick)
    (hP' : (S.R 114).length = P) (hs' : (S.R 97).length = s) (ht' : (S.R 98).length = t)
    (hu' : (S.R 99).length = u) (hq : (S.R 112).length = q)
    (hL' : (S.R 102).length = L) (hrows : (S.R 103).length = L)
    (hw : (S.R 94).length = w) (hB : S.R 116 = List.replicate B tick)
    (hpacket : S.R 109 = (List.range B).flatMap
      (fun i => binSyms (weightWorkspaceWidth P q w t u) (lo i)) ++ tail)
    (hblank : ∀ r, S.R (coefficientReg r) = [])
    (hfresh : ∀ k ∈ [(64 : Fin 117), 65, 96, 104, 105, 106, 107, 108, 111, 115], S.R k = [])
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hlo : ∀ i < B, lo i < s) (hL : L ≤ s) :
    ∃ v' m, v'.user = v.user ∧ m ≤ generateReplicaWeightPageCost N P s t u q L w B ∧
      Exec body generateReplicaWeightPage (mk v S) m
        (mk v' (replicaFactoryDimensionsBank { S with R := (Function.update (Function.update S.R 109 tail)
          110 (batchWeightPage A w q P s t u B L lo ++ S.R 110)) } N B L)) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := sharedBatchWeightSetup_exec (body := body)
    P s t u q L w B lo v S tail hP' hs' ht' hu' hq hL' hrows hw (by simp [hB]) hpacket hblank hfresh
    hP hs hst hu hlo hL
  let W : Stacks 117 A := { S with R := (Function.update (Function.update S.R 109 tail)
    110 (batchWeightPage A w q P s t u B L lo ++ S.R 110)) }
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := prepareReplicaFactoryDimensions_exec (body := body) N B L v₁ W
    (by simpa [W] using hN)
    (by simpa [W] using hB)
    (by simpa [W] using hrows)
    (by simpa [W] using hfresh 64 (by simp))
    (by simpa [W] using hfresh 115 (by simp))
    (by simpa [W] using hfresh 104 (by simp))
    (by simpa [W] using hfresh 105 (by simp))
  exact ⟨v₂,m₁+m₂,hu₂.trans hu₁,Nat.add_le_add hm₁ hm₂,Exec.seq he₁ he₂⟩

theorem generateReplicaWeightPage_exec_within (N P s t u q L w B : ℕ) (lo : ℕ → ℕ)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tail : List (Fin (A+4)))
    (hN : S.R 113 = List.replicate N tick)
    (hP' : (S.R 114).length = P) (hs' : (S.R 97).length = s) (ht' : (S.R 98).length = t)
    (hu' : (S.R 99).length = u) (hq : (S.R 112).length = q)
    (hL' : (S.R 102).length = L) (hrows : (S.R 103).length = L)
    (hw : (S.R 94).length = w) (hB : S.R 116 = List.replicate B tick)
    (hpacket : S.R 109 = (List.range B).flatMap
      (fun i => binSyms (weightWorkspaceWidth P q w t u) (lo i)) ++ tail)
    (hblank : ∀ r, S.R (coefficientReg r) = [])
    (hfresh : ∀ k ∈ [(64 : Fin 117), 65, 96, 104, 105, 106, 107, 108, 111, 115], S.R k = [])
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hlo : ∀ i < B, lo i < s) (hL : L ≤ s) (depth : ℕ) :
    ∃ v' m, v'.user = v.user ∧ m ≤ generateReplicaWeightPageCost N P s t u q L w B ∧
      ExecWithin (fun p : Empty => nomatch p) (fun level z => mnSize z+level ≤ mnSize (mk v S)+depth+
        mnProgPush (generateReplicaWeightPage (P₀ := Empty) (Q := Q) (A := A) (U := U))*
          generateReplicaWeightPageCost N P s t u q L w B)
        depth generateReplicaWeightPage (mk v S) m
        (mk v' (replicaFactoryDimensionsBank { S with R := (Function.update (Function.update S.R 109 tail)
          110 (batchWeightPage A w q P s t u B L lo ++ S.R 110)) } N B L)) := by
  obtain ⟨v',m,hu',hm,he⟩ := generateReplicaWeightPage_exec
    (body := fun p : Empty => nomatch p) N P s t u q L w B lo v S tail hN
    hP' hs' ht' hu' hq hL' hrows hw hB hpacket hblank hfresh hP hs hst hu hlo hL
  exact ⟨v',m,hu',hm,mn_native_exec_within he _ (WordCmd.empty_native _) depth _
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ hm) _)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
