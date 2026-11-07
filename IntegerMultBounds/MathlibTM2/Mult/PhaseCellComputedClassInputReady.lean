module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComputedClassInput

/-! Ordinary generated-input class facts have a source-stream frame rule.
Exposure may replace that stream without rebuilding readiness proofs. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix
namespace ComputedClassBanks
variable {T A : ℕ}

structure InputReady (bank : ComputedClassBank → Fin T) (hinj : Function.Injective bank)
    (rg : TblR 12 → Fin T) (B D s width radius L : ℕ) (st : TblSt 12 A) (S : Stacks T A) : Prop where
  hs : S.R (geometry bank 32) = binSyms B s
  hw : S.R (geometry bank 33) = binSyms B width
  hr : S.R (geometry bank 34) = binSyms B radius
  hH : S.R (geometry bank 35) = binSyms B L
  hz : S.R (geometry bank 36) = []
  htable : ∀ k : Fin 117, k.val < 31 → S.R (geometry bank k) = []
  h104 : S.R (geometry bank 104) = []
  h106 : S.R (geometry bank 106) = []
  h116 : S.R (geometry bank 116) = []
  hprepBlank : ∀ k ∈ [(control bank .symbols),(control bank .count),(control bank .prepSaved),(control bank .prepTmp)], S.R k = []
  hreaderBlank : ∀ k ∈ [(control bank .binary),(plan bank hinj).master.parameters 6,(plan bank hinj).master.parameters 7,
      (control bank .endpointWork),(control bank .endpointSaved),(control bank .endpointTmp)], S.R k = []
  hinput : tblHolds rg S (tblRho D (List.replicate D tick) [] st)
  hinputBlank : ∀ k ∈ inputRegisters bank, S.R k = []
  hscalar : ∀ i : TblR 25, i ≠ .wr → S.R (recovery bank (.scalar i)) = []
  hmasters : ∀ i, S.R (recovery bank (.master i)) = []
  hcontrols : ∀ i, i ∉ RecoveryBanks.liveControls → S.R (recovery bank (.control i)) = []
  hleft : ∀ i, S.L (recovery bank (.work i)) = []
  hblank : ∀ i, S.R ((plan bank hinj).work i) = []
  hsaved : S.R (control bank .saved) = []
  htmp : S.R (control bank .tmp) = []
  hloopSaved : S.R (control bank .loopSaved) = []

namespace InputReady
variable {bank : ComputedClassBank → Fin T} {hinj : Function.Injective bank}
  {rg : TblR 12 → Fin T} {B D s width radius L : ℕ} {st : TblSt 12 A} {S F : Stacks T A}

/-- External routing registers may change; only the numerical bank and retained
scalar table are observed by readiness. -/
theorem of_bank_frame (h : InputReady bank hinj rg B D s width radius L st S)
    (hbank : ∀ k : ComputedClassBank, k ≠ .control .source → F.R (bank k) = S.R (bank k))
    (htable : ∀ r, F.R (rg r) = S.R (rg r))
    (hL : ∀ i, F.L (recovery bank (.work i)) = S.L (recovery bank (.work i))) :
    InputReady bank hinj rg B D s width radius L st F := by
  have hg (i : Fin 117) : F.R (geometry bank i) = S.R (geometry bank i) :=
    hbank (.geometry i) (by intro he; cases he)
  have hn (i : RecoveryBank) : F.R (recovery bank i) = S.R (recovery bank i) :=
    hbank (.recovery i) (by intro he; cases he)
  have hc (i : ComputedClassControl) (hi : i ≠ .source) : F.R (control bank i) = S.R (control bank i) :=
    hbank (.control i) (by intro he; exact hi (ComputedClassBank.control.inj he))
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hg]; exact h.hs
  · rw [hg]; exact h.hw
  · rw [hg]; exact h.hr
  · rw [hg]; exact h.hH
  · rw [hg]; exact h.hz
  · intro k hk; rw [hg]; exact h.htable k hk
  · rw [hg]; exact h.h104
  · rw [hg]; exact h.h106
  · rw [hg]; exact h.h116
  · intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    all_goals rw [hc _ (by decide)]; exact h.hprepBlank _ (by simp)
  · intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (rw [hc _ (by decide)]; exact h.hreaderBlank _ (by simp [plan,RecoveryBanks.plan,RecoveryBanks.masterPlan]))
      | (change F.R (recovery bank _) = []; rw [hn]; exact h.hreaderBlank _ (by simp [plan,RecoveryBanks.plan,RecoveryBanks.masterPlan]))
  · change ∀ r : TblR 12, F.R (rg r) = tblRho D (List.replicate D tick) [] st r
    intro r; rw [htable]; exact h.hinput r
  · intro k hk
    have hregs : inputRegisters bank = (inputAssignments.map Prod.snd).map bank := by
      simp only [inputRegisters,inputCopies,List.map_map,Function.comp_def]
    rw [hregs] at hk
    obtain ⟨role,hrole,rfl⟩ := List.mem_map.mp hk
    have hne : role ≠ .control .source := by
      intro he
      subst role
      simp [inputAssignments] at hrole
    rw [hbank role hne]
    exact h.hinputBlank _ (by rw [hregs]; exact List.mem_map.mpr ⟨role,hrole,rfl⟩)
  · intro i hi; rw [hn]; exact h.hscalar i hi
  · intro i; rw [hn]; exact h.hmasters i
  · intro i hi; rw [hn]; exact h.hcontrols i hi
  · intro i; rw [hL]; exact h.hleft i
  · intro i; change F.R (recovery bank (.work i)) = []; rw [hn]; exact h.hblank i
  · rw [hc .saved (by decide)]; exact h.hsaved
  · rw [hc .tmp (by decide)]; exact h.htmp
  · rw [hc .loopSaved (by decide)]; exact h.hloopSaved

theorem of_frame (h : InputReady bank hinj rg B D s width radius L st S)
    (hR : ∀ k, k ≠ control bank .source → F.R k = S.R k)
    (hL : ∀ i, F.L (recovery bank (.work i)) = S.L (recovery bank (.work i)))
    (hRg : ∀ r, rg r ≠ control bank .source) : InputReady bank hinj rg B D s width radius L st F := by
  exact h.of_bank_frame
    (fun k hk => hR _ (by intro he; exact hk (hinj he)))
    (fun r => hR _ (hRg r)) hL

end InputReady
end ComputedClassBanks
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
