module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellComputedClassInputReady

/-! Four geometry words and an external input table suffice for a fresh
numerical class bank. The supplier stream remains free for preparation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedClassBanks
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T A : ℕ}

def inputLivePorts : List ComputedClassBank :=
  [.geometry 32,.geometry 33,.geometry 34,.geometry 35,.control .source]

theorem inputReady_of_raw (bank : ComputedClassBank → Fin T) (hinj : Function.Injective bank)
    (rg : TblR 12 → Fin T) (B D s width radius L : ℕ) (st : TblSt 12 A) (S : Stacks T A)
    (hs : S.R (geometry bank 32) = binSyms B s)
    (hw : S.R (geometry bank 33) = binSyms B width)
    (hr : S.R (geometry bank 34) = binSyms B radius)
    (hL : S.R (geometry bank 35) = binSyms B L)
    (hinput : tblHolds rg S (tblRho D (List.replicate D tick) [] st))
    (hfresh : ∀ i, i ∉ inputLivePorts → S.R (bank i) = [])
    (hleft : ∀ i, S.L (recovery bank (.work i)) = []) :
    InputReady bank hinj rg B D s width radius L st S := by
  have hn (i : RecoveryBank) : S.R (recovery bank i) = [] :=
    hfresh (.recovery i) (by simp [inputLivePorts])
  have hc (i : ComputedClassControl) (hi : i ≠ .source) : S.R (control bank i) = [] :=
    hfresh (.control i) (by simpa [inputLivePorts] using hi)
  have hg (i : Fin 117) (hi : i ∉ [(32 : Fin 117),33,34,35]) : S.R (geometry bank i) = [] :=
    hfresh (.geometry i) (by simpa [inputLivePorts] using hi)
  refine {
    hs := hs, hw := hw, hr := hr, hH := hL
    hz := hg 36 (by decide), htable := ?_
    h104 := hg 104 (by decide), h106 := hg 106 (by decide), h116 := hg 116 (by decide)
    hprepBlank := ?_, hreaderBlank := ?_, hinput := hinput, hinputBlank := ?_
    hscalar := fun i _ => hn (.scalar i), hmasters := fun i => hn (.master i)
    hcontrols := fun i _ => hn (.control i), hleft := hleft
    hblank := fun i => hn (.work i), hsaved := hc .saved (by decide)
    htmp := hc .tmp (by decide), hloopSaved := hc .loopSaved (by decide) }
  · intro i hi
    apply hg
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or,Fin.ext_iff]
    norm_num
    omega
  · intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> apply hc <;> decide
  · intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hc .binary (by decide)
    · exact hn (.parameter 6)
    · exact hn (.parameter 7)
    · exact hc .endpointWork (by decide)
    · exact hc .endpointSaved (by decide)
    · exact hc .endpointTmp (by decide)
  · intro k hk
    simp only [inputRegisters,inputCopies,List.map_map,List.mem_map] at hk
    obtain ⟨r,hr,rfl⟩ := hk
    apply hfresh
    simp only [inputAssignments,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedClassBanks
