module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAllocatedExposureBank

/-! Derive exposure readiness from six live headers, two unary counters and a
fresh private suffix. All register separation follows from allocation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
variable {T A : ℕ}

def exposureLivePorts : List (Fin 175) := [145,150,152,165,163,94,168,173]

def allocatedExposureReady (input output : Fin T) (hne : input ≠ output)
    (V s width radius L w : ℕ) (Fs : List (ZMod s → GaussianInt))
    (borrowed : List (Fin (A+4))) (S : Stacks (T+175) A)
    (hwidth : 0 < width) (hwide : s+width+2*radius < 2^V) (hLfit : L < 2^V)
    (hwV : w < 2^V) (hvol : s*w < 2^V) (hA : 4 ≤ A) (hVpos : 0 < V)
    (hgroup : 0 < (coreGatherIndices s width radius L).length)
    (hV : (S.R (Fin.natAdd T 163)).length = V)
    (hs : S.R (Fin.natAdd T 145) = binSyms V s)
    (hw : S.R (Fin.natAdd T 150) = binSyms V width)
    (hr : S.R (Fin.natAdd T 152) = binSyms V radius)
    (hL : S.R (Fin.natAdd T 165) = binSyms V L)
    (hword : (S.R (Fin.natAdd T 94)).length = w)
    (hcount : (S.R (Fin.natAdd T 168)).length = s*w)
    (hreplicas : (S.R (Fin.natAdd T 173)).length = Fs.length)
    (hsource : S.R (Fin.castAdd 175 input) = Fs.flatMap (fun C => cstream A w (chirpLine s C))++borrowed)
    (hblank : ∀ i, i ∉ exposureLivePorts → S.R (Fin.natAdd T i) = []) :
    RealGatherExposureData V s width radius L w Fs borrowed S := by
  have hfresh (i : Fin 168) (hi : i ∉ [(145 : Fin 168),150,152,165,163,94,108]) :
      S.R (exposurePlacement output i) = [] := by
    have hout : i ≠ 108 := by
      intro he; subst i; simp at hi
    rw [exposurePlacement_private output i hout]
    apply hblank
    simp only [exposureLivePorts,List.mem_cons,List.not_mem_nil,or_false,not_or,Fin.ext_iff] at hi ⊢
    have := i.isLt
    simp only [Fin.val_castAdd]
    norm_num at hi ⊢
    omega
  have hcontrol (j : Fin 7) (hj : j ∉ [(0 : Fin 7),1,5]) :
      S.R (exposureControl input j) = [] := by
    have hj1 : j ≠ 1 := by intro he; subst j; simp at hj
    rw [exposureControl_private input j hj1]
    apply hblank
    simp only [exposureLivePorts,List.mem_cons,List.not_mem_nil,or_false,not_or,Fin.ext_iff] at hj ⊢
    have := j.isLt
    simp only [Fin.val_natAdd]
    norm_num at hj ⊢
    omega
  refine {
    e := exposurePlacement output, he := exposurePlacement_injective output
    count := exposureControl input 0, source := exposureControl input 1
    archive := exposureControl input 2, saved := exposureControl input 3
    tmp := exposureControl input 4, replicas := exposureControl input 5
    savedReplicas := exposureControl input 6
    hreg := exposureControls_nodup input
    hsep := ?_
    hwidth := hwidth, hwide := hwide, hLfit := hLfit, hwV := hwV, hvol := hvol
    hA := hA, hVpos := hVpos, hgroup := hgroup
    h163 := by simpa [exposurePlacement,redirectRegister,Fin.castAdd,Fin.natAdd] using hV
    hs := by simpa [exposurePlacement,redirectRegister,Fin.castAdd,Fin.natAdd] using hs
    hw := by simpa [exposurePlacement,redirectRegister,Fin.castAdd,Fin.natAdd] using hw
    hr := by simpa [exposurePlacement,redirectRegister,Fin.castAdd,Fin.natAdd] using hr
    hL := by simpa [exposurePlacement,redirectRegister,Fin.castAdd,Fin.natAdd] using hL
    hword := by simpa [exposurePlacement,redirectRegister,Fin.castAdd,Fin.natAdd] using hword
    hcount := by simpa [exposureControl,redirectRegister,Fin.castAdd,Fin.natAdd] using hcount
    hreplicas := by simpa [exposureControl,redirectRegister,Fin.castAdd,Fin.natAdd] using hreplicas
    hsource := by simpa only [exposureControl_input] using hsource
    h115 := hfresh 115 (by decide), h103 := hfresh 103 (by decide)
    h105 := hfresh 105 (by decide), hz := hfresh 154 (by decide), hblank := ?_
    h104 := hfresh 104 (by decide), h106 := hfresh 106 (by decide), h116 := hfresh 116 (by decide)
    harchive := hcontrol 2 (by decide), hsavedReplicas := hcontrol 6 (by decide)
    hlocal := hfresh 110 (by decide), hsaved := hcontrol 3 (by decide), htmp := hcontrol 4 (by decide)
    hcontrol := hfresh 91 (by decide), horigin := hfresh 109 (by decide), hclean := ?_, hfresh := ?_ }
  · intro k hk i
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact exposureControl_off_placement input output hne _ i
  · intro i hi
    apply hfresh
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or,Fin.ext_iff]
    norm_num
    omega
  · intro i hi
    apply hfresh
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro i hi
    apply hfresh
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl <;> decide

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
