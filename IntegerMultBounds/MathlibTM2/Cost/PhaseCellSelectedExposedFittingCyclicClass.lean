module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedFittingCyclicClass
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExposeCyclicClassQueue
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareCyclicClassOrigins

/-! Execute one fitting class with the concrete generated callback. Ordinary
headers and blank workspace survive each iteration; numerical seeds do not. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement CyclicComplexCallerLayout
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {T Q K : ℕ} {P U : Type} {body : P → Pr P T Q (prime+K) U}

theorem selectedExposedFittingCyclicClass_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ prime+K)
    (ct cW cV cZ : ℕ) (hcZ : 1 ≤ cZ) :
    let b := 8*executionPush (A := (prime+K)) (U := U) hR hQ+1
    ∃ B₀ : ℝ, 0 ≤ B₀ ∧ ∀ᶠ m : ℕ in atTop, ∀ (_h : Sizes.Big m) (i : Fin (Sizes.d m)) [NeZero (Sizes.s m i)],
    ∀ (ports : CyclicComplexCallerLayout T) (g : CyclicSeedLayout T)
      (dst width origins binary work readerSaved readerTmp count saved : Fin T),
    ports.seedL = g.left → ports.seedR = g.right →
    (∀ r ∈ ports.fixedControls, ∀ j, g.masters j ≠ r) →
    (∀ j, ports.bank j ≠ dst) → dst ≠ ports.archive → (∀ j, g.masters j ≠ dst) →
    [count,saved,origins,ports.archive,dst].Nodup →
    [width,ports.span,origins,binary,g.source 6,g.source 7,work,readerSaved,readerTmp].Nodup →
    (∀ r, g.retained r → origins ≠ r ∧ g.source 6 ≠ r ∧ g.source 7 ≠ r) →
    (∀ r, ports.generatedReaderProtected dst r → r ≠ origins ∧ r ≠ g.source 6 ∧ r ≠ g.source 7) →
    (∀ r, ports.classProtected g width binary work readerSaved readerTmp r → r ≠ count ∧ r ≠ saved) →
    (∀ r, ports.classProtected g width binary work readerSaved readerTmp r →
      r ≠ origins ∧ r ≠ ports.archive ∧ r ≠ dst) →
    let p := Sizes.p m
    let s := Sizes.s m i
    let t := Sizes.t m i
    let l := haloInverseRingLog s t
    ∀ (B u target n coreWidth depth W V : ℕ) (α d : ℝ)
      (axis : RecoveryAxisBounds s t p u l α d) (hn : n ≤ s),
    let radius := depth*PhaseCellBand.width p u
    let jobs := coreGatherIndices s coreWidth radius n
    let cs := jobs.attach
    let index := fun c : {k // k ∈ jobs} => c.val
    let a := fun c : {k // k ∈ jobs} => coreStart coreWidth c.val-radius
    let ha := fun c : {k // k ∈ jobs} => coreGatherOrigin_lt c.property

    0 < coreWidth → coreWidth ≤ s → radius ≤ coreWidth →
    s/(t-s)+1 ≤ coreWidth → p^2+(PhaseCellBand.width p u)^2 ≤ coreWidth →
    u ≤ p → target ≤ ct*p → B ≤ cZ*p → l ≤ cZ*p → target ≤ cZ*p →
    PhaseCellBand.width p u ≤ cZ*p →
    64*(p+1)+u < 2^B → 8*(t+1)^2+2*PhaseCellBand.width p u+8 < 2^B →
    (∀ c ∈ cs, min n (s-a c)+PhaseCellBand.width p u ≤ s ∧
      n-min n (s-a c)+PhaseCellBand.width p u ≤ s) →
    (∀ c ∈ cs, inversePrecisionRoom p l target
      (haloBoundary s t (PhaseCellBand.width p u) (a c) (a c+n)).card (PhaseCellBand.width p u) < 2^B) →
    (∀ c ∈ cs, ∀ j : Fin 8, ![p,u,l,target,s,t,a c,a c+n] j < 2^B) →
    let boundary := fun c => cyclicPrincipalBoundary s t (PhaseCellBand.width p u) (a c) n
    let solveTarget := boundaryRecoveryTarget p (target+1)
    let stage := fun c => initialSchurTarget p u (boundaryTableBits p solveTarget 2 (boundary c).card) 2
    ∀ (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs.reverse, ∀ j, ‖value p (F j)‖ ≤ 1),
    2*p+13 ≤ W → (∀ c ∈ cs, executionWidth p l (stage c) 2 ≤ W) → W ≤ cW*p → V ≤ cV*p →
    (∀ c ∈ cs, a c < 2^V) →
    ∀ (localityTarget qRef : ℕ) (Y : (ZMod s → GaussianInt) → ZMod s → ℝ), p+1 ≤ qRef →
    (∀ c ∈ cs, cyclicPrincipalVertices s (a c) n =
      (PhaseCellInterface.generatedWindow s coreWidth p u localityTarget (index c)).halo) →
    (∀ F ∈ complexComponentFields Fs.reverse, SchurDominance.Solves (realMatrix s t p u) Finset.univ (Y F)
      (fun j => (value qRef ((2 : GaussianInt)^(qRef-p-1)*F j)).re)) →
    ∀ (v : HS T Q (prime+K) U) (S : Stacks T (prime+K)) (borrowed : List (Fin (prime+K+4)))
      (Vg replicasBits D : ℕ)
      (gather : GeometryRealGatherData (Q := Q) Vg s coreWidth radius n W replicasBits D Fs borrowed S),
    gather.route (PackedTranspose.extra 1) = ports.archive →
    ports.ClassReady g width binary work readerSaved readerTmp B p u l target s t W V Fs.length n radius (n-2*radius) S →
    S.R count = [] → S.R saved = [] →
    ∀ (e : Fin 117 → Fin T), Function.Injective e → e 109 = origins → e 116 = count →
    s+coreWidth+2*radius < 2^V → n < 2^V → 0 < V →
    (∀ j ∈ [(37 : Fin 117),32,33,34,35,36,104,106,116], e j ≠ ports.archive) →
    (∀ j : Fin 117, j.val < 31 → e j ≠ ports.archive) →
    (S.R (e 37)).length = V → S.R (e 32) = binSyms V s → S.R (e 33) = binSyms V coreWidth →
    S.R (e 34) = binSyms V radius → S.R (e 35) = binSyms V n → S.R (e 36) = [] →
    (∀ j : Fin 117, j.val < 31 → S.R (e j) = []) → S.R (e 104) = [] → S.R (e 106) = [] →
    ∃ v', ∃ steps : ℕ, ∃ outputs, v'.user = v.user ∧
      (steps : ℝ) ≤ (gather.timeCost : ℝ)+(preparedCoreOriginsCost V s coreWidth radius n : ℝ)+(2*jobs.length+3 : ℕ)+ (8*(b : ℝ)+3)*(Sizes.T m : ℝ)+B₀*(2*(Fs.length : ℝ)+1)*
        ((t : ℝ)*(1+(PhaseCellBand.width p u : ℝ)^2/(Sizes.d m : ℝ)))*(p : ℝ)^(129/128 : ℝ) ∧
      List.Forall₂ (fun k word => PackedNormalizedOutput p W target coreWidth k localityTarget Fs.reverse Y word) jobs outputs ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+0+
        (gather.stockAllowance+(3*preparedCoreOriginsCost V s coreWidth radius n+
          (fittingCyclicWorkspaceTrafficFactor (A := (prime+K)) (U := U) hR hQ ct cW*Fs.length*t*p+45*Sizes.T m)))) 0
        (.seq gather.program (.seq (placedCoreOrigins e)
          (.seq (scanP count saved (ports.generatedOriginProgram g dst width origins binary work readerSaved readerTmp hR hQ))
            (clearWords [count]))))
        (Host.mk v S) steps (Host.mk v' {S with R := Function.update S.R dst (outputs.reverse.flatten++S.R dst)}) := by
  classical
  dsimp only
  obtain ⟨B₀,hB₀,hclass⟩ := selectedFittingCyclicClass_exec (T := T) (A := (prime+K)) (U := U) (body := body)
    hR hQ hA ct cW cV cZ hcZ
  refine ⟨B₀,hB₀,?_⟩
  filter_upwards [hclass] with m hclass
  intro h i _ ports g dst width origins binary work readerSaved readerTmp count saved
    hwireL hwireR hfixed hdst harchiveDst hmastersDst hreg hreader hretained hprotected hcounter hconsume
    B u target n coreWidth depth W V α d axis hn hw hwidth hguard hcell hprepare
    hu htarget hB hl htargetMax hbandMax hbandRoom hgeometryRoom hrooms hprecisionRoom hvaluesFit
    Fs hF hW hWin hWmax hVmax hfit localityTarget qRef Y hqRef hwindow hY
    v S borrowed Vg replicasBits D gather harchive ready hcountBlank hsaved
    e he h109 h116 hwide hnfit hV hmetaOff htableOff h37 hs hcw hr hnSrc hz hblank h104 h106
  let p := Sizes.p m
  let s := Sizes.s m i
  let t := Sizes.t m i
  let l := haloInverseRingLog s t
  let radius := depth*PhaseCellBand.width p u
  let jobs := coreGatherIndices s coreWidth radius n
  let payload := jobs.attach.flatMap (fun c => cstream (prime+K) W
    (Fs.reverse.map (packedInterval (coreStart coreWidth c.val-radius) n)).flatten)
  let M : Stacks T (prime+K) := {S with R := Function.update S.R ports.archive payload}
  obtain ⟨vm,nm,hum,htm,hem,readyM,hpayload⟩ := ports.exposeCyclicClassQueue_exec (body := body) g
    width binary work readerSaved readerTmp Fs borrowed v S gather harchive
    (by intro r hr; exact (hconsume r hr).2.1) ready
  have hM (r) (hr : r ≠ ports.archive) : M.R r = S.R r := Function.update_of_ne hr _ _
  have hmeta (j : Fin 117) (hj : j ∈ [(37 : Fin 117),32,33,34,35,36,104,106,116]) := hM (e j) (hmetaOff j hj)
  obtain ⟨vi,ni,hui,hti,hei,readyE,hloopCount⟩ := ports.prepareCyclicClassOrigins_exec (body := body) g e he
    width binary work readerSaved readerTmp
    (by intro r hr; simpa only [h109,h116] using ⟨(hconsume r hr).1,(hcounter r hr).1⟩)
    hw hwide hnfit (by omega) hV vm M readyM
    (by rw [hmeta _ (by simp)]; exact h37) (by rw [hmeta _ (by simp)]; exact hs)
    (by rw [hmeta _ (by simp)]; exact hcw) (by rw [hmeta _ (by simp)]; exact hr)
    (by rw [hmeta _ (by simp)]; exact hnSrc) (by rw [hmeta _ (by simp)]; exact hz)
    (by intro j hj; rw [hM _ (htableOff j hj)]; exact hblank j hj)
    (by rw [hmeta _ (by simp)]; exact h104) (by rw [hmeta _ (by simp)]; exact h106)
    (by rw [hmeta _ (by simp),h116]; exact hcountBlank)
  let E : Stacks T (prime+K) := {M with R := (Function.update (Function.update M.R origins
    (jobs.attach.flatMap (fun c => binSyms V (coreStart coreWidth c.val-radius))++M.R origins))
    count (List.replicate jobs.length tick))}
  rw [h109,h116] at hei readyE hloopCount
  have hregs := hreg
  regs_ne hregs
  obtain ⟨vf,nf,outputs,huf,htf,hfast,hcert,hwitness,hef⟩ := hclass h i ports g dst width origins binary work readerSaved readerTmp count saved
    hwireL hwireR hfixed hdst harchiveDst hmastersDst hreg hreader hretained hprotected hcounter hconsume
    B u target n coreWidth depth W V α d axis hn hw hwidth hguard hcell hprepare
    hu htarget hB hl htargetMax hbandMax hbandRoom hgeometryRoom hrooms hprecisionRoom hvaluesFit
    Fs.reverse hF hW hWin hWmax hVmax hfit localityTarget qRef Y hqRef hwindow hY
    vi E (S.R origins) [] (by simpa only [List.length_reverse] using readyE)
    (by simp [E,M,jobs,radius,p,s,‹count ≠ origins›.symm,‹origins ≠ ports.archive›])
    (by simp [E,M,payload,jobs,radius,p,s,‹origins ≠ ports.archive›.symm,‹count ≠ ports.archive›.symm])
    (by simpa only [List.length_reverse] using hloopCount)
    (by simp [E,M,‹saved ≠ origins›,‹count ≠ saved›.symm,‹saved ≠ ports.archive›,hsaved])
  have harchiveBlank : S.R ports.archive = [] := by rw [←harchive]; exact gather.houtput
  let Ffinal : Stacks T (prime+K) := {E with R := (Function.update (Function.update (Function.update E.R origins (S.R origins))
    ports.archive []) dst (outputs.reverse.flatten++E.R dst))}
  let Dfinal : Stacks T (prime+K) := {S with R := Function.update S.R dst (outputs.reverse.flatten++S.R dst)}
  have hdstE : E.R dst = S.R dst := by
    simp [E,M,‹origins ≠ dst›.symm,‹count ≠ dst›.symm,‹ports.archive ≠ dst›.symm]
  have hblankCount : Dfinal.R count = [] := by
    simp [Dfinal,‹count ≠ dst›,hcountBlank]
  have hcountFinal : (Ffinal.R count).length = jobs.length := by
    simp [Ffinal,E,‹count ≠ dst›,‹count ≠ origins›,‹count ≠ ports.archive›]
  have hframeFinal (r : Fin T) (hc : count ≠ r) : Ffinal.R r = Dfinal.R r := by
    by_cases hd : r = dst
    · subst r; simp [Ffinal,Dfinal,hdstE]
    · by_cases ho : r = origins
      · subst r; simp [Ffinal,Dfinal,hd,‹origins ≠ ports.archive›]
      · by_cases ha : r = ports.archive
        · subst r; simp [Ffinal,Dfinal,hd,harchiveBlank]
        · simp [Ffinal,Dfinal,E,M,hd,ho,ha,Ne.symm hc]
  obtain ⟨vend,huend,heClear⟩ := retireGeneratedHeaders_exec (body := body)
    (fun _ : Fin 1 => count) (by intro x y hxy; exact Subsingleton.elim x y)
    (fun _ => jobs.length) vf Dfinal Ffinal (by intro j; exact hblankCount)
    (by intro j; exact hcountFinal) rfl rfl rfl
    (by intro r hr; exact hframeFinal r (hr 0)) 0
  have heClear' : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk vf Ffinal)+0) 0
      (clearWords [count]) (Host.mk vf Ffinal) (2*jobs.length+3) (Host.mk vend Dfinal) := by
    simpa [List.ofFn_succ] using heClear
  have heRunClear := hef.seq (heClear'.mono (by
    intro d z hz
    have hp := hef.final
    change mnSize (Host.mk vf Ffinal)+0 ≤ _ at hp
    omega))
  have hmiddle := execWithin_seq_two_budget body _ _ _ _ _ _ _ 0 _ _ hei heRunClear
  have hwhole := execWithin_seq_two_budget body _ _ _ _ _ _ _ 0 _ _ hem hmiddle
  refine ⟨vend,nm+(ni+(nf+(2*jobs.length+3))),outputs,huend.trans (huf.trans (hui.trans hum)),?_,hcert,?_⟩
  · have hmR := (Nat.cast_le (α := ℝ)).mpr htm
    have hiR := (Nat.cast_le (α := ℝ)).mpr hti
    simp only [Nat.cast_add,List.length_reverse] at hfast ⊢
    linarith only [hmR,hiR,hfast]
  · simpa only [List.length_reverse] using hwhole

end IntegerMultBounds.MathlibTM2.Cost
