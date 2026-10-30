module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedNormalizedFactorySetup

/-! Execute the concrete normalized packed caller from constructed ordinary
words. Only mathematical and sizing hypotheses remain as input premises. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

noncomputable def packedNormalizedFactoryInput {A : ℕ} (H : Stacks 242 A)
    (B V p u l targetOut s t a b coreWidth k radius W : ℕ) [NeZero s]
    (Fs : List (ZMod s → GaussianInt)) : Stacks 325 A :=
  let S := packedNormalizedFactoryBank H p u l targetOut s t a b V
  let M := packedKeyDescriptorInput (packedKeyPublicationInput S V radius) p W Fs.length ((b-a)*W)
    (cstream A W (Fs.map (packedInterval a (b-a))).flatten)
  packedNormalizedInputBank M B (coreLength s coreWidth k) (List.replicate B Node.tick)
    ((inverseParameterWords p u l targetOut s t a b).flatMap (fun r => binSyms B r.2))

theorem packedNormalizedFactoryInput_words {A : ℕ} (H : Stacks 242 A)
    (B V p u l targetOut s t a b coreWidth k radius W : ℕ) [NeZero s]
    (Fs : List (ZMod s → GaussianInt)) :
    (packedNormalizedFactoryInput H B V p u l targetOut s t a b coreWidth k radius W Fs).R =
      packedNormalizedFactoryPacketWords H B V p u l targetOut s t a b coreWidth k radius W Fs := rfl

/-- The packet contains private data only; the ambient host tapes are not serialized. -/
theorem packedNormalizedFactoryPacketWords_host {A : ℕ} (H H' : Stacks 242 A)
    (B V p u l targetOut s t a b coreWidth k radius W : ℕ) [NeZero s]
    (Fs : List (ZMod s → GaussianInt)) :
    packedNormalizedFactoryPacketWords H B V p u l targetOut s t a b coreWidth k radius W Fs =
      packedNormalizedFactoryPacketWords H' B V p u l targetOut s t a b coreWidth k radius W Fs := rfl

/-- Changing the host tapes preserves the entire private input bank. -/
theorem packedNormalizedFactoryInput_host {A : ℕ} (H H' : Stacks 242 A)
    (B V p u l targetOut s t a b coreWidth k radius W : ℕ) [NeZero s]
    (Fs : List (ZMod s → GaussianInt)) :
    packedNormalizedFactoryInput H B V p u l targetOut s t a b coreWidth k radius W Fs =
      {packedNormalizedFactoryInput H' B V p u l targetOut s t a b coreWidth k radius W Fs with
        inp := H.inp, out := H.out} := by
  refine Stacks.ext rfl rfl rfl rfl

/-- Loading the complete ordinary packet supplies exactly the bank used by the
execution theorem. All private left stacks are initially empty. -/
theorem descriptorReadyBank_factoryInput {A T : ℕ} (work : Fin 325 → Fin T)
    (Hbase : Stacks 242 A) (parent : Stacks T A)
    (B V p u l targetOut s t a b coreWidth k radius W : ℕ) [NeZero s]
    (Fs : List (ZMod s → GaussianInt))
    (hinp : Hbase.inp = parent.inp) (hout : Hbase.out = parent.out)
    (hleft : ∀ i, parent.L (work i) = []) :
    descriptorReadyBank work
      (packedNormalizedFactoryPacketWords Hbase B V p u l targetOut s t a b coreWidth k radius W Fs) parent =
      packedNormalizedFactoryInput Hbase B V p u l targetOut s t a b coreWidth k radius W Fs := by
  let S := packedNormalizedFactoryBank Hbase p u l targetOut s t a b V
  let source := cstream A W (Fs.map (packedInterval a (b-a))).flatten
  let M := packedKeyDescriptorInput (packedKeyPublicationInput S V radius) p W Fs.length ((b-a)*W) source
  have hSleft (i : Fin 242) : S.L i = [] := by
    dsimp only [S, packedNormalizedFactoryBank]
    exact packedFactoryInputBank_left _ _ _ _ _ _ _ _ _ _ _ _ i
  exact descriptorReadyBank_packedNormalized work M parent B (coreLength s coreWidth k)
    (List.replicate B Node.tick)
    ((inverseParameterWords p u l targetOut s t a b).flatMap (fun r => binSyms B r.2))
    hinp hout (packedKeyDescriptorInput_left S V radius p W Fs.length ((b-a)*W) source hSleft) hleft

theorem packedNormalizedFactoryInput_left {A : ℕ} (Hbase : Stacks 242 A)
    (B V p u l targetOut s t a b coreWidth k radius W : ℕ) [NeZero s]
    (Fs : List (ZMod s → GaussianInt)) (i : Fin 325) :
    (packedNormalizedFactoryInput Hbase B V p u l targetOut s t a b coreWidth k radius W Fs).L i = [] := by
  let parent : Stacks 325 A := ⟨Hbase.inp,Hbase.out,fun _ => [],fun _ => []⟩
  have hv := descriptorReadyBank_factoryInput (id : Fin 325 → Fin 325) Hbase parent
    B V p u l targetOut s t a b coreWidth k radius W Fs rfl rfl (by intro i; rfl)
  exact (congrArg (fun S : Stacks 325 A => S.L i) hv).symm

theorem packedNormalizedFactory_exec {Q A p l s t u targetOut a b V : ℕ} {U : Type} [NeZero s]
    {α gap : ℝ} {C : ZMod s → GaussianInt} (Hbase : Stacks 242 A)
    (h : PackedHaloParameterBounds (p := p) (l := l) (t := t) (u := u)
      (target := targetOut+1) (rhsExp := 2) (a := a) (b := b) (V := V) α gap C)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (Bcore : ℕ) (hsCore : s < 2^Bcore) (q W : ℕ)
    (hqSizing : q = executionPrecision p l
      (boundaryHaloTarget p u (boundaryRecoveryTarget p (targetOut+1)) 2
        (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2)
    (hpq : p+1 ≤ q) (hW : 2*q+8 ≤ W)
    (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1)
    (coreWidth k radius : ℕ) (haEq : a = coreStart coreWidth k-radius)
    (hbEq : b = coreStart coreWidth k+coreLength s coreWidth k+radius)
    (hleft : radius ≤ coreStart coreWidth k)
    (hright : coreStart coreWidth k+coreLength s coreWidth k+radius ≤ s)
    (hcoeff : ∀ j < b-a, ∀ z ∈ couplingCoefficientWords (2^15*p) q s t u (PhaseCellBand.width p u) (a+j),
      Fits (2*q+8) z ∧ z.im = 0)
    (hvaluesFit : ∀ i : Fin 8, ![p,u,l,targetOut,s,t,a,b] i < 2^Bcore)
    (hbandRoom : 64*(p+1)+u < 2^Bcore)
    (hgeometryRoom : 8*(t+1)^2+2*PhaseCellBand.width p u+8 < 2^Bcore)
    (hprecisionRoom : inversePrecisionRoom p l targetOut
      (haloBoundary s t (PhaseCellBand.width p u) a b).card (PhaseCellBand.width p u) < 2^Bcore)
    (localityTarget : ℕ)
    (hhalo : haloVertices s a b = (PhaseCellInterface.generatedWindow s coreWidth p u localityTarget k).halo)
    (Y : (ZMod s → GaussianInt) → ZMod s → ℝ)
    (hY : ∀ F ∈ complexComponentFields Fs, SchurDominance.Solves (realMatrix s t p u) Finset.univ (Y F)
      (fun i => (value q ((2 : GaussianInt)^(q-p-1)*F i)).re))
    (v : HS 325 Q A U) :
    let H₀ := packedNormalizedFactoryInput Hbase Bcore V p u l targetOut s t a b coreWidth k radius W Fs
    let j := inverseNormalizationShift p
    ∃ v' H n, ∃ Gs : List (ZMod s → GaussianInt), v'.user = v.user ∧ Gs.length = Fs.length ∧
      n ≤ packedKeyNormalizedBatchCost Bcore p q W u l s t a b V
        (boundaryRecoveryTarget p (targetOut+1)) (targetOut+1) 2 targetOut coreWidth k radius Fs.length ∧
      Exec (fun f : Empty => nomatch f) (packedNormalizedLocalBatch hR hQ) (mk v H₀) n (mk v' H) ∧
      H.inp = H₀.inp ∧ H.out = H₀.out ∧
      H.R 253 = (Gs.map (fun D => cstream A W (ownedCoreWords coreWidth k D))).flatten ∧
      List.Forall₂ (fun F D => PhaseCellInterface.ErrorOn (ownedCore s coreWidth k)
        (packedIntervalRead p W (coreStart coreWidth k) (cstream A W (ownedCoreWords coreWidth k D)))
        (fun i => ((2 : ℂ)^j)⁻¹*componentSolution Y F i)
        ((2/(2 : ℝ)^p+(1/(2 : ℝ)^targetOut)/(2 : ℝ)^j)+
          (1/(2 : ℝ)^localityTarget+1/(2 : ℝ)^localityTarget)/(2 : ℝ)^j)) Fs Gs ∧
      ∀ c, mnProgPush (packedNormalizedLocalBatch (P := Empty) (U := U) (A := A) hR hQ) ≤ c → ∀ depth,
        ExecWithin (fun f : Empty => nomatch f) (fun d z => mnSize z+d ≤ mnSize (mk v H₀)+
          ((2*Fs.length)*((b-a)*(2*q+8))+V)+depth+(c+1)*
            packedKeyNormalizedWorkspace Bcore p q W u l s t a b V
              (boundaryRecoveryTarget p (targetOut+1)) (targetOut+1) 2 targetOut coreWidth k radius Fs.length)
          depth (packedNormalizedLocalBatch hR hQ) (mk v H₀) n (mk v' H) := by
  dsimp only
  let S := packedNormalizedFactoryBank Hbase p u l targetOut s t a b V
  let B := packedKeyPublicationInput S V radius
  let source := cstream A W (Fs.map (packedInterval a (b-a))).flatten
  let M := packedKeyDescriptorInput B p W Fs.length ((b-a)*W) source
  let S₀ := extendStacks (by decide : 242 ≤ 249) S
  let wl : List (Fin (A+4)) := List.replicate Bcore Node.tick
  let parameters : List (Fin (A+4)) := (inverseParameterWords p u l targetOut s t a b).flatMap (fun r => binSyms Bcore r.2)
  let H₀ := packedNormalizedInputBank M Bcore (coreLength s coreWidth k) wl parameters
  have hread (i : Fin 263) : M.R (packedKeySolverReg i) = B.R i :=
    packedKeyDescriptorInput_native B p W Fs.length ((b-a)*W) source i
  have hreadNative (i : Fin 242) : M.R (Fin.castLE (by decide : 242 ≤ 276) i) = S.R i :=
    (hread (Fin.castLE (by decide) i)).trans (packedKeyPublicationInput_native S V radius i)
  have hsrc : S.R 110 = [] := by
    dsimp only [S, packedNormalizedFactoryBank]
    exact packedFactoryInputBank_source _ _ _ _ _ _ _ _ _ _ _ _
  have hq : (M.R 119).length = q := by
    have hr119 : M.R 119 = S.R 119 := hreadNative 119
    rw [hr119]
    dsimp only [S, packedNormalizedFactoryBank]
    rw [packedFactoryInputBank_precision]
    exact (boundaryHaloTarget_sizing p u l (boundaryRecoveryTarget p (targetOut+1)) 2
      (haloBoundary s t (PhaseCellBand.width p u) a b).card).1.symm.trans hqSizing.symm
  have hheaders := packedKeyDescriptorInput_headers B p W Fs.length ((b-a)*W) source
  have hfresh (i : Fin 263) (hi : 242 ≤ i.val) (hne : i ≠ 252) : B.R i = [] :=
    packedKeyPublicationInput_fresh S V radius i hi hne
  have hblank : ∀ i ∈ ([110,268,269,270,271,272,273,274,275] : List (Fin 276)), M.R i = [] := by
    have hc : ([110,268,269,270,271,272,273,274,275] : List (Fin 276)).all
        (fun i => decide (i = 110 ∨ 268 ≤ i.val)) = true := by decide +kernel
    intro i hi
    rcases of_decide_eq_true (List.all_eq_true.mp hc i hi) with rfl | hh
    · exact (hreadNative 110).trans hsrc
    · exact packedKeyDescriptorInput_fresh B p W Fs.length ((b-a)*W) source i hh
  have hclean : ∀ i ∈ ([254,255,256,257,258,259,260,261,262] : List (Fin 263)), B.R i = [] := by
    have hc : ([254,255,256,257,258,259,260,261,262] : List (Fin 263)).all
        (fun i => decide (242 ≤ i.val ∧ i ≠ 252)) = true := by decide +kernel
    intro i hi
    obtain ⟨hh, hn⟩ := of_decide_eq_true (List.all_eq_true.mp hc i hi)
    exact hfresh i hh hn
  have harchive : M.R 253 = [] := (hread 253).trans (hfresh 253 (by decide) (by decide))
  obtain ⟨v', H, n, Gs, hu, hlen, hn, he, hi, ho, hout, _, _, _, _, _, hgood, ht⟩ :=
    packedKeyNormalizedBatch_exec
      (body := fun f : Empty => nomatch f) (body' := fun f : Empty => nomatch f)
      (body'' := fun f : Empty => nomatch f) (bodyLarge := fun f : Empty => nomatch f)
      (by intro f; nomatch f) (by intro f; nomatch f) (by intro f; nomatch f)
      (fun f : Empty => nomatch f) (by intro f; nomatch f)
      (fun f : Empty => nomatch f) (by intro f; nomatch f)
      (fun f : Empty => nomatch f) (by intro f; nomatch f)
      (by decide : 280 ≤ 325) (fun f : Empty => nomatch f) (by intro f; nomatch f)
      hR hQ hA Bcore hsCore q W hpq hW hqSizing Fs hF C [] v M B S₀ S
      (packedKeyDescriptorInput_views S V radius p W Fs.length ((b-a)*W) source)
      (packedNormalizedFactoryBank_setup Hbase h) hq
      (by simpa only [List.length_replicate] using congrArg List.length hheaders.2.2.2.1)
      (by simpa only [List.length_replicate] using congrArg List.length hheaders.2.2.1)
      (by simpa only [List.length_replicate] using congrArg List.length hheaders.2.1)
      (by simpa only [List.length_replicate] using congrArg List.length hheaders.2.2.2.2)
      (by simpa only [List.append_nil] using hheaders.1) hblank
      ((hread 251).trans (hfresh 251 (by decide) (by decide)))
      (extendStacks_fresh (by decide : 242 ≤ 249) S 248 (by decide)).2
      (packedNormalizedFactoryBank_scratch Hbase) rfl rfl
      coreWidth k radius haEq hbEq hleft hright (hfresh 249 (by decide) (by decide))
      (hfresh 250 (by decide) (by decide)) hclean (packedKeyPublicationInput_radius S V radius)
      hcoeff targetOut rfl rfl packedNormalizedScalarReg packedNormalizedScalarReg_injective
      (fun r => (packedNormalizedScalarReg_bounds r).1) packedNormalizedPort packedNormalizedPort_injective
      324 (by decide) packedNormalizedRegisters_nodup (fun i r => packedNormalizedScalarReg_port r i)
      packedNormalizedScalarReg_header packedNormalizedPort_high hvaluesFit wl (List.length_replicate ..)
      hbandRoom hgeometryRoom hprecisionRoom [] H₀ (packedNormalizedInputBank_view M _ _ wl parameters)
      (packedNormalizedInputBank_width M _ _ wl parameters) (packedNormalizedInputBank_scalar M _ _ wl parameters)
      (by simpa only [List.append_nil] using packedNormalizedInputBank_parameters M Bcore (coreLength s coreWidth k) wl parameters)
      (packedNormalizedInputBank_ports M _ _ wl parameters) localityTarget hhalo Y hY
  rw [harchive, List.append_nil] at hout
  simp only [harchive, List.append_nil] at hgood
  exact ⟨v', H, n, Gs, hu, hlen, hn, he, hi, ho, hout, hgood,
    fun c hc depth => ht c hc (by intro f; nomatch f) depth⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
