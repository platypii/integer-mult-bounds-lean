module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedNormalizedFactoryExec
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorCleanupStock

/-! An actual descriptor step: load the constructed packet, execute the packed
kernel, collect its certified output and restore the entire private bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

/-- The ordinary published word carries the generated-window accuracy certificate. -/
def PackedNormalizedOutput {A s : ℕ} [NeZero s] (p W targetOut coreWidth k localityTarget : ℕ)
    (Fs : List (ZMod s → GaussianInt)) (Y : (ZMod s → GaussianInt) → ZMod s → ℝ)
    (word : List (Fin (A+4))) : Prop :=
  let j := inverseNormalizationShift p
  ∃ Gs : List (ZMod s → GaussianInt), Gs.length = Fs.length ∧
    word = (Gs.map (fun D => cstream A W (ownedCoreWords coreWidth k D))).flatten ∧
    List.Forall₂ (fun F D => PhaseCellInterface.ErrorOn (ownedCore s coreWidth k)
      (packedIntervalRead p W (coreStart coreWidth k) (cstream A W (ownedCoreWords coreWidth k D)))
      (fun i => ((2 : ℂ)^j)⁻¹*componentSolution Y F i)
      ((2/(2 : ℝ)^p+(1/(2 : ℝ)^targetOut)/(2 : ℝ)^j)+
        (1/(2 : ℝ)^localityTarget+1/(2 : ℝ)^localityTarget)/(2 : ℝ)^j)) Fs Gs

theorem packedNormalizedFactoryDescriptorStep_exec {T Q A p l s t u targetOut a b V : ℕ} {P U : Type} [NeZero s]
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
    (work : Fin 325 → Fin T) (hwork : Function.Injective work)
    (src saved count tmp spare result : Fin T)
    (hreg : [src,saved,count,tmp,spare,result].Nodup)
    (hsep : ∀ i, work i ∉ [src,saved,count,tmp,spare,result])
    (body : P → Pr P T Q A U) (v : HS T Q A U) (parent : Stacks T A)
    (hinp : Hbase.inp = parent.inp) (hout : Hbase.out = parent.out)
    (hblank : ∀ i, parent.R (work i) = []) (hleftBank : ∀ i, parent.L (work i) = [])
    (rest : List (Fin (A+4)))
    (hsource : parent.R src = descriptorBankTape (placedDescriptorFields work
      (packedNormalizedFactoryPacketWords Hbase Bcore V p u l targetOut s t a b coreWidth k radius W Fs)) ++ rest)
    (hcount : parent.R count = []) (htmp : parent.R tmp = []) (hspare : parent.R spare = []) :
    let words := packedNormalizedFactoryPacketWords Hbase Bcore V p u l targetOut s t a b coreWidth k radius W Fs
    let initial := packedNormalizedFactoryInput Hbase Bcore V p u l targetOut s t a b coreWidth k radius W Fs
    let persistent := (2*Fs.length)*((b-a)*(2*q+8))+V
    let workspace := packedKeyNormalizedWorkspace Bcore p q W u l s t a b V
      (boundaryRecoveryTarget p (targetOut+1)) (targetOut+1) 2 targetOut coreWidth k radius Fs.length
    let stock := persistent+workspace
    let finalBudget := registerBankStock initial+persistent+
      (mnProgPush (packedNormalizedLocalBatch (P := Empty) (U := U) (A := A) hR hQ)+1)*workspace
    let cleanup := 6*finalBudget+1956
    ∃ v' n output, v'.user = v.user ∧
      n ≤ takeDescriptorBankCost (placedDescriptorFields work words)+
        packedKeyNormalizedBatchCost Bcore p q W u l s t a b V
          (boundaryRecoveryTarget p (targetOut+1)) (targetOut+1) 2 targetOut coreWidth k radius Fs.length+cleanup ∧
      Exec body (packedNormalizedDescriptorStep work src saved count tmp spare result hR hQ) (mk v parent) n
        (mk v' (dispatchedDescriptorState work words src saved result rest output parent)) ∧
      PackedNormalizedOutput p W targetOut coreWidth k localityTarget Fs Y output ∧
      ∀ C, mnProgPush (packedNormalizedDescriptorStep (P := P) (U := U) (A := A)
          work src saved count tmp spare result hR hQ) ≤ C →
        (∀ f, mnProgPush (body f) ≤ C) → ∀ depth,
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v parent)+depth+
          (C+1)*(takeDescriptorBankCost (placedDescriptorFields work words)+stock+cleanup)) depth
          (packedNormalizedDescriptorStep work src saved count tmp spare result hR hQ) (mk v parent) n
          (mk v' (dispatchedDescriptorState work words src saved result rest output parent)) := by
  dsimp only
  let words := packedNormalizedFactoryPacketWords Hbase Bcore V p u l targetOut s t a b coreWidth k radius W Fs
  let initial := packedNormalizedFactoryInput Hbase Bcore V p u l targetOut s t a b coreWidth k radius W Fs
  let solve : Pr Empty 325 Q A U := packedNormalizedLocalBatch hR hQ
  let time := packedKeyNormalizedBatchCost Bcore p q W u l s t a b V
    (boundaryRecoveryTarget p (targetOut+1)) (targetOut+1) 2 targetOut coreWidth k radius Fs.length
  let persistent := (2*Fs.length)*((b-a)*(2*q+8))+V
  let workspace := packedKeyNormalizedWorkspace Bcore p q W u l s t a b V
    (boundaryRecoveryTarget p (targetOut+1)) (targetOut+1) 2 targetOut coreWidth k radius Fs.length
  let stock := persistent+workspace
  let finalBudget := registerBankStock initial+persistent+(mnProgPush solve+1)*workspace
  let cleanup := 6*finalBudget+1956
  let post : Stacks 325 A → Prop := fun F => F.inp = parent.inp ∧ F.out = parent.out ∧
    PackedNormalizedOutput p W targetOut coreWidth k localityTarget Fs Y (F.R 253) ∧
    registerBankStock F ≤ finalBudget
  have hready : descriptorReadyBank work words parent = initial :=
    descriptorReadyBank_factoryInput work Hbase parent Bcore V p u l targetOut s t a b coreWidth k radius W Fs
      hinp hout hleftBank
  have hsolve : ∀ vi : HS 325 Q A U, ∃ vf F n, vf.user = vi.user ∧ n ≤ time ∧
      Exec (fun f : Empty => nomatch f) solve (mk vi (descriptorReadyBank work words parent)) n (mk vf F) ∧ post F ∧
      ∀ C, mnProgPush solve ≤ C → ∀ depth,
        ExecWithin (fun f : Empty => nomatch f)
          (fun d z => mnSize z+d ≤ mnSize (mk vi (descriptorReadyBank work words parent))+depth+(C+1)*stock)
          depth solve (mk vi (descriptorReadyBank work words parent)) n (mk vf F) := by
    intro vi
    rw [hready]
    obtain ⟨vf,F,n,Gs,hu,hlen,hn,he,hi,ho,hw,hgood,ht⟩ :=
      packedNormalizedFactory_exec Hbase h hR hQ hA Bcore hsCore q W hqSizing hpq hW Fs hF
        coreWidth k radius haEq hbEq hleft hright hcoeff hvaluesFit hbandRoom hgeometryRoom hprecisionRoom
        localityTarget hhalo Y hY vi
    have hb₀ := registerBankStock_le_of_execWithin (ht (mnProgPush solve) le_rfl 0) hi ho
    have hb : registerBankStock F ≤ finalBudget := hb₀
    refine ⟨vf,F,n,hu,hn,he,⟨hi.trans hinp,ho.trans hout,⟨Gs,hlen,hw,hgood⟩,hb⟩,?_⟩
    intro C hc depth
    exact execWithin_absorb_persistent (ht C hc depth)
  have hr := hreg
  regs_ne hr
  have hreg' : [src,saved,count,tmp,spare].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hreg ⊢
    tauto
  have houter : [src,saved,result].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨⟨‹src ≠ saved›,‹src ≠ result›⟩,‹saved ≠ result›,by simp⟩
  have hsep' (i : Fin 325) : work i ∉ [src,saved,count,tmp,spare] := by
    have hi := hsep i
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi ⊢
    tauto
  have hresult (i : Fin 325) : work i ≠ result := by
    have hi := hsep i
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    exact hi.2.2.2.2.2
  obtain ⟨v',F,n,hu,hn,he,hp,ht⟩ := descriptorBankStep_exec_restored (body := body)
    work hwork src saved count tmp spare result hreg' hsep' hresult ‹tmp ≠ result›.symm houter
    words rest 253 solve time stock cleanup post v parent hblank hleftBank hsource hcount htmp hspare hsolve
    (by
      intro F hp
      have hc := descriptorBankCleanupCost_le_stock (253 : Fin 325) F
      have hb := hp.2.2.2
      dsimp only [cleanup]
      omega)
    (by intro F hp; exact ⟨hp.1,hp.2.1⟩)
  exact ⟨v',n,F.R 253,hu,hn,he,hp.2.2.1,ht⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
