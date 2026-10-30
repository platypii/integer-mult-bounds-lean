module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloClosedBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedCoreArchiveFromDimensions

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.BandFactor
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {Q A : ℕ} {P U : Type}

def packedHaloPublishedReg : Fin 249 → Fin 263 := Fin.castLE (by decide)

def packedCoreBatchPublicationCost (N radius core w : ℕ) : ℕ :=
  packedCoreArchiveControlsCost radius core w N+
    (N*(packedCoreArchiveStepCost radius core (core+2*radius) w+3)+2)+
    (2*(radius*w+core*w+(core+2*radius))+7)

noncomputable def packedHaloPublishedBatch (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 263 Q A U :=
  .seq (embProg packedHaloPublishedReg id (packedHaloClosedBatch hR hQ))
    (packedCoreArchiveFromDimensions 249 250 251 248 254 255 132 253 257 258 259 256 252 260 261 262)

variable {body : P → Pr P 249 Q A U} {bodyLarge : P → Pr P 263 Q A U}

/-- Structural execution handoff from a closed solver to its publisher. Numerical
setup parameters stay outside this register/queue composition proof. -/
theorem packedHaloClosedBatch_publish_exec
    (hbody : ∀ f, bodyLarge f = embProg packedHaloPublishedReg id (body f))
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    {s : ℕ} [NeZero s] (q w a b coreWidth k radius : ℕ)
    (haEq : a = coreStart coreWidth k-radius)
    (hbEq : b = coreStart coreWidth k+coreLength s coreWidth k+radius)
    (hleft : radius ≤ coreStart coreWidth k)
    (hright : coreStart coreWidth k+coreLength s coreWidth k+radius ≤ s)
    (inputs : List ((ZMod s → GaussianInt) × (ZMod s → ℝ)))
    (Ds : List (ZMod s → GaussianInt)) (e : ℝ)
    (savedArchive : List (Fin (A+4)))
    {vi vf : HS 249 Q A U} {S₀ H : Stacks 249 A} {n₁ : ℕ}
    (he : Exec body (packedHaloClosedBatch hR hQ) (mk vi S₀) n₁ (mk vf H))
    (hcounter : H.R 248 = [])
    (houtputs : H.R 132 = (Ds.reverse.map (fun D => cstream A w
      (packedInterval a (b-a) D))).flatten++savedArchive)
    (hgood : List.Forall₂ (fun x D => PhaseCellInterface.ErrorOn
      (haloVertices s a b)
      (fun i => (packedIntervalRead q w a
        (cstream A w (packedInterval a (b-a) D)) i).re)
      x.2 e) inputs Ds)
    (v : HS 263 Q A U) (Sbig : Stacks 263 A)
    (hv : embDn packedHaloPublishedReg v = vi) (hview : embStk packedHaloPublishedReg Sbig = S₀)
    (hRdim : (Sbig.R 249).length = radius)
    (hLdim : (Sbig.R 250).length = coreLength s coreWidth k)
    (hNdim : (Sbig.R 251).length = inputs.length) (hwdim : (Sbig.R 252).length = w)
    (hclean : ∀ i ∈ ([254,255,256,257,258,259,260,261,262] : List (Fin 263)), Sbig.R i = []) :
    ∃ v' F n, v'.user = vf.user ∧ n ≤ n₁+packedCoreBatchPublicationCost inputs.length radius (coreLength s coreWidth k) w ∧
      Exec bodyLarge (packedHaloPublishedBatch hR hQ) (mk v Sbig) n (mk v' F) ∧
      F.R 132 = savedArchive ∧
      F.R 253 = (Ds.map (fun D => cstream A w (ownedCoreWords coreWidth k D))).flatten++Sbig.R 253 ∧
      List.Forall₂ (fun x D => PhaseCellInterface.ErrorOn (ownedCore s coreWidth k)
        (fun i => (packedIntervalRead q w (coreStart coreWidth k)
          (cstream A w (ownedCoreWords coreWidth k D)++Sbig.R 253) i).re) x.2 e) inputs Ds ∧
      (∀ i : Fin 249, i ≠ 132 → F.R (packedHaloPublishedReg i) = H.R i) ∧
      (∀ i : Fin 263, 249 ≤ i.val → i ≠ 253 → F.R i = Sbig.R i) := by
  have hlen : coreStart coreWidth k+coreLength s coreWidth k+radius-(coreStart coreWidth k-radius) =
      coreLength s coreWidth k+2*radius := by omega
  rw [haEq,hbEq,hlen] at houtputs hgood
  have hinj : Function.Injective packedHaloPublishedReg := by
    intro i j he; exact Fin.ext (congrArg (fun i : Fin 263 => i.val) he)
  obtain ⟨v₂,M,he₂,hv₂,hu₂,hproj,hframe⟩ := exec_emb hinj hbody he v hv Sbig hview
  have hexternal (i : Fin 263) (hi : 249 ≤ i.val) : M.R i = Sbig.R i :=
    (hframe i (by
      intro j hj
      have he := congrArg (fun i : Fin 263 => i.val) hj
      have hb := j.isLt
      change j.val = i.val at he
      omega)).2
  have hDs : Ds.length = inputs.length := hgood.length_eq.symm
  have hprojR (i : Fin 249) : M.R (packedHaloPublishedReg i) = H.R i :=
    congrArg (fun T : Stacks 249 A => T.R i) hproj
  obtain ⟨v₃,F,n₂,hu₃,hn₂,he₃,harchive,hdst,hi,ho,hl,hpubFrame,hcoreGood⟩ :=
    packedCoreArchiveFromDimensions_exec (body := bodyLarge) 249 250 251 248 254 255 132 253 257 258 259 256 252 260 261 262
      (by decide) v₂ M q w coreWidth k radius hleft hright Ds savedArchive
      ((hprojR 132).trans houtputs)
      (by rw [hexternal 249 (by decide)]; exact hRdim)
      (by rw [hexternal 250 (by decide)]; exact hLdim)
      (by rw [hexternal 252 (by decide)]; exact hwdim)
      (by rw [hexternal 251 (by decide),hDs]; exact hNdim)
      (by
        intro i hi
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact (hprojR 248).trans hcounter
        all_goals rw [hexternal _ (by decide)]; exact hclean _ (by decide))
      inputs e hgood
  have h253 := hexternal 253 (by decide)
  have hn₂' : n₂ ≤ packedCoreBatchPublicationCost inputs.length radius (coreLength s coreWidth k) w := by
    simpa only [packedCoreBatchPublicationCost,hDs] using hn₂
  refine ⟨v₃,F,n₁+n₂,hu₃.trans hu₂,Nat.add_le_add_left hn₂' _,Exec.seq he₂ he₃,
    harchive,by simpa only [h253] using hdst,by simpa only [h253] using hcoreGood,?_,?_⟩
  · intro i h132
    have hi := i.isLt
    rw [hpubFrame _ (by
      intro he; exact h132 (Fin.ext (congrArg (fun k : Fin 263 => k.val) he))) (by
      intro he; have hh := congrArg (fun k : Fin 263 => k.val) he; change i.val = 253 at hh; omega)]
    exact hprojR i
  · intro i hi h253'
    rw [hpubFrame i (by intro he; have hh := congrArg Fin.val he; change i.val = 132 at hh; omega) h253']
    exact hexternal i hi

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
