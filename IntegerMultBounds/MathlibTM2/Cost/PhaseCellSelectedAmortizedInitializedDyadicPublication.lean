module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedAmortizedDyadicPublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicPublicationHeaderRetirement
public import IntegerMultBounds.MathlibTM2.Host.SequentialBudget

/-! Generate binary dimensions from unary masters, execute selected dyadic
publication, and retire the owned headers. Only source and output change. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz ScalarPlacement PackedTranspose FixedStreamedBank
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open Filter IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
variable {Q K : ℕ} {P U : Type}

theorem selectedAmortizedInitializedDyadicPublication_exec (body : P → Pr P PackedTranspose.tapeCount Q (prime+K) U)
    (hstates : FixedStreamedBank.stateCount ≤ Q) (ct cV : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ (h : Sizes.Big m) (i : Fin (Sizes.d m)) [NeZero (Sizes.s m i)],
    let p := Sizes.p m
    let s := Sizes.s m i
    ∀ (u target : ℕ) (htarget : target ≤ ct*p) (W : ℕ) (hW : 1 ≤ W) (b V : ℕ),
    V ≤ cV*p → 2^b ≤ Sizes.T m →
    let width := amortizedCoreWidth ct p
    let radius := localityDepth p target*PhaseCellBand.width p u
    let g := gatherPublicationClass s width radius (width+2*radius)
    let hw : 0 < width := (amortizedCoreWidth_bounds ct p u target (by have := h.thirteen_le_p; omega) htarget).1
    let a := Nat.clog 2 g.indices.length
    ∀
    (hbits : a+b < V) (hfit : (g.length*W)*2^(a+b) < 2^V) (hA : 4 ≤ prime+K)
    (exponent packet pad tmp saved : Fin PackedTranspose.tapeCount)
    (hpadReg : [exponent,packet,extra 1,pad,tmp,saved].Nodup)
    (Fs : List (ZMod s → GaussianInt)) (hFs : Fs.length = 2^b)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (batches : List (List (List GaussianInt)))
    (hrows : List.Forall₂ (fun k rows => ExactCoreRows (A := (prime+K)) p W width k Fs J rows) (coreBulkIndices s width (PhaseCellBand.width p u) (localityDepth p target)) batches)
    (depth : ℕ)
    (v : HS PackedTranspose.tapeCount Q (prime+K) U) (S : Stacks PackedTranspose.tapeCount (prime+K))
    (hworkspace : PublicationWorkspaceReady (fun i => i) exponent packet pad tmp saved a b g.length W V S)
    (hpadOff : ∀ r ∈ [exponent,packet,pad,tmp,saved], r ∉ publicationBinaryRegisters)
    (ha : Nat.size a ≤ V) (hb : Nat.size b ≤ V) (hC : Nat.size (g.length*W) ≤ V)
    (hsourceA : (S.R (headerReg 84)).length = a)
    (hsourceB : (S.R (headerReg 85)).length = b)
    (hsourceC : (S.R packetWidth).length = g.length*W)
    (hheaderBlank : ∀ i ∈ [(97 : Fin 117),98,102,40,41,42,43,44,45], S.R (headerReg i) = [])
    (hsrc : S.R (extra 1) = (batches.map (fun rows => cstream (prime+K) W rows.flatten)).flatten)
    (dst : Fin PackedTranspose.tapeCount) (pub : PreparedPublicationPlan PackedTranspose.tapeCount (extra 1) dst)
    (clock lineRows : Fin PackedTranspose.tapeCount)
    (hports : (pub.support++[extra 1,dst,clock,lineRows]).Nodup)
    (hpubOff : ∀ r ∈ pub.support++[extra 1,dst,clock,lineRows], r ∉ publicationBinaryRegisters)
    (ambient : Fin Fs.length → List (Fin (prime+K+4)))
    (hambient : ∀ j, (ambient j).length = s*W)
    (outputTail borrowed : List (Fin (prime+K+4)))
    (pubReady : pub.Ready (coreSubsetPublicationWindows s width g.length hw g.indices g.sublist)
      W (2^a-g.indices.length) borrowed S)
    (hdst : S.R dst = (List.ofFn ambient).flatten++outputTail)
    (hclock : (S.R clock).length = Fs.length) (hline : (S.R lineRows).length = s),
    let headerBill := 21*(a+b+g.length*W)+36*V+85
    ∃ lines : List (List (Fin (prime+K+4))), ∃ v' F, ∃ n : ℕ, v'.user = v.user ∧ (n : ℝ) ≤ (headerBill+6*V+7 : ℕ)+(2*(Sizes.T m : ℝ)+1700*(2^b*(s*W) : ℕ)+
        108*(generatedDyadicStageCoeff FixedStreamedBank.tapeCount 6 1+300)*
          (2^b*(s*W) : ℕ)*Sizes.d m*((Sizes.ℓ m : ℝ)^Parameters.tau+1)) ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (Host.mk v S)+depth+
        (2*headerBill+(2*Sizes.T m+(3200+3*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+40))*(2^b*(s*W)))+0)) depth
        (.seq (.seq gatherHeadersProgram (.seq (.seq (ownedPrefixPadding exponent packet (extra 1) pad tmp saved (pairSym (prime+K) false false))
          (PackedTranspose.program hstates)) (pub.replicaProgram clock lineRows))) (clearWords publicationBinaryRegisters)) (Host.mk v S) n (Host.mk v' F) ∧
      F.R (extra 1) = [] ∧ F.R dst = lines.flatten++outputTail ∧
      g.BankAccurate p W (inversePublicationTargets p Fs.reverse J) lines (3/(2 : ℝ)^p) ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ r, r ≠ extra 1 → r ≠ dst → F.R r = S.R r := by
  dsimp only
  filter_upwards [selectedAmortizedDyadicPublication_exec body hstates ct cV] with m hpub
  intro h i _ u target htarget W hW b V hV hreplicas hbits hfit hA exponent packet pad tmp saved hpadReg
    Fs hFs J batches hrows depth v S hworkspace hpadOff ha hb hC hsourceA hsourceB hsourceC hheaderBlank hsrc
    dst pub clock lineRows hports hpubOff ambient hambient outputTail borrowed pubReady hdst hclock hline
  let p := Sizes.p m
  let s := Sizes.s m i
  let width := amortizedCoreWidth ct p
  let radius := localityDepth p target*PhaseCellBand.width p u
  let g := gatherPublicationClass s width radius (width+2*radius)
  let a := Nat.clog 2 g.indices.length
  let M := publicationHeadersState a b (g.length*W) V S
  have hread (r : Fin PackedTranspose.tapeCount) (hr : r ∉ publicationBinaryRegisters) : M.R r = S.R r := by
    simp only [publicationBinaryRegisters,List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [M,publicationHeadersState,Function.update_of_ne hr.2.2,Function.update_of_ne hr.2.1,Function.update_of_ne hr.1]
  obtain ⟨v₁,n₁,hu₁,hn₁,ready,he₁⟩ := publicationHeaders_exec_within body exponent packet pad tmp saved
    a b g.length W V ha hb hC depth v S hworkspace hpadOff hsourceA hsourceB hsourceC hheaderBlank
  have pubReadyM := pubReady.of_frame (F := M) (by
    intro r hr
    exact hread r (hpubOff r (List.mem_append_left _ hr)))
  have hsrcOff := hpubOff (extra 1) (by simp)
  have hdstOff := hpubOff dst (by simp)
  obtain ⟨lines,v₂,F,n₂,hu₂,hn₂,he₂,hs,hd,hgood,hi,ho,hl,hframe⟩ := hpub h i u target htarget W hW b V hV hreplicas
    hbits hfit hA exponent packet pad tmp saved hpadReg Fs hFs J batches hrows depth v₁ M
    ready.exponent ready.packet ready.pad ready.tmp ready.saved ready.a ready.b ready.seed ready.zero ready.width
    ready.blank ready.stages ready.left ready.fresh (by rw [hread _ hsrcOff]; exact hsrc) ready.count ready.codec
    dst pub clock lineRows hports ambient hambient outputTail borrowed pubReadyM
    (by rw [hread _ hdstOff]; exact hdst)
    (by rw [hread _ (hpubOff clock (by simp))]; exact hclock)
    (by rw [hread _ (hpubOff lineRows (by simp))]; exact hline)
  have hF : F = {M with R := Function.update (Function.update M.R (extra 1) []) dst (lines.flatten++outputTail)} := by
    refine Stacks.ext hi ho hl ?_
    funext r
    by_cases hr : r = dst
    · subst r; simp only [Function.update_self,hd]
    · by_cases hs' : r = extra 1
      · subst r
        change F.R (extra 1) = Function.update (Function.update M.R (extra 1) []) dst _ (extra 1)
        rw [Function.update_of_ne hr,Function.update_self,hs]
      · change F.R r = Function.update (Function.update M.R (extra 1) []) dst _ r
        rw [Function.update_of_ne hr,Function.update_of_ne hs']
        exact hframe r hs' hr
  have hblank : ∀ r ∈ publicationBinaryRegisters, S.R r = [] := by
    intro r hr
    simp only [publicationBinaryRegisters,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl <;> apply hheaderBlank <;> simp
  obtain ⟨v',hu₃,he₃⟩ := retirePublicationBinaryHeaders_exec_within body a b (g.length*W) V
    (extra 1) dst hsrcOff hdstOff [] (lines.flatten++outputTail) S hblank depth v₂
  have he₂' := he₂.cast rfl (congrArg (Host.mk v₂) hF)
  have heTotal := execWithin_seq_two_budget body _ _ _ _ _ _ _ depth _ _
    (execWithin_seq_two_budget body _ _ _ _ _ _ _ depth _ _ he₁ he₂') he₃
  have hne := pub.src_ne_dst
  refine ⟨lines,v',_,n₁+n₂+(6*V+7),hu₃.trans (hu₂.trans hu₁),?_,heTotal,?_,?_,hgood,rfl,rfl,rfl,?_⟩
  · have hn₁Real := Nat.cast_le (α := ℝ).mpr hn₁
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hn₁Real hn₂ ⊢
    linarith only [hn₁Real,hn₂]
  · exact (Function.update_of_ne hne _ _).trans (Function.update_self _ _ _)
  · exact Function.update_self _ _ _
  · intro r hs hd
    exact (Function.update_of_ne hd _ _).trans (Function.update_of_ne hs _ _)

end IntegerMultBounds.MathlibTM2.Cost
