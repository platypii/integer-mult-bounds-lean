module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializedCoreGather
public import IntegerMultBounds.MathlibTM2.Host.RightWrites

/-! Place generated batches and their origin/count streams directly in the
queued solver's private bank, then retire the spent movement controls. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def queuedCoreGather (reg : Fin 168 → Fin T) : Pr P T Q A U :=
  .seq (embProg reg Empty.elim (initializedCoreGather (P := Empty))) (uclear (reg 91))

def queuedCoreGatherCost (V s width radius L w : ℕ) : ℕ :=
  initializedCoreGatherCost V s width radius L w+
    2*(s*w+(coreGatherIndices s width radius L).length+1)+2

theorem queuedCoreGather_spec (reg : Fin 168 → Fin T) (hreg : Function.Injective reg) {V s width radius L w : ℕ}
    (hwidth : 0 < width) (hwide : s+width+2*radius < 2^V) (hLfit : L < 2^V)
    (hwV : w < 2^V) (hvol : s*w < 2^V) (hA : 4 ≤ A) (hVpos : 0 < V)
    (hgroup : 0 < (coreGatherIndices s width radius L).length)
    (v : HS T Q A U) (M : Stacks T A) (S : Stacks 168 A)
    (hview : embStk reg M = S)
    (h163 : (S.R 163).length = V) (h115 : S.R 115 = []) (h103 : S.R 103 = []) (h105 : S.R 105 = [])
    (hs : S.R 145 = binSyms V s) (hw : S.R 150 = binSyms V width)
    (hr : S.R 152 = binSyms V radius) (hL : S.R 165 = binSyms V L) (hz : S.R 154 = [])
    (hblank : ∀ k : Fin 168, k.val < 31 → S.R k = [])
    (h104 : S.R 104 = []) (h106 : S.R 106 = []) (h116 : S.R 116 = [])
    (C : ZMod s → GaussianInt) (hsource : S.R 110 = cstream A w (chirpLine s C))
    (hword : (S.R 94).length = w) (hcontrol : S.R 91 = [])
    (hclean : ∀ k ∈ [(92 : Fin 168), 93, 95, 96, 97, 98, 99, 100, 101, 102], S.R k = [])
    (hfresh : ∀ k ∈ [(88 : Fin 168), 89, 90], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ queuedCoreGatherCost V s width radius L w ∧
      Exec body (queuedCoreGather reg) (mk v M) n
        (mk v' {M with R := (Function.update (Function.update (Function.update M.R
          (reg 108) ((coreGatherIndices s width radius L).flatMap
            (fun k => cstream A w (packedInterval (coreStart width k-radius) L C))++M.R (reg 108)))
          (reg 109) ((coreGatherIndices s width radius L).flatMap
            (fun k => binSyms V (coreStart width k-radius))++M.R (reg 109)))
          (reg 116) (List.replicate (coreGatherIndices s width radius L).length tick))}) := by
  obtain ⟨vi,Fi,n,hu,hn,he,hin,hout,hleft,h108,h91,h109,h116',hrest⟩ :=
    initializedCoreGather_packed_exec (body := fun p : Empty => nomatch p)
      hwidth hwide hLfit hwV hvol hA hVpos hgroup
      (embDn reg v) S h163 h115 h103 h105 hs hw hr hL hz hblank h104 h106 h116
      C hsource hword hcontrol hclean hfresh
  let batch := (coreGatherIndices s width radius L).flatMap
    (fun k => cstream A w (packedInterval (coreStart width k-radius) L C))
  let origins := (coreGatherIndices s width radius L).flatMap
    (fun k => binSyms (A := A) V (coreStart width k-radius))
  let controls := coreGatherControls A s width radius L w
  let count := List.replicate (coreGatherIndices s width radius L).length (tick : Fin (A+4))
  let writes : List (Fin 168 × List (Fin (A+4))) :=
    [(108,batch++S.R 108),(91,controls),(109,origins++S.R 109),(116,count)]
  have hFi : Fi = writeRight writes S := by
    refine Stacks.ext hin hout hleft ?_
    funext i
    by_cases h108i : i = 108
    · subst i; simpa [writeRight,writes,batch] using h108
    by_cases h91i : i = 91
    · subst i; simpa [writeRight,writes,controls] using h91
    by_cases h109i : i = 109
    · subst i; simpa [writeRight,writes,origins] using h109
    by_cases h116i : i = 116
    · subst i; simpa [writeRight,writes,count] using h116'
    simpa [writeRight,writes,h108i,h91i,h109i,h116i] using hrest i h108i h91i h109i h116i
  obtain ⟨v₁,hv₁,hu₁,he₁⟩ := exec_emb_ovr (ι := Empty.elim) (body' := body)
    hreg (fun p => nomatch p) he v rfl M hview
  have hover : embOvr reg Fi.get M =
      writeRight (writes.map (fun (i,xs) => (reg i,xs))) M := by
    rw [hFi,←hview]
    exact embOvr_writeRight_view hreg writes M
  let G := writeRight (writes.map (fun (i,xs) => (reg i,xs))) M
  have he₁' : Exec body (embProg reg Empty.elim (initializedCoreGather (P := Empty)))
      (mk v M) n (mk v₁ G) := he₁.cast rfl (congrArg (mk v₁) hover)
  have hGcontrol : G.R (reg 91) = controls := by
    simp [G,writes,writeRight,hreg.eq_iff]
  have hread (i : Fin 168) : S.R i = M.R (reg i) :=
    (congrArg (fun D : Stacks 168 A => D.R i) hview).symm
  have hcontrolM : M.R (reg 91) = [] := (hread 91).symm.trans hcontrol
  obtain ⟨v₂,hu₂,he₂⟩ := uclear_exec body (reg 91) v₁ G
  refine ⟨v₂,n+(2*controls.length+2),hu₂.trans (hu₁.trans hu),?_,
    (Exec.seq he₁' he₂).cast (by rw [hGcontrol]) ?_⟩
  · have hc := coreGatherControls_length_le A s width radius L w hgroup
    unfold queuedCoreGatherCost
    dsimp only [controls] at *
    omega
  · apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    simp only [G,writes,List.map_cons,List.map_nil,writeRight]
    rw [hread 108,hread 109]
    by_cases h108i : i = reg 108 <;> by_cases h109i : i = reg 109 <;>
      by_cases h116i : i = reg 116 <;> by_cases h91i : i = reg 91 <;>
      simp [h108i,h109i,h116i,h91i,hreg.eq_iff,hcontrolM,batch,origins,count]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
