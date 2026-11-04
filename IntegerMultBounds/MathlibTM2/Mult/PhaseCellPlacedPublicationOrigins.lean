module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedCoreOrigins
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGatherPublicationClass
public import IntegerMultBounds.MathlibTM2.Host.EmbedStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOwnedOriginPacket

/-! Generate publication's actual core-origin packet and its count from
retained binary geometry. The same fitting-halo scan also serves exposure. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.NLogN.PhaseCellMatrix
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

/-- Ordinary retained geometry and fresh arithmetic storage for the origin scan. -/
structure PublicationOriginInput (e : Fin 117 → Fin T) (V s width radius L : ℕ) (S : Stacks T A) : Prop where
  geometryFit : s+width+2*radius < 2^V
  lengthFit : L < 2^V
  widthLength : (S.R (e 37)).length = V
  ambientWord : S.R (e 32) = binSyms V s
  coreWidthWord : S.R (e 33) = binSyms V width
  radiusWord : S.R (e 34) = binSyms V radius
  haloLengthWord : S.R (e 35) = binSyms V L
  zero : S.R (e 36) = []
  tableBlank : ∀ j : Fin 117, j.val < 31 → S.R (e j) = []
  savedBlank : S.R (e 104) = []
  tmpBlank : S.R (e 106) = []

def placedPublicationOrigins (e : Fin 117 → Fin T) : Pr P T Q A U :=
  embProg e Empty.elim (preparedCoreOriginsFor (P := Empty) false)

theorem placedPublicationOrigins_exec_within (e : Fin 117 → Fin T) (he : Function.Injective e)
    {V s width radius L : ℕ} (hwidth : 0 < width) (hwide : s+width+2*radius < 2^V)
    (hLfit : L < 2^V) (hA : 4 ≤ A) (hV : 0 < V)
    (v : HS T Q A U) (S : Stacks T A) (h37 : (S.R (e 37)).length = V)
    (hs : S.R (e 32) = binSyms V s) (hw : S.R (e 33) = binSyms V width)
    (hr : S.R (e 34) = binSyms V radius) (hL : S.R (e 35) = binSyms V L) (hz : S.R (e 36) = [])
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R (e k) = [])
    (h104 : S.R (e 104) = []) (h106 : S.R (e 106) = []) (h116 : S.R (e 116) = []) (depth : ℕ) :
    let g := gatherPublicationClass s width radius L
    let origins := (coreSubsetPublicationWindows s width g.length hwidth g.indices g.sublist).origins
    ∃ v' n, v'.user = v.user ∧ n ≤ preparedCoreOriginsCost V s width radius L ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        3*preparedCoreOriginsCost V s width radius L) depth (placedPublicationOrigins e) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R (e 109)
          (origins.flatMap (binSyms V)++S.R (e 109))) (e 116) (List.replicate origins.length tick))}) := by
  dsimp only
  obtain ⟨w,n,hu,hn,hw⟩ := preparedCoreOriginsFor_exec_within (body := fun f : Empty => nomatch f)
    false hwidth hwide hLfit hA hV (embDn e v) (embStk e S) h37 hs hw hr hL hz hblank h104 h106 h116 depth
  obtain ⟨v',_,hu',hex⟩ := exec_emb_ovr_within_stock (e := e) he
    (body' := body) (ι := Empty.elim) (fun f => nomatch f) hw v rfl S rfl
  rw [embOvr_updateR_updateR he] at hex
  refine ⟨v',n,hu'.trans hu,hn,?_⟩
  simpa [placedPublicationOrigins,coreSubsetPublicationWindows,PublicationWindows.restrict,
    gatherPublicationClass,List.flatMap_map,embStk,Function.comp_apply] using hex

/-- Owned packets start blank and are returned in the common retirement state. -/
theorem placedOwnedPublicationOrigins_exec_within (e : Fin 117 → Fin T) (he : Function.Injective e)
    {V s width radius L : ℕ} (hwidth : 0 < width) (hwide : s+width+2*radius < 2^V)
    (hLfit : L < 2^V) (hA : 4 ≤ A) (hV : 0 < V)
    (v : HS T Q A U) (S : Stacks T A) (h37 : (S.R (e 37)).length = V)
    (hs : S.R (e 32) = binSyms V s) (hw : S.R (e 33) = binSyms V width)
    (hr : S.R (e 34) = binSyms V radius) (hL : S.R (e 35) = binSyms V L) (hz : S.R (e 36) = [])
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R (e k) = [])
    (h109 : S.R (e 109) = []) (h104 : S.R (e 104) = []) (h106 : S.R (e 106) = []) (h116 : S.R (e 116) = []) (depth : ℕ) :
    let g := gatherPublicationClass s width radius L
    let origins := (coreSubsetPublicationWindows s width g.length hwidth g.indices g.sublist).origins
    ∃ v' n, v'.user = v.user ∧ n ≤ preparedCoreOriginsCost V s width radius L ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        3*preparedCoreOriginsCost V s width radius L) depth (placedPublicationOrigins e) (Host.mk v S) n
        (Host.mk v' (originPacketState (e 109) (e 116) V origins S)) := by
  dsimp only
  obtain ⟨v',n,hu,hn,hx⟩ := placedPublicationOrigins_exec_within (body := body) e he
    hwidth hwide hLfit hA hV v S h37 hs hw hr hL hz hblank h104 h106 h116 depth
  refine ⟨v',n,hu,hn,?_⟩
  simpa only [originPacketState,h109,List.append_nil] using hx

/-- Generate owned metadata beside an external numerical result without unfolding its bank. -/
theorem placedOwnedPublicationOrigins_after_update_exec_within (e : Fin 117 → Fin T) (he : Function.Injective e)
    (packet count : Fin T) (he109 : e 109 = packet) (he116 : e 116 = count)
    (k : Fin T) (xs : List (Fin (A+4))) (heOff : ∀ j, e j ≠ k)
    {V s width radius L : ℕ} (hwidth : 0 < width) (hwide : s+width+2*radius < 2^V)
    (hLfit : L < 2^V) (hA : 4 ≤ A) (hV : 0 < V)
    (v : HS T Q A U) (S : Stacks T A) (h37 : (S.R (e 37)).length = V)
    (hs : S.R (e 32) = binSyms V s) (hw : S.R (e 33) = binSyms V width)
    (hr : S.R (e 34) = binSyms V radius) (hL : S.R (e 35) = binSyms V L) (hz : S.R (e 36) = [])
    (hblank : ∀ k : Fin 117, k.val < 31 → S.R (e k) = [])
    (h109 : S.R (e 109) = []) (h104 : S.R (e 104) = []) (h106 : S.R (e 106) = []) (h116 : S.R (e 116) = []) (depth : ℕ) :
    let g := gatherPublicationClass s width radius L
    let origins := (coreSubsetPublicationWindows s width g.length hwidth g.indices g.sublist).origins
    ∃ v' n, v'.user = v.user ∧ n ≤ preparedCoreOriginsCost V s width radius L ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v {S with R := Function.update S.R k xs})+depth+
        3*preparedCoreOriginsCost V s width radius L) depth (placedPublicationOrigins e) (Host.mk v {S with R := Function.update S.R k xs}) n
        (Host.mk v' {originPacketState packet count V origins S with R :=
          (Function.update (originPacketState packet count V origins S).R k xs)}) := by
  dsimp only
  let F : Stacks T A := {S with R := Function.update S.R k xs}
  have hread (j : Fin 117) : F.R (e j) = S.R (e j) := by
    simp only [F,Function.update_of_ne (heOff j)]
  obtain ⟨v',n,hu,hn,hx⟩ := placedOwnedPublicationOrigins_exec_within (body := body) e he
    hwidth hwide hLfit hA hV v F
    (by rw [hread]; exact h37) (by rw [hread]; exact hs) (by rw [hread]; exact hw)
    (by rw [hread]; exact hr) (by rw [hread]; exact hL) (by rw [hread]; exact hz)
    (by intro j hj; rw [hread]; exact hblank j hj)
    (by rw [hread]; exact h109) (by rw [hread]; exact h104)
    (by rw [hread]; exact h106) (by rw [hread]; exact h116) depth
  rw [he109,he116] at hx
  have hp : packet ≠ k := by simpa only [he109] using heOff 109
  have hc : count ≠ k := by simpa only [he116] using heOff 116
  have hend := originPacketState_update_off packet count V
    (coreSubsetPublicationWindows s width (gatherPublicationClass s width radius L).length hwidth
      (gatherPublicationClass s width radius L).indices (gatherPublicationClass s width radius L).sublist).origins
    S k xs hp hc
  rw [hend] at hx
  exact ⟨v',n,hu,hn,hx⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
