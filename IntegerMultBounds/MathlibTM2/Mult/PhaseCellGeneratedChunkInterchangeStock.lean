module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedChunkInterchange
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterchangeHeaderStock
public import IntegerMultBounds.MathlibTM2.Host.PlacedSwapStock

/-! One generated chunk stage pays its native header construction, reuses the
selected swap reserve and erases headers without boundary stock growth. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

theorem generatedChunkInterchange_exec_within {t₀ T Q K : ℕ} {U P : Type}
    (body : P → Pr P T Q (prime+K) U)
    (hd : Fin 5 → Fin t₀) (pay : Fin t₀) (hi : Function.Injective hd)
    (hpay : ∀ k, hd k ≠ pay) (hQ : swapStates hd pay hi ≤ Q)
    (ι : Fin (swapT t₀) → Fin T) (hι : Function.Injective ι) (hT : swapT t₀ ≤ T)
    (dims : Fin 5 → Fin T) (a half par bits cnt work : Fin T)
    (hgen : ∀ k, [dims k,ι (reg (hd k)),a,half,par,bits,cnt,work].Nodup)
    (hdisjoint : ∀ k j, ι (reg (hd k)) ≠ dims j)
    (outerCount blockWidth d : ℕ) (houter : 0 < outerCount) (hblock : 0 < blockWidth)
    (xs : List Bool)
    (hlen : xs.length = BinaryAdjacentWidthInterchange.volume outerCount (2^d) 1 (2^d) blockWidth)
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K))
    (hL : ∀ i, S.L i = [])
    (hpriv : ∀ j : Fin (swapT t₀), t₀ ≤ j.val → S.R (ι j) = [])
    (hdims : ∀ k, (S.R (dims k)).length = swapValues outerCount 1 blockWidth d d k)
    (hhdr : ∀ k, S.R (ι (reg (hd k))) = [])
    (hgenBlank : ∀ i ∈ [a,half,par,bits,cnt,work], S.R i = [])
    (hsrc : S.R (ι (reg pay)) = xs.map bitSymbol)
    (hother : ∀ i, i ≠ pay → (∀ k, hd k ≠ i) →
      ∀ s ∈ S.R (ι (reg i)), s ≠ blank ∧ s.val < prime+4) (depth : ℕ) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ generatedChunkInterchangeCost T t₀ outerCount blockWidth d (∑ j, (S.R (ι j)).length) ∧
      ExecWithin body (fun z c => mnSize c+z ≤ mnSize (mk v S)+depth+
        2*(21*(outerCount+1+blockWidth+d+d)+56)+
        T*(2*SwapMachineStock.reserve outerCount 1 blockWidth d d+2)+3*T+20) depth (generatedChunkInterchange hd pay hi hQ ι hι hT dims a half par bits cnt work)
        (mk v S) n (mk v' {S with L := fun _ => [], R := (Function.update S.R (ι (reg pay))
          ((swapList outerCount (2^d) 1 (2^d) blockWidth false xs).map bitSymbol))}) := by
  obtain ⟨x,hx⟩ := bitArray_of_length xs hlen
  let dst := fun k => ι (reg (hd k))
  have hdst : Function.Injective dst := fun i j he => hi (BinaryInterchangeRun.slot_injective (hι he))
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁,hheaders,hoff,hv,hc⟩ := interchangeHeaders_exec (body := body)
    dims dst hdst a half par bits cnt work hgen hdisjoint outerCount 1 blockWidth d d v S hdims hhdr hgenBlank
  let R := canonicalHeaderListR (fun i => (S.R i).length) (replicaKeyHeaderFields dims dst) S.R
  let M : Stacks T (prime+K) := {S with R := R}
  have hframe (i : Fin T) (hi : ∀ k, dst k ≠ i) : M.R i = S.R i := hoff i hi
  have hsrcOff (k : Fin 5) : dst k ≠ ι (reg pay) := by
    intro he
    exact hpay k (BinaryInterchangeRun.slot_injective (hι he))
  have hsource : M.R (ι (reg pay)) = S.R (ι (reg pay)) := hframe _ hsrcOff
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := placedSwapProg_exec_within body hd pay hi hQ ι hι hT
    outerCount 1 blockWidth d d (interchangeHeaderBits outerCount 1 blockWidth d d)
    (by omega) (by omega) hv hc houter (by decide) hblock x v₁ M hL
    (by
      intro j hj
      rw [hframe]
      · exact hpriv j hj
      · intro k he
        have hh := congrArg Fin.val (hι he)
        change (hd k).val = j.val at hh
        have hk := (hd k).isLt
        omega)
    hheaders (by rw [hsource,hsrc,←hx,List.map_ofFn]; rfl)
    (by
      intro i hip hheads s hs
      rw [hframe] at hs
      · exact hother i hip hheads s hs
      · intro k he
        exact hheads k (BinaryInterchangeRun.slot_injective (hι he))) depth
  let H := 21*(outerCount+1+blockWidth+d+d)+56
  let extra := T*(2*SwapMachineStock.reserve outerCount 1 blockWidth d d+2)+3*T+20
  let bound := mnSize (mk v S)+depth+2*H+extra
  have hw₁ := mn_native_exec_within he₁ 2 (replicaKeyHeaders_native dims dst a half par bits cnt work)
    depth (mnSize (mk v S)+depth+2*H) (by omega)
  have hsetup := hw₁.final
  change mnSize (mk v₁ M)+depth ≤ mnSize (mk v S)+depth+2*H at hsetup
  have hw₁' := hw₁.mono (J := fun z c => mnSize c+z ≤ bound) (by
    intro z c hc
    dsimp only [bound]
    omega)
  have hw₂ := he₂.mono (J := fun z c => mnSize c+z ≤ bound) (by
    intro z c hc
    dsimp only [bound,extra]
    omega)
  let F : Stacks T (prime+K) := {M with L := fun _ => [], R := (Function.update M.R (ι (reg pay))
    (swapList outerCount (2^d) 1 (2^d) blockWidth blank (M.R (ι (reg pay)))))}
  change ExecWithin body _ depth _ _ n₂ (mk v₂ F) at hw₂
  obtain ⟨v₃,hu₃,he₃⟩ := clearWords_exec (body := body) (List.ofFn dst)
    (List.nodup_ofFn_ofInjective hdst) v₂ F
  have hw₃ := mn_native_exec_within he₃ 0 (clearWords_native (List.ofFn dst))
    depth bound (by have hh := hw₂.final; omega)
  have hwhole := ExecWithin.seq hw₁' (ExecWithin.seq hw₂ hw₃)
  change ExecWithin body _ depth
    (generatedChunkInterchange hd pay hi hQ ι hι hT dims a half par bits cnt work) (mk v S) _ _ at hwhole
  obtain ⟨vf,n,huser,htime,he⟩ := generatedChunkInterchange_exec body hd pay hi hpay hQ ι hι hT
    dims a half par bits cnt work hgen hdisjoint outerCount blockWidth d houter hblock
    xs hlen v S hL hpriv hdims hhdr hgenBlank hsrc hother
  obtain ⟨hsteps,hfinal⟩ := hwhole.toExec.unique he
  rw [hsteps,hfinal] at hwhole
  refine ⟨vf,n,huser,htime,?_⟩
  simpa only [bound,H,extra,Nat.add_assoc] using hwhole

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
