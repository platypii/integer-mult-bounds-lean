module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpGatherSetup
public import IntegerMultBounds.MathlibTM2.Mult.ChirpGatherExec

/-! # Gather cyclic windows with generated or retained advance controls -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {T Q A : ℕ} {U P : Type} {body : P → Pr P T Q A U} {rg : TblR 10 → Fin T}

/-- Shared mode consumes and restores the supplied control schedule without generating it. -/
def chirpGatherMode (shared : Bool) (rg : TblR 10 → Fin T)
    (dst control savedControl advance window src acc current savedSource buf tmp count : Fin T) : Pr P T Q A U :=
  if shared then gatherBatch dst control savedControl advance window src acc current savedSource buf tmp
  else chirpGatherSetup rg dst control savedControl advance window src acc current savedSource buf tmp count

def chirpGatherModeCost (shared : Bool) (W e s t m w M : ℕ) : ℕ :=
  if shared then M * (14 * ((3 * m + 1) * w) + 25) + 12 * (chirpCenter s t m M * w) + 8
  else M * (6 * tblC W e + 11 * W + 14 * ((3 * m + 1) * w) + 41) +
    22 * (chirpCenter s t m M * w) + 6 * tblC W e + 16

theorem chirpGatherMode_exec (shared : Bool) (hrg : Function.Injective rg)
    {dst control savedControl advance window src acc current savedSource buf tmp count : Fin T}
    (hreg : [dst, control, savedControl, advance, window, src, acc, current, savedSource, buf, tmp, count].Nodup)
    (hcount : ∀ r, rg r ≠ count) (hsaved : ∀ r, rg r ≠ savedControl)
    (hacc : ∀ r, rg r ≠ acc) (hcontrolBank : ∀ r, rg r ≠ control)
    {W e : ℕ} (wl nl : List (Fin (A + 4)))
    (hwl : wl.length = W) (hnl : nl.length = e) (heW : e ≤ W)
    (s t m w M : ℕ) (hs : 0 < s) (hst : s ≤ t) (ht : 0 < t)
    (hk : ∀ j < M, (j + 1) * m < 2 ^ W)
    (hnum : ∀ j < M, s * ((j + 1) * m) < 2 ^ W) (hwidth : m * w < 2 ^ W)
    (st : TblSt 10 A) (hready : ChirpControlReady st s t m w 0)
    (hzero : ∀ i : Fin 10, 4 ≤ i.val → st.val i = 0) (hfit : ∀ i, st.val i < 2 ^ W)
    (u : ZMod s → GaussianInt) (hvalid : ∀ n < M, n * m < t)
    (v : HS T Q A U) (S : Stacks T A) (hS : tblHolds rg S (tblRho W wl nl st))
    (hlen : (S.R count).length = M) (hsrc : S.R src = cstream A w (chirpExtended s m u))
    (hw : (S.R window).length = (3 * m + 1) * w)
    (hcontrol : S.R control = if shared then gatherControls A (chirpAdvancesFrom s t m w 0 M) else [])
    (hclean : ∀ k ∈ [savedControl, advance, acc, current, savedSource, buf, tmp], S.R k = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ chirpGatherModeCost shared W e s t m w M ∧
      Exec body (chirpGatherMode shared rg dst control savedControl advance window src acc current savedSource buf tmp count)
        (mk v S) n (mk v' { S with R := (Function.update S.R dst
          ((List.range M).flatMap (fun j => cstream A w (chirpWindow s t m j u)) ++ S.R dst)) }) := by
  cases shared with
  | false =>
      have hc : S.R control = [] := by simpa only [Bool.false_eq_true, ite_false] using hcontrol
      obtain ⟨v', n, hu, hn, he⟩ := chirpGatherSetup_exec (body := body) hrg hreg
        hcount hsaved hacc hcontrolBank wl nl hwl hnl heW s t m w M hs hst ht hk hnum hwidth
        st hready hzero hfit u hvalid v S hS hlen hsrc hw (by
          intro k hk
          rcases List.mem_cons.mp hk with rfl | hk
          · exact hc
          · exact hclean k hk)
      exact ⟨v', n, hu, hn, he⟩
  | true =>
      have hgather : [dst, control, savedControl, advance, window, src, acc, current, savedSource, buf, tmp].Nodup :=
        (List.nodup_append.mp (show ([dst, control, savedControl, advance, window, src, acc,
          current, savedSource, buf, tmp] ++ [count]).Nodup from hreg)).1
      obtain ⟨v', hu, he⟩ := chirpGather_exec (body := body) hgather s t m w M hs hst ht u hvalid
        v S hcontrol hsrc hw hclean
      exact ⟨v', _, hu, le_rfl, he⟩

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
