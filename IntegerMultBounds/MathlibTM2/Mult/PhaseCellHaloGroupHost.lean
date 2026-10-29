module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloGroupCode
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloOriginPackets
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalGroupHost
public import IntegerMultBounds.MathlibTM2.Fast.TableBounds
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedOriginHost

/-! Execute a clipped length class and publish its binary origins and owned
unary count, preserving the borrowed output suffix. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

theorem countedOriginHost_exec {W V s t band a b L steps : ℕ}
    (code : TblCode 16) (st : TblSt 16 A)
    (hc : TblDo A W V code st (fun st' =>
      st'.acc = ((haloLengthGroup s t band a b L).flatMap
        (fun phase => tblPairs A V (haloStart s t band a phase) 0)).reverse ++ st.acc) steps)
    (hpacket : s ≤ 2^V) (hw : V ≤ W) (hA : 4 ≤ A)
    (hV : 0 < V) (hbound : ∀ j, st.val j < 2^W) (hacc : st.acc = [])
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho W (List.replicate W tick) (List.replicate V tick) st))
    (h104 : S.R 104 = []) (h106 : S.R 106 = []) (h116 : S.R 116 = []) :
    ∃ v' S' m, ∃ st' : TblSt 16 A, v'.user = v.user ∧
      m ≤ steps*tblC W V + (haloLengthGroup s t band a b L).length*(8*V+6)+6 ∧
      Exec body (countedOriginHost code) (mk v S) m (mk v' S') ∧
      S'.R 109 = haloOriginPackets A V s t band a b L ++ S.R 109 ∧
      S'.R 116 = List.replicate (haloLengthGroup s t band a b L).length tick ∧
      tblHolds originReg S' (tblRho W (List.replicate W tick) (List.replicate V tick) ⟨st'.val, []⟩) ∧
      (∀ j, st'.val j < 2^W) ∧ S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ k, k ≠ 109 → k ≠ 116 → (∀ r, originReg r ≠ k) → S'.R k = S.R k := by
  let xs := (haloLengthGroup s t band a b L).map (haloStart s t band a)
  have hx : ∀ x ∈ xs, x < 2^V := by
    intro x hx
    obtain ⟨phase, hp, rfl⟩ := List.mem_map.mp hx
    obtain ⟨_, hL, hlen⟩ := (mem_haloLengthGroup s t band a b L phase).mp hp
    have hstop := haloStop_le s t band b phase
    have hstart : haloStart s t band a phase < s := by
      dsimp only [haloLength] at hlen
      omega
    exact hstart.trans_le hpacket
  have hc' : TblDo A W V code st (fun st' =>
      st'.acc = (xs.flatMap (fun x => tblPairs A V x 0)).reverse ++ st.acc) steps := by
    simpa only [xs, List.flatMap_map] using hc
  simpa only [xs, List.length_map, List.flatMap_map, haloOriginPackets] using
    countedOriginListHost_exec xs code st hc' hx hw hA hV hbound hacc v S hS h104 h106 h116


/-- The ambient scan is an instance of the shared counted-origin publisher. -/
def haloGroupCountedHost : Pr P₀ 117 Q A U := countedOriginHost haloGroupCode

theorem haloGroupCountedHost_exec {W V s t band a b L : ℕ} (st : TblSt 16 A)
    (hs' : st.val 0 = s) (hband : st.val 2 = band) (hL' : st.val 3 = L)
    (hden : st.val 6 = 2*(t-s)) (hone : st.val 7 = 1) (hz : st.val 12 = 0)
    (hcount : st.val 15 = t-s+1) (ha : st.val 13 = a) (hb : st.val 14 = b) (has : a ≤ s) (hbs : b ≤ s)
    (hs : 0 < s) (hst : s < t) (hL : 0 < L)
    (hwide : 8*(t+1)^2+2*band+8 < 2^W) (hpacket : s ≤ 2^V) (hw : V ≤ W) (hA : 4 ≤ A)
    (hV : 0 < V) (hbound : ∀ j, st.val j < 2^W) (hacc : st.acc = [])
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho W (List.replicate W tick) (List.replicate V tick) st))
    (h104 : S.R 104 = []) (h106 : S.R 106 = []) (h116 : S.R 116 = []) :
    ∃ v' S' m, ∃ st' : TblSt 16 A, v'.user = v.user ∧
      m ≤ (36*(t-s+1)+3)*tblC W V + (haloLengthGroup s t band a b L).length*(8*V+6)+6 ∧
      Exec body haloGroupCountedHost (mk v S) m (mk v' S') ∧
      S'.R 109 = haloOriginPackets A V s t band a b L ++ S.R 109 ∧
      S'.R 116 = List.replicate (haloLengthGroup s t band a b L).length tick ∧
      tblHolds originReg S' (tblRho W (List.replicate W tick) (List.replicate V tick) ⟨st'.val, []⟩) ∧
      (∀ j, st'.val j < 2^W) ∧ S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      ∀ k, k ≠ 109 → k ≠ 116 → (∀ r, originReg r ≠ k) → S'.R k = S.R k :=
  countedOriginHost_exec haloGroupCode st
    (haloGroupCode_do st hs' hband hL' hden hone hz hcount ha hb has hbs hs hst hL hwide)
    hpacket hw hA hV hbound hacc v S hS h104 h106 h116


end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
