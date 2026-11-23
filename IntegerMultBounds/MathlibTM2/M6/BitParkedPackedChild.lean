module

public import IntegerMultBounds.MathlibTM2.M6.BitFlatNodeHandoff

/-! Prepare exact words for a packed recursive entry and read its returned fan. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover.Fallback
open RecursiveInterchangeLayout (Descriptor volume)
open Shared50ModularControl (prime)

theorem packedRowEntry {T N Q : ℕ} {P A U : Type} (body : P → Pr P N Q prime U)
    (host : A → Pr A T Q prime U) (place : Fin N ↪ Fin T) (label : P → A)
    (installed : ∀ p, host (label p) = embProg place label (body p))
    (live : Fin (142080+2) ↪ Fin T) (src dst : Fin (142081+2) ↪ Fin N) (tmp : Fin T)
    (apart : ∀ (r : Fin 142080) (i : Fin 142081), live (r.castAdd 2) ≠ place (src (i.castAdd 2)))
    (srcTmp : ∀ r : Fin 142080, live (r.castAdd 2) ≠ tmp)
    (dstTmp : ∀ i : Fin 142081, place (src (i.castAdd 2)) ≠ tmp)
    (controls : ∀ j : Fin 2, place (src (j.natAdd 142081)) = live (j.natAdd 142080))
    (entry : P) :
    let privatePorts := (List.finRange N).filter (fun j => ∀ i, childReturnFan dst i ≠ j)
    let scratch := privatePorts.map place
    ∃ code : Pr A T Q prime U, ∀ (lane : Descriptor) (seed : Stacks N prime) price,
      let V := volume prime lane
      PackedPieceHandoffWithCharge cleanupWeight V (fun x y => ∀ r : Fin 142080,
        y r.castSucc = Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (x r.castSucc))
        body (body entry) src dst seed price →
      ∀ (data : Fin 142080 → Fin V → ZMod 2) u S, HelperFan live data S →
      S.L tmp = [] → S.R tmp = [] →
      (∀ i : Fin 142081, S.L (place (src (i.castAdd 2))) = [] ∧ S.R (place (src (i.castAdd 2))) = []) →
      (∀ j, (∀ i, src i ≠ j) → S.L (place j) = seed.L j ∧ S.R (place j) = seed.R j) →
      ∃ z F t, Exec host code (mk u S) t (mk z F) ∧ t ≤ tapeCharge cleanupWeight scratch S + 142081*(8*V+10+2*V)+1+price+3 ∧
        z.user = u.user ∧ HelperFan ((childReturnFan dst).trans place) (fun r =>
          Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (data r)) F ∧
        (∀ j, (∀ i, childReturnFan dst i ≠ j) → F.L (place j) = [] ∧ F.R (place j) = []) ∧
        ∀ j, (∀ i, place i ≠ j) → F.L j = S.L j ∧ F.R j = S.R j := by
  intro privatePorts scratch
  have distinct : scratch.Nodup := ((List.nodup_finRange N).filter _).map place.injective
  have mem (j : Fin N) : place j ∈ scratch ↔ ∀ i, childReturnFan dst i ≠ j := by
    simp [scratch,privatePorts,place.injective.eq_iff]
  have retain (i) : place (childReturnFan dst i) ∉ scratch := fun h => (mem _).mp h i rfl
  obtain ⟨prep,prepare⟩ := prepareChildOwners_exec host live (src.trans place) tmp apart srcTmp dstTmp
  refine ⟨(prep.seq (.call (label entry))).seq (clearWorkTapes scratch),?_⟩
  intro lane seed price V child data u S represented left right empty privateTapes
  obtain ⟨v,R,a,setup,paid,user,words,keep,prepBill⟩ := prepare data u S represented controls left right empty
  let D := {S with R := R}
  have physical := words.next place src (fun _ => rfl) (fun _ => rfl)
  obtain ⟨z,F,b,y,run,cost,final,out,effect⟩ := child _ (embDn place v) (embStk place D) physical (by
    intro j off
    exact ⟨(privateTapes j off).1,(keep (place j) (fun i => place.injective.ne (off (i.castAdd 2)))).trans (privateTapes j off).2⟩)
  obtain ⟨q,G,lifted,_,same,view,frame⟩ := exec_emb place.injective installed run v rfl D rfl
  have called := Exec.call (installed entry ▸ lifted : Exec host (host (label entry)) (mk v D) b (mk q G))
  obtain ⟨last,lastUser,erase⟩ := clearWorkTapes_exec host scratch distinct q G
  have childBill := placedCleanup_cost_le place D G cleanupWeight b price frame
    (view ▸ cost) scratch distinct
  have before := prepBill cleanupWeight (2*V) (by
    intro word length
    simp [cleanupWeight,length,Nat.add_comm]) scratch distinct
  refine ⟨last,_,_,(setup.seq called).seq erase,?_,lastUser.trans (same.trans (final.trans user)),?_,?_,?_⟩
  · change a+(b+2)+(tapeCharge cleanupWeight scratch G+1) ≤ _
    change a+tapeCharge cleanupWeight scratch D ≤ _ at before
    omega
  · rw [← view] at out
    have rows : (fun r : Fin 142080 => y r.castSucc) = fun r =>
        Shared50RecursiveNodeRows.transpose (one_dvd lane.rows) (data r) := by
      funext r
      simpa only [Function.comp_apply,Fin.lastCases_castSucc,id_eq] using effect r
    rw [← rows]
    have rep := ParentStageWords.returnFan (bank := place) (F := G) out
    intro i z
    simpa only [embStk,Function.comp_apply,Function.Embedding.trans_apply,ite_eq_right (retain i)] using rep i z
  · intro j away
    simp only [ite_eq_left ((mem j).mpr away),and_self]
  · intro j off
    have away : j ∉ scratch := fun h => by
      obtain ⟨i,_,eq⟩ := List.mem_map.mp h
      exact off i eq
    simpa only [ite_eq_right away] using
      And.intro (frame j off).1 ((frame j off).2.trans (keep j (fun i => off (src (i.castAdd 2)))))

end IntegerMultBounds.MathlibTM2.M6.BitNode
