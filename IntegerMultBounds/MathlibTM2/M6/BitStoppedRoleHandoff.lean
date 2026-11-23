module

public import IntegerMultBounds.MathlibTM2.M6.BitIdleChartHandoff
public import IntegerMultBounds.MathlibTM2.M6.BitFlatIdleLeaf

/-! Execute a stopped interval transpose on the role bank, sharing one leaf workspace. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Machine IntegerMultBounds.Networks Stack Host Cover Cover.Fallback M8.RevMachine
open RecursiveInterchangeLayout
open Shared50ModularControl (prime)

private theorem runOwnerList {T Q V c : ℕ} {P U : Type} (fan : Fin (c+2) ↪ Fin T)
    (body : P → Pr P T Q prime U) (code : Fin c → Pr P T Q prime U)
    (step : (Fin V → ZMod 2) → (Fin V → ZMod 2)) (price : ℝ) (ready : Stacks T prime → Prop)
    (run : ∀ i x u S, HelperFan fan x S → ready S →
      ∃ z F n, Exec body (code i) (mk u S) n (mk z F) ∧ (n : ℝ) ≤ price ∧ z.user = u.user ∧
        HelperFan fan (Function.update x i (step (x i))) F ∧ ready F)
    (ls : List (Fin c)) (distinct : ls.Nodup) (x : Fin c → Fin V → ZMod 2) u S
    (live : HelperFan fan x S) (stock : ready S) :
    ∃ z F n y, Exec body (Prog.seqList (ls.map code)) (mk u S) n (mk z F) ∧
      (n : ℝ) ≤ ls.length*price+1 ∧ z.user = u.user ∧ HelperFan fan y F ∧
      (∀ i ∈ ls, y i = step (x i)) ∧ ∀ i ∉ ls, y i = x i := by
  induction ls generalizing x u S with
  | nil => exact ⟨u,S,1,x,Exec.act .done _,by simp,rfl,live,by simp,by simp⟩
  | cons i ls ih =>
    obtain ⟨fresh,tail⟩ := List.nodup_cons.mp distinct
    obtain ⟨v,D,m,exec,paid,user,updated,prepared⟩ := run i x u S live stock
    obtain ⟨z,F,n,y,rest,cost,same,out,acts,off⟩ := ih tail _ v D updated prepared
    refine ⟨z,F,m+n,y,Exec.seq exec rest,?_,same.trans user,out,?_,?_⟩
    · simp only [List.length_cons,Nat.cast_add,Nat.cast_one]; linarith
    · intro j hj
      rcases List.mem_cons.mp hj with rfl|h
      · rw [off j fresh,Function.update_self]
      · rw [acts j h,Function.update_of_ne (fun (e : j = i) => fresh (e ▸ h))]
    · intro j hj
      simp only [List.mem_cons,not_or] at hj
      rw [off j hj.2,Function.update_of_ne hj.1]

private theorem leafStock {B scratch : ℕ} (headers : Fin 6 → List (Fin (prime+4))) :
    let fan := (Fin.castAddEmb 6 (n := B)).trans (Fin.castAddEmb scratch)
    let slots := (Fin.natAddEmb B (m := 6)).trans (Fin.castAddEmb scratch)
    ∃ seed : Stacks ((B+6)+scratch) prime,
      (∀ i, seed.R (slots i) = headers i) ∧
      (∀ j, (∀ i, fan i ≠ j) → seed.L j = [] ∧ ((∀ i, slots i ≠ j) → seed.R j = [])) ∧ ∀ D : Stacks ((B+6)+scratch) prime,
      (∀ t, (∀ j, fan j ≠ t) → D.L t = seed.L t ∧ D.R t = seed.R t) →
      (∀ j : Fin 6, D.R ((j.natAdd B).castAdd scratch) = headers j) ∧
      ∀ j : Fin scratch, D.L (j.natAdd (B+6)) = [] ∧ D.R (j.natAdd (B+6)) = [] := by
  intro fan slots
  let seed : Stacks ((B+6)+scratch) prime := ⟨[],[],fun _ => [],
    Fin.addCases (Fin.addCases (fun _ => []) headers) (fun _ => [])⟩
  refine ⟨seed,fun i => by simp [seed,slots],?_,?_⟩
  · intro j _
    refine ⟨rfl,fun away => ?_⟩
    revert away
    induction j using Fin.addCases with
    | right j => simp [seed]
    | left j =>
      induction j using Fin.addCases with
      | left j => simp [seed]
      | right j => exact fun away => (away j rfl).elim
  intro D stock
  constructor
  · intro j
    have h := stock ((j.natAdd B).castAdd scratch) (by
      intro l eq
      have e := congrArg Fin.val eq
      change l.val = B+j.val at e
      omega)
    simpa [seed] using h.2
  · intro j
    have h := stock (j.natAdd (B+6)) (by
      intro l eq
      have e := congrArg Fin.val eq
      change l.val = B+6+j.val at e
      omega)
    simpa [seed] using h

private theorem leafSlots_apart {B scratch T : ℕ} (place : Fin ((B+6)+scratch) ↪ Fin T)
    (i : Fin 6) (j : Fin B) :
    place ((i.natAdd B).castAdd scratch) ≠ place ((j.castAdd 6).castAdd scratch) := by
  apply place.injective.ne
  intro eq
  have h := congrArg Fin.val eq
  change B+i.val = j.val at h
  omega

/-- All role words are transposed at the inherited interval addresses. Headers
and scratch are shared by successive owners, then the output is materialized. -/
theorem stoppedRoleSeedHandoff [M8.Machine.Net] {Q : ℕ} {U : Type} (capacity : columnCapacity ≤ Q)
    : ∃ (T : ℕ) (host : Empty → Pr Empty T Q prime U) (program : Pr Empty T Q prime U)
      (input output : Fin (142081+2) ↪ Fin T) (slots : Fin 6 ↪ Fin T),
    (∀ i j, slots i ≠ input j) ∧ (∀ j : Fin 2, output (j.natAdd 142081) = input (j.natAdd 142081)) ∧ ∀ (child lane : Descriptor), 0 < volume prime lane →
    ∀ (position : Fin (volume prime child) ≃ Fin (volume prime lane)),
    lane.width = child.width → InheritedIntervalPositions child lane rfl position →
    let V := volume prime lane
    let price := (descriptorHeaderCost lane : ℝ) +
      ((LeafCore.small+5 : ℕ)*|LeafCore.C|+8+LeafCore.small*(16+8*|LeafCore.C|))*
        ((V : ℝ)*((max 1 child.width : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)
    ∃ prepared : Stacks T prime, (∀ i, prepared.R (slots i) = (Routines.hdr lane i).map bitSymbol) ∧
      (∀ j, (∀ i, input i ≠ j) → prepared.L j = [] ∧ ((∀ i, slots i ≠ j) → prepared.R j = [])) ∧
      PackedPieceHandoff V (fun x y => ∀ (r : Fin 142080) j, y r.castSucc (position j) =
      Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (x r.castSucc ∘ position) j)
      host program input output prepared (⌊142080*price+1⌋₊+142081*(8*V+10)+1) := by
  let B := 142081+2
  let n := B+6
  let fan := (Fin.castAddEmb 6 (n := B)).trans (Fin.castAddEmb LeafCore.small)
  let src := Fin.natAddEmb B (m := 6)
  let port := fun i : Fin 142081 => (i.castAdd 2).castAdd 6
  let body : Empty → Pr Empty (n+LeafCore.small) Q prime U := Empty.elim
  let code := fun i => hostedStoppedDirectory (P := Empty) (U := U) capacity src (port i)
  let roles := (List.finRange 142080).map Fin.castSucc
  obtain ⟨program,materialize⟩ := uniformWordStageSeedHandoff fan body (Prog.seqList (roles.map code))
  let slots := src.trans (Fin.castAddEmb LeafCore.small)
  let place := SweepFile.Exit.chart 0 (n+LeafCore.small)
  refine ⟨_,fun f => embProg (SweepFile.Exit.chart 0 _) id (body f),program,fan.trans (SweepFile.Exit.chart 0 _),returnedFan fan,slots.trans place,?_,returnedFan_counter fan,?_⟩
  · exact leafSlots_apart place
  intro child lane positive position width coords V price
  obtain ⟨seed,headers,blank,prepare⟩ := leafStock (B := B) (scratch := LeafCore.small)
    (fun j => (Routines.hdr lane j).map bitSymbol)
  let step := Shared50RecursiveNodeRows.transpose (α := ZMod 2) (one_dvd lane.rows)
  let ready (S : Stacks (n+LeafCore.small) prime) := ∀ t, (∀ j, fan j ≠ t) →
    S.L t = seed.L t ∧ S.R t = seed.R t
  have placed := flatStageSeed_private seed fan slots _ headers blank
  refine ⟨flatStageSeed seed,placed.1,placed.2,?_⟩
  apply materialize
    seed (fun x y => ∀ (r : Fin 142080) j, y r.castSucc (position j) =
      Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (x r.castSucc ∘ position) j)
    (142080*price+1)
  · intro x u S words stock
    have live := words.helperFan
    obtain ⟨z,F,n',y,ran,paid,user,out,acts,_⟩ := runOwnerList fan body code step price ready (by
      intro i data v D owners fresh
      obtain ⟨b,G,m,changed,exec,cost,same,payload,off,reads⟩ := inheritedLeaf_exec capacity body src (port i)
        child lane rfl position width coords (data i) v D positive (prepare D fresh).1
          (fanPayload owners i) (prepare D fresh).2
      have result : changed = step (data i) := (coords.transpose_iff width _ _).1 reads
      subst changed
      refine ⟨b,G,m,exec,cost,same,fanUpdate i _ owners payload (fun j h => off _ (fan.injective.ne h)),?_⟩
      intro t away
      obtain ⟨l,r⟩ := off t (away (i.castAdd 2)).symm
      exact ⟨l.trans (fresh _ away).1,r.trans (fresh _ away).2⟩)
      _ ((List.nodup_finRange _).map (Fin.castSucc_injective _)) x u S live stock
    refine ⟨z,F,n',y,ran,by simpa only [List.length_map,List.length_finRange,Nat.cast_ofNat] using paid,user,out,?_⟩
    intro r
    exact (coords.transpose_iff width _ _).2 (acts r.castSucc (List.mem_map.mpr ⟨r,List.mem_finRange _,rfl⟩))

theorem stoppedRoleHandoff [M8.Machine.Net] {Q : ℕ} {U : Type} (capacity : columnCapacity ≤ Q)
    : ∃ (T : ℕ) (host : Empty → Pr Empty T Q prime U) (program : Pr Empty T Q prime U)
      (input output : Fin (142081+2) ↪ Fin T), ∀ (child lane : Descriptor), 0 < volume prime lane →
    ∀ (position : Fin (volume prime child) ≃ Fin (volume prime lane)),
    lane.width = child.width → InheritedIntervalPositions child lane rfl position →
    let V := volume prime lane
    let price := (descriptorHeaderCost lane : ℝ) +
      ((LeafCore.small+5 : ℕ)*|LeafCore.C|+8+LeafCore.small*(16+8*|LeafCore.C|))*
        ((V : ℝ)*((max 1 child.width : ℕ) : ℝ)^M8.Machine.BudgetBound.tau)
    ∃ prepared, PackedPieceHandoff V (fun x y => ∀ (r : Fin 142080) j, y r.castSucc (position j) =
      Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (x r.castSucc ∘ position) j)
      host program input output prepared (⌊142080*price+1⌋₊+142081*(8*V+10)+1) := by
  obtain ⟨T,body,code,src,dst,_,_,_,run⟩ := stoppedRoleSeedHandoff (U := U) capacity
  refine ⟨T,body,code,src,dst,?_⟩
  intro child lane pos position width coords
  obtain ⟨seed,_,_,exec⟩ := run child lane pos position width coords
  exact ⟨seed,exec⟩

theorem leafBill_bound (V width header : ℕ) (rate tau : ℝ)
    (vol : 0 < V) (active : 0 < width) (headers : header ≤ 110*V) (nonneg : 0 ≤ rate)
    (exponent : 0 ≤ tau) :
    ((⌊142080*((header : ℝ)+rate*(V*((max 1 width : ℕ) : ℝ)^tau))+1⌋₊+
      142081*(8*V+10)+1 : ℕ) : ℝ) ≤
      ((130+rate)*(width : ℝ)^tau)*(V*142080 : ℕ) := by
  rw [max_eq_right active]
  have v : (1 : ℝ) ≤ V := by exact_mod_cast vol
  have w : (1 : ℝ) ≤ width := by exact_mod_cast active
  have power := Real.one_le_rpow w exponent
  have hv := le_mul_of_one_le_right (Nat.cast_nonneg (α := ℝ) V) power
  have hh : (header : ℝ) ≤ 110*V := by exact_mod_cast headers
  have floorBound := Nat.floor_le (by positivity :
    0 ≤ 142080*((header : ℝ)+rate*(V*(width : ℝ)^tau))+1)
  push_cast
  nlinarith only [floorBound,hh,v,hv]

/-- A single leaf constant covers all positive stopped widths. The volume
in the bound counts the entire scheduled child, including every role. -/
theorem stoppedRoleCost [M8.Machine.Net] {U : Type} :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Q : ℕ}, columnCapacity ≤ Q → ∀ (child lane : Descriptor)
      (positive : 0 < volume prime lane) (active : 0 < child.width)
      (position : Fin (volume prime child) ≃ Fin (volume prime lane)),
      lane.width = child.width → InheritedIntervalPositions child lane rfl position →
      ∃ price : ℕ, (price : ℝ) ≤ (C*(child.width : ℝ)^M8.Machine.BudgetBound.tau)*(volume prime lane*142080 : ℕ) ∧
      PackedWindowHandoff U Q (volume prime lane) (fun x y => ∀ (r : Fin 142080) j, y r.castSucc (position j) =
        Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (x r.castSucc ∘ position) j) price := by
  let rate : ℝ := (LeafCore.small+5 : ℕ)*|LeafCore.C|+8+LeafCore.small*(16+8*|LeafCore.C|)
  have pos : 0 ≤ rate := by dsimp [rate]; positivity
  refine ⟨130+rate,by positivity,?_⟩
  intro Q capacity child lane positive active position width coords
  obtain ⟨T,host,program,input,output,run⟩ := stoppedRoleHandoff (U := U) capacity
  obtain ⟨prepared,ran⟩ := run child lane positive position width coords
  refine ⟨_,?_,Empty,T,host,program,input,output,prepared,ran⟩
  exact leafBill_bound _ _ _ rate _ positive active
    (descriptorHeaderCost_le lane (LeafCore.positive_of_volume positive)) pos M8.Machine.BudgetBound.exponent_range.1.le

/-- At a stopped child the same finite program works at every descriptor width.
Its push bound can therefore be absorbed once into the leaf coefficient,
including the cleanup of any selected private tapes. -/
theorem stoppedRoleSeedCleanupCost [M8.Machine.Net] {U : Type} {Q : ℕ} (capacity : columnCapacity ≤ Q) :
    ∃ (C : ℝ) (T : ℕ) (host : Empty → Pr Empty T Q prime U) (program : Pr Empty T Q prime U)
      (src dst : Fin (142081+2) ↪ Fin T) (slots : Fin 6 ↪ Fin T), 0 ≤ C ∧
    (∀ i j, slots i ≠ src j) ∧ (∀ j : Fin 2, dst (j.natAdd 142081) = src (j.natAdd 142081)) ∧
    ∀ (child lane : Descriptor) (position : Fin (volume prime child) ≃ Fin (volume prime lane)),
      0 < volume prime lane → 0 < child.width → lane.width = child.width →
      InheritedIntervalPositions child lane rfl position →
      let V := volume prime lane
      ∃ seed : Stacks T prime, (∀ i, seed.R (slots i) = (Routines.hdr lane i).map bitSymbol) ∧
      (∀ j, (∀ i, src i ≠ j) → seed.L j = [] ∧ ((∀ i, slots i ≠ j) → seed.R j = [])) ∧
      PackedPieceHandoffWithCharge cleanupWeight V
        (fun x y => ∀ (r : Fin 142080) j, y r.castSucc (position j) =
          Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (x r.castSucc ∘ position) j)
        host program src dst seed ⌊(C*(child.width : ℝ)^M8.Machine.BudgetBound.tau)*(V*142080 : ℕ)⌋₊ := by
  obtain ⟨T,host,program,src,dst,slots,privateSlots,controls,worker⟩ := stoppedRoleSeedHandoff (U := U) capacity
  let rate : ℝ := (LeafCore.small+5 : ℕ)*|LeafCore.C|+8+LeafCore.small*(16+8*|LeafCore.C|)
  let push := Fast.Main.mnProgPush program
  let factor := 1+6*push
  have rate_nonneg (m : ℕ) (r : ℝ) : 0 ≤ ((m+5 : ℕ) : ℝ)*|r|+8+m*(16+8*|r|) := by positivity
  have nonneg : 0 ≤ rate := rate_nonneg _ _
  refine ⟨(factor : ℝ)*(130+rate),T,host,program,src,dst,slots,mul_nonneg (Nat.cast_nonneg _) (add_nonneg (by norm_num) nonneg),privateSlots,controls,?_⟩
  intro child lane position positive active width coords V
  obtain ⟨seed,headers,blank,run⟩ := worker child lane positive position width coords
  refine ⟨seed,headers,blank,?_⟩
  intro x u S ready prepared
  obtain ⟨z,F,n,y,exec,paid,user,out,effect⟩ := run x u S ready prepared
  refine ⟨z,F,n,y,exec,?_,user,out,effect⟩
  intro js distinct
  let stock := tapeCharge cleanupWeight js
  have growth := recordCleanup_cost_le js distinct exec (c := push) le_rfl (fun e => nomatch e)
  change stock F+1 ≤ stock S+1+6*(push*n) at growth
  have joint : n+stock F ≤ stock S+factor*n := by
    dsimp only [factor]
    rw [Nat.add_mul,Nat.one_mul,Nat.mul_assoc]
    omega
  have time := (Nat.cast_le (α := ℝ)).mpr paid
  have bill := time.trans (leafBill_bound _ _ _ rate _ positive active
    (descriptorHeaderCost_le lane (LeafCore.positive_of_volume positive)) nonneg M8.Machine.BudgetBound.exponent_range.1.le)
  have scaled := mul_le_mul_of_nonneg_left bill (Nat.cast_nonneg (α := ℝ) factor)
  apply joint.trans (Nat.add_le_add_left (Nat.le_floor _) _)
  simpa only [Nat.cast_mul,mul_assoc] using scaled

theorem stoppedRoleCleanupCost [M8.Machine.Net] {U : Type} {Q : ℕ} (capacity : columnCapacity ≤ Q) :
    ∃ (C : ℝ) (T : ℕ) (host : Empty → Pr Empty T Q prime U) (program : Pr Empty T Q prime U)
      (src dst : Fin (142081+2) ↪ Fin T), 0 ≤ C ∧
    ∀ (child lane : Descriptor) (position : Fin (volume prime child) ≃ Fin (volume prime lane)),
      0 < volume prime lane → 0 < child.width → lane.width = child.width →
      InheritedIntervalPositions child lane rfl position →
      let V := volume prime lane
      ∃ seed : Stacks T prime, PackedPieceHandoffWithCharge cleanupWeight V
        (fun x y => ∀ (r : Fin 142080) j, y r.castSucc (position j) =
          Shared50RecursiveNodeRows.transpose (one_dvd child.rows) (x r.castSucc ∘ position) j)
        host program src dst seed ⌊(C*(child.width : ℝ)^M8.Machine.BudgetBound.tau)*(V*142080 : ℕ)⌋₊ := by
  obtain ⟨C,T,body,code,src,dst,_,pos,_,_,run⟩ := stoppedRoleSeedCleanupCost (U := U) capacity
  refine ⟨C,T,body,code,src,dst,pos,?_⟩
  intro child lane position live width same coords
  obtain ⟨seed,_,_,exec⟩ := run child lane position live width same coords
  exact ⟨seed,exec⟩

/-- Only active scheduled children require a recursive handoff. Below the
cutoff the role program fits the ordinary linear leaf allowance. -/
theorem roleHandoffAtCutoff [M8.Machine.Net] {U : Type} :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Q : ℕ}, columnCapacity ≤ Q → ∀ (scheduled lane : Descriptor)
      (cutoff budget : ℕ), let stream := role scheduled 142080
      ∀ position : Fin (volume prime stream) ≃ Fin (volume prime lane),
      0 < volume prime lane → 0 < scheduled.width → lane.width = scheduled.width →
      volume prime lane*142080 = volume prime scheduled →
      InheritedIntervalPositions stream lane rfl position →
      let effect := fun (x y : Fin 142081 → Fin (volume prime lane) → ZMod 2) => ∀ (r : Fin 142080) j, y r.castSucc (position j) =
        Shared50RecursiveNodeRows.transpose (one_dvd stream.rows) (x r.castSucc ∘ position) j
      (scheduled.width ≤ cutoff → ⌊(C*(scheduled.width : ℝ)^M8.Machine.BudgetBound.tau)*volume prime scheduled⌋₊ ≤ budget) →
      (cutoff < scheduled.width → PackedWindowHandoff U Q (volume prime lane) effect budget) →
      PackedWindowHandoff U Q (volume prime lane) effect budget := by
  obtain ⟨C,pos,leaf⟩ := stoppedRoleCost (U := U)
  refine ⟨C,pos,?_⟩
  intro Q capacity scheduled lane cutoff budget stream position vol width same size coords effect allowance recurse
  by_cases active : cutoff < scheduled.width
  · exact recurse active
  obtain ⟨price,bill,P,T,body,code,src,dst,seed,run⟩ := leaf capacity stream lane vol width position same coords
  rw [size] at bill
  have paid := (Nat.le_floor bill).trans (allowance (Nat.le_of_not_gt active))
  refine ⟨P,T,body,code,src,dst,seed,?_⟩
  intro x u S words stock
  obtain ⟨z,F,n,y,exec,cost,rest⟩ := run x u S words stock
  exact ⟨z,F,n,y,exec,cost.trans paid,rest⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
