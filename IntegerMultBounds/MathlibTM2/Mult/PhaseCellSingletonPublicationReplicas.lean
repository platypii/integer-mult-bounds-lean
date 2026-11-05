module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaPublicationData
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSeamRowsCommonWidth

/-! Pair actual seam rows with ambient replica lines without decoding or
reordering the archive. Each boundary class publishes one owned core. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.LayerMachine

variable {A s L : ℕ}

def singletonPublicationReplicas (rows : List (List GaussianInt))
    (ambient : List (List (Fin (A+4)))) : List (PublicationReplica A) :=
  List.zipWith (fun row line => ⟨[row],[row],line⟩) rows ambient

theorem singletonPublicationReplicas_spec (windows : PublicationWindows s L)
    (hwindow : windows.origins.length = 1) (W : ℕ)
    (rows : List (List GaussianInt)) (ambient : List (List (Fin (A+4))))
    (hlen : rows.length = ambient.length) (hrows : ∀ row ∈ rows, row.length = L)
    (hambient : ∀ line ∈ ambient, line.length = s*W) :
    let replicas := singletonPublicationReplicas rows ambient
    replicas.length = rows.length ∧ replicas.map PublicationReplica.ambient = ambient ∧
    replicas.flatMap (PublicationReplica.input W) = cstream A W rows.flatten ∧
    List.Forall₂ (fun row r => r.rows = [row]) rows replicas ∧
    ∀ r ∈ replicas, r.Valid windows W 0 := by
  induction rows generalizing ambient with
  | nil =>
    have ha : ambient = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen.symm)
    subst ambient
    simp [singletonPublicationReplicas,cstream]
  | cons row rows ih =>
    cases ambient with
    | nil => simp at hlen
    | cons line ambient =>
      obtain ⟨hn,ha,hinput,hpairs,hvalid⟩ := ih ambient (by simpa using hlen)
        (fun xs hx => hrows xs (by simp [hx])) (fun xs hx => hambient xs (by simp [hx]))
      let r : PublicationReplica A := ⟨[row],[row],line⟩
      have hr : r.Valid windows W 0 := by
        refine ⟨by simpa [r] using hwindow.symm,?_,?_,by simp [r],by simp [r],hambient line (by simp)⟩
        all_goals
          intro xs hx
          have he : xs = row := by simpa [r] using hx
          subst xs
          exact hrows row (by simp)
      dsimp only
      rw [show singletonPublicationReplicas (row::rows) (line::ambient) =
        r::singletonPublicationReplicas rows ambient from rfl]
      refine ⟨by simp [hn],by simpa [r] using congrArg (List.cons line) ha,?_,.cons rfl hpairs,?_⟩
      · simp only [List.flatMap_cons,hinput,List.flatten_cons,←cstream_append,PublicationReplica.input,r,
          List.flatten_cons,List.flatten_nil,List.append_nil]
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hr
        · exact hvalid x hx


open IntegerMultBounds.NLogN.PhaseCellMatrix ScalarPlacement

theorem seamPublicationReplicas_spec [NeZero s] (p width k W : ℕ)
    (r : FamilyDispatchInput s A)
    (J : FamilyDispatchInput s A → (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (rows : List (List GaussianInt)) (h : SeamCropRows p width r J k rows)
    (windows : PublicationWindows s (coreLength s width k)) (hwindow : windows.origins.length = 1)
    (ambient : List (List (Fin (A+4)))) (hlen : ambient.length = r.inputs.length)
    (hambient : ∀ line ∈ ambient, line.length = s*W) :
    let wideRows := rows.map (List.map (symZ (2*p+13)))
    let replicas := singletonPublicationReplicas wideRows ambient
    replicas.length = r.inputs.length ∧ replicas.map PublicationReplica.ambient = ambient ∧
    replicas.flatMap (PublicationReplica.input W) = cstream A W (rows.flatten.map (symZ (2*p+13))) ∧
    List.Forall₂ (fun row replica => replica.rows = [row]) wideRows replicas ∧
    ∀ replica ∈ replicas, replica.Valid windows W 0 := by
  have hn : rows.length = r.inputs.length := by
    simpa only [List.length_reverse] using h.2.length_eq.symm
  have hr : ∀ row ∈ rows.map (List.map (symZ (2*p+13))), row.length = coreLength s width k := by
    intro row hrow
    obtain ⟨xs,hxs,rfl⟩ := List.mem_map.mp hrow
    simpa only [List.length_map] using h.1 xs hxs
  have hh := singletonPublicationReplicas_spec windows hwindow W
    (rows.map (List.map (symZ (2*p+13)))) ambient (by simp [hn,hlen]) hr hambient
  simpa only [List.length_map,hn,List.map_flatten] using hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
