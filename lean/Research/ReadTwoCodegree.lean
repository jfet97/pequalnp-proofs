import Mathlib
import PEqualNP.Defs.ReadTwo

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

namespace PEqualNP.ReadTwo.Research

-- The prefix evaluation argument is adapted from L_meta_1942 (upstream PR #4373).
private def run (gates : List Gate) (xs : List Bool) : List Bool :=
  (Circuit.mk gates 0).wires xs

private theorem runCons (g : Gate) (gates : List Gate) (xs : List Bool) :
    run (g :: gates) xs = run gates (xs ++ [g.op.eval (g.inputs.map (xs.getD · false))]) := rfl

private theorem runLength (gates : List Gate) (xs : List Bool) :
    (run gates xs).length = xs.length + gates.length := by
  induction gates generalizing xs with
  | nil => simp [run, Circuit.wires]
  | cons g gates ih => rw [runCons, ih]; simp; omega

private theorem runKeeps (gates : List Gate) (xs : List Bool) (i : ℕ) (hi : i < xs.length) :
    (run gates xs).getD i false = xs.getD i false := by
  induction gates generalizing xs with
  | nil => rfl
  | cons g gates ih =>
    rw [runCons, ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

private theorem wvalInput {n w : ℕ} {C : Circuit} {x : Fin n → Bool} (hw : w < n) :
    wval C x w = x ⟨w, hw⟩ := by
  have hi : w < (List.ofFn x).length := by simpa using hw
  change (run C.gates (List.ofFn x)).getD w false = _
  rw [runKeeps _ _ _ hi, List.getD_eq_getElem _ _ hi]
  simp

private theorem twoInputs {n j : ℕ} {C : Circuit} (model : TopForm.IsAO2 n C)
    (hj : j < C.gates.length) : (gateAt C j).inputs = [in0 C j, in1 C j] := by
  have real : gateAt C j ∈ C.gates := by
    rw [gateAt, List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  obtain ⟨a, b, eq⟩ := List.length_eq_two.mp (model.2.2 _ real)
  simp [in0, in1, eq]

private theorem wvalGate {n j : ℕ} {C : Circuit} (model : TopForm.IsAO2 n C)
    (x : Fin n → Bool) (hj : j < C.gates.length) :
    wval C x (n + j) = (gateAt C j).op.eval [wval C x (in0 C j), wval C x (in1 C j)] := by
  let front := run (C.gates.take j) (List.ofFn x)
  have length : front.length = n + j := by
    simp [front, runLength, Nat.min_eq_left hj.le]
  have split : run C.gates (List.ofFn x) = run (gateAt C j :: C.gates.drop (j + 1)) front := by
    simp only [front, gateAt, List.getD_eq_getElem _ _ hj, run, Circuit.wires, ← List.foldl_append,
      ← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have read (i : ℕ) (hi : i ∈ (gateAt C j).inputs) :
      (run C.gates (List.ofFn x)).getD i false = front.getD i false := by
    rw [split, runKeeps _ _ _ (by rw [length]; exact model.2.1 j hj i hi)]
  have first : in0 C j ∈ (gateAt C j).inputs := by rw [twoInputs model hj]; simp
  have second : in1 C j ∈ (gateAt C j).inputs := by rw [twoInputs model hj]; simp
  change (run C.gates (List.ofFn x)).getD (n + j) false =
    (gateAt C j).op.eval [(run C.gates (List.ofFn x)).getD (in0 C j) false,
      (run C.gates (List.ofFn x)).getD (in1 C j) false]
  rw [read _ first, read _ second, split, runCons, runKeeps _ _ _ (by simp [length]),
    List.getD_append_right _ _ _ _ (by omega)]
  simp [length, twoInputs model hj]

private theorem andTrue {n j a b : ℕ} {C : Circuit} {x : Fin n → Bool}
    (model : TopForm.IsAO2 n C) (gate : andOn C j a b)
    (left : wval C x a = true) (right : wval C x b = true) : wval C x (n + j) = true := by
  rw [wvalGate model x gate.1.1, gate.1.2]
  rcases gate.2 with ⟨ea, eb⟩ | ⟨eb, ea⟩
  · simp [ea, eb, left, right, GateOp.eval]
  · simp [ea, eb, left, right, GateOp.eval]

private theorem orPathTrue {n a b : ℕ} {C : Circuit} {x : Fin n → Bool}
    (model : TopForm.IsAO2 n C) (path : orp C n a b) (start : wval C x a = true) :
    wval C x b = true := by
  induction path with
  | refl => exact start
  | @tail u v _ edge ih =>
    obtain ⟨_, j, rfl, hor, member⟩ := edge
    rw [twoInputs model hor.1] at member
    rw [wvalGate model x hor.1, hor.2]
    rcases List.mem_cons.mp member with eq | eq
    · simp [← eq, ih, GateOp.eval]
    · have eq' := List.mem_singleton.mp eq
      simp [← eq', ih, GateOp.eval]

private theorem indWireTrue {n w : ℕ} {C : Circuit} {W : Finset ℕ}
    (input : w < n) (member : w ∈ W) : wval C (indW n W) w = true := by
  rw [wvalInput input]
  simp [indW, member]

theorem junkStarOfSoundness {n N M g c cb : ℕ} {C : Circuit}
    {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop}
    (model : TopForm.IsAO2 n C) (layout : Layout n pw lw) (sound : Snd22 n C pw lw I)
    (top : andOn C g c cb) (toOutput : orp C n (n + g) C.output) :
    junkStar C n pw lw I g c cb := by
  classical
  refine ⟨top, toOutput, ?_⟩
  intro p l j₁ a v j₂ u b source₁ path₁ bottom₂ path₂ noPL m hm z hz
  by_contra noZM
  let points : Finset (Fin N) := {p, z}
  let lines : Finset (Fin M) := {l, m}
  have noIncidences (r : Fin N) (hr : r ∈ points) (s : Fin M) (hs : s ∈ lines) : ¬ I r s := by
    simp only [points, lines, Finset.mem_insert, Finset.mem_singleton] at hr hs
    rcases hr with rfl | rfl <;> rcases hs with rfl | rfl
    · exact noPL
    · exact hm.2
    · exact hz.2
    · exact noZM
  have pointCount : points.card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
  have lineCount : lines.card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
  let wires := points.image pw ∪ lines.image lw
  have pointTrue (r : Fin N) (hr : r ∈ points) : wval C (indW n wires) (pw r) = true :=
    indWireTrue (layout.2.2.2.1 r) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hr))
  have lineTrue (s : Fin M) (hs : s ∈ lines) : wval C (indW n wires) (lw s) = true :=
    indWireTrue (layout.2.2.2.2 s) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hs))
  have pReaches : orp C n (pw p) a := by
    change p ∈ sh C n pw a
    rw [source₁.1.2]
    exact Set.mem_singleton p
  have lReaches : orp C n (lw l) b := by
    change l ∈ sh C n lw b
    rw [bottom₂.2.1]
    exact Set.mem_singleton l
  have leftGate := andTrue model source₁.1.1
    (orPathTrue model pReaches (pointTrue p (by simp [points])))
    (orPathTrue model hm.1 (lineTrue m (by simp [lines])))
  have rightGate := andTrue model bottom₂.1
    (orPathTrue model hz.1 (pointTrue z (by simp [points])))
    (orPathTrue model lReaches (lineTrue l (by simp [lines])))
  have accepted := orPathTrue model toOutput
    (andTrue model top (orPathTrue model path₁ leftGate) (orPathTrue model path₂ rightGate))
  have rejected := sound points lines pointCount lineCount noIncidences
  change wval C (indW n wires) C.output = false at rejected
  rw [accepted] at rejected
  contradiction

def CommonLineBound {N M : ℕ} (I : Fin N → Fin M → Prop) (k : ℕ) : Prop :=
  ∀ p q, p ≠ q → {l | I p l ∧ I q l}.ncard ≤ k

private theorem firstGrowth {n : ℕ} {C : Circuit} {a b : ℕ} (large : ℕ → Prop)
    (path : orp C n a b) (start : ¬ large a) (finish : large b) :
    ∃ u j, orp C n a u ∧ isOr C j ∧ u ∈ (gateAt C j).inputs ∧
      ¬ large u ∧ large (n + j) ∧ orp C n (n + j) b := by
  classical
  induction path with
  | refl => exact (start finish).elim
  | @tail c d path edge ih =>
    by_cases hc : large c
    · obtain ⟨u, j, hu, hor, read, hsmall, hbig, hv⟩ := ih hc
      exact ⟨u, j, hu, hor, read, hsmall, hbig, hv.tail edge⟩
    · obtain ⟨_, j, rfl, hor, read⟩ := edge
      exact ⟨c, j, path, hor, read, hc, finish, .refl⟩

private theorem inputShadowAtMostOne {n N : ℕ} {C : Circuit} {pw : Fin N → ℕ}
    (distinct : Function.Injective pw) (inputWire : ∀ p, pw p < n) (p : Fin N) :
    (sh C n pw (pw p)).ncard ≤ 1 := by
  have onlyPoint : ∀ q ∈ sh C n pw (pw p), q = p := by
    intro q hq
    change orp C n (pw q) (pw p) at hq
    rcases hq.cases_tail with eq | ⟨_, _, _, j, eq, _, _⟩
    · exact distinct eq.symm
    · have hp := inputWire p
      omega
  apply (Set.ncard_le_one (Set.toFinite _)).2
  intro a ha b hb
  exact (onlyPoint a ha).trans (onlyPoint b hb).symm

private theorem countShadowCharges {N M k : ℕ} {Slot : Type} [Fintype Slot]
    {I : Fin N → Fin M → Prop} {S : Set (Fin N × Fin M)}
    (common : CommonLineBound I k) (incoming target : Slot → Set (Fin N))
    (choices : ∀ e : S, ∃ c, e.val.1 ∈ incoming c ∧ (incoming c).ncard ≤ 1 ∧
      2 ≤ (target c).ncard ∧ ∀ q ∈ target c, I q e.val.2) :
    S.ncard ≤ k * Fintype.card Slot := by
  classical
  let _ : Fintype S := (Set.toFinite S).fintype
  choose code details using choices
  have fiberBound (c : Slot) :
      (Finset.univ.filter (fun e : S => code e = c)).card ≤ k := by
    let fiber : Finset S := Finset.univ.filter (fun e => code e = c)
    change fiber.card ≤ k
    by_cases nonempty : fiber.Nonempty
    · obtain ⟨e, he⟩ := nonempty
      have eCode := (Finset.mem_filter.mp he).2
      have data := details e
      rw [eCode] at data
      obtain ⟨_, smallCard, hbig, _⟩ := data
      change 1 < (target c).ncard at hbig
      obtain ⟨p, hp, q, hq, different⟩ := (Set.one_lt_ncard (Set.toFinite _)).mp hbig
      let lines : Set (Fin M) := {l | I p l ∧ I q l}
      have mapLine (f : S) (hf : f ∈ fiber) : f.val.2 ∈ (Set.toFinite lines).toFinset := by
        have fCode := (Finset.mem_filter.mp hf).2
        have data := details f
        rw [fCode] at data
        exact (Set.Finite.mem_toFinset _).2 ⟨data.2.2.2 p hp, data.2.2.2 q hq⟩
      have pointEq (f g : S) (hf : f ∈ fiber) (hg : g ∈ fiber) : f.val.1 = g.val.1 := by
        have fShadow := (details f).1
        have gShadow := (details g).1
        rw [(Finset.mem_filter.mp hf).2] at fShadow
        rw [(Finset.mem_filter.mp hg).2] at gShadow
        exact ((Set.ncard_le_one (Set.toFinite _)).mp smallCard) _ fShadow _ gShadow
      calc
        fiber.card ≤ (Set.toFinite lines).toFinset.card := by
          apply Finset.card_le_card_of_injOn (fun f : S => f.val.2) mapLine
          intro f hf g hg eq
          exact Subtype.ext (Prod.ext (pointEq f g hf hg) eq)
        _ = lines.ncard := (Set.ncard_eq_toFinset_card _ _).symm
        _ ≤ k := common p q different
    · simp [Finset.not_nonempty_iff_eq_empty.mp nonempty]
  have count := Finset.card_le_mul_card_image_of_maps_to
    (f := code) (s := Finset.univ) (t := Finset.univ) (fun _ _ => Finset.mem_univ _) k
    (fun c _ => fiberBound c)
  simpa only [Finset.card_univ, Set.fintypeCard_eq_ncard] using count

theorem countTightIncidences {n N M k : ℕ} {C : Circuit} {pw : Fin N → ℕ}
    {I : Fin N → Fin M → Prop} {S : Set (Fin N × Fin M)}
    (two : TopForm.IsAO2 n C) (distinct : Function.Injective pw)
    (inputWire : ∀ p, pw p < n) (common : CommonLineBound I k)
    (roots : ∀ e ∈ S, ∃ w, e.1 ∈ sh C n pw w ∧ 2 ≤ (sh C n pw w).ncard ∧
      ∀ q ∈ sh C n pw w, I q e.2) :
    S.ncard ≤ 2 * k * {j | isOr C j}.ncard := by
  classical
  let gates : Set ℕ := {j | isOr C j}
  have finiteGates : gates.Finite := (Set.finite_lt_nat C.gates.length).subset (fun _ h => h.1)
  let _ : Fintype gates := finiteGates.fintype
  let slotWire (c : gates × Fin 2) := (gateAt C c.1.val).inputs.getD c.2.val 0
  let gateWire (c : gates × Fin 2) := n + c.1.val
  let large (w : ℕ) := 2 ≤ (sh C n pw w).ncard
  have choices (e : S) : ∃ c : gates × Fin 2,
      e.val.1 ∈ sh C n pw (slotWire c) ∧ (sh C n pw (slotWire c)).ncard ≤ 1 ∧ large (gateWire c) ∧
        ∀ q ∈ sh C n pw (gateWire c), I q e.val.2 := by
    obtain ⟨w, reach, big, tight⟩ := roots e.val e.property
    have initial := inputShadowAtMostOne distinct inputWire (C := C) e.val.1
    have small : ¬ large (pw e.val.1) := by
      change ¬ 2 ≤ (sh C n pw (pw e.val.1)).ncard
      omega
    obtain ⟨u, j, hu, hor, read, hsmall, hbig, hv⟩ := firstGrowth large reach small big
    have real : gateAt C j ∈ C.gates := by
      rw [gateAt, List.getD_eq_getElem _ _ hor.1]
      exact List.getElem_mem hor.1
    have len := two.2.2 _ real
    obtain ⟨i, hi, reads⟩ := List.mem_iff_getElem.mp read
    let code : gates × Fin 2 := (⟨j, hor⟩, ⟨i, by omega⟩)
    have hwire : slotWire code = u := (List.getD_eq_getElem _ _ hi).trans reads
    refine ⟨code, ?_, ?_, hbig, ?_⟩
    · rwa [hwire]
    · rw [hwire]
      change ¬ 2 ≤ (sh C n pw u).ncard at hsmall
      omega
    · intro q hq
      exact tight q (Relation.ReflTransGen.trans hq hv)
  have count := countShadowCharges common (fun c => sh C n pw (slotWire c))
    (fun c => sh C n pw (gateWire c)) choices
  rw [Fintype.card_prod, Fintype.card_fin, Set.fintypeCard_eq_ncard] at count
  simpa only [gates, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using count

private theorem aPointsAlongOR {n N M u v : ℕ} {C : Circuit} {pw : Fin N → ℕ}
    {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} (path : orp C n u v) :
    aPoints C n pw lw I u ⊆ aPoints C n pw lw I v := by
  rintro p ⟨j, a, b, source, reach⟩
  exact ⟨j, a, b, source, reach.trans path⟩

def HasTightSource {n N M : ℕ} (C : Circuit) (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (p : Fin N) (l : Fin M) : Prop :=
  ∃ c, p ∈ aPoints C n pw lw I c ∧ 2 ≤ (aPoints C n pw lw I c).ncard ∧
    ∀ q ∈ aPoints C n pw lw I c, I q l

-- Count edges whose point is supplied by a source below a wire with a tight source set.
theorem countTightSourceIncidences {n N M k : ℕ} {C : Circuit} {pw : Fin N → ℕ}
    {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} {S : Set (Fin N × Fin M)}
    (two : TopForm.IsAO2 n C) (common : CommonLineBound I k)
    (roots : ∀ e ∈ S, HasTightSource (n := n) C pw lw I e.1 e.2) :
    S.ncard ≤ 2 * k * C.size := by
  classical
  let points := aPoints C n pw lw I
  let Slot := Fin C.gates.length × Fin 2
  let incoming (slot : Slot) :=
    if isOr C slot.1.val then points (TopForm.opnd C slot.1.val slot.2)
    else sh C n pw (TopForm.opnd C slot.1.val slot.2)
  let target (slot : Slot) := points (n + slot.1.val)
  let large (w : ℕ) := 2 ≤ (points w).ncard
  have choices (e : S) : ∃ slot, e.val.1 ∈ incoming slot ∧ (incoming slot).ncard ≤ 1 ∧
      2 ≤ (target slot).ncard ∧ ∀ q ∈ target slot, I q e.val.2 := by
    obtain ⟨c, ⟨h, a, v, start, path⟩, big, tight⟩ := roots e.val e.property
    have sourceMem : e.val.1 ∈ points (n + h) := ⟨h, a, v, start, .refl⟩
    by_cases bigStart : large (n + h)
    · have notOr : ¬ isOr C h := by
        simp [isOr, start.1.1.1.2]
      have pos : ∃ i : Fin 2, TopForm.opnd C h i = a := by
        rcases start.1.1.2 with forward | backward
        · exact ⟨0, forward.1⟩
        · exact ⟨1, backward.2⟩
      obtain ⟨i, hi⟩ := pos
      let slot : Slot := (⟨h, start.1.1.1.1⟩, i)
      have singleton : incoming slot = {e.val.1} := by
        simpa only [incoming, slot, notOr, ite_false, hi] using start.1.2
      exact ⟨slot, by rw [singleton]; exact Set.mem_singleton _, by simp [singleton], bigStart,
        fun q hq => tight q (aPointsAlongOR path hq)⟩
    · obtain ⟨u, j, hu, hor, read, small, largeTarget, reach⟩ := firstGrowth large path bigStart big
      have len : (gateAt C j).inputs.length = 2 := by rw [twoInputs two hor.1]; rfl
      obtain ⟨i, hi, eq⟩ := List.mem_iff_getElem.mp read
      let slot : Slot := (⟨j, hor.1⟩, ⟨i, by omega⟩)
      have same : incoming slot = points u := by
        have operand : TopForm.opnd C j slot.2 = u := (List.getD_eq_getElem _ _ hi).trans eq
        simpa only [incoming, slot, hor, ite_true] using congrArg points operand
      refine ⟨slot, ?_, ?_, largeTarget, fun q hq => tight q (aPointsAlongOR reach hq)⟩
      · rw [same]
        exact aPointsAlongOR hu sourceMem
      · rw [same]
        change ¬ 2 ≤ (points u).ncard at small
        omega
  have count := countShadowCharges common incoming target choices
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at count
  simpa only [Circuit.size, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using count

private theorem leafReaches {n w : ℕ} {C : Circuit} {s : Sk} (valid : ptv C n w s)
    {gv : ℕ × ℕ} (member : gv ∈ ptl C w s) : orp C n gv.2 gv.1 := by
  induction s generalizing w with
  | lf v =>
    obtain rfl := List.mem_singleton.mp member
    exact valid.2
  | nd j s t ihs iht =>
    exact (List.mem_append.mp member).elim (ihs valid.2.2.1) (iht valid.2.2.2)

theorem countOutsidePointExceptions {n N M k : ℕ} {C : Circuit}
    {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop}
    (two : TopForm.IsAO2 n C) (distinct : Function.Injective pw)
    (inputWire : ∀ p, pw p < n) (common : CommonLineBound I k) :
    (incid I \ Exs n C pw lw I).card ≤ 2 * k * {j | isOr C j}.ncard := by
  classical
  rw [← Set.ncard_coe_finset]
  apply countTightIncidences two distinct inputWire common
  intro e he
  have h := Finset.mem_sdiff.mp (Finset.mem_coe.mp he)
  have witness : ∃ s, tree2 n C pw lw e.1 e.2 s ∧
      ∃ gv ∈ ptl C C.output s, xBig C n pw I e.1 e.2 gv := by
    by_contra noWitness
    exact h.2 (Finset.mem_filter.mpr ⟨h.1, noWitness⟩)
  obtain ⟨s, tree, gv, member, ⟨label, contained⟩, big⟩ := witness
  have reaches := leafReaches tree.1 member
  rw [label] at reaches
  exact ⟨gv.1, reaches, big, contained⟩

theorem countIncidencesWithExceptions {n N M kp kl : ℕ} {C : Circuit}
    {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop}
    (two : TopForm.IsAO2 n C) (layout : Layout n pw lw)
    (pointCommon : CommonLineBound I kp) (lineCommon : CommonLineBound (fun l p => I p l) kl) :
    (incid I).card ≤ 2 * (kp + kl) * {j | isOr C j}.ncard + (Epp n C pw lw I).card := by
  classical
  let J : Fin M → Fin N → Prop := fun l p => I p l
  have swapIncidences : (incid J).image Prod.swap = incid I := by
    ext e
    simp only [Finset.mem_image, incid, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact hf
    · intro he
      exact ⟨e.swap, he, Prod.swap_swap e⟩
  have pointCount := countOutsidePointExceptions (lw := lw) two layout.1 layout.2.2.2.1 pointCommon
  have lineCount := countOutsidePointExceptions (lw := pw) two layout.2.1 layout.2.2.2.2 lineCommon
  have lineCount' : (incid I \ Eys n C pw lw I).card ≤ 2 * kl * {j | isOr C j}.ncard := by
    change (incid I \ (Exs n C lw pw J).image Prod.swap).card ≤ _
    rw [← swapIncidences, ← Finset.image_sdiff _ _ Prod.swap_injective,
      Finset.card_image_of_injective _ Prod.swap_injective]
    exact lineCount
  let X := incid I \ Exs n C pw lw I
  let Y := incid I \ Eys n C pw lw I
  let E := Epp n C pw lw I
  have covers : incid I ⊆ X ∪ Y ∪ E := by
    intro e he
    by_cases hx : e ∈ Exs n C pw lw I
    · by_cases hy : e ∈ Eys n C pw lw I
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hx, hy⟩)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨he, hy⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨he, hx⟩))
  calc
    (incid I).card ≤ (X ∪ Y ∪ E).card := Finset.card_le_card covers
    _ ≤ (X ∪ Y).card + E.card := Finset.card_union_le _ _
    _ ≤ X.card + Y.card + E.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ 2 * kp * {j | isOr C j}.ncard + 2 * kl * {j | isOr C j}.ncard + E.card :=
      Nat.add_le_add_right (Nat.add_le_add pointCount lineCount') _
    _ = _ := by rw [Nat.mul_add, Nat.add_mul]

theorem smallSideOfRectangle {N M k : ℕ} {I : Fin N → Fin M → Prop}
    {points : Set (Fin N)} {lines : Set (Fin M)} (common : CommonLineBound I k)
    (rectangle : ∀ p ∈ points, ∀ l ∈ lines, I p l) : points.ncard ≤ 1 ∨ lines.ncard ≤ k := by
  by_cases small : points.ncard ≤ 1
  · exact Or.inl small
  · have big : 1 < points.ncard := Nat.lt_of_not_ge small
    obtain ⟨p, hp, q, hq, distinct⟩ := (Set.one_lt_ncard (Set.toFinite _)).mp big
    have subset : lines ⊆ {l | I p l ∧ I q l} := fun l hl => ⟨rectangle p hp l hl, rectangle q hq l hl⟩
    exact Or.inr ((Set.ncard_le_ncard subset).trans (common p q distinct))

def sourceJunkLines {n N M : ℕ} (C : Circuit) (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (p : Fin N) (c : ℕ) : Set (Fin M) :=
  {m | ∃ j a v, source C n pw lw I p j a v ∧ orp C n (n + j) c ∧ m ∈ jl C n lw I p v}

def oppositeJunkPoints {n N M : ℕ} (C : Circuit) (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (p : Fin N) (cb : ℕ) : Set (Fin N) :=
  {z | ∃ l j u b, ¬ I p l ∧ bottom C n pw lw I l j u b ∧
    orp C n (n + j) cb ∧ z ∈ jp C n pw I l u}

theorem boundedJunkRectangle {n N M kp kl g c cb : ℕ} {C : Circuit}
    {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} (p : Fin N)
    (model : TopForm.IsAO2 n C) (layout : Layout n pw lw) (sound : Snd22 n C pw lw I)
    (pointCommon : CommonLineBound I kp) (lineCommon : CommonLineBound (fun l p => I p l) kl)
    (top : andOn C g c cb) (toOutput : orp C n (n + g) C.output) :
    let P := oppositeJunkPoints (n := n) C pw lw I p cb
    let L := sourceJunkLines (n := n) C pw lw I p c
    (P.ncard ≤ 1 ∨ L.ncard ≤ kp) ∧ (L.ncard ≤ 1 ∨ P.ncard ≤ kl) := by
  intro P L
  have rectangle (z : Fin N) (hz : z ∈ P) (m : Fin M) (hm : m ∈ L) : I z m := by
    obtain ⟨l, j₂, u, b, noPL, bottom₂, path₂, hz⟩ := hz
    obtain ⟨j₁, a, v, source₁, path₁, hm⟩ := hm
    exact (junkStarOfSoundness model layout sound top toOutput).2.2
      p l j₁ a v j₂ u b source₁ path₁ bottom₂ path₂ noPL m hm z hz
  exact ⟨smallSideOfRectangle pointCommon rectangle,
    smallSideOfRectangle lineCommon (fun m hm z hz => rectangle z hz m hm)⟩

private theorem directSlots {n N M : ℕ} {C : Circuit} {pw : Fin N → ℕ} {lw : Fin M → ℕ}
    {I : Fin N → Fin M → Prop} {p : Fin N} {l : Fin M} {s : Sk}
    (valid : ptv C n C.output s) (shape : hasDirect C n pw lw I p l s) :
    ∃ j, isAnd C j ∧
      ((sh C n pw (in0 C j) = {p} ∧ sh C n lw (in1 C j) = {l}) ∨
       (sh C n pw (in1 C j) = {p} ∧ sh C n lw (in0 C j) = {l})) := by
  cases s with
  | lf v => exact False.elim shape
  | nd j a b =>
    refine ⟨j, valid.1, ?_⟩
    cases a <;> cases b <;> simp [hasDirect, tDIRECT, fitsShape, hasTy] at shape
    exact shape.elim (fun h => Or.inl ⟨h.1.2, h.2.2⟩) (fun h => Or.inr ⟨h.2.2, h.1.2⟩)

private theorem countPairedSingletons {N M : ℕ} {C : Circuit} {S : Set (Fin N × Fin M)}
    (points : ℕ → Set (Fin N)) (lines : ℕ → Set (Fin M))
    (witness : ∀ e ∈ S, ∃ j c cb, andOn C j c cb ∧ points c = {e.1} ∧ lines cb = {e.2}) :
    S.ncard ≤ 2 * {j | isAnd C j}.ncard := by
  classical
  let gates : Set ℕ := {j | isAnd C j}
  have finiteGates : gates.Finite := (Set.finite_lt_nat C.gates.length).subset (fun _ h => h.1)
  let _ : Finite gates := finiteGates.to_subtype
  let pointWire (c : gates × Fin 2) := if c.2 = 0 then in0 C c.1.val else in1 C c.1.val
  let lineWire (c : gates × Fin 2) := if c.2 = 0 then in1 C c.1.val else in0 C c.1.val
  have choices (e : S) : ∃ c : gates × Fin 2,
      points (pointWire c) = {e.val.1} ∧ lines (lineWire c) = {e.val.2} := by
    obtain ⟨j, c, cb, ⟨hj, forward | backward⟩, hp, hl⟩ := witness e.val e.property
    · refine ⟨(⟨j, hj⟩, 0), ?_, ?_⟩
      · change points (in0 C j) = _
        rwa [forward.1]
      · change lines (in1 C j) = _
        rwa [forward.2]
    · refine ⟨(⟨j, hj⟩, 1), ?_, ?_⟩
      · change points (in1 C j) = _
        rwa [backward.2]
      · change lines (in0 C j) = _
        rwa [backward.1]
  choose code details using choices
  have injective : Function.Injective code := by
    intro e f eq
    have fData := details f
    rw [← eq] at fData
    exact Subtype.ext (Prod.ext
      (Set.singleton_injective ((details e).1.symm.trans fData.1))
      (Set.singleton_injective ((details e).2.symm.trans fData.2)))
  have count := Nat.card_le_card_of_injective code injective
  rw [Nat.card_prod, Nat.card_coe_set_eq, Nat.card_fin, Nat.mul_comm] at count
  exact count

theorem countDirectIncidences {n N M : ℕ} {C : Circuit} {pw : Fin N → ℕ} {lw : Fin M → ℕ}
    {I : Fin N → Fin M → Prop} {S : Set (Fin N × Fin M)}
    (direct : ∀ e ∈ S, ∃ s, ptv C n C.output s ∧ hasDirect C n pw lw I e.1 e.2 s) :
    S.ncard ≤ 2 * {j | isAnd C j}.ncard := by
  apply countPairedSingletons (sh C n pw) (sh C n lw)
  intro e he
  obtain ⟨s, valid, shape⟩ := direct e he
  obtain ⟨j, hj, forward | backward⟩ := directSlots valid shape
  · exact ⟨j, in0 C j, in1 C j, ⟨hj, Or.inl ⟨rfl, rfl⟩⟩, forward⟩
  · exact ⟨j, in1 C j, in0 C j, ⟨hj, Or.inr ⟨rfl, rfl⟩⟩, backward⟩

theorem countIncidencesWithDirectExceptions {n N M kp kl : ℕ} {C : Circuit}
    {pw : Fin N → ℕ} {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop}
    (two : TopForm.IsAO2 n C) (layout : Layout n pw lw)
    (pointCommon : CommonLineBound I kp) (lineCommon : CommonLineBound (fun l p => I p l) kl)
    (direct : ∀ e ∈ Epp n C pw lw I, ∃ s, ptv C n C.output s ∧ hasDirect C n pw lw I e.1 e.2 s) :
    (incid I).card ≤ 2 * (kp + kl) * {j | isOr C j}.ncard + 2 * {j | isAnd C j}.ncard := by
  have exceptions := countDirectIncidences (n := n) (C := C) (pw := pw) (lw := lw) (I := I)
    (S := (Epp n C pw lw I : Set (Fin N × Fin M))) direct
  rw [Set.ncard_coe_finset] at exceptions
  exact (countIncidencesWithExceptions two layout pointCommon lineCommon).trans
    (Nat.add_le_add_left exceptions _)

private theorem andOnSwap {C : Circuit} {j a b : ℕ} (gate : andOn C j a b) : andOn C j b a :=
  ⟨gate.1, gate.2.symm⟩

private theorem bLinesTranspose {n N M w : ℕ} {C : Circuit} {pw : Fin N → ℕ}
    {lw : Fin M → ℕ} {I : Fin N → Fin M → Prop} :
    bLines C n pw lw I w = aPoints C n lw pw (fun l p => I p l) w := by
  ext l
  constructor
  · rintro ⟨j, u, b, ⟨gate, fixed, nonempty⟩, path⟩
    exact ⟨j, b, u, ⟨⟨andOnSwap gate, fixed⟩, nonempty⟩, path⟩
  · rintro ⟨j, b, u, ⟨⟨gate, fixed⟩, nonempty⟩, path⟩
    exact ⟨j, u, b, ⟨andOnSwap gate, fixed, nonempty⟩, path⟩

private theorem singletonOfSmall {A : Type} {s : Set A} (finite : s.Finite) {a : A}
    (member : a ∈ s) (small : s.ncard ≤ 1) : s = {a} :=
  Set.Subset.antisymm (fun b hb => Set.mem_singleton_iff.mpr ((Set.ncard_le_one finite).mp small b hb a member))
    (Set.singleton_subset_iff.mpr member)

-- This witnesses the B2 part with a tight source set and a tight bottom set, namely classes L, P and O.
def CompatibleB2 {n N M : ℕ} (C : Circuit) (pw : Fin N → ℕ) (lw : Fin M → ℕ)
    (I : Fin N → Fin M → Prop) (p : Fin N) (l : Fin M) : Prop :=
  ∃ j c cb, andOn C j c cb ∧ p ∈ aPoints C n pw lw I c ∧ l ∈ bLines C n pw lw I cb ∧
    (∀ q ∈ aPoints C n pw lw I c, I q l) ∧ ∀ m ∈ bLines C n pw lw I cb, I p m

theorem countCompatibleB2 {n N M kp kl : ℕ} {C : Circuit} {pw : Fin N → ℕ} {lw : Fin M → ℕ}
    {I : Fin N → Fin M → Prop} {S : Set (Fin N × Fin M)}
    (model : TopForm.IsAO2 n C) (pointCommon : CommonLineBound I kp)
    (lineCommon : CommonLineBound (fun l p => I p l) kl)
    (witness : ∀ e ∈ S, CompatibleB2 (n := n) C pw lw I e.1 e.2) :
    S.ncard ≤ 2 * (kp + kl) * C.size + 2 * {j | isAnd C j}.ncard := by
  classical
  let J : Fin M → Fin N → Prop := fun l p => I p l
  let points := aPoints C n pw lw I
  let lines := bLines C n pw lw I
  let X : Set (Fin N × Fin M) := {e | HasTightSource (n := n) C pw lw I e.1 e.2}
  let Y : Set (Fin M × Fin N) := {e | HasTightSource (n := n) C lw pw J e.1 e.2}
  let D : Set (Fin N × Fin M) :=
    {e | ∃ j c cb, andOn C j c cb ∧ points c = {e.1} ∧ lines cb = {e.2}}
  have xBound := countTightSourceIncidences (S := X) model pointCommon (fun _ h => h)
  have yBound := countTightSourceIncidences (S := Y) model lineCommon (fun _ h => h)
  have ySwap : (Prod.swap '' Y).ncard ≤ 2 * kl * C.size := by
    rw [Set.ncard_image_of_injective _ Prod.swap_injective]
    exact yBound
  have dBound := countPairedSingletons (S := D) points lines (fun _ h => h)
  have covers : S ⊆ X ∪ (Prod.swap '' Y ∪ D) := by
    intro e he
    obtain ⟨j, c, cb, gate, hp, hl, tightP, tightL⟩ := witness e he
    by_cases bigP : 2 ≤ (points c).ncard
    · exact Or.inl ⟨c, hp, bigP, tightP⟩
    by_cases bigL : 2 ≤ (lines cb).ncard
    · have transpose : lines cb = aPoints C n lw pw J cb := bLinesTranspose
      have flipped : e.swap ∈ Y := by
        refine ⟨cb, ?_⟩
        rw [← transpose]
        exact ⟨hl, bigL, tightL⟩
      exact Or.inr (Or.inl ⟨e.swap, flipped, Prod.swap_swap e⟩)
    · have oneP : (points c).ncard ≤ 1 := by omega
      have oneL : (lines cb).ncard ≤ 1 := by omega
      exact Or.inr (Or.inr ⟨j, c, cb, gate, singletonOfSmall (Set.toFinite _) hp oneP,
        singletonOfSmall (Set.toFinite _) hl oneL⟩)
  calc
    S.ncard ≤ (X ∪ (Prod.swap '' Y ∪ D)).ncard := Set.ncard_le_ncard covers
    _ ≤ X.ncard + (Prod.swap '' Y ∪ D).ncard := Set.ncard_union_le _ _
    _ ≤ X.ncard + ((Prod.swap '' Y).ncard + D.ncard) := Nat.add_le_add_left (Set.ncard_union_le _ _) _
    _ ≤ 2 * kp * C.size + (2 * kl * C.size + 2 * {j | isAnd C j}.ncard) :=
      Nat.add_le_add xBound (Nat.add_le_add ySwap dBound)
    _ = _ := by rw [Nat.mul_add, Nat.add_mul, Nat.add_assoc]

end PEqualNP.ReadTwo.Research
