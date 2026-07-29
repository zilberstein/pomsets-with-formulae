import Pom.Lpo.Operations.Seq.PathCond

namespace Lpofin

variable {act test : Type}

def ReachableWith (α : Lpofin (Label act test)) (φ : PathCond α) (x : Node) : Prop :=
  ∃ ψ : PathCond α, φ ≤ ψ ∧
    --(∀ z ∈ ψ.tests, α.rel z x) ∧
    ψ.toForm ≤ α.form x

def Reachable (α : Lpofin (Label act test)) : Node → Prop :=
  α.ReachableWith PathCond.empty

lemma reachable_isotone [LE act] [LE test] {α β : Lpofin (Label act test)} (hle : α ≤ β)
    {x : Node} (hx : x ∈ α.nodes) : α.Reachable x ↔ β.Reachable x := by
  sorry

def reachable_pred {α : Lpofin (Label act test)} {x z : Node}
    (hr : α.Reachable x) (hz : α.rel z x) : α.Reachable z := by sorry

-- stuck is a path condition formula indicating that the execution will definitely
-- encounter a ⊥ node
def stuck (α : Lpofin (Label act test)) : Form Node :=
  Form.sOr fun x : ↑{ x ∈ α.nodes | α.lab x = ⊥ ∧ α.Reachable x } ↦ α.form x.val

lemma stuck_antitone [PartialOrder act] [PartialOrder test] :
    @Antitone (Lpofin (Label act test)) _ _ _ stuck := by
  intro α β hle v ⟨⟨x, hx, hlab, hr⟩, hform⟩
  rcases hle.succ _ hx with hx' | ⟨y, ⟨hy, hlab'⟩, hyx⟩
  · refine ⟨⟨x, hx', ?_, ?_⟩, ?_⟩
    · refine le_antisymm ?_ bot_le
      rw [← hlab]; exact hle.lab x
    · exact (reachable_isotone hle hx').mpr hr
    · refine (congrFun (hle.form x hx') v).mpr ?_
      exact hform
  · refine ⟨⟨y, hy, hlab', ?_⟩, ?_⟩
    · have hry := reachable_pred hr hyx
      exact (reachable_isotone hle hy).mpr hry
    · refine (congrFun (hle.form _ hy) _).mpr ?_
      refine (β.val.property.form _ (hle.nodes hy)).2 _ hyx _ ?_
      exact hform

def conj (α : Lpofin (Label act test)) (S : Set Node) : Form Node :=
  Form.sAnd fun x : ↑S ↦ α.form x.val

def branches (α : Lpofin (Label act test)) : Set (PathCond α) :=
  { φ : PathCond α
  | (∀ x ∈ φ.tests, φ.toForm ≤ α.form x) ∧
    φ.toForm ≤ α.stuck.not ∧
    ∀ {x}, x ∉ φ.tests → α.isTest x →
      ¬ (α.form x ≤ α.stuck) → ¬ α.ReachableWith φ x
  }

lemma branches_finite (α : Lpofin (Label act test)) : α.branches.Finite := Set.toFinite _

lemma isTest_of_le_or_bot [PartialOrder act] [PartialOrder test]
    {α β : Lpofin (Label act test)} (hle : α ≤ β) {x : Node}
    (ht : β.isTest x) : α.isTest x ∨ α.lab x = ⊥ := by
  have hlab := hle.lab x
  obtain ⟨b, hb⟩ := (Label.isTest_iff _).mp ht
  change α.lab x ≤ β.lab x at hlab
  rw [hb] at hlab
  cases ha : α.lab x with
  | bot => exact Or.inr rfl
  | fork => rw [ha] at hlab; contradiction
  | act a => rw [ha] at hlab; contradiction
  | test c => exact Or.inl ((Label.isTest_iff _).mpr ⟨c, ha⟩)

lemma branches_monotone [PartialOrder act] [PartialOrder test]
    {α β : Lpofin (Label act test)} (hle : α ≤ β)
    {φ : PathCond α} (hφ : φ ∈ α.branches) : φ.up_cast hle ∈ β.branches := by
  have ⟨himp, hstk, hmax⟩ := hφ
  have ⟨v, hform⟩ := φ.sat
  refine ⟨?_, ?_, ?_⟩
  · intro x hx; rw [PathCond.cast_toForm]
    exact (himp _ hx).trans <| le_form hle
  · rw [PathCond.cast_toForm]; refine hstk.trans ?_
    intro v h h'; apply h; exact stuck_antitone hle _ h'
  · intro x hx htest hstk' ⟨ψ, hext, hreach⟩
    have htest' : α.isTest x := by
      rcases hle.succ x (tests_sub_nodes htest) with hxα | ⟨z, hz, hrel⟩
      · cases hl : α.val.lab x <;>
          have hlab := le_of_eq_of_le hl.symm (hle.lab x) <;> try simp at hlab
        · exfalso; have ⟨v, hv⟩ := φ.sat
          refine hstk _ hv ⟨⟨x, hxα, hl, ?_⟩, ?_⟩
          · sorry
          · conv => exact congrFun (hle.form _ hxα) _
            sorry
        · simp only [LE.le] at hlab; have ⟨b, h⟩ := (Label.isTest_iff _).mp htest
          have := h.symm.trans hlab; contradiction
        · simp only [LE.le] at hlab; have ⟨b, h⟩ := (Label.isTest_iff _).mp htest
          conv at hlab => arg 2; exact h
          exfalso; exact hlab
        · exact (Label.isTest_iff _).mpr ⟨_, hl⟩
      · sorry
    refine hmax hx ?_ ?_ ⟨⟨ψ.tests, ψ.truth, ?_⟩, hext, ?_⟩
    · sorry
    · sorry
    · sorry
    · conv => rhs; exact hle.form _ (tests_sub_nodes htest')
      exact hreach

lemma le_branches [PartialOrder act] [PartialOrder test] {α β : Lpofin (Label act test)}
    (hle : α ≤ β) : α.branches = { φ | ∃ φ' ∈ β.branches, φ' = φ.up_cast hle ∧  φ.toForm ≤ α.stuck.not } := by
  ext φ; constructor
  · intro h; refine ⟨φ.up_cast hle, ?_, rfl, ?_⟩
    · exact branches_monotone hle h
    · obtain ⟨_, hstuck, _⟩ := h; exact hstuck
  · rintro ⟨_, ⟨himp, _, hmax⟩, rfl, hstuck⟩
    have ⟨v, hsat⟩ := φ.sat; sorry
    -- have hsub : t ⊆ α.nodes := by
    --   intro x hxt
    --   have hx := tests_sub_nodes <| ht hxt
    --   rcases hle.succ _ hx with hxα | ⟨y, hbot, hyx⟩
    --   · exact hxα
    --   · exfalso; refine forall_not_of_not_exists (hstuck v hsat) ⟨y, hbot⟩ ?_
    --     refine (congrFun (hle.form y hbot.1) _).mpr ?_
    --     refine (β.val.property.form y (hle.nodes hbot.1)).2 _ hyx v ?_
    --     exact himp _ hsat ⟨_, hxt⟩
    -- refine ⟨t, ?_, f, rfl, ⟨?_, hstuck⟩, ?_⟩
    -- · intro x hx; rcases isTest_of_le_or_bot hle (ht hx) with htest | hbot
    --   · exact htest
    --   · exfalso
    --     exact (hstuck v hsat) ⟨⟨x, hsub hx, hbot⟩,
    --       (congrFun (hle.form x (hsub hx)) v).mpr (himp _ hsat ⟨x, hx⟩)⟩
    -- · intro v hform x
    --   exact (congrFun (hle.form x (hsub x.property)) _).mpr (himp _ hform x)
    -- · intro x b hx htst hreach
    --   apply hmax hx
    --   · have ⟨c, hc⟩ := (Label.isTest_iff _).mp htst
    --     apply (Label.isTest_iff _).mpr
    --     obtain ⟨d, hd, _⟩ := lab_is_test_le (le_of_eq_of_le hc.symm (hle.lab x))
    --     exact ⟨d, hd⟩
    --   · obtain ⟨hwconj, hwstk⟩ := hreach
    --     refine ⟨?_, ?_⟩
    --     · intro v hform z
    --       exact le_form hle _ (hwconj _ hform z)
    --     · intro u hu hs
    --       exact hwstk u hu (stuck_antitone hle u hs)

lemma branches_not_mutually_sat {α : Lpofin (Label act test)} {φ ψ : PathCond α}
    (hφ : φ ∈ α.branches) (hψ : ψ ∈ α.branches) (hneq : φ ≠ ψ) :
    ∀ v, ¬ (φ.toForm v ∧ ψ.toForm v) := by
  intro v ⟨h₁, h₂⟩
  obtain ⟨himp, hstuck, hmax⟩ := hφ
  obtain ⟨himp', hstuck', hmax'⟩ := hψ
  sorry

end Lpofin
