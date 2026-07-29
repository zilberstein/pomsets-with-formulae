import Pom.Lpo.Operations.Seq.PathCond

namespace Lpofin

variable {act test : Type}

def ReachableWith (α : Lpofin (Label act test)) (φ : PathCond α) (x : Node) : Prop :=
  ∃ ψ : PathCond α, φ ≤ ψ ∧
    --(∀ z ∈ ψ.tests, α.rel z x) ∧
    ψ.toForm ≤ α.form x

def Reachable (α : Lpofin (Label act test)) : Node → Prop :=
  α.ReachableWith PathCond.empty

lemma reachable_isotone [Preorder act] [Preorder test] {α β : Lpofin (Label act test)} (hle : α ≤ β)
    {x : Node} (hx : x ∈ α.nodes) : α.Reachable x ↔ β.Reachable x := by
  constructor
  · rintro ⟨ψ, _, hform⟩
    refine ⟨ψ.up_cast hle, bot_le, ?_⟩; exact hform.trans (le_form hle)
  · rintro ⟨ψ, _, hform⟩
    let ψ' : PathCond α := {
      tests := ψ.tests ∩ α.tests
      truth := fun ⟨z, hz⟩ ↦ ψ.truth ⟨z, Set.inter_subset_left hz⟩
      tests_valid := Set.inter_subset_right
    }
    refine ⟨ψ', bot_le, ?_⟩
    rw [← PathCond.cast_toForm (hle := hle)]; conv => rhs; exact hle.form x hx
    refine PathCond.implies_weaken ?_ hform ?_
    · refine ⟨Set.inter_subset_left, fun _ ↦ rfl⟩
    · conv => arg 1; exact (hle.form x hx).symm
      refine (α.val.property.form _ hx).1.monotone _ ?_
      intro y hyx ⟨hyt, h⟩; refine h ⟨hyt, ?_⟩
      obtain ⟨b, hb⟩ := (Label.isTest_iff _).mp (ψ.tests_valid hyt)
      have hlab := le_of_le_of_eq (hle.lab y) hb
      cases hy : α.lab y with
      | bot => exfalso; exact α.val.property.bot y hy x hyx
      | fork => have := le_of_eq_of_le hy.symm hlab; contradiction
      | act a => have := le_of_eq_of_le hy.symm hlab; contradiction
      | test t => exact (Label.isTest_iff _).mpr ⟨t, hy⟩

def reachable_pred {α : Lpofin (Label act test)} {x z : Node}
    (hr : α.Reachable x) (hz : α.rel z x) : α.Reachable z := by
  rcases hr with ⟨ψ, _, hform⟩
  refine ⟨ψ, bot_le, ?_⟩
  exact hform.trans ((α.val.property.form z (α.val.property.rel_dom hz).1).2 x hz)

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
  sorry

lemma le_branches [PartialOrder act] [PartialOrder test] {α β : Lpofin (Label act test)}
    (hle : α ≤ β) : α.branches = { φ | ∃ φ' ∈ β.branches, φ' = φ.up_cast hle ∧  φ.toForm ≤ α.stuck.not } := by
  sorry

lemma branches_not_mutually_sat {α : Lpofin (Label act test)} {φ ψ : PathCond α}
    (hφ : φ ∈ α.branches) (hψ : ψ ∈ α.branches) (hneq : φ ≠ ψ) :
    ∀ v, ¬ (φ.toForm v ∧ ψ.toForm v) := by
  intro v ⟨h₁, h₂⟩
  obtain ⟨himp, hstuck, hmax⟩ := hφ
  obtain ⟨himp', hstuck', hmax'⟩ := hψ
  sorry

end Lpofin
