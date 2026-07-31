import Pom.Lpo.Operations.Seq.PathCond

namespace Lpofin

variable {act test : Type}

def ReachableWith (α : Lpofin (Label act test)) (φ : PathCond α) (x : Node) : Prop :=
  ∃ ψ : PathCond α, φ ≤ ψ ∧
    ψ.toForm ≤ α.form x

namespace ReachableWith

lemma minimal {α : Lpofin (Label act test)} {φ : PathCond α}
    {x : Node} (hx : x ∈ α.nodes) (hr : α.ReachableWith φ x) :
    ∃ ψ, φ ≤ ψ ∧ ψ.toForm ≤ α.form x ∧
      ∀ z ∈ ψ.tests, z ∈ φ.tests ∨ α.rel z x := by
  have ⟨ψ, hext, himp⟩ := hr
  -- Construct `ψ'` to be a minimal reachability witness
  use ψ.restrict (φ.tests ∪ { y | α.rel y x})
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro y; refine hext.2 y
    · intro y hy; exact ⟨hext.1 hy, Or.inl hy⟩
  · refine PathCond.implies_weaken (ψ.restrict_le _) himp ?_
    refine (α.val.property.form _ hx).1.monotone _ ?_
    intro y hrel ⟨hy, hy'⟩; refine hy' ⟨hy, Or.inr hrel⟩
  · intro z ⟨_, hz⟩; exact hz

end ReachableWith

lemma reachable_isotone [Preorder act] [Preorder test] {α β : Lpofin (Label act test)}
    {φ : PathCond α} (hle : α ≤ β)
    {x : Node} (hx : x ∈ α.nodes) :
    α.ReachableWith φ x ↔ β.ReachableWith (φ.up_cast hle) x := by
  constructor
  · rintro ⟨ψ, hext, hform⟩
    refine ⟨ψ.up_cast hle, hext, ?_⟩; exact hform.trans (le_form hle)
  · rintro ⟨ψ, hext, hform⟩
    let ψ' : PathCond α := {
      tests := ψ.tests ∩ α.tests
      truth := fun ⟨z, hz⟩ ↦ ψ.truth ⟨z, Set.inter_subset_left hz⟩
      tests_valid := Set.inter_subset_right
    }
    refine ⟨ψ', ⟨?_, ?_⟩, ?_⟩
    · exact Set.subset_inter hext.1 φ.tests_valid
    · intro x; exact hext.2 x
    · rw [← PathCond.cast_toForm (hle := hle)]; conv => rhs; exact hle.form x hx
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

def reachable_pred {α : Lpofin (Label act test)} {x z : Node} {φ : PathCond α}
    (hr : α.ReachableWith φ x) (hz : α.rel z x) : α.ReachableWith φ z := by
  rcases hr with ⟨ψ, hext, hform⟩
  refine ⟨ψ, hext, ?_⟩
  exact hform.trans ((α.val.property.form z (α.val.property.rel_dom hz).1).2 x hz)

-- stuck is a path condition formula indicating that the execution will definitely
-- encounter a ⊥ node
def stuck (α : Lpofin (Label act test)) (φ : PathCond α) : Form Node :=
  Form.sOr fun x : ↑{ x ∈ α.nodes | α.lab x = ⊥ ∧ α.ReachableWith φ x } ↦ α.form x.val

lemma stuck_antitone [PartialOrder act] [PartialOrder test] {α β : Lpofin (Label act test)}
    {φ : PathCond α} (hle : α ≤ β) : β.stuck (φ.up_cast hle) ≤ α.stuck φ := by
  intro v ⟨⟨x, hx, hlab, hr⟩, hform⟩
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
    φ.toForm ≤ (α.stuck φ).not ∧
    ∀ {x}, x ∉ φ.tests → α.isTest x →
      ¬ (α.form x ≤ α.stuck φ) → ¬ α.ReachableWith φ x
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

lemma reachableWith_isotone [Preorder act] [Preorder test]
    {α β : Lpofin (Label act test)} (hle : α ≤ β)
    {φ : PathCond α} {x : Node} (hx : x ∈ α.nodes) :
    α.ReachableWith φ x ↔ β.ReachableWith (φ.up_cast hle) x := by
  constructor
  · rintro ⟨ψ, hext, hform⟩
    refine ⟨ψ.up_cast hle, hext, ?_⟩
    rw [PathCond.cast_toForm]
    exact hform.trans (le_form hle)
  · rintro ⟨ψ, hext, hform⟩
    let ψ' : PathCond α := {
      tests := ψ.tests ∩ α.tests
      truth := fun ⟨z, hz⟩ ↦ ψ.truth ⟨z, hz.1⟩
      tests_valid := Set.inter_subset_right
    }
    have hext' : φ ≤ ψ' := by
      rcases hext with ⟨hsub, htruth⟩
      refine ⟨fun z hz ↦ ⟨hsub hz, φ.tests_valid hz⟩, ?_⟩
      intro z; exact htruth z
    refine ⟨ψ', hext', ?_⟩
    rw [← PathCond.cast_toForm (hle := hle)]
    conv => rhs; exact hle.form x hx
    refine PathCond.implies_weaken ?_ hform ?_
    · refine ⟨Set.inter_subset_left, fun _ ↦ rfl⟩
    · conv => arg 1; exact (hle.form x hx).symm
      refine (α.val.property.form _ hx).1.monotone _ ?_
      intro y hyx ⟨hyt, h⟩
      refine h ⟨hyt, ?_⟩
      obtain ⟨b, hb⟩ := (Label.isTest_iff _).mp (ψ.tests_valid hyt)
      have hlab := le_of_le_of_eq (hle.lab y) hb
      cases hy : α.lab y with
      | bot => exfalso; exact α.val.property.bot y hy x hyx
      | fork => have := le_of_eq_of_le hy.symm hlab; contradiction
      | act a => have := le_of_eq_of_le hy.symm hlab; contradiction
      | test t => exact (Label.isTest_iff _).mpr ⟨t, hy⟩

lemma not_reachableWith_of_form_le_stuck
    {α : Lpofin (Label act test)} {φ : PathCond α} {x : Node}
    (havoid : φ.toForm ≤ (α.stuck φ).not) (hform : α.form x ≤ α.stuck φ) :
    ¬ α.ReachableWith φ x := by
  rintro ⟨η, hext, hη⟩
  rcases η.sat with ⟨v, hv⟩
  have hφv := PathCond.toForm_antitone hext v hv
  exact (havoid v hφv) (hform v (hη v hv))

lemma branches_monotone [PartialOrder act] [PartialOrder test]
    {α β : Lpofin (Label act test)} (hle : α ≤ β)
    {φ : PathCond α} (hφ : φ ∈ α.branches) : φ.up_cast hle ∈ β.branches := by
  rcases hφ with ⟨htests, hstuck, hmax⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [PathCond.cast_toForm]
    exact (htests x hx).trans (le_form hle)
  · intro v hφ hβstuck
    apply hstuck v hφ
    exact stuck_antitone hle v hβstuck
  · intro x hx htest hnot hreach
    have hxβ : x ∈ β.nodes := tests_sub_nodes htest
    rcases isTest_of_le_or_bot hle htest with htestα | hbot
    · have hxα : x ∈ α.nodes := tests_sub_nodes htestα
      have hreachα := (reachableWith_isotone hle hxα).mpr hreach
      by_cases hαstuck : α.form x ≤ α.stuck φ
      · exact not_reachableWith_of_form_le_stuck hstuck hαstuck hreachα
      · exact hmax hx htestα hαstuck hreachα
    · rcases hle.succ x hxβ with hxα | ⟨y, ⟨hyα, hybot⟩, hyx⟩
      · have hreachα := (reachableWith_isotone hle hxα).mpr hreach
        apply not_reachableWith_of_form_le_stuck hstuck _ hreachα
        intro v hxform
        exact ⟨⟨x, hxα, hbot, hreachα⟩, hxform⟩
      · have hreachyβ : β.ReachableWith (φ.up_cast hle) y :=
          reachable_pred hreach hyx
        have hreachy : α.ReachableWith φ y :=
          (reachableWith_isotone hle hyα).mpr hreachyβ
        apply not_reachableWith_of_form_le_stuck hstuck _ hreachy
        intro v hyform
        refine ⟨⟨y, hyα, hybot, hreachy⟩, hyform⟩

lemma le_branches [PartialOrder act] [PartialOrder test] {α β : Lpofin (Label act test)}
    (hle : α ≤ β) :
    α.branches =
    { φ | φ.up_cast hle ∈ β.branches ∧ φ.toForm ≤ (α.stuck φ).not } := by
  ext φ
  constructor
  · intro hφ
    exact ⟨branches_monotone hle hφ, hφ.2.1⟩
  · rintro ⟨hφ', hstuck⟩
    refine ⟨?_, hstuck, ?_⟩
    · intro x hx
      rw [← PathCond.cast_toForm (hle := hle)]
      have himp := hφ'.1 x hx
      conv at himp => rhs; exact (hle.form x (tests_sub_nodes (φ.tests_valid hx))).symm
      exact himp
    · intro x hx htest hnot hreach
      have hxnode : x ∈ α.nodes := tests_sub_nodes htest
      apply hφ'.2.2 hx
      · obtain ⟨b, hb⟩ := (Label.isTest_iff _).mp htest
        obtain ⟨c, hc, _⟩ := lab_is_test_le (le_of_eq_of_le hb.symm (hle.lab x))
        exact (Label.isTest_iff _).mpr ⟨c, hc⟩
      · intro hβ
        apply hnot
        intro v hα
        apply stuck_antitone hle v
        exact hβ v ((congrFun (hle.form x hxnode) v).mp hα)
      · exact (reachableWith_isotone hle hxnode).mp hreach

lemma pathCond_eq_of_tests_eq_of_common_sat {α : Lpofin (Label act test)}
    {φ ψ : PathCond α} (htests : φ.tests = ψ.tests) {v : Set Node}
    (hφ : φ.toForm v) (hψ : ψ.toForm v) : φ = ψ := by
  have ⟨s, f, hf⟩ := φ
  have ⟨t, g, hg⟩ := ψ
  dsimp at htests; subst t; congr
  funext x; exact PathCond.truth_eq_of_common_sat hφ hψ x.property x.property

lemma branch_tests_subset_of_common_sat {α : Lpofin (Label act test)}
    {φ ψ : PathCond α} (hφ : φ ∈ α.branches) (hψ : ψ ∈ α.branches)
    {v : Set Node} (hsatφ : φ.toForm v) (hsatψ : ψ.toForm v) :
    φ.tests ⊆ ψ.tests := by
  intro x hx
  by_contra hnx
  have htest : α.isTest x := φ.tests_valid hx
  have hnstuck : ¬ (α.form x ≤ α.stuck φ) := by
    intro hle
    exact (hφ.2.1 v hsatφ) (hle v (hφ.1 x hx v hsatφ))
  let η := ψ.union φ
  have hcompat {z} (hz : z ∈ ψ.tests ∩ φ.tests) :
      ψ.truth ⟨z, hz.1⟩ = φ.truth ⟨z, hz.2⟩ := by
    apply Bool.eq_iff_iff.mpr
    rw [ψ.truth_iff_mem hsatψ, φ.truth_iff_mem hsatφ]
  have hr : α.ReachableWith ψ x := by
    refine ⟨η, PathCond.le_union_left, ?_⟩
    exact (PathCond.toForm_antitone (PathCond.le_union_right hcompat)).trans (hφ.1 x hx)
  refine hψ.2.2 hnx htest ?_ hr
  · apply (not_reachableWith_of_form_le_stuck hψ.2.1).mt
    exact not_not.mpr hr

lemma branches_not_mutually_sat {α : Lpofin (Label act test)} {φ ψ : PathCond α}
    (hφ : φ ∈ α.branches) (hψ : ψ ∈ α.branches) (hneq : φ ≠ ψ) :
    ∀ v, ¬ (φ.toForm v ∧ ψ.toForm v) := by
  intro v ⟨h₁, h₂⟩
  have hsub₁ := branch_tests_subset_of_common_sat hφ hψ h₁ h₂
  have hsub₂ := branch_tests_subset_of_common_sat hψ hφ h₂ h₁
  apply hneq
  exact pathCond_eq_of_tests_eq_of_common_sat (Set.Subset.antisymm hsub₁ hsub₂) h₁ h₂

end Lpofin
