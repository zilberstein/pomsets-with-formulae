import Mathlib.Data.Finite.Sigma

import Pom.Lpo.Linearization.Label
import Pom.Lpo.Operations.Seq.Equiv
import Pom.Lpo.Order.FinApprox

namespace Lpofin

variable {act test : Type}

def isTest (α : Lpofin (Label act test)) (x : Node) : Prop := Label.isTest (α.lab x)

def tests (α : Lpofin (Label act test)) : Set Node := { x | α.isTest x }

lemma tests_sub_nodes {α : Lpofin (Label act test)} : α.tests ⊆ α.nodes := by
  intro x hx
  refine (α.val.property.lab_dom x).mt ?_ |> not_not.mp
  have ⟨b, hlab⟩ := (Label.isTest_iff _).mp hx
  conv => arg 1; lhs; exact hlab
  exact Label.test_ne_bot _

structure PathCond (α : Lpofin (Label act test)) where
  tests : Set Node
  truth : ↑tests → Bool
  tests_valid : tests ⊆ α.tests
attribute [ext] PathCond

namespace PathCond

instance finite (α : Lpofin (Label act test)) : Finite (PathCond α) := by
  have hfin : Finite ↑α.tests.powerset := by
    refine (α.property.subset ?_).powerset.to_subtype
    intro x hx; exact tests_sub_nodes hx
  refine @Finite.of_injective _ (Σ (s : ↑α.tests.powerset), ↑s.val → Bool) ?_
    (fun φ ↦ ⟨⟨φ.tests, φ.tests_valid⟩, φ.truth⟩) ?_
  · refine @Finite.instSigma _ _ hfin ?_
    intro s; refine @Pi.finite _ _ ?_ _
    refine Set.Finite.to_subtype (α.property.subset ?_)
    exact s.property.trans tests_sub_nodes
  · intro φ ψ heq; simp only [Sigma.mk.injEq, Subtype.mk.injEq] at heq
    ext1
    · exact heq.1
    · exact heq.2

def empty (α : Lpofin (Label act test)) : PathCond α := {
  tests := ∅
  truth := fun ⟨_, h⟩ ↦ False.elim <| Set.notMem_empty _ h
  tests_valid := Set.empty_subset _
}

instance {α : Lpofin (Label act test)} : Bot (PathCond α) where
  bot := empty α

def toForm {α : Lpofin (Label act test)} (φ : PathCond α) : Form Node :=
  Form.sAnd fun x ↦ if φ.truth x then Form.literal x.val else (Form.literal x.val).not

lemma empty_toForm (α : Lpofin (Label act test)) :
    (empty α).toForm = Form.true := by
  ext v; constructor
  · intro _; trivial
  · intro _ x; exfalso; exact Set.notMem_empty _ x.property

def extend {α : Lpofin (Label act test)} (φ : PathCond α) {x : Node} (hx : α.isTest x) (b : Bool) :
    PathCond α := {
  tests := φ.tests.insert x
  truth := fun ⟨z, hz⟩ ↦ if h : z = x then b else φ.truth ⟨z, Set.mem_of_mem_insert_of_ne hz h⟩
  tests_valid := by
    intro z hz; rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact hx
    · exact φ.tests_valid hz
}

open Classical in
noncomputable def union {α : Lpofin (Label act test)} (φ ψ : PathCond α) : PathCond α := {
  tests := φ.tests ∪ ψ.tests
  truth := fun ⟨z, hz⟩ ↦
    if h : z ∈ φ.tests then φ.truth ⟨z, h⟩ else ψ.truth ⟨z, Or.resolve_left hz h⟩
  tests_valid := Set.union_subset φ.tests_valid ψ.tests_valid
}

def restrict {α : Lpofin (Label act test)} (φ : PathCond α) (s : Set Node) : PathCond α := {
  tests := φ.tests ∩ s
  truth := fun x ↦ φ.truth ⟨x.val, x.property.1⟩
  tests_valid := fun _ hx ↦ φ.tests_valid hx.1
}

instance {α : Lpofin (Label act test)} : LE (PathCond α) where
  le φ ψ :=
    ∃ (h : φ.tests ⊆ ψ.tests),
      ∀ x : ↑φ.tests, φ.truth x = ψ.truth ⟨x.val, h x.property⟩

instance {α : Lpofin (Label act test)} : Preorder (PathCond α) where
  le_refl φ := ⟨subset_refl _, fun _ ↦ rfl⟩
  le_trans _ _ _ := by
    intro ⟨hsub₁, heq₁⟩ ⟨hsub₂, heq₂⟩
    refine ⟨hsub₁.trans hsub₂, ?_⟩; intro x
    exact (heq₁ x).trans <| heq₂ ⟨x.val, hsub₁ x.property⟩

instance {α : Lpofin (Label act test)} : OrderBot (PathCond α) where
  bot_le _ := ⟨Set.empty_subset _, fun x ↦ False.elim x.property⟩

lemma extend_le {α : Lpofin (Label act test)} (φ : PathCond α) {x : Node}
    (hx : x ∉ φ.tests) (ht : α.isTest x) (b : Bool) : φ ≤ φ.extend ht b := by
  refine ⟨Set.subset_insert _ _, ?_⟩
  intro z; have hz : z ≠ x := by rintro rfl; exact hx z.property
  symm; exact dif_neg hz

lemma le_union_left {α : Lpofin (Label act test)} {φ ψ : PathCond α} :
    φ ≤ φ.union ψ := by
  refine ⟨Set.subset_union_left, ?_⟩; intro x; symm; exact dif_pos x.property

lemma le_union_right {α : Lpofin (Label act test)} {φ ψ : PathCond α}
    (h : ∀ {x}, ∀ hx : x ∈ φ.tests ∩ ψ.tests,
      φ.truth ⟨x, Set.inter_subset_left hx⟩ = ψ.truth ⟨x, Set.inter_subset_right hx⟩) :
    ψ ≤ φ.union ψ := by
  refine ⟨Set.subset_union_right, ?_⟩; intro x; by_cases hx : x.val ∈ φ.tests
  · conv => rhs; exact dif_pos hx
    symm; exact h ⟨hx, x.property⟩
  · symm; exact dif_neg hx

lemma restrict_le {α : Lpofin (Label act test)} (φ : PathCond α) (s : Set Node) :
    φ.restrict s ≤ φ := by
  constructor
  · intro x; rfl
  · exact Set.inter_subset_left

lemma toForm_antitone {α : Lpofin (Label act test)} : Antitone (toForm (α := α)) := by
  intro φ ψ ⟨hsub, heq⟩ v hψ x
  rw [heq x]; exact hψ ⟨x.val, hsub x.property⟩

lemma truth_iff_mem {α : Lpofin (Label act test)} (φ : PathCond α) {v : Set Node}
    (hsat : φ.toForm v) {x : φ.tests} : φ.truth x = true ↔ x.val ∈ v := by
  constructor
  · intro h; exact hsat x |> (congrFun (if_pos h) _).mp
  · intro h; by_contra ht
    apply hsat x |> (congrFun (if_neg ht) _).mp; exact h

lemma dependsOn {α : Lpofin (Label act test)} (φ : PathCond α) : φ.toForm.DependsOn φ.tests := by
  rw [← Set.iUnion_of_singleton_coe φ.tests]
  refine Form.DependsOn.sAnd fun x ↦ ?_; cases φ.truth x
  · exact Form.DependsOn.literal.not
  · exact Form.DependsOn.literal

lemma sat {α : Lpofin (Label act test)} (φ : PathCond α) : φ.toForm.sat := by
  use { x | ∃ (hx : x ∈ φ.tests), φ.truth ⟨x, hx⟩ = true }
  intro x; cases heq : φ.truth x
  · apply not_exists.mpr; intro hx
    simp only [Subtype.coe_eta, heq, Bool.false_eq_true, not_false_eq_true]
  · exact ⟨x.property, heq⟩

def up_cast [Preorder act] [Preorder test] {α β : Lpofin (Label act test)} (φ : PathCond α)
    (hle : α ≤ β) : PathCond β := {
  tests := φ.tests
  truth := φ.truth
  tests_valid := by
    apply φ.tests_valid.trans
    intro x hx; have ⟨_, hlab⟩ := (Label.isTest_iff _).mp hx
    have ⟨_, h, _⟩ := lab_is_test_le (le_of_eq_of_le hlab.symm <| hle.lab x)
    exact (Label.isTest_iff _).mpr ⟨_, h⟩
}

lemma cast_toForm [Preorder act] [Preorder test] {α β : Lpofin (Label act test)} {φ : PathCond α}
    {hle : α ≤ β} : (φ.up_cast hle).toForm = φ.toForm := by
  ext v; refine forall_congr' ?_; intro x; rfl

def permute {α : Lpofin (Label act test)} {Y : Set Node} (φ : PathCond α) (e : α.nodes ≃ Y) :
    PathCond (α.permute e) :=
  let e' := Lpo.perm_subset e (φ.tests_valid.trans tests_sub_nodes)
  {
    tests := Set.range fun x ↦ (e' x).val
    truth := fun x ↦ φ.truth (e'.symm x)
    tests_valid := by
      rintro _ ⟨x, rfl⟩
      have ⟨b, hlab⟩ := (Label.isTest_iff _).mp (φ.tests_valid x.property)
      refine (Label.isTest_iff _).mpr ⟨b, ?_⟩
      have ⟨x', heq⟩ := Set.mem_range.mp (e' x).property
      simp only; rw [← heq]
      refine (dif_pos ?_).trans ?_
      · exact Subtype.coe_prop _
      · conv => lhs; arg 2; arg 1; exact e.symm_apply_apply _
        simp only [Lpo.perm_subset, Equiv.coe_fn_mk, e'] at heq
        apply Subtype.val_injective at heq
        apply e.injective at heq; simp only [Subtype.mk.injEq] at heq
        rw [heq]; exact hlab
  }

lemma implies_weaken {α : Lpofin (Label act test)} {φ ψ : PathCond α} {P : Form Node}
    (hext : φ ≤ ψ) (himp : ψ.toForm ≤ P)
    (hdep : P.DependsOn (ψ.tests \ φ.tests).compl) :
    φ.toForm ≤ P := by
  intro v hφ; have ⟨v', hψ'⟩ := ψ.sat; have ⟨hsub, htr⟩ := hext
  let u := (v ∩ (ψ.tests \ φ.tests).compl) ∪ (v' ∩ (ψ.tests \ φ.tests))
  have hψ : ψ.toForm u := by
    subst u; refine (ψ.dependsOn _ _ ?_).mp hψ'
    refine Set.disjoint_left.mpr ?_; intro x hsd ht
    rcases Set.mem_symmDiff.mp hsd with ⟨hv', h'⟩ | ⟨h | h, hv'⟩
    · apply h'; clear h'; by_cases ht' : x ∈ ψ.tests \ φ.tests
      · right; exact ⟨hv', ht'⟩
      · left; refine ⟨?_, ht'⟩
        have hxt := (Set.mem_sdiff_of_mem ht).mt ht' |> not_not.mp
        apply (φ.truth_iff_mem hφ (x := ⟨_, hxt⟩)).mp
        rw [htr ⟨_, hxt⟩]
        exact (ψ.truth_iff_mem hψ' (x := ⟨_, ht⟩)).mpr hv'
    · apply Set.mem_compl h.2; refine ⟨ht, ?_⟩
      intro hxt;
      apply (ψ.truth_iff_mem hψ' (x := ⟨_, ht⟩)).mp.mt hv'
      rw [← htr ⟨_, hxt⟩]
      exact (φ.truth_iff_mem hφ (x := ⟨_, hxt⟩)).mpr h.1
    · exact hv' h.1
  apply hdep.restrict.mpr
  refine (congrArg P ?_).mp <| hdep.restrict.mp <| himp _ hψ; subst u
  ext x; constructor
  · rintro ⟨h | h, h'⟩
    · exact h
    · exfalso; exact h' h.2
  · intro h; exact ⟨Or.inl h, h.2⟩

lemma restrict_entails {α : Lpofin (Label act test)} (φ : PathCond α)
    {q : Form Node} {s : Set Node} (hq : q.DependsOn s) (hφq : φ.toForm ≤ q) :
    (φ.restrict s).toForm ≤ q := by
  refine implies_weaken (φ.restrict_le s) hφq ?_
  refine hq.monotone _ ?_
  intro x hx ⟨ht, h⟩; apply h
  exact ⟨ht, hx⟩

end PathCond

end Lpofin
