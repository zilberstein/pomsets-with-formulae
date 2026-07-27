import Pom.Lpo.Linearization.Label
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

-- stuck is a path condition formula indicating that the execution will definitely
-- encounter a ⊥ node
def stuck (α : Lpofin (Label act test)) : Form Node := Form.sOr fun x : ↑α.val.bots ↦ α.form x.val

lemma stuck_antitone [PartialOrder act] [PartialOrder test] :
    @Antitone (Lpofin (Label act test)) _ _ _ stuck := by
  intro α β hle v ⟨⟨x, hx, hlab⟩, hform⟩
  rcases hle.succ _ hx with hx' | ⟨y, ⟨hy, hlab'⟩, hyx⟩
  · refine ⟨⟨x, hx', ?_⟩, ?_⟩
    · refine le_antisymm ?_ bot_le
      rw [← hlab]; exact hle.lab x
    · refine (congrFun (hle.form x hx') v).mpr ?_
      exact hform
  · refine ⟨⟨y, hy, hlab'⟩, ?_⟩
    refine (congrFun (hle.form _ hy) _).mpr ?_
    refine (β.val.property.form _ (hle.nodes hy)).2 _ hyx _ ?_
    exact hform

def conj (α : Lpofin (Label act test)) (S : Set Node) : Form Node :=
  Form.sAnd fun x : ↑S ↦ α.form x.val

def node_lit (x : Node) (b : Bool) : Form Node :=
  if b then Form.literal x else (Form.literal x).not

lemma node_lit_depends_on {x : Node} {b : Bool} : Form.DependsOn (node_lit x b) {x} := by
  cases b
  · exact Form.DependsOn.literal.not
  · exact Form.DependsOn.literal

def mk_form {t : Set Node} (f : ↑t → Bool) : Form Node :=
  Form.sAnd (fun x ↦ node_lit x.val (f x))

lemma mk_form_depends_on {t : Set Node} (f : ↑t → Bool) : Form.DependsOn (mk_form f) t := by
  conv => arg 2; exact (Set.iUnion_of_singleton_coe t).symm
  refine Form.DependsOn.sAnd fun _ ↦ node_lit_depends_on

def reachable (α : Lpofin (Label act test)) (t : Set Node) (f : ↑t → Bool) : Prop :=
  (mk_form f).sat ∧
  mk_form f ≤ α.conj t ∧
  mk_form f ≤ α.stuck.not

def branches (α : Lpofin (Label act test)) : Set (Form Node) :=
  { φ : Form Node
  | ∃ t ⊆ α.tests,
    ∃ f : ↑t → Bool,
      φ = mk_form f ∧
      reachable α t f ∧
      ∀ {x b}, x ∉ t → α.isTest x →
        ¬ α.reachable (insert x t)
          fun ⟨z, hz⟩ ↦ if h : z = x then b else f ⟨z, Set.mem_of_mem_insert_of_ne hz h⟩
  }

lemma branches_finite (α : Lpofin (Label act test)) : α.branches.Finite := by
  sorry

lemma branches_monotone [PartialOrder act] [PartialOrder test] :
    @Monotone (Lpofin (Label act test)) _ _ _ branches := by
  rintro α β hle φ ⟨t, ht, f, rfl, ⟨⟨v, hform⟩, himp, hstk⟩, hmax⟩
  refine ⟨t, ?_, f, rfl, ?_, ?_⟩
  · intro x hx
    have ⟨b, heq⟩ := (Label.isTest_iff _).mp (ht hx)
    apply (Label.isTest_iff _).mpr
    have hlab := le_of_eq_of_le heq.symm <| hle.lab x
    have ⟨b', hb, _⟩ := lab_is_test_le hlab; exact ⟨b', hb⟩
  · refine ⟨⟨v, hform⟩, ?_, ?_⟩
    · intro v hv x; exact le_form hle v (himp _ hv x)
    · intro v hf h; apply hstk v hf
      exact stuck_antitone hle _ h
  · sorry

lemma le_branches [PartialOrder act] [PartialOrder test] {α β : Lpofin (Label act test)} (hle : α ≤ β) :
    α.branches = { φ ∈ β.branches | φ ≤ α.stuck.not } := by
  ext φ; constructor
  · intro h; constructor
    · exact branches_monotone hle h
    · obtain ⟨_, _, _, rfl, ⟨_, _, hstuck⟩, _⟩ := h
      exact hstuck
  · rintro ⟨⟨t, ht, f, rfl, ⟨⟨v, hsat⟩, himp, _⟩, hmax⟩, hstuck⟩
    have hsub : t ⊆ α.nodes := by
      intro x hxt
      have hx := tests_sub_nodes <| ht hxt
      rcases hle.succ _ hx with hxα | ⟨y, hbot, hyx⟩
      · exact hxα
      · exfalso; refine forall_not_of_not_exists (hstuck v hsat) ⟨y, hbot⟩ ?_
        refine (congrFun (hle.form y hbot.1) _).mpr ?_
        refine (β.val.property.form y (hle.nodes hbot.1)).2 _ hyx v ?_
        exact himp _ hsat ⟨_, hxt⟩
    refine ⟨t, ?_, f, rfl, ⟨⟨v, hsat⟩, ?_, hstuck⟩, ?_⟩
    · intro x hx; sorry
    · intro v hform x; have hx := hsub x.property
      exact (congrFun (hle.form _ hx) _).mpr (himp _ hform x)
    · intro x b hx htst; sorry

lemma branches_not_mutually_sat {α : Lpofin (Label act test)} {φ ψ : Form Node}
    (hφ : φ ∈ α.branches) (hψ : ψ ∈ α.branches) (hneq : φ ≠ ψ) :
    ∀ v, ¬ (φ v ∧ ψ v) := by
  intro v ⟨h₁, h₂⟩
  obtain ⟨t, ht, f, rfl, hr, hmax⟩ := hφ
  obtain ⟨u, hu, g, rfl, hr', hmax'⟩ := hψ
  sorry

end Lpofin
