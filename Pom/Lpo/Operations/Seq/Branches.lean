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

lemma mk_form_sat {t : Set Node} (f : ↑t → Bool) : (mk_form f).sat := by
  use { x | ∃ (hx : x ∈ t), f ⟨x, hx⟩ = true }
  intro x; cases heq : f x
  · apply not_exists.mpr; intro hx
    simp only [Subtype.coe_eta, heq, Bool.false_eq_true, not_false_eq_true]
  · exact ⟨x.property, heq⟩

lemma mk_form_depends_on {t : Set Node} (f : ↑t → Bool) : Form.DependsOn (mk_form f) t := by
  conv => arg 2; exact (Set.iUnion_of_singleton_coe t).symm
  refine Form.DependsOn.sAnd fun _ ↦ node_lit_depends_on

def reachable (α : Lpofin (Label act test)) (t : Set Node) (f : ↑t → Bool) : Prop :=
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
  have htests : α.tests.Finite := α.property.subset (by
    intro x hx
    have hn : α.lab x ≠ ⊥ := by
      have ⟨b, hb⟩ := (Label.isTest_iff _).mp hx
      rw [hb]
      exact Label.test_ne_bot b
    exact not_not.mp ((α.val.property.lab_dom x).mt hn))
  let T : Set (Set Node) := {t | t ⊆ α.tests}
  have hT : T.Finite := htests.finite_subsets
  let X := Σ t : ↑T, (↑(t.val) → Bool)
  letI : Fintype ↑T := hT.fintype
  letI : ∀ t : ↑T, Fintype ↑(t.val) := fun t => (htests.subset t.property).fintype
  haveI : Fintype X := inferInstance
  refine (Set.finite_range (fun p : X => mk_form p.2)).subset ?_
  rintro φ ⟨t, ht, f, rfl, _⟩
  exact ⟨⟨⟨t, ht⟩, f⟩, rfl⟩

/-- A branch formula depends only on the nodes of `α`. -/
lemma branch_dependsOn (α : Lpofin (Label act test)) {φ : Form Node} (hφ : φ ∈ α.branches) :
    φ.DependsOn α.nodes := by
  obtain ⟨t, ht, f, rfl, _⟩ := hφ
  refine (mk_form_depends_on f).monotone _ ?_
  intro x hx; exact tests_sub_nodes <| ht hx

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

lemma mk_form_insert_restrict {t : Set Node} {x : Node} {f : ↑t → Bool} {b : Bool}
    {v : Set Node} (hx : x ∉ t)
    (h : mk_form (fun ⟨z, hz⟩ ↦ if heq : z = x then b
      else f ⟨z, Set.mem_of_mem_insert_of_ne hz heq⟩) v) :
    mk_form f v := by
  intro z
  have hz := h ⟨z.val, Set.mem_insert_of_mem x z.property⟩
  simp only [node_lit] at hz ⊢
  split at hz <;> rename_i heq
  · exact (hx (heq ▸ z.property)).elim
  · simpa using hz

lemma branches_monotone [PartialOrder act] [PartialOrder test] :
    @Monotone (Lpofin (Label act test)) _ _ _ branches := by
  rintro α β hle φ ⟨t, ht, f, rfl, ⟨himp, hstk⟩, hmax⟩
  have ⟨v, hform⟩ := mk_form_sat f
  refine ⟨t, ?_, f, rfl, ?_, ?_⟩
  · intro x hx
    have ⟨b, heq⟩ := (Label.isTest_iff _).mp (ht hx)
    apply (Label.isTest_iff _).mpr
    have hlab := le_of_eq_of_le heq.symm <| hle.lab x
    have ⟨b', hb, _⟩ := lab_is_test_le hlab; exact ⟨b', hb⟩
  · refine ⟨?_, ?_⟩
    · intro v hv x; exact le_form hle v (himp _ hv x)
    · intro v hf h; apply hstk v hf
      exact stuck_antitone hle _ h
  · intro x b hx htest hreach
    obtain ⟨hwconj, hwstuck⟩ := hreach
    have hxnode : x ∈ β.nodes := tests_sub_nodes htest
    have ⟨w, hform⟩ :=
      mk_form_sat fun ⟨z, hz⟩ ↦
        if heq : z = x then b else f ⟨z, Set.mem_of_mem_insert_of_ne hz heq⟩
    rcases hle.succ x hxnode with hxα | ⟨y, hybot, hyx⟩
    · rcases isTest_of_le_or_bot hle htest with htestα | hbot
      · apply hmax hx htestα (b := b)
        refine ⟨?_, ?_⟩
        · intro v hf z
          refine (congrFun (hle.form z ?_) _).mpr (hwconj _ hf z)
          rcases z.property with hz | hz
          · simpa [hz] using hxα
          · exact tests_sub_nodes (ht hz)
        · intro u hu hs
          exact hstk u (mk_form_insert_restrict hx hu) hs
      · apply hstk _ (mk_form_insert_restrict hx hform)
        refine ⟨⟨x, hxα, hbot⟩, ?_⟩
        refine (congrFun (hle.form x hxα) _).mpr ?_
        exact hwconj _ hform ⟨x, Set.mem_insert x t⟩
    · apply hstk _ (mk_form_insert_restrict hx hform)
      refine ⟨⟨y, hybot⟩, ?_⟩
      refine (congrFun (hle.form y hybot.1) _).mpr ?_
      exact (β.val.property.form y (hle.nodes hybot.1)).2 x hyx _
         (hwconj _ hform ⟨x, Set.mem_insert x t⟩)

lemma le_branches [PartialOrder act] [PartialOrder test] {α β : Lpofin (Label act test)}
    (hle : α ≤ β) : α.branches = { φ ∈ β.branches | φ ≤ α.stuck.not } := by
  ext φ; constructor
  · intro h; constructor
    · exact branches_monotone hle h
    · obtain ⟨_, _, _, rfl, ⟨_, hstuck⟩, _⟩ := h
      exact hstuck
  · rintro ⟨⟨t, ht, f, rfl, ⟨himp, _⟩, hmax⟩, hstuck⟩
    have ⟨v, hsat⟩ := mk_form_sat f
    have hsub : t ⊆ α.nodes := by
      intro x hxt
      have hx := tests_sub_nodes <| ht hxt
      rcases hle.succ _ hx with hxα | ⟨y, hbot, hyx⟩
      · exact hxα
      · exfalso; refine forall_not_of_not_exists (hstuck v hsat) ⟨y, hbot⟩ ?_
        refine (congrFun (hle.form y hbot.1) _).mpr ?_
        refine (β.val.property.form y (hle.nodes hbot.1)).2 _ hyx v ?_
        exact himp _ hsat ⟨_, hxt⟩
    refine ⟨t, ?_, f, rfl, ⟨?_, hstuck⟩, ?_⟩
    · intro x hx; rcases isTest_of_le_or_bot hle (ht hx) with htest | hbot
      · exact htest
      · exfalso
        exact (hstuck v hsat) ⟨⟨x, hsub hx, hbot⟩,
          (congrFun (hle.form x (hsub hx)) v).mpr (himp _ hsat ⟨x, hx⟩)⟩
    · intro v hform x
      exact (congrFun (hle.form x (hsub x.property)) _).mpr (himp _ hform x)
    · intro x b hx htst hreach
      apply hmax hx
      · have ⟨c, hc⟩ := (Label.isTest_iff _).mp htst
        apply (Label.isTest_iff _).mpr
        obtain ⟨d, hd, _⟩ := lab_is_test_le (le_of_eq_of_le hc.symm (hle.lab x))
        exact ⟨d, hd⟩
      · obtain ⟨hwconj, hwstk⟩ := hreach
        refine ⟨?_, ?_⟩
        · intro v hform z
          exact le_form hle _ (hwconj _ hform z)
        · intro u hu hs
          exact hwstk u hu (stuck_antitone hle u hs)

lemma branches_not_mutually_sat {α : Lpofin (Label act test)} {φ ψ : Form Node}
    (hφ : φ ∈ α.branches) (hψ : ψ ∈ α.branches) (hneq : φ ≠ ψ) :
    ∀ v, ¬ (φ v ∧ ψ v) := by
  intro v ⟨h₁, h₂⟩
  obtain ⟨t, ht, f, rfl, hr, hmax⟩ := hφ
  obtain ⟨u, hu, g, rfl, hr', hmax'⟩ := hψ
  sorry

end Lpofin
