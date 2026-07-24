import Pom.Lpo.Operations.Guard
import Pom.Lpo.Operations.Par.FinApprox
import Pom.Linearization

open Linearization

namespace Lpofin

noncomputable def guard {l : Type} [Bot l] {x : Node} {ℓ : l} {α β : Lpofin l}
    (hx : x ∉ α.nodes) (hx' : x ∉ β.nodes) (hd : Disjoint α.nodes β.nodes)
    (hroot : ℓ ≠ ⊥) : Lpofin l :=
  ⟨Lpo.guard hx hx' hd hroot,
    Set.finite_insert.mpr (Set.finite_union.mpr ⟨α.property, β.property⟩)⟩

open Classical in
lemma next_guard_eq_singleton {act test : Type}
    (p q : Lpofin (Label act test)) (b : test)
    {x : Node} (hx : x ∉ p.nodes) (hx' : x ∉ q.nodes)
    (hd : Disjoint p.nodes q.nodes) :
    next (Lpofin.guard hx hx' hd (Label.test_ne_bot b))
      (Lpofin.guard hx hx' hd (Label.test_ne_bot b)).nodes_finset = {x} := by
  ext y; constructor
  · intro hy; have ⟨hy, _, hmin⟩ := Finset.mem_filter.mp hy
    rcases (Set.Finite.mem_toFinset _).mp hy with rfl | hy
    · exact Finset.mem_singleton_self _
    · exfalso; apply hmin x (Or.inl ⟨rfl, hy⟩)
      exact (Set.Finite.mem_toFinset _).mpr <| Set.mem_insert x _
  · rintro hy; obtain rfl := Finset.mem_singleton.mp hy
    refine Finset.mem_filter.mpr ⟨?_, ?_, ?_⟩ <;>
      try exact (Set.Finite.mem_toFinset _).mpr <| Set.mem_insert y _
    intro z hz
    rcases hz with ⟨rfl, hy⟩ | hp | hq
    · exact (hy.elim hx hx').elim
    · exact (hx ((p.val.property.rel_dom hp).2)).elim
    · exact (hx' ((q.val.property.rel_dom hq).2)).elim

lemma filter_guard_root_true {act test : Type}
    (p q : Lpofin (Label act test)) (b : test)
    {x : Node} (hx : x ∉ p.nodes) (hx' : x ∉ q.nodes)
    (hd : Disjoint p.nodes q.nodes) :
    let a := Lpofin.guard hx hx' hd (Label.test_ne_bot b)
    a.filter_by_outcome a.nodes_finset x true = p.nodes_finset := by
  classical
  dsimp only; ext y
  simp only [filter_by_outcome, Finset.mem_filter, Finset.mem_erase,
    Lpofin.nodes_finset, Set.Finite.mem_toFinset, Lpofin.form, Lpo.form,
    Form.and, Form.sat, cond_true]
  constructor
  · rintro ⟨⟨_, hy⟩, v, hv, hvx⟩
    rcases hv with rfl | ⟨hyp, _, _⟩ | ⟨hyq, _, hnx⟩
    · contradiction
    · exact hyp
    · exact (hnx hvx).elim
  · intro hyp
    obtain ⟨v, hv⟩ := (p.val.property.form_dom y).mpr hyp
    refine ⟨⟨?_, ?_⟩, Set.insert x v, ?_, Set.mem_insert x _⟩
    · exact fun h ↦ hx (h ▸ hyp)
    · exact Set.mem_insert_of_mem x (Or.inl hyp)
    · right; left
      refine ⟨hyp, ?_, Set.mem_insert x _⟩
      exact (((p.val.property.form y) hyp).1 _ _ <| by
        refine Set.disjoint_left.mpr ?_
        intro z hz hrel
        have hz' : z = x := by
          rcases Set.mem_symmDiff.mp hz with ⟨hz, hn⟩ | ⟨hz, hn⟩
          · rcases Set.mem_insert_iff.mp hz with hzx | hzv
            · exact hzx
            · exact (hn hzv).elim
          · exact (hn (Set.mem_insert_of_mem x hz)).elim
        subst z
        exact hx (p.val.property.rel_dom hrel).1).mpr hv

lemma filter_guard_root_false {act test : Type}
    (p q : Lpofin (Label act test)) (b : test)
    {x : Node} (hx : x ∉ p.nodes) (hx' : x ∉ q.nodes)
    (hd : Disjoint p.nodes q.nodes) :
    let a := Lpofin.guard hx hx' hd (Label.test_ne_bot b)
    a.filter_by_outcome a.nodes_finset x false = q.nodes_finset := by
  classical
  dsimp only
  ext y
  simp only [filter_by_outcome, Finset.mem_filter, Finset.mem_erase,
    Lpofin.nodes_finset, Set.Finite.mem_toFinset, Lpofin.form, Lpo.form,
    Form.and, Form.sat, cond_false]
  constructor
  · rintro ⟨⟨_, hy⟩, v, hv, hnx⟩
    rcases hv with rfl | ⟨hyp, _, hvx⟩ | ⟨hyq, _, _⟩
    · contradiction
    · exact (hnx hvx).elim
    · exact hyq
  · intro hyq
    obtain ⟨v, hv⟩ := (q.val.property.form_dom y).mpr hyq
    refine ⟨⟨?_, ?_⟩, v \ {x}, ?_, ?_⟩
    · exact fun h ↦ hx' (h ▸ hyq)
    · exact Set.mem_insert_of_mem x (Or.inr hyq)
    · right; right
      refine ⟨hyq, ?_, ?_⟩
      · exact (((q.val.property.form y) hyq).1 _ _ <| by
          refine Set.disjoint_left.mpr ?_
          intro z hz hrel
          have hz' : z = x := by
            simp only [Set.mem_symmDiff, Set.mem_sdiff, Set.mem_singleton_iff] at hz
            aesop
          subst z
          exact hx' (q.val.property.rel_dom hrel).1).mpr hv
      · intro h
        exact ((Set.mem_sdiff x).mp h).2 (Set.mem_singleton x)
    · intro h
      exact ((Set.mem_sdiff x).mp h).2 (Set.mem_singleton x)

lemma guard_left_next {act test : Type}
    (p q : Lpofin (Label act test)) (b : test)
    {x : Node} (hx : x ∉ p.nodes) (hx' : x ∉ q.nodes)
    (hd : Disjoint p.nodes q.nodes) (u : Finset Node) (hu : ↑u ⊆ p.nodes) :
    (Lpofin.guard hx hx' hd (Label.test_ne_bot b)).next u = p.next u := by
  classical
  ext y
  simp only [next, Finset.mem_filter, Lpofin.nodes_finset, Set.Finite.mem_toFinset,
    Lpo.nodes, Lpofin.rel, Lpo.rel]
  constructor
  · rintro ⟨hy, hyu, hmin⟩
    exact ⟨hu hyu, hyu, fun z hz hzu ↦ hmin z (Or.inr (Or.inl hz)) hzu⟩
  · rintro ⟨hyp, hyu, hmin⟩
    refine ⟨Set.mem_insert_of_mem x (Or.inl hyp), hyu, ?_⟩
    intro z hz hzu
    rcases hz with ⟨rfl, _⟩ | hp | hq
    · exact hx (hu hzu)
    · exact hmin z hp hzu
    · exact (Set.disjoint_left.mp hd (hu hzu) (q.val.property.rel_dom hq).1).elim

lemma guard_left_lab {act test : Type}
    (p q : Lpofin (Label act test)) (b : test)
    {x y : Node} (hx : x ∉ p.nodes) (hx' : x ∉ q.nodes)
    (hd : Disjoint p.nodes q.nodes) (hy : y ∈ p.nodes) :
    (Lpofin.guard hx hx' hd (Label.test_ne_bot b)).lab y = p.lab y := by
  refine (if_neg ?_).trans <| if_pos hy
  rintro rfl; exact hx hy

lemma guard_left_filter {act test : Type}
    (p q : Lpofin (Label act test)) (b : test)
    {x y : Node} (hx : x ∉ p.nodes) (hx' : x ∉ q.nodes)
    (hd : Disjoint p.nodes q.nodes) (u : Finset Node) (hu : ↑u ⊆ p.nodes)
    (hy : y ∈ u) (r : Bool) :
    (Lpofin.guard hx hx' hd (Label.test_ne_bot b)).filter_by_outcome u y r =
    p.filter_by_outcome u y r := by
  classical
  ext z
  simp only [filter_by_outcome, Finset.mem_filter, Finset.mem_erase,
    Lpofin.form, Lpo.form]
  constructor
  · rintro ⟨hze, v, hv, hb⟩
    rcases hv with rfl | ⟨hzp, hpv, _⟩ | ⟨hzq, _, _⟩
    · exact (hx (hu hze.2)).elim
    · exact ⟨hze, v, hpv, hb⟩
    · exact (Set.disjoint_right.mp hd hzq (hu hze.2)).elim
  · rintro ⟨hze, v, hpv, hb⟩
    have hxy : x ≠ y := fun h ↦ hx (h ▸ hu hy)
    refine ⟨hze, Set.insert x v, ?_, ?_⟩
    · right; left
      refine ⟨hu hze.2, ?_, Set.mem_insert x _⟩
      exact (((p.val.property.form z) (hu hze.2)).1 _ _ <| by
        refine Set.disjoint_left.mpr ?_
        intro w hw hrel
        have hwx : w = x := by
          rcases Set.mem_symmDiff.mp hw with ⟨hw, hn⟩ | ⟨hw, hn⟩
          · rcases Set.mem_insert_iff.mp hw with h | h
            · exact h
            · exact (hn h).elim
          · exact (hn (Set.mem_insert_of_mem x hw)).elim
        subst w
        exact hx (p.val.property.rel_dom hrel).1).mpr hpv
    · match r with
      | true =>
        exact Set.mem_insert_of_mem x hb
      | false =>
        intro h
        rcases Set.mem_insert_iff.mp h with heq | hv
        · exact hxy heq.symm
        · exact hb hv

/-- For a node `y` on the left branch of a guard, the guard's formula at `y` holds of
a valuation `v` iff `p`'s formula holds and the root `x` is present in `v`. -/
lemma guard_left_form_eq {act test : Type}
    (p q : Lpofin (Label act test)) (b : test)
    {x y : Node} (hx : x ∉ p.nodes) (hx' : x ∉ q.nodes)
    (hd : Disjoint p.nodes q.nodes) (hy : y ∈ p.nodes) (v : Set Node) :
    (Lpofin.guard hx hx' hd (Label.test_ne_bot b)).form y v ↔ (p.form y v ∧ x ∈ v) := by
  have hxy : x ≠ y := fun h ↦ hx (h ▸ hy)
  have hyq : y ∉ q.nodes := Set.disjoint_left.mp hd hy
  simp only [Lpofin.form, guard, Lpo.form, Lpo.guard, Lpo.par_gen, Lpo.par_base, Form.and,
    Form.literal]
  constructor
  · rintro (heq | ⟨_, hpf⟩ | ⟨hyq', _⟩)
    · exact (hxy heq).elim
    · exact hpf
    · exact (hyq hyq').elim
  · intro hpf
    exact Or.inr (Or.inl ⟨hy, hpf⟩)

/-- The path-condition test in `lin_rec` behaves the same on the left branch of a guard as
on `p` itself, provided the accumulated path condition `φ` depends only on `p`'s nodes. -/
lemma guard_left_le_iff {act test : Type}
    (p q : Lpofin (Label act test)) (b : test)
    {x y : Node} (hx : x ∉ p.nodes) (hx' : x ∉ q.nodes)
    (hd : Disjoint p.nodes q.nodes) (φ : Form Node) (hφ : φ.DependsOn p.nodes)
    (hy : y ∈ p.nodes) :
    ((φ.and (Form.literal x)) ≤ (Lpofin.guard hx hx' hd (Label.test_ne_bot b)).form y) ↔
    (φ ≤ p.form y) := by
  have hpy : (p.form y).DependsOn {z | p.rel z y} := (p.val.property.form y hy).1
  have hpysub : {z | p.rel z y} ⊆ p.nodes := fun z hz ↦ (p.val.property.rel_dom hz).1
  have hdisj : ∀ v : Set Node, Disjoint (symmDiff v (insert x v)) p.nodes := by
    intro v
    rw [Set.disjoint_left]
    intro a ha hpa
    rcases Set.mem_symmDiff.mp ha with ⟨hav, hain⟩ | ⟨hain, hav⟩
    · exact hain (Set.mem_insert_of_mem x hav)
    · rcases Set.mem_insert_iff.mp hain with rfl | h
      · exact hx hpa
      · exact hav h
  constructor
  · intro H v hv
    have hxv : x ∈ insert x v := Set.mem_insert x v
    have hφv' : φ (insert x v) := (hφ v (insert x v) (hdisj v)) ▸ hv
    have hg := (guard_left_form_eq p q b hx hx' hd hy (insert x v)).mp
      (H (insert x v) ⟨hφv', hxv⟩)
    rw [hpy v (insert x v) (Set.disjoint_of_subset_right hpysub (hdisj v))]
    exact hg.1
  · intro H v hv
    exact (guard_left_form_eq p q b hx hx' hd hy v).mpr ⟨H v hv.1, hv.2⟩

lemma lin_rec_guard_left_aux {t : Type → Type} {s act test : Type}
    [Linearizable t s] [∀ {β : Type}, Preorder (t β)] [∀ {β : Type}, OrderBot (t β)]
    [Sem act s (t s)] [Sem test s (t Bool)]
    (p q : Lpofin (Label act test)) (b : test)
    {x : Node} (hx : x ∉ p.nodes) (hx' : x ∉ q.nodes)
    (hd : Disjoint p.nodes q.nodes) (u : Finset Node) (φ : Form Node)
    (hφ : φ.DependsOn p.nodes) (hu : ↑u ⊆ p.nodes) :
    ((Lpofin.guard hx hx' hd (Label.test_ne_bot b)).lin_rec u (φ.and (Form.literal x)) : s → t s) =
    p.lin_rec u φ := by
  classical
  induction u using Finset.strongInduction generalizing φ with
  | H u ih =>
    ext σ
    unfold lin_rec; refine if_congr (Iff.refl _) rfl ?_
    refine Nondet.finset_congr (guard_left_next p q b hx hx' hd u hu) ?_; ext ⟨y, hy⟩
    have hyu : y ∈ u := (Finset.mem_filter.mp hy).2.1
    have hyp : y ∈ p.nodes := hu hyu
    refine if_congr (guard_left_le_iff p q b hx hx' hd φ hφ hyp) ?_ rfl
    simp only [lin_node]
    rw [guard_left_lab p q b hx hx' hd hyp]
    match hl : p.lab y with
    | Label.bot => rfl
    | Label.fork =>
      exact congrFun (ih (u.erase y) (Finset.erase_ssubset hyu) φ hφ
        (fun _ h ↦ hu (Finset.mem_of_mem_erase h))) σ
    | Label.act ac =>
      refine congrArg₂ Bind.bind rfl ?_; funext τ
      exact congrFun (ih (u.erase y) (Finset.erase_ssubset hyu) φ hφ
        (fun _ h ↦ hu (Finset.mem_of_mem_erase h))) τ
    | Label.test bb =>
      refine congrArg₂ Bind.bind rfl ?_; funext r
      rw [guard_left_filter p q b hx hx' hd u hu hyu r, Form.and_comm_assoc]
      have hφ' :
          (φ.and (if r then Form.literal y else (Form.literal y).not)).DependsOn p.nodes := by
        have hun : p.nodes ∪ {y} = p.nodes :=
          Set.union_eq_self_of_subset_right (Set.singleton_subset_iff.mpr hyp)
        rw [← hun]
        refine Form.DependsOn.and hφ ?_
        split
        · exact Form.DependsOn.literal
        · exact Form.DependsOn.literal.not
      exact congrFun (ih (p.filter_by_outcome u y r)
        (Finset.ssubset_of_subset_of_ssubset filter_by_outcome_sub_erase
          (Finset.erase_ssubset hyu)) _ hφ'
        (fun z hz ↦ hu (filter_by_outcome_sub_erase hz |> Finset.mem_of_mem_erase))) σ

lemma guard_right_next {act test : Type}
    (p q : Lpofin (Label act test)) (b : test)
    {x : Node} (hx : x ∉ p.nodes) (hx' : x ∉ q.nodes)
    (hd : Disjoint p.nodes q.nodes) (u : Finset Node) (hu : ↑u ⊆ q.nodes) :
    (Lpofin.guard hx hx' hd (Label.test_ne_bot b)).next u = q.next u := by
  classical
  ext y
  simp only [next, Finset.mem_filter, Lpofin.nodes_finset, Set.Finite.mem_toFinset,
    Lpo.nodes, Lpofin.rel, Lpo.rel]
  constructor
  · rintro ⟨hy, hyu, hmin⟩
    exact ⟨hu hyu, hyu, fun z hz hzu ↦ hmin z (Or.inr (Or.inr hz)) hzu⟩
  · rintro ⟨hyq, hyu, hmin⟩
    refine ⟨Set.mem_insert_of_mem x (Or.inr hyq), hyu, ?_⟩
    intro z hz hzu
    rcases hz with ⟨rfl, _⟩ | hp | hq
    · exact hx' (hu hzu)
    · exact (Set.disjoint_left.mp hd (p.val.property.rel_dom hp).1 (hu hzu)).elim
    · exact hmin z hq hzu

lemma guard_right_lab {act test : Type}
    (p q : Lpofin (Label act test)) (b : test)
    {x y : Node} (hx : x ∉ p.nodes) (hx' : x ∉ q.nodes)
    (hd : Disjoint p.nodes q.nodes) (hy : y ∈ q.nodes) :
    (Lpofin.guard hx hx' hd (Label.test_ne_bot b)).lab y = q.lab y := by
  refine (if_neg ?_).trans <| if_neg ?_
  · rintro rfl; exact hx' hy
  · exact Set.disjoint_right.mp hd hy

lemma guard_right_filter {act test : Type}
    (p q : Lpofin (Label act test)) (b : test)
    {x y : Node} (hx : x ∉ p.nodes) (hx' : x ∉ q.nodes)
    (hd : Disjoint p.nodes q.nodes) (u : Finset Node) (hu : ↑u ⊆ q.nodes)
    (hy : y ∈ u) (r : Bool) :
    (Lpofin.guard hx hx' hd (Label.test_ne_bot b)).filter_by_outcome u y r =
    q.filter_by_outcome u y r := by
  classical
  ext z
  simp only [filter_by_outcome, Finset.mem_filter, Finset.mem_erase,
    Lpofin.form, Lpo.form]
  constructor
  · rintro ⟨hze, v, hv, hb⟩
    rcases hv with rfl | ⟨hzp, _, _⟩ | ⟨hzq, hqv, _⟩
    · exact (hx' (hu hze.2)).elim
    · exact (Set.disjoint_left.mp hd hzp (hu hze.2)).elim
    · exact ⟨hze, v, hqv, hb⟩
  · rintro ⟨hze, v, hqv, hb⟩
    have hxy : x ≠ y := fun h ↦ hx' (h ▸ hu hy)
    refine ⟨hze, v \ {x}, ?_, ?_⟩
    · right; right
      refine ⟨hu hze.2, ?_, ?_⟩
      · exact (((q.val.property.form z) (hu hze.2)).1 _ _ <| by
          refine Set.disjoint_left.mpr ?_
          intro w hw hrel
          have hwx : w = x := by
            simp only [Set.mem_symmDiff, Set.mem_sdiff, Set.mem_singleton_iff] at hw
            aesop
          subst w
          exact hx' (q.val.property.rel_dom hrel).1).mpr hqv
      · intro h
        exact ((Set.mem_sdiff x).mp h).2 (Set.mem_singleton x)
    · match r with
      | true =>
        exact (Set.mem_sdiff y).mpr ⟨hb, hxy.symm⟩
      | false =>
        intro h
        exact hb ((Set.mem_sdiff y).mp h).1

/-- For a node `y` on the right branch of a guard, the guard's formula at `y` holds of
a valuation `v` iff `q`'s formula holds and the root `x` is absent from `v`. -/
lemma guard_right_form_eq {act test : Type}
    (p q : Lpofin (Label act test)) (b : test)
    {x y : Node} (hx : x ∉ p.nodes) (hx' : x ∉ q.nodes)
    (hd : Disjoint p.nodes q.nodes) (hy : y ∈ q.nodes) (v : Set Node) :
    (Lpofin.guard hx hx' hd (Label.test_ne_bot b)).form y v ↔ (q.form y v ∧ x ∉ v) := by
  have hxy : x ≠ y := fun h ↦ hx' (h ▸ hy)
  have hyp : y ∉ p.nodes := Set.disjoint_right.mp hd hy
  simp only [Lpofin.form, guard, Lpo.form, Lpo.guard, Lpo.par_gen, Lpo.par_base, Form.and,
    Form.literal, Form.not]
  constructor
  · rintro (heq | ⟨hyp', _⟩ | ⟨_, hqf⟩)
    · exact (hxy heq).elim
    · exact (hyp hyp').elim
    · exact hqf
  · intro hqf
    exact Or.inr (Or.inr ⟨hy, hqf⟩)

/-- The path-condition test in `lin_rec` behaves the same on the right branch of a guard as
on `q` itself, provided the accumulated path condition `φ` depends only on `q`'s nodes. -/
lemma guard_right_le_iff {act test : Type}
    (p q : Lpofin (Label act test)) (b : test)
    {x y : Node} (hx : x ∉ p.nodes) (hx' : x ∉ q.nodes)
    (hd : Disjoint p.nodes q.nodes) (φ : Form Node) (hφ : φ.DependsOn q.nodes)
    (hy : y ∈ q.nodes) :
    ((φ.and (Form.literal x).not) ≤ (Lpofin.guard hx hx' hd (Label.test_ne_bot b)).form y) ↔
    (φ ≤ q.form y) := by
  have hqy : (q.form y).DependsOn {z | q.rel z y} := (q.val.property.form y hy).1
  have hqysub : {z | q.rel z y} ⊆ q.nodes := fun z hz ↦ (q.val.property.rel_dom hz).1
  have hdisj : ∀ v : Set Node, Disjoint (symmDiff v (v \ {x})) q.nodes := by
    intro v
    rw [Set.disjoint_left]
    intro a ha hqa
    rcases Set.mem_symmDiff.mp ha with ⟨hav, hain⟩ | ⟨hain, hav⟩
    · by_cases hax : a = x
      · exact hx' (hax ▸ hqa)
      · exact hain ⟨hav, fun h ↦ hax (Set.mem_singleton_iff.mp h)⟩
    · exact hav hain.1
  constructor
  · intro H v hv
    have hxv : x ∉ v \ {x} := by simp
    have hφv' : φ (v \ {x}) := (hφ v (v \ {x}) (hdisj v)) ▸ hv
    have hg := (guard_right_form_eq p q b hx hx' hd hy (v \ {x})).mp
      (H (v \ {x}) ⟨hφv', hxv⟩)
    rw [hqy v (v \ {x}) (Set.disjoint_of_subset_right hqysub (hdisj v))]
    exact hg.1
  · intro H v hv
    exact (guard_right_form_eq p q b hx hx' hd hy v).mpr ⟨H v hv.1, hv.2⟩

lemma lin_rec_guard_right_aux {t : Type → Type} {s act test : Type}
    [Linearizable t s] [∀ {β : Type}, Preorder (t β)] [∀ {β : Type}, OrderBot (t β)]
    [Sem act s (t s)] [Sem test s (t Bool)]
    (p q : Lpofin (Label act test)) (b : test)
    {x : Node} (hx : x ∉ p.nodes) (hx' : x ∉ q.nodes)
    (hd : Disjoint p.nodes q.nodes) (u : Finset Node) (φ : Form Node)
    (hφ : φ.DependsOn q.nodes) (hu : ↑u ⊆ q.nodes) :
    ((Lpofin.guard hx hx' hd (Label.test_ne_bot b)).lin_rec u
      (φ.and (Form.literal x).not) : s → t s) =
    q.lin_rec u φ := by
  classical
  induction u using Finset.strongInduction generalizing φ with
  | H u ih =>
    ext σ
    unfold lin_rec; refine if_congr (Iff.refl _) rfl ?_
    refine Nondet.finset_congr (guard_right_next p q b hx hx' hd u hu) ?_; ext ⟨y, hy⟩
    have hyu : y ∈ u := (Finset.mem_filter.mp hy).2.1
    have hyq : y ∈ q.nodes := hu hyu
    refine if_congr (guard_right_le_iff p q b hx hx' hd φ hφ hyq) ?_ rfl
    simp only [lin_node]
    rw [guard_right_lab p q b hx hx' hd hyq]
    match hl : q.lab y with
    | Label.bot => rfl
    | Label.fork =>
      exact congrFun (ih (u.erase y) (Finset.erase_ssubset hyu) φ hφ
        (fun _ h ↦ hu (Finset.mem_of_mem_erase h))) σ
    | Label.act ac =>
      refine congrArg₂ Bind.bind rfl ?_; funext τ
      exact congrFun (ih (u.erase y) (Finset.erase_ssubset hyu) φ hφ
        (fun _ h ↦ hu (Finset.mem_of_mem_erase h))) τ
    | Label.test bb =>
      refine congrArg₂ Bind.bind rfl ?_; funext r
      rw [guard_right_filter p q b hx hx' hd u hu hyu r, Form.and_comm_assoc]
      have hφ' :
          (φ.and (if r then Form.literal y else (Form.literal y).not)).DependsOn q.nodes := by
        have hun : q.nodes ∪ {y} = q.nodes :=
          Set.union_eq_self_of_subset_right (Set.singleton_subset_iff.mpr hyq)
        rw [← hun]
        refine Form.DependsOn.and hφ ?_
        split
        · exact Form.DependsOn.literal
        · exact Form.DependsOn.literal.not
      exact congrFun (ih (q.filter_by_outcome u y r)
        (Finset.ssubset_of_subset_of_ssubset filter_by_outcome_sub_erase
          (Finset.erase_ssubset hyu)) _ hφ'
        (fun z hz ↦ hu (filter_by_outcome_sub_erase hz |> Finset.mem_of_mem_erase))) σ

lemma lin_guard_branch {t : Type → Type} {s act test : Type}
    [Linearizable t s] [∀ {β : Type}, Preorder (t β)] [∀ {β : Type}, OrderBot (t β)]
    [Sem act s (t s)] [Sem test s (t Bool)]
    (p q : Lpofin (Label act test)) (b : test) (σ : s) (r : Bool)
    {x : Node} (hx : x ∉ p.nodes) (hx' : x ∉ q.nodes)
    (hd : Disjoint p.nodes q.nodes) :
    let a := Lpofin.guard hx hx' hd (Label.test_ne_bot b)
    a.lin_rec (t := t) (a.filter_by_outcome a.nodes_finset x r)
      (bif r then Form.literal x else (Form.literal x).not)
      σ =
      bif r then p.lin σ else q.lin σ := by
  dsimp only; cases r <;> simp only [cond_true, cond_false]
  · rw [filter_guard_root_false p q b hx hx' hd, ← Form.true_and (p := Form.not _)]
    refine congrFun (lin_rec_guard_right_aux p q b hx hx' hd _ _
      (Form.DependsOn.monotone _ (Set.empty_subset _) Form.DependsOn.true) ?_) σ
    intro x hx; exact q.property.mem_toFinset.mp hx
  · rw [filter_guard_root_true p q b hx hx' hd, ← Form.true_and (p := Form.literal _)]
    refine congrFun (lin_rec_guard_left_aux p q b hx hx' hd _ _
      (Form.DependsOn.monotone _ (Set.empty_subset _) Form.DependsOn.true) ?_) σ
    intro x hx; exact p.property.mem_toFinset.mp hx

lemma lin_guard {t : Type → Type} {s act test : Type}
    [Linearizable t s] [∀ {β : Type}, Preorder (t β)] [∀ {β : Type}, OrderBot (t β)]
    [Sem act s (t s)] [Sem test s (t Bool)]
    {p q : Lpofin (Label act test)} {b : test}
    {x : Node} {hx : x ∉ p.nodes} {hx' : x ∉ q.nodes}
    {hd : Disjoint p.nodes q.nodes} :
    (lin (Lpofin.guard hx hx' hd (Label.test_ne_bot b)) : s → t s) =
    fun σ ↦ Sem.sem b σ >>= fun r ↦ bif r then lin p σ else lin q σ := by
  classical
  ext σ
  conv => lhs; unfold Lpofin.lin Lpofin.lin_rec
  have hnext := next_guard_eq_singleton p q b hx hx' hd
  refine (if_neg ?_).trans ?_
  · exact Finset.ne_empty_of_mem ((Set.Finite.mem_toFinset _).mpr (Set.mem_insert x _))
  · conv => lhs; exact Nondet.finset_singleton _ (next_guard_eq_singleton p q b hx hx' hd)
    simp only [lin_node]
    have halab : (Lpofin.guard hx hx' hd (Label.test_ne_bot b)).lab x = Label.test b := by
      simp only [lab, Lpo.lab, guard, Lpo.guard, Lpo.par_gen, Lpo.par_base, Set.mem_union,
        ↓reduceIte]
    simp only [halab]; refine (if_pos ?_).trans ?_
    · refine le_of_eq <| (form_root_true (Set.mem_insert _ _) ?_).symm
      rintro y (rfl | hy | hy) hne
      · contradiction
      · left; exact ⟨rfl, Or.inl hy⟩
      · left; exact ⟨rfl, Or.inr hy⟩
    · refine congrArg₂ Bind.bind rfl ?_
      ext r; rw [Form.true_and, ← Bool.cond_eq_ite]
      exact lin_guard_branch p q b σ r hx hx' hd

lemma guard_trunc {l : Type} [Preorder l] [OrderBot l] {x : Node} {ℓ : l} {α β : Lpo l}
    {hx : x ∉ α.nodes} {hx' : x ∉ β.nodes} {hd : Disjoint α.nodes β.nodes}
    {hroot : ℓ ≠ ⊥}
    (n : ℕ) :
    (Lpo.guard hx hx' hd hroot).trunc (n + 1) =
    Lpofin.guard
      (fun h ↦ hx <| (α.trunc_le n).nodes h)
      (fun h ↦ hx' <| (β.trunc_le n).nodes h)
      (hd.mono (α.trunc_le n).nodes (β.trunc_le n).nodes)
      hroot := Subtype.ext <| Lpo.par_trunc n

end Lpofin
