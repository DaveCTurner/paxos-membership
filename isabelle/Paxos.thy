theory Paxos
  imports Main PropNo Weight FixedSeq Topology Synod
begin

locale propTvL
  = propNoL lt
  for lt :: "'pid \<Rightarrow> 'pid \<Rightarrow> bool" (infixl "\<prec>" 50) 
  +

  fixes prop_topology_version          :: "'pid \<Rightarrow> nat"
  assumes prop_topology_version_mono: "p0 \<preceq> p1 \<Longrightarrow> prop_topology_version p0 \<le> prop_topology_version p1"

locale paxosL
  = topologyL quorums_seq epochs_seq value_chosen
  + propTvL lt
  for lt :: "'pid \<Rightarrow> 'pid \<Rightarrow> bool" (infixl "\<prec>" 50)
  and quorums_seq :: "'value list \<Rightarrow> (('aid set \<Rightarrow> bool) * ('aid set \<Rightarrow> bool)) list"
  and epochs_seq :: "'value list \<Rightarrow> nat list"
  and multi_promised :: "nat \<Rightarrow> 'aid \<Rightarrow> 'pid \<Rightarrow> bool"
  and promised_free  :: "nat \<Rightarrow> 'aid \<Rightarrow> 'pid \<Rightarrow> bool"
  and promised_prev  :: "nat \<Rightarrow> 'aid \<Rightarrow> 'pid \<Rightarrow> 'pid \<Rightarrow> bool"
  and proposed       :: "nat \<Rightarrow> 'pid \<Rightarrow> bool"
  and accepted       :: "nat \<Rightarrow> 'aid \<Rightarrow> 'pid \<Rightarrow> bool"
  and chosen :: "nat \<Rightarrow> 'pid \<Rightarrow> bool"
  and value_proposed :: "nat \<Rightarrow> 'pid \<Rightarrow> 'value"
  and value_chosen :: "nat \<Rightarrow> 'value"
  +

  (* Message predicates *)

  fixes some_chosen    :: "nat \<Rightarrow> bool"
  defines "some_chosen == (%i. EX p. chosen i p)"

  fixes chosen_to      :: "nat \<Rightarrow> bool"
  defines "chosen_to == (%i. ALL j < i. some_chosen j)"

  fixes max_chosen_to :: nat
  defines "max_chosen_to == GREATEST i. chosen_to i"

  fixes i_max :: nat
  defines "i_max == length (epochs_to max_chosen_to)"

  fixes e_max :: nat
  defines "e_max == length (quorums_to max_chosen_to)"

  assumes value_chosen_def: "value_chosen == (%i. THE v. EX p'. chosen i p' \<and> value_proposed i p' = v)"

  assumes some_chosen_i_max: "some_chosen i \<Longrightarrow> i < i_max"
  assumes i_max_positive:    "0 < i_max"

  fixes promised :: "nat \<Rightarrow> 'aid \<Rightarrow> 'pid \<Rightarrow> bool"
  defines "promised i a p == ((\<exists>j \<le> i. multi_promised j a p) \<or> promised_free i a p) \<or> (\<exists> p1. promised_prev i a p p1)"

  fixes forced :: "nat \<Rightarrow> 'pid \<Rightarrow> 'aid set \<Rightarrow> 'pid set"
  defines "forced i p S == { p1. \<exists> a \<in> S. promised_prev i a p p1 }"

  assumes proposed_quorum:
    "proposed i p \<Longrightarrow> \<exists> S. 
        (read_quorum (prop_topology_version p) S)
      \<and> (\<forall> a \<in> S. promised i a p)
      \<and> (forced i p S = {} \<or> value_proposed i p = value_proposed i (max_of (forced i p S)))"

  assumes all_proposed_finite: "finite {(i,p). proposed i p}"

  fixes instance_with_epoch :: "nat \<Rightarrow> nat"
  defines "instance_with_epoch i == (GREATEST j. j \<le> i \<and> j < i_max)"

  assumes promised_topology:
    "promised i a p \<Longrightarrow> prop_topology_version p \<le> epoch (instance_with_epoch i)"

  assumes multi_promised:
    "\<lbrakk> multi_promised i a p0; accepted j a p1; i \<le> j \<rbrakk> \<Longrightarrow> p0 \<preceq> p1"

  assumes promised_free:
    "\<lbrakk> promised_free i a p0; accepted i a p1 \<rbrakk> \<Longrightarrow> p0 \<preceq> p1"

  assumes promised_prev_accepted:
    "promised_prev i a p0 p1 \<Longrightarrow> accepted i a p1"
  assumes promised_prev_prev:
    "promised_prev i a p0 p1 \<Longrightarrow> p1 \<prec> p0"
  assumes promised_prev_max:
    "\<lbrakk> promised_prev i a p0 p1; accepted i a p2; p2 \<prec> p0 \<rbrakk> \<Longrightarrow> p2 \<preceq> p1"

  assumes accepts_proposed:
    "accepted i a p \<Longrightarrow> proposed i p"

  assumes chosen_quorum:
    "chosen i p \<Longrightarrow> EX S. write_quorum (epoch i) S \<and> (ALL a:S. accepted i a p)"

  assumes chosen_topology:
    "chosen i p \<Longrightarrow> epoch i \<le> Suc (prop_topology_version p)"

lemma (in paxosL)
  shows chosen_to_initial: "chosen_to 0"
  by (auto simp add: chosen_to_def)

lemma (in paxosL)
  assumes chosen: "chosen_to i"
  assumes ji: "j \<le> i"
  shows chosen_to_mono: "chosen_to j"
  using assms by (auto simp add: chosen_to_def)

lemma (in paxosL)
  assumes chosen: "some_chosen i"
  shows some_chosen_valid_epoch: "valid_epoch i"
using assms some_chosen_i_max by (auto simp add: i_max_def e.valid_index_def)

lemma (in paxosL)
  assumes i_max: "i < i_max"
  shows epoch_defined_i_max: "epoch i < e_max"
proof -
  from i_max
  have eq: "epoch i = epochs_to max_chosen_to ! i"
    by (intro e.element_at, simp add: i_max_def)

  from i_max
  have "epoch i \<in> set (epochs_to max_chosen_to)"
    by (unfold eq, intro nth_mem, simp add: i_max_def)

  thus ?thesis
    by (unfold e_max_def q.sequence_to_def e.sequence_to_def, intro epoch_quorum_defined)
qed

lemma (in paxosL)
  assumes chosen: "some_chosen i"
  shows some_chosen_e_max: "epoch i < e_max"
  by (intro epoch_defined_i_max some_chosen_i_max chosen)

lemma (in paxosL)
  assumes chosen: "some_chosen i"
  shows some_chosen_valid_quorum:  "valid_quorum (epoch i)"
using assms some_chosen_e_max by (auto simp add: e_max_def q.valid_index_def)

lemma (in paxosL)
  assumes chosen: "some_chosen i"
  shows instance_with_epoch_chosen_eq: "instance_with_epoch i = i"
  by (unfold instance_with_epoch_def, intro Greatest_equality conjI some_chosen_i_max chosen, simp_all)

lemma (in paxosL)
  shows instance_with_epoch_le: "instance_with_epoch i \<le> i"
    and instance_with_epoch_lt: "instance_with_epoch i < i_max"
proof -
  have "(GREATEST j. j \<le> i \<and> j < i_max) \<le> i \<and> (GREATEST j. j \<le> i \<and> j < i_max) < i_max"
  proof (intro GreatestI, auto)
    show "0 < i_max" by (intro i_max_positive chosen_to_initial)
  qed
  thus "instance_with_epoch i \<le> i" "instance_with_epoch i < i_max"
    by (simp_all add: instance_with_epoch_def)
qed

lemma (in paxosL)
  assumes lt: "i < i_max"
  shows instance_with_epoch_eq: "instance_with_epoch i = i"
using assms by (unfold instance_with_epoch_def, intro Greatest_equality, auto)

lemma (in paxosL)
  assumes le: "i1 \<le> i2"
  shows instance_with_epoch_mono: "instance_with_epoch i1 \<le> instance_with_epoch i2"
apply (unfold instance_with_epoch_def)
apply (intro Greatest_le [where b = i_max] conjI)
apply (fold instance_with_epoch_def)
proof -
  note instance_with_epoch_le
  also note le
  finally show "instance_with_epoch i1 \<le> i2" .
  show "instance_with_epoch i1 < i_max" by (intro instance_with_epoch_lt)
qed simp

lemma (in paxosL)
  shows instance_with_epoch_valid: "valid_epoch (instance_with_epoch i)"
using instance_with_epoch_lt
  by (auto simp add: e.valid_index_def i_max_def)

lemma (in paxosL)
  assumes chosen: "some_chosen i"
  assumes proposed: "proposed i p"
  shows proposed_topology_chosen: "prop_topology_version p \<le> epoch i"
proof -
  from proposed_quorum [OF proposed] obtain a where "promised i a p"
    by (auto simp add: read_quorum_def)
  from promised_topology [OF this]
  show ?thesis by (simp only: instance_with_epoch_chosen_eq [OF chosen])
qed

lemma (in paxosL)
  assumes chosen: "chosen i p0" and proposed: "proposed i p1" and p01: "p0 \<prec> p1"
  shows chosen_proposed_epochs: "prop_topology_version p1 \<in> { epoch i - 1, epoch i }"
proof -
  from chosen have "some_chosen i" by (auto simp add: some_chosen_def)

  hence p1i: "prop_topology_version p1 \<le> epoch i"
    by (metis proposed_topology_chosen proposed)

  note chosen_topology [OF chosen]
  also from p01 have "Suc (prop_topology_version p0) \<le> Suc (prop_topology_version p1)"
    by (unfold Suc_le_mono, intro prop_topology_version_mono, auto)
  finally have "epoch i \<le> ..." by simp
  with p1i show ?thesis by auto
qed

lemma (in paxosL)
  assumes vq: "valid_quorum (epoch i)"
  assumes S1: "read_quorum (epoch i - 1) S1"
  assumes S2: "write_quorum (epoch i) S2"
  shows chosen_quorum_inter': "S1 \<inter> S2 \<noteq> {}"
proof (cases "epoch i")
  case 0
  with S1 have "read_quorum (epoch i) S1" by simp
  with S2 vq show ?thesis by (intro quorum_inter)
next
  case (Suc e)
  from vq S1 S2 have "valid_quorum (Suc e)" "read_quorum e S1" "write_quorum (Suc e) S2"
    by (simp_all add: Suc)
  thus ?thesis by (metis quorum_inter_Suc)
qed

lemma (in paxosL)
  shows proposed_finite: "finite {p. proposed i p}"
proof -
  have "{p. proposed i p} \<subseteq> snd ` ((%p. (i,p)) ` {p. proposed i p})" by (simp add: image_Collect)
  also have "... \<subseteq> snd ` {(i,p). proposed i p}" by auto
  finally show "finite {p. proposed i p}"
    by (intro finite_subset [OF _ finite_imageI [OF all_proposed_finite]])
qed

lemma (in paxosL)
  assumes chosen: "some_chosen i"
  shows multi_instances: "synodL lt
    (%p S. read_quorum  (prop_topology_version p) S)
    (%p S. write_quorum (epoch i)                 S)
    (%a p. (EX j. j \<le> i \<and> multi_promised j a p) \<or> promised_free i a p)
    (promised_prev i) (proposed i) (accepted i) (chosen i)
    (value_proposed i)"
apply unfold_locales
apply (fold promised_def forced_def max_of_def)
proof -
  fix i
  show "finite {p. proposed i p}" by (intro proposed_finite)

next
  fix a p
  assume acc: "accepted i a p"
  from accepts_proposed acc show "proposed i p" by simp

next
  fix p
  assume chosen: "chosen i p"
  from chosen_quorum [OF this]
  show "\<exists>S. (write_quorum (epoch i) S) \<and> (\<forall>a\<in>S. accepted i a p)" by auto

next
  fix a p0 p1
  assume acc: "accepted i a p1"
  assume "(\<exists>j \<le> i. multi_promised j a p0) \<or> promised_free i a p0"
  thus "p0 \<preceq> p1"
  proof (elim disjE exE conjE)
    assume "promised_free i a p0"
    thus ?thesis by (metis promised_free acc)
  next
    fix j assume ji: "j \<le> i" and mp: "multi_promised j a p0"
    thus ?thesis by (metis multi_promised acc)
  qed

next
  fix a p0 p1
  assume pp: "promised_prev i a p0 p1"
  show "accepted i a p1" by (metis promised_prev_accepted pp)
  show "p1 \<prec> p0" by (metis promised_prev_prev pp)

  fix p2
  assume "accepted i a p2" and "p2 \<prec> p0"
  with promised_prev_max pp
  show "p2 \<preceq> p1" by metis

next
  fix p
  assume "proposed i p"
  thus "\<exists>S. (read_quorum (prop_topology_version p) S) \<and> (\<forall>a\<in>S. promised i a p) \<and> (forced i p S = {} \<or> value_proposed i p = value_proposed i (max_of (forced i p S)))"
    by (metis proposed_quorum)

next
  fix SL assume "write_quorum (epoch i) SL"
  thus "SL \<noteq> {}"
    by (metis write_quorum_nonempty)
next

  have vq: "valid_quorum (epoch i)"
    by (intro some_chosen_valid_quorum chosen)
  fix SP SL p0 p1
  assume SP: "read_quorum (prop_topology_version p1) SP"
     and SL: "write_quorum (epoch i) SL"

  assume "chosen i p0" "proposed i p1" "p0 \<prec> p1"
  from chosen_proposed_epochs [OF this]
  have "prop_topology_version p1 = epoch i - 1 \<or> prop_topology_version p1 = epoch i" by simp
  thus "SP \<inter> SL \<noteq> {}"
  proof (elim disjE)
    assume eq: "prop_topology_version p1 = epoch i"
    with SP have SP: "read_quorum (epoch i) SP" by simp
    show ?thesis
      by (metis quorum_inter vq SP SL)
  next
    assume eq: "prop_topology_version p1 = epoch i - 1"
    with SP have SP: "read_quorum (epoch i - 1) SP" by simp
    show ?thesis
      by (metis chosen_quorum_inter' vq SP SL)
  qed
qed

theorem (in paxosL)
  assumes "chosen i p1" "chosen i p2"
  shows multi_paxos_consistent: "value_proposed i p1 = value_proposed i p2"
  using assms by (intro synodL.synod_consistent [OF multi_instances], auto simp add: some_chosen_def)

lemma (in paxosL) multiPaxos_the_value:
  assumes c: "chosen i p"
  shows "value_chosen i = value_proposed i p"
proof (unfold value_chosen_def, rule theI2)
  from c
  show "\<exists>p'. chosen i p' \<and> value_proposed i p' = value_proposed i p" by auto

  fix v
  assume "\<exists>p'. chosen i p' \<and> value_proposed i p' = v"
  then obtain p' where c': "chosen i p'"
    and v: "v = value_proposed i p'" by auto

  note v
  also have "value_proposed i p' = value_proposed i p"
    by (intro multi_paxos_consistent c c')
  finally show "v = value_proposed i p" .
  thus "v = value_proposed i p" .
qed

end
