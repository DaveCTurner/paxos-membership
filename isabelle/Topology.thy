theory Topology
  imports Main FixedSeq
begin

locale topologyL
  = q: fixedSeqL quorums_seq "(\<lambda>(q1,_) (_,q2). (\<forall> S1 S2. q1 S1 \<longrightarrow> q2 S2 \<longrightarrow> S1 \<inter> S2 \<noteq> {}))"
  all_values quorums_to quorum valid_quorum
  + e: fixedSeqL epochs_seq  "(\<lambda>e1 e2. e1 \<le> e2)"  all_values epochs_to  epoch  valid_epoch
  for quorums_seq  :: "'value list \<Rightarrow> (('aid set \<Rightarrow> bool) * ('aid set \<Rightarrow> bool)) list"
    and epochs_seq   :: "'value list \<Rightarrow> nat list"
    and all_values   :: "nat \<Rightarrow> 'value"
    and quorums_to   :: "nat \<Rightarrow> (('aid set \<Rightarrow> bool) * ('aid set \<Rightarrow> bool)) list"
    and quorum       :: "nat \<Rightarrow> ('aid set \<Rightarrow> bool) * ('aid set \<Rightarrow> bool)"
    and valid_quorum :: "nat \<Rightarrow> bool"
    and epochs_to    :: "nat \<Rightarrow> nat list"
    and epoch        :: "nat \<Rightarrow> nat"
    and valid_epoch  :: "nat \<Rightarrow> bool"
    +
    (* predicate for phase-1 quorums in epoch e *)
  fixes read_quorum :: "nat \<Rightarrow> 'aid set \<Rightarrow> bool"
  defines "read_quorum e S == S \<noteq> {} \<and> fst (quorum e) S"
    (* predicate for phase-2 quorums in epoch e *)
  fixes write_quorum :: "nat \<Rightarrow> 'aid set \<Rightarrow> bool"
  defines "write_quorum e S == S \<noteq> {} \<and> snd (quorum e) S"
    (* well-definedness *)
  assumes epoch_quorum_defined: "\<And>vs e. e \<in> set (epochs_seq vs) \<Longrightarrow> e < length (quorums_seq vs)"

lemma (in topologyL)
  assumes vq: "valid_quorum n"
    and qs: "read_quorum n S1" "write_quorum n S2"
  shows quorum_inter: "S1 \<inter> S2 \<noteq> {}"
  using qs q.property_at_reflexive [OF vq] by (cases "quorum n", simp add: read_quorum_def write_quorum_def)

lemma (in topologyL)
  assumes vq: "valid_quorum (Suc n)"
    and qs: "read_quorum n S1" "write_quorum (Suc n) S2"
  shows quorum_inter_Suc: "S1 \<inter> S2 \<noteq> {}"
  using qs q.property_at_Suc [OF vq] by (cases "quorum n", cases "quorum (Suc n)", simp add: read_quorum_def write_quorum_def)

lemma (in topologyL)
  assumes "read_quorum n S"
  shows read_quorum_nonempty: "S \<noteq> {}"
  using assms by (simp add: read_quorum_def)

lemma (in topologyL)
  assumes "write_quorum n S"
  shows write_quorum_nonempty: "S \<noteq> {}"
  using assms by (simp add: write_quorum_def)

lemma (in topologyL)
  assumes ve: "valid_epoch e2" and e12: "e1 \<le> e2"
  shows epoch_mono: "epoch e1 \<le> epoch e2"
  using assms proof (induct e2 arbitrary: e1)
  case (Suc e2 e1)
  hence "e1 \<le> e2 \<or> e1 = Suc e2" by auto
  thus ?case
  proof (elim disjE)
    assume e12: "e1 \<le> e2"
    from Suc.prems(1) have ve2: "valid_epoch e2"
      apply (unfold e.valid_index_def)
      using Suc_lessD by blast
    from Suc.hyps [OF ve2 e12] have e12: "epoch e1 \<le> epoch e2" .
    also from Suc.prems have "... \<le> epoch (Suc e2)" by (metis e.property_at_Suc)
    finally show ?thesis .
  qed simp
qed simp

end
