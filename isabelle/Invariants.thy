theory Invariants
  imports Paxos
begin

lemma (in paxosL) chosen_obtain_accepted:
  assumes "chosen i p"
  obtains a where "accepted i a p"
proof -
  from chosen_quorum [OF assms]
  obtain S where qS: "write_quorum (epoch i) S" and acc_S: "\<And>a. a \<in> S \<Longrightarrow> accepted i a p" by auto

  have "S \<noteq> {}" by (intro write_quorum_nonempty [OF qS])
  then obtain a where aS: "a \<in> S" by auto
  thus thesis by (intro that acc_S)
qed

lemma (in paxosL) chosen_proposed:
  assumes "chosen i p"
  shows "proposed i p"
proof -
  from chosen_obtain_accepted [OF assms]
  obtain a where aS: "accepted i a p" by auto
  from accepts_proposed [OF this] show ?thesis .
qed

lemma (in paxosL) finite_forced: "finite (forced i p S)"
  by (unfold forced_def, intro finite_subset [OF _ proposed_finite] subsetI CollectI, elim CollectE bexE, intro accepts_proposed promised_prev_accepted)

definition (in paxosL) "isConsistent multi_promised' promised_free' promised_prev' proposed' accepted' chosen' value_proposed'
  == paxosL prop_topology_version lt quorums_seq epochs_seq
                                     multi_promised' promised_free' promised_prev' proposed' accepted' chosen' value_proposed' (\<lambda>i. THE v. EX p'. chosen' i p' \<and> value_proposed' i p' = v)"

lemma (in topologyL) paxos_empty:
  assumes propTv:    "propTvL lt prop_topology_version"

  assumes epoch0:  "0 < length (epochs_seq [])"
  assumes quorum0: "epochs_seq [] ! 0 < length (quorums_seq [])"

  assumes no_mprom:  "\<And> i a p.    \<not>multi_promised i a p"
  assumes no_fprom:  "\<And> i a p.    \<not>promised_free  i a p"
  assumes no_bprom:  "\<And> i a p p1. \<not>promised_prev  i a p p1"
  assumes no_prop:   "\<And> i   p.    \<not>proposed       i   p"
  assumes no_acc:    "\<And> i a p.    \<not>accepted       i a p"
  assumes no_chosen: "\<And> i p.      \<not>chosen         i   p"

  shows "paxosL prop_topology_version lt quorums_seq epochs_seq multi_promised promised_free promised_prev proposed accepted chosen value_proposed (\<lambda>i. THE v. False)"
proof (intro_locales)
  from propTv
  show "propNoL lt" "propTvL_axioms lt prop_topology_version"
    by (simp_all add: propTvL_def)

  have i0: "\<And>i. (\<forall>j. \<not> j < i) = (i = (0 :: nat))" by auto

  have e0: "epochs_seq (map (\<lambda>i. THE v. False) [0..<SOME n. epochs_seq (map (\<lambda>i. THE v. False) [0..<n]) \<noteq> []]) ! 0 = epochs_seq [] ! 0"
  proof (intro someI2 [where Q = "\<lambda>n. epochs_seq (map (\<lambda>i. THE v. False) [0..<n]) ! 0 = epochs_seq [] ! 0"])
    from epoch0 show "epochs_seq (map (\<lambda>i. THE v. False) [0..<0]) \<noteq> []" by simp
    fix n
    from e.sequence_append_only [of "[]" "map (\<lambda>i. THE v. False) [0..<n]"]
      obtain appended
      where eq: "epochs_seq (map (\<lambda>i. THE v. False) [0..<n]) = epochs_seq [] @ appended"
      by auto

    from epoch0
    show "epochs_seq (map (\<lambda>i. THE v. False) [0..<n]) ! 0 = epochs_seq [] ! 0"
      by (cases "epochs_seq []", auto simp add: eq)
  qed

  have g0: "(GREATEST i. i = 0) = (0 :: nat)"
    by (intro Greatest_equality, simp_all)

  have f: "{(i, p). False} = {}" by auto

  from assms i0 e0
  show "paxosL_axioms prop_topology_version lt quorums_seq epochs_seq multi_promised promised_free promised_prev proposed accepted chosen value_proposed (\<lambda>i. THE v. False)"
    by (auto simp add: paxosL_axioms_def g0 f)
qed

lemma (in paxosL) multiPaxos_intro_simple:

  fixes multi_promised' promised_free' promised_prev'

  defines "forced'   i p S == { p1. \<exists> a \<in> S. promised_prev' i a p p1 }"
  defines "promised' i a p == ((\<exists>j \<le> i. multi_promised' j a p) \<or> promised_free' i a p) \<or> (\<exists> p1. promised_prev' i a p p1)"

  assumes proposed_quorum:
   "\<And> i p . proposed' i p \<Longrightarrow> \<exists> S.
        (read_quorum (prop_topology_version p) S)
      \<and> (\<forall> a \<in> S. promised' i a p)
      \<and> (forced' i p S = {} \<or> value_proposed i p = value_proposed i (max_of (forced' i p S)))"

  assumes promised_topology:
    "\<And> i a p. promised' i a p
      \<Longrightarrow> prop_topology_version p \<le> epoch (GREATEST j. j \<le> i \<and> j < i_max)"

  assumes proposed_finite: "finite {(i,p). proposed' i p}"

  assumes promised_free:
    "\<And> i a p0 p1. \<lbrakk> promised_free' i a p0; accepted' i a p1 \<rbrakk> \<Longrightarrow> p0 \<preceq> p1"

  assumes multi_promised:
    "\<And>i j a p0 p1. \<lbrakk> multi_promised' i a p0; accepted' j a p1; i \<le> j \<rbrakk> \<Longrightarrow> p0 \<preceq> p1"

  assumes promised_prev_accepted:
    "\<And> i a p0 p1. promised_prev' i a p0 p1 \<Longrightarrow> accepted' i a p1"
  assumes promised_prev_prev:
    "\<And> i a p0 p1. promised_prev' i a p0 p1 \<Longrightarrow> p1 \<prec> p0"
  assumes promised_prev_max:
    "\<And> i a p0 p1 p2. \<lbrakk> promised_prev' i a p0 p1; accepted' i a p2; p2 \<prec> p0 \<rbrakk> \<Longrightarrow> p2 \<preceq> p1"

  assumes accepts_proposed:
    "\<And> i p a. accepted' i a p \<Longrightarrow> proposed' i p"

  assumes chosen_quorum:
    "\<And> i p. chosen i p \<Longrightarrow> EX S. write_quorum (epoch i) S \<and> (ALL a:S. accepted' i a p)"

  shows "isConsistent
  multi_promised' promised_free' promised_prev' proposed' accepted' chosen value_proposed"
proof -
  have s: "\<And>i. epochs_to i  = epochs_seq  (map value_chosen [0..<i])"
          "\<And>i. quorums_to i = quorums_seq (map value_chosen [0..<i])"
          "\<And>i. epoch i = epochs_to (SOME n. i < length (epochs_to n)) ! i"
          "\<And>i. some_chosen i = (\<exists>p. chosen i p)"
          "\<And>i. chosen_to i = (\<forall>j<i. some_chosen j)"
          "\<And>e S. read_quorum  e S = (S \<noteq> {} \<and> fst (quorums_to (SOME n. e < length (quorums_to n)) ! e) S)"
          "\<And>e S. write_quorum e S = (S \<noteq> {} \<and> snd (quorums_to (SOME n. e < length (quorums_to n)) ! e) S)"
    by (simp_all add: e.sequence_to_def value_chosen_def q.sequence_to_def e.element_at_def
        some_chosen_def chosen_to_def read_quorum_def q.element_at_def write_quorum_def)

  from assms chosen_topology some_chosen_e_max some_chosen_i_max i_max_positive
  show ?thesis
  apply (unfold isConsistent_def)
  apply unfold_locales
  apply (fold value_chosen_def s)
  apply (fold s forced'_def promised'_def)
  apply (fold max_chosen_to_def e_max_def i_max_def)
    by auto
qed

(* the Acceptor only needs to know what it has previously accepted and promised
to send promised messages *)
lemma (in paxosL) multiPaxos_add_multi_promise:
  fixes p0
  assumes not_accepted: "\<And>p j. i0 \<le> j \<Longrightarrow> \<not>accepted j a0 p"
  assumes topology: "prop_topology_version p0 \<le> epoch (instance_with_epoch i0)"
  defines "multi_promised' i a p == (i,a,p) = (i0,a0,p0) \<or> multi_promised i a p"
  shows "isConsistent multi_promised' promised_free promised_prev proposed accepted chosen value_proposed"
using promised_topology all_proposed_finite promised_free
  promised_prev_accepted promised_prev_prev promised_prev_max
  accepts_proposed chosen_quorum
apply (intro multiPaxos_intro_simple, fold forced_def instance_with_epoch_def, unfold multi_promised'_def)
proof -
  fix i p
  assume p: "proposed i p"
  from proposed_quorum [OF this]
  obtain S where "read_quorum (prop_topology_version p) S"
                 "\<forall>a\<in>S. promised i a p"
                 "forced i p S = {} \<or> value_proposed i p = value_proposed i (max_of (forced i p S))" by auto
  thus "\<exists>S. read_quorum (prop_topology_version p) S \<and> (\<forall>a\<in>S. ((\<exists>j\<le>i. (j, a, p) = (i0, a0, p0) \<or> multi_promised j a p) \<or> promised_free i a p) \<or> (\<exists>p1. promised_prev i a p p1)) \<and> (forced i p S = {} \<or> value_proposed i p = value_proposed i (max_of (forced i p S)))"
    by (intro exI [of _ S], auto simp add: promised_def)
next
  fix i j a p p1
  assume a: "accepted j a p1" and ij: "i \<le> j"
  assume "(i, a, p) = (i0, a0, p0) \<or> multi_promised i a p"
  with multi_promised [OF _ a ij] not_accepted ij a show "p \<preceq> p1" by auto
next

  fix i a p
  assume promised': "((\<exists>j\<le>i. (j, a, p) = (i0, a0, p0) \<or> multi_promised j a p) \<or> promised_free i a p) \<or> (\<exists>p1. promised_prev i a p p1)"
  show "prop_topology_version p \<le> epoch (instance_with_epoch i)"
  proof (cases "\<exists> j \<le> i. (j, a, p) = (i0, a0, p0)")
    case False
    with promised' have "promised i a p" by (auto simp add: promised_def)
    with promised_topology show ?thesis by simp
  next
    case True
    hence i0i: "i0 \<le> i" and a: "a = a0" and p: "p = p0" by auto

    note topology
    also have "epoch (instance_with_epoch i0) \<le> epoch (instance_with_epoch i)"
      by (intro epoch_mono instance_with_epoch_mono instance_with_epoch_valid, simp add: i0i)
    finally show "prop_topology_version p \<le> epoch (instance_with_epoch i)"
      by (simp add: p)
  qed
qed simp_all

(* the Acceptor only needs to know what it has previously accepted and promised
to send promised messages *)
lemma (in paxosL) multiPaxos_add_promise_free:
  fixes p0
  assumes not_accepted: "\<And>p. \<not>accepted i0 a0 p"
  assumes topology: "prop_topology_version p0 \<le> epoch (instance_with_epoch i0)"
  defines "promised_free' i a p == (i,a,p) = (i0,a0,p0) \<or> promised_free i a p"
  shows "isConsistent multi_promised promised_free' promised_prev proposed accepted chosen value_proposed"
using all_proposed_finite multi_promised
  promised_prev_accepted promised_prev_prev promised_prev_max
  accepts_proposed chosen_quorum
apply (intro multiPaxos_intro_simple, fold forced_def instance_with_epoch_def, unfold promised_free'_def)
proof -
  fix i p
  assume p: "proposed i p"
  from proposed_quorum [OF this]
  obtain S where "read_quorum (prop_topology_version p) S"
                 "\<forall>a\<in>S. promised i a p"
                 "forced i p S = {} \<or> value_proposed i p = value_proposed i (max_of (forced i p S))" by auto
  thus "\<exists>S. read_quorum (prop_topology_version p) S \<and> (\<forall>a\<in>S. ((\<exists>j\<le>i. multi_promised j a p) \<or> (i, a, p) = (i0, a0, p0) \<or> promised_free i a p) \<or> (\<exists>p1. promised_prev i a p p1)) \<and> (forced i p S = {} \<or> value_proposed i p = value_proposed i (max_of (forced i p S)))"
    by (intro exI [of _ S], auto simp add: promised_def)
next

  fix i a p p1
  assume a: "accepted i a p1"
  assume "(i, a, p) = (i0, a0, p0) \<or> promised_free i a p"
  with promised_free [OF _ a] not_accepted a show "p \<preceq> p1" by auto
next

  fix i a p
  assume promised': "((\<exists>j\<le>i. multi_promised j a p) \<or> (i, a, p) = (i0, a0, p0) \<or> promised_free i a p) \<or> (\<exists>p1. promised_prev i a p p1)"
  from topology
  show "prop_topology_version p \<le> epoch (instance_with_epoch i)"
  proof (cases "(i,a,p) = (i0, a0, p0)")
    case False
    with promised' have "promised i a p" by (auto simp add: promised_def)
    from promised_topology [OF this] show ?thesis .
  qed simp
qed simp_all

lemma (in paxosL) multiPaxos_add_promise_prev:
  assumes accepted: "accepted i0 a0 p'0"
  assumes accepted_max: "\<And>p2. accepted i0 a0 p2 \<Longrightarrow> p2 \<preceq> p'0"
  assumes lt: "p'0 \<prec> p0"
  assumes topology: "prop_topology_version p0 \<le> epoch (instance_with_epoch i0)"

  defines "promised_prev' == (\<lambda> i a p p'. (i,a,p,p') = (i0, a0, p0, p'0) \<or> promised_prev i a p p')"
  defines "forced' i p S == {p1. \<exists>a\<in>S. promised_prev' i a p p1}"
  defines "promised' i a p == ((\<exists>j \<le> i. multi_promised j a p) \<or> promised_free i a p) \<or> (\<exists> p1. promised_prev' i a p p1)"
  shows "isConsistent multi_promised promised_free promised_prev' proposed accepted chosen value_proposed"
using all_proposed_finite multi_promised promised_free
  accepts_proposed chosen_quorum
apply (intro multiPaxos_intro_simple, fold forced'_def instance_with_epoch_def, unfold promised_prev'_def)
proof -
  fix i p
  assume p: "proposed i p"
  from proposed_quorum [OF this]
  obtain S where S: "read_quorum (prop_topology_version p) S"
                    "\<forall>a\<in>S. promised i a p"
                    "forced i p S = {} \<or> value_proposed i p = value_proposed i (max_of (forced i p S))" by auto

  have forced_eq: "forced' i p S = forced i p S"
  proof (cases "a0 \<in> S \<and> i = i0 \<and> p = p0")
    case True
    with S have promised: "promised i0 a0 p0"
            and s: "i = i0" "p = p0" by auto

    from promised have "promised_prev i0 a0 p0 p'0"
    proof (unfold promised_def, elim disjE exE conjE)
      assume p: "promised_free i0 a0 p0"
      from promised_free [OF p accepted] lt show ?thesis by auto
    next
      fix j assume ji: "j \<le> i0" and mp: "multi_promised j a0 p0"
      from multi_promised [OF mp accepted ji] lt show ?thesis by auto
    next
      fix p1
      assume pp: "promised_prev i0 a0 p0 p1"
      have p01: "p'0 \<preceq> p1" by (metis promised_prev_max pp accepted lt)
      have p10: "p1 \<preceq> p'0" by (metis accepted_max promised_prev_accepted pp)
      from p01 p10 pp show ?thesis by auto
    qed

    thus "forced' i p S = forced i p S"
      by (unfold forced'_def promised_prev'_def forced_def s, auto)
  qed (auto simp add: forced_def forced'_def promised_prev'_def)

  from S show "\<exists>S. read_quorum (prop_topology_version p) S \<and> (\<forall>a\<in>S. ((\<exists>j\<le>i. multi_promised j a p) \<or> promised_free i a p) \<or> (\<exists>p1. (i, a, p, p1) = (i0, a0, p0, p'0) \<or> promised_prev i a p p1)) \<and> (forced' i p S = {} \<or> value_proposed i p = value_proposed i (max_of (forced' i p S)))"
    by (intro exI [of _ S], auto simp add: promised_def forced_eq)
next
  fix i a p p'
  assume "(i, a, p, p') = (i0, a0, p0, p'0) \<or> promised_prev i a p p'"
  hence p: "promised_prev i a p p' \<or> (i, a, p, p') = (i0, a0, p0, p'0)" by auto

  from p accepted show "accepted i a p'"
    by (elim disjE, intro promised_prev_accepted, simp_all)

  from p lt show "p' \<prec> p"
    by (elim disjE, intro promised_prev_prev, simp_all)

  fix p''
  assume a: "accepted i a p''" and lt: "p'' \<prec> p"
  from a p accepted_max show "p'' \<preceq> p'"
    by (elim disjE, intro promised_prev_max [OF _ a lt], auto)

next
  fix i a p
  assume promised': "((\<exists>j\<le>i. multi_promised j a p) \<or> promised_free i a p) \<or> (\<exists>p1. (i, a, p, p1) = (i0, a0, p0, p'0) \<or> promised_prev i a p p1)"
  from topology show "prop_topology_version p \<le> epoch (instance_with_epoch i)"
  proof (cases "\<exists>p1. (i, a, p, p1) = (i0, a0, p0, p'0)")
    case False
    with promised' have promised: "promised i a p" by (auto simp add: promised_def)
    with promised_topology show ?thesis by metis
  qed simp_all

qed simp_all

lemma Greatest_lt:
  assumes lt: "\<And>n. P n \<Longrightarrow> n < m"
  assumes ex: "P n0"
  shows "(GREATEST n. P n) < (m :: nat)"
proof -
  have "P (GREATEST n. P n)" using lt GreatestI_nat ex nat_less_le by blast
  from lt [OF this] show ?thesis .
qed

lemma (in paxosL) multiPaxos_add_proposal_without_changing_value:
  assumes quorum_S: "read_quorum (prop_topology_version p0) S"
  assumes promised_S: "\<And>a. a \<in> S \<Longrightarrow> promised i0 a p0"
  assumes value_unless_proposed: "\<not>proposed i0 p0 \<Longrightarrow> forced i0 p0 S = {} \<or> value_proposed i0 p0 = value_proposed i0 (max_of (forced i0 p0 S))"

  defines "proposed' == \<lambda> i p. (i, p) = (i0, p0) \<or> proposed i p"

  shows "isConsistent multi_promised promised_free promised_prev proposed' accepted chosen value_proposed"
using promised_topology multi_promised promised_free
  promised_prev_accepted promised_prev_prev promised_prev_max
  accepts_proposed chosen_quorum
apply (intro multiPaxos_intro_simple, fold promised_def forced_def instance_with_epoch_def, unfold proposed'_def)
proof -
  fix i p
  assume p': "(i, p) = (i0, p0) \<or> proposed i p"
  from p' proposed_quorum [of i p]
  show "\<exists>S. read_quorum (prop_topology_version p) S \<and> (\<forall>a\<in>S. promised i a p) \<and> (forced i p S = {} \<or> value_proposed i p = value_proposed i (max_of (forced i p S)))"
  proof (elim disjE)
    assume "(i, p) = (i0, p0)" hence s: "i = i0" "p = p0" by simp_all
    show ?thesis
    proof (cases "proposed i0 p0")
      case False
      show ?thesis
      apply (unfold s)
        by (intro exI [of _ S] conjI quorum_S ballI promised_S value_unless_proposed False)
    next
      case True
      from proposed_quorum [OF this] show ?thesis by (simp add: s)
    qed
  qed
next
  have "{(i, p). (i, p) = (i0, p0) \<or> proposed i p} = insert (i0,p0) {(i,p). proposed i p}" by auto
  with all_proposed_finite show "finite {(i, p). (i, p) = (i0, p0) \<or> proposed i p}" by auto
qed simp_all

(* The Acceptor only needs to know about what it's promised previously to accept a proposal *)
lemma (in paxosL) multiPaxos_add_accepted:
  assumes proposed_p0: "proposed i0 p0"
  assumes promised_free_le: "\<And>p1. promised_free i0 a0 p1 \<Longrightarrow> p1 \<preceq> p0"
  assumes promised_prev_le: "\<And>p1 p2. promised_prev i0 a0 p1 p2 \<Longrightarrow> p1 \<preceq> p0"
  assumes multi_promised_le: "\<And>j p1. multi_promised j a0 p1 \<Longrightarrow> j \<le> i0 \<Longrightarrow> p1 \<preceq> p0"

  defines "accepted' == (\<lambda>i a p. (i,a,p) = (i0, a0, p0) \<or> accepted i a p)"
  shows "isConsistent multi_promised promised_free promised_prev proposed accepted' chosen value_proposed"
using proposed_quorum promised_topology all_proposed_finite proposed_finite
  promised_prev_accepted promised_prev_prev promised_prev_max
  accepts_proposed chosen_quorum
apply (intro multiPaxos_intro_simple, fold promised_def forced_def instance_with_epoch_def, unfold accepted'_def)
proof -
  fix i a p1 p0a
  assume a: "(i, a, p1) = (i0, a0, p0) \<or> accepted i a p1"
  {
    assume "promised_free i a p0a"
    with a show "p0a \<preceq> p1" by (metis prod.sel promised_free promised_free_le)
  next
    fix j assume "multi_promised j a p0a" "j \<le> i"
    with a show "p0a \<preceq> p1" by (metis prod.sel multi_promised multi_promised_le)
  next
    fix p2 assume "promised_prev i a p0a p2" "p1 \<prec> p0a"
    with a show "p1 \<preceq> p2"
      by (metis prod.sel promised_prev_le promised_prev_max propNo_leE propNo_lt_not_ge_E)
  next
    from a show "proposed i p1" by (metis prod.sel accepts_proposed proposed_p0)
  }
next
  fix i p
  assume "chosen i p"
  thus "(\<exists>S. write_quorum (epoch i) S \<and> (\<forall>a\<in>S. (i, a, p) = (i0, a0, p0) \<or> accepted i a p))"
    by (metis chosen_quorum)
qed simp_all

lemma (in paxosL) multiPaxos_change_value_proposed:
  assumes proposed_eq: "\<And> i p. proposed i p \<Longrightarrow> value_proposed i p = value_proposed' i p"
  shows "isConsistent multi_promised promised_free promised_prev proposed accepted chosen value_proposed'"
proof -
  from proposed_eq [OF chosen_proposed]
  have value_chosen_eq:
    "\<And>i p v. (chosen i p \<and> value_proposed' i p = v) = (chosen i p \<and> value_proposed i p = v)"
    by auto

  have s: "\<And>i. (\<exists>p. chosen i p) = some_chosen i"
          "\<And>i. (\<forall>j<i. some_chosen j) = chosen_to i"
          "\<And>i. (THE v. \<exists>p'. chosen i p' \<and> value_proposed' i p' = v) = value_chosen i"
          "\<And>i. epochs_seq  (map value_chosen [0..<i]) = epochs_to i"
          "\<And>i. quorums_seq (map value_chosen [0..<i]) = quorums_to i"
          "\<And>i. epochs_to (SOME n. i < length (epochs_to n)) ! i = epoch i"
          "\<And>i. quorums_to (SOME n. i < length (quorums_to n)) ! i = quorum i"
          "\<And>e S. (S \<noteq> {} \<and> fst (quorum e) S) = read_quorum e S"
          "\<And>e S. (S \<noteq> {} \<and> snd (quorum e) S) = write_quorum e S"
    by (auto simp add: some_chosen_def chosen_to_def value_chosen_eq value_chosen_def
        e.sequence_to_def e.element_at_def
        q.sequence_to_def q.element_at_def
        promised_def read_quorum_def write_quorum_def)

  show ?thesis
  using some_chosen_valid_epoch some_chosen_i_max i_max_positive
    all_proposed_finite promised_topology
    multi_promised promised_free
    promised_prev_accepted promised_prev_prev promised_prev_max
    accepts_proposed
    chosen_quorum chosen_topology
  apply (unfold isConsistent_def)
  apply (unfold_locales)
  apply (simp_all only: s)
  apply (fold forced_def promised_def max_chosen_to_def i_max_def)
  apply (fold instance_with_epoch_def)
  proof -
    fix i p assume p: "proposed i p"
    from proposed_quorum [OF p]
    obtain S where S_quorum: "read_quorum (prop_topology_version p) S"
               and S_promised: "\<forall>a\<in>S. promised i a p"
               and S_value: "forced i p S = {} \<or> value_proposed i p = value_proposed i (max_of (forced i p S))"
               by auto

    have r: "\<And>P Q.(\<not>P \<Longrightarrow> Q) \<Longrightarrow> P \<or> Q" by auto
    have forced: "forced i p S = {} \<or> value_proposed' i p = value_proposed' i (max_of (forced i p S))"
    proof (intro impI r)
      assume forced: "forced i p S \<noteq> {}"

      have forced_proposed: "\<And>p'. p' \<in> forced i p S \<Longrightarrow> proposed i p'"
      apply (unfold forced_def)
      apply (elim CollectE bexE)
        by (intro accepts_proposed promised_prev_accepted)

      have "value_proposed' i p = value_proposed i p" by (metis proposed_eq p)
      also from S_value forced have "... = value_proposed i (max_of (forced i p S))" by simp
      also from forced_proposed have "... = value_proposed' i (max_of (forced i p S))"
        by (intro proposed_eq forced_proposed max_of_mem forced finite_subset [OF _ proposed_finite] subsetI CollectI)
      finally show "value_proposed' i p = ..." .
    qed

    from S_value
    show "\<exists>S. read_quorum (prop_topology_version p) S \<and> (\<forall>a\<in>S. promised i a p) \<and> (forced i p S = {} \<or> value_proposed' i p = value_proposed' i (max_of (forced i p S)))"
      by (intro exI [of _ S] conjI S_quorum S_promised, simp add: forced)
  qed
qed

lemma (in paxosL) multiPaxos_add_proposal:
  assumes quorum_S: "read_quorum (prop_topology_version p0) S"
  assumes promised_S: "\<And>a. a \<in> S \<Longrightarrow> promised i0 a p0"
  assumes not_proposed: "\<not>proposed i0 p0"

  fixes free_value
  defines "value_proposed' == \<lambda> i p. if (i, p) = (i0, p0) then (if forced i0 p0 S = {} then free_value else value_proposed i0 (max_of (forced i0 p0 S))) else value_proposed i p"
  defines "proposed' == \<lambda> i p. (i, p) = (i0, p0) \<or> proposed i p"

  shows "isConsistent multi_promised promised_free promised_prev proposed' accepted chosen value_proposed'"
proof -
  from not_proposed
  have proposed_eq: "\<And>i p. proposed i p \<Longrightarrow> value_proposed' i p = value_proposed i p"
    by (auto simp add: value_proposed'_def)

  from proposed_eq [OF chosen_proposed]
  have value_chosen_eq:
    "\<And>i p v. (chosen i p \<and> value_proposed i p = v) = (chosen i p \<and> value_proposed' i p = v)"
    by auto
  hence simps: "\<And>i. (THE v. \<exists>p'. chosen i p' \<and> value_proposed' i p' = v) = value_chosen i"
               "\<And>n. epochs_seq  (map value_chosen [0..<n]) = epochs_to  n"
               "\<And>n. quorums_seq (map value_chosen [0..<n]) = quorums_to n"
               "\<And>i. epochs_to  (SOME n. i < length (epochs_to  n)) ! i = epoch  i"
               "\<And>i. quorums_to (SOME n. i < length (quorums_to n)) ! i = quorum i"
    by (auto simp add: value_chosen_def e.sequence_to_def q.sequence_to_def
                       q.element_at_def e.element_at_def)

  from quorum_S promised_S
  show ?thesis
  apply (unfold proposed'_def)
  apply (intro paxosL.multiPaxos_add_proposal_without_changing_value [where S = S and value_chosen = value_chosen])
  apply (fold promised_def forced_def)
  apply (unfold simps)
  proof -
    from not_proposed
    have v': "isConsistent multi_promised promised_free promised_prev proposed accepted chosen value_proposed'"
      by (intro multiPaxos_change_value_proposed, auto simp add: value_proposed'_def)
    thus "paxosL prop_topology_version (\<prec>) quorums_seq epochs_seq multi_promised promised_free promised_prev proposed accepted chosen value_proposed' value_chosen"
      by (simp add: isConsistent_def value_chosen_def value_chosen_eq)
  qed (auto simp add: read_quorum_def value_proposed'_def)
qed

lemma (in paxosL) chosen_to_max: "chosen_to max_chosen_to"
proof -
  have "finite {i. (\<exists> p. proposed i p)}"
  proof (rule finite_subset [OF _ finite_imageI])
    from all_proposed_finite show "finite {(i, p). proposed i p}" .
    show "{i. (\<exists>p. proposed i p)} \<subseteq> fst ` {(i, p). proposed i p}"
    proof (intro subsetI, elim CollectE conjE exE, intro image_eqI)
      fix i p assume p: "proposed i p"
      thus "(i,p) \<in> {(i,p). proposed i p}" by simp
      show "i = fst (i, p)" by simp
    qed
  qed
  hence "{i. (\<exists> p. proposed i p)} \<noteq> UNIV" by (intro notI, simp)
  then obtain im where not_proposed: "\<And>p. \<not> proposed im p" by auto

  have "\<And>p. \<not> chosen im p"
    by (intro contrapos_nn [OF not_proposed] chosen_proposed)
  hence not_chosen: "\<not> some_chosen im" by (auto simp add: some_chosen_def)

  show ?thesis
  proof (unfold max_chosen_to_def, intro GreatestI_nat impI)
    from chosen_to_initial show "chosen_to 0" .
    show "\<forall>i. chosen_to i \<longrightarrow> i \<le> im"
    proof (intro allI impI)
      fix i assume "chosen_to i"
      hence sc: "\<And>j. j < i \<Longrightarrow> some_chosen j" by (simp add: chosen_to_def)
      show "i \<le> im"
      proof (rule ccontr)
        assume "\<not>i \<le> im" hence "im < i" by auto
        with sc not_chosen show False by simp
      qed
    qed
  qed
qed

lemma (in paxosL) multiPaxos_add_choice:
  assumes quorum_S: "write_quorum (epoch i0) S"
  assumes accepted_S: "\<And>a. a \<in> S \<Longrightarrow> accepted i0 a p0"
  assumes topo_version: "epoch i0 \<le> Suc (prop_topology_version p0)"
  assumes i0_max: "i0 < i_max"

  defines "chosen' == (\<lambda>i p. (i, p) = (i0, p0) \<or> chosen i p)"

  shows "isConsistent multi_promised promised_free promised_prev proposed accepted chosen' value_proposed"
proof -

  define value_chosen'        where "value_chosen' \<equiv> \<lambda>i. THE v. \<exists>p'. chosen' i p' \<and> value_proposed i p' = v"

  define epochs_to'           where "epochs_to'  \<equiv> \<lambda>n. epochs_seq   (map value_chosen' [0..<n])"
  define quorums_to'          where "quorums_to' \<equiv> \<lambda>n. quorums_seq  (map value_chosen' [0..<n])"

  define epoch'               where "epoch'      \<equiv> \<lambda>i. epochs_to'  (SOME n. i < length (epochs_to' n))  ! i"
  define quorum'              where "quorum'     \<equiv> \<lambda>i. quorums_to' (SOME n. i < length (quorums_to' n)) ! i"

  define read_quorum'         where "read_quorum'  \<equiv> \<lambda>e S. S \<noteq> {} \<and> fst (quorum' e) S"
  define write_quorum'        where "write_quorum' \<equiv> \<lambda>e S. S \<noteq> {} \<and> snd (quorum' e) S"

  define some_chosen'         where "some_chosen'   \<equiv> \<lambda>i. \<exists>p. chosen' i p"
  define chosen_to'           where "chosen_to'     \<equiv> \<lambda>i. \<forall>j<i. some_chosen' j"
  define max_chosen_to'       where "max_chosen_to' \<equiv> GREATEST i. chosen_to' i"

  define i_max'               where "i_max' \<equiv> length (epochs_to' max_chosen_to')"
  define e_max'               where "e_max' \<equiv> length (quorums_to' max_chosen_to')"
  define instance_with_epoch' where "instance_with_epoch' \<equiv> \<lambda>i. GREATEST j. j \<le> i \<and> j < i_max'"

  have s: "\<And>n. epochs_to'   n = epochs_seq  (map value_chosen' [0..<n])"
          "\<And>n. quorums_to'  n = quorums_seq (map value_chosen' [0..<n])"
          "\<And>i. epoch'       i = epochs_to'  (SOME n. i < length (epochs_to'  n)) ! i"
          "\<And>i. quorum'      i = quorums_to' (SOME n. i < length (quorums_to' n)) ! i"
          "\<And>i. some_chosen' i = (\<exists>p. chosen' i p)"
          "\<And>i. chosen_to'   i = (\<forall>j<i. some_chosen' j)"
          "\<And>i. instance_with_epoch' i = (GREATEST j. j \<le> i \<and> j < i_max')"
          "\<And>e S. read_quorum'  e S = (S \<noteq> {} \<and> fst (quorum' e) S)"
          "\<And>e S. write_quorum' e S = (S \<noteq> {} \<and> snd (quorum' e) S)"
        by (simp_all add: epochs_to'_def quorums_to'_def epoch'_def quorum'_def
                          instance_with_epoch'_def some_chosen'_def chosen_to'_def
                          read_quorum'_def write_quorum'_def)

  have value_chosen'_eq: "\<And>i. some_chosen i \<Longrightarrow> value_chosen i = value_chosen' i"
  proof -
    fix i
    assume chosen: "some_chosen i"
    show "?thesis i"
    proof (cases "i = i0")
      case False
      thus ?thesis
        by (simp add: value_chosen_def value_chosen'_def chosen'_def)
    next
      case True
      with chosen have chosen0: "some_chosen i0" by simp
      then obtain p where chosen_p: "chosen i0 p" by (auto simp add: some_chosen_def)

      from multiPaxos_the_value [OF chosen_p] have "value_chosen i0 = value_proposed i0 p" .

      moreover have "value_chosen' i0 = value_proposed i0 p"
      proof (unfold value_chosen'_def, intro the_equality exI [of _ p] conjI refl)
        from chosen_p show "chosen' i0 p" by (auto simp add: chosen'_def)
        fix v assume "\<exists>p'. chosen' i0 p' \<and> value_proposed i0 p' = v"
        then obtain p' where chosen_p': "chosen' i0 p'"
                         and eq_v: "v = value_proposed i0 p'" by auto
        show "v = value_proposed i0 p"
        apply (unfold eq_v)
        apply (intro synodL.synod_consistent [OF synodL.synod_add_chosen [OF multi_instances, OF chosen0 quorum_S accepted_S]])
        proof -
          from chosen_p show "p = p0 \<or> chosen i0 p" by simp
          from chosen_p' show "p' = p0 \<or> chosen i0 p'"by (simp add: chosen'_def)
        next
          fix SP SL p1
          assume SP: "read_quorum (prop_topology_version p1) SP"
             and SL: "write_quorum (epoch i0) SL"
             and proposed: "proposed i0 p1" and p01: "p0 \<prec> p1"

          show "SP \<inter> SL \<noteq> {}"
          proof (cases "epoch i0 = prop_topology_version p1")
            case True
            show ?thesis
            proof (intro quorum_inter)
              from chosen0 show "valid_quorum (epoch i0)" by (intro some_chosen_valid_quorum)
              from SL show "write_quorum (epoch i0) SL" .
              from SP show "read_quorum (epoch i0) SP" by (simp add: True)
            qed
          next
            case False
            moreover from proposed_quorum [OF proposed]
            obtain a where "promised i0 a p1" by (auto simp add: read_quorum_def)
            from promised_topology [OF this]
            have "prop_topology_version p1 \<le> epoch (instance_with_epoch i0)" .
            moreover have "instance_with_epoch i0 = i0" by (metis instance_with_epoch_chosen_eq chosen0)
            ultimately have p1i0: "prop_topology_version p1 < epoch i0" by simp

            note topo_version
            moreover from p01 have "prop_topology_version p0 \<le> prop_topology_version p1"
              by (intro prop_topology_version_mono, simp)
            ultimately have "epoch i0 \<le> Suc (prop_topology_version p1)" by simp

            with p1i0 False have eq: "epoch i0 = Suc (prop_topology_version p1)" by auto

            show ?thesis
              by (intro chosen_quorum_inter' [of i0] some_chosen_valid_quorum SL chosen0, simp add: eq SP)
          qed
        qed
      qed

      ultimately show ?thesis by (simp add: True)
    qed
  qed

  have topologyL: "topologyL quorums_seq epochs_seq" by (intro_locales)

  have max_chosen_to_le: "max_chosen_to \<le> max_chosen_to'"
  proof -
    have "finite {i. i \<le> i0 \<or> (\<exists> p. proposed i p)}"
    apply (unfold Collect_disj_eq finite_Un)
    apply (intro conjI, simp)
    proof (rule finite_subset [OF _ finite_imageI])
      from all_proposed_finite show "finite {(i, p). proposed i p}" .
      show "{i. (\<exists>p. proposed i p)} \<subseteq> fst ` {(i, p). proposed i p}"
      proof (intro subsetI, elim CollectE conjE exE, intro image_eqI)
        fix i p assume p: "proposed i p"
        thus "(i,p) \<in> {(i,p). proposed i p}" by simp
        show "i = fst (i, p)" by simp
      qed
    qed
    hence "{i. i \<le> i0 \<or> (\<exists> p. proposed i p)} \<noteq> UNIV" by (intro notI, simp)
    then obtain im where "\<not> (im \<le> i0 \<or> (\<exists> p. proposed im p))" by auto
    hence imi0: "im > i0" and not_proposed: "\<And>p. \<not> proposed im p" by auto

    have "\<And>p. \<not> chosen im p"
      by (intro contrapos_nn [OF not_proposed] chosen_proposed)
    with imi0 have "\<And>p. \<not> chosen' im p" by (auto simp add: chosen'_def)
    hence not_chosen: "\<not> some_chosen' im" by (auto simp add: some_chosen'_def)

    have chosen_to_implies: "\<And>i. chosen_to i \<Longrightarrow> chosen_to' i"
      by (auto simp add: chosen_to_def chosen_to'_def some_chosen_def some_chosen'_def chosen'_def)

    show ?thesis
    proof (unfold max_chosen_to_def max_chosen_to'_def, intro Greatest_le_nat chosen_to_implies GreatestI_nat impI)
      from chosen_to_initial show "chosen_to 0" .
      show "\<forall>i. chosen_to' i \<longrightarrow> i \<le> im"
      proof (intro allI impI)
        fix i assume "chosen_to' i"
        hence sc: "\<And>j. j < i \<Longrightarrow> some_chosen' j" by (simp add: chosen_to'_def)
        show "i \<le> im"
        proof (rule ccontr)
          assume "\<not>i \<le> im" hence "im < i" by auto
          with sc not_chosen show False by simp
        qed
      qed
      with chosen_to_implies show "\<forall>i. chosen_to i \<longrightarrow> i \<le> im" by auto
    qed
  qed

  have i_max_le: "i_max \<le> i_max'"
  proof -
    from max_chosen_to_le
    have eq: "max_chosen_to + (max_chosen_to' - max_chosen_to) = max_chosen_to'" by auto
    have "[0..<max_chosen_to'] = [0 ..< max_chosen_to + (max_chosen_to' - max_chosen_to)]" by (simp add: eq)
    also have "... = [0..<max_chosen_to] @ [max_chosen_to..<max_chosen_to + (max_chosen_to' - max_chosen_to)]"
      by (intro upt_add_eq_append, simp)
    also have "... = [0..<max_chosen_to] @ [max_chosen_to..<max_chosen_to']" by (simp add: eq)
    finally have upt': "[0..<max_chosen_to'] = ..." .

    moreover have "map value_chosen' [0..<max_chosen_to] = map value_chosen [0..<max_chosen_to]"
    proof (intro map_ext impI sym [OF value_chosen'_eq], simp)
      fix i assume "i < max_chosen_to"
      with chosen_to_max show "some_chosen i" by (simp add: chosen_to_def)
    qed

    ultimately obtain vs where vs: "map value_chosen' [0..<max_chosen_to']
      = map value_chosen [0..<max_chosen_to] @ vs" by auto

    show "i_max \<le> i_max'"
      by (unfold i_max_def i_max'_def e.sequence_to_def epochs_to'_def vs, intro e.append_only_length_mono)
  qed

  have epochs_eq_i_max: "\<And>i. i < i_max \<Longrightarrow> epoch i = epoch' i"
  proof -
    have epochs_to_max_eq: "epochs_to max_chosen_to = epochs_to' max_chosen_to"
    proof (unfold e.sequence_to_def epochs_to'_def, intro cong [OF refl, where f = epochs_seq] map_ext impI value_chosen'_eq, simp)
      fix i
      assume "i < max_chosen_to"
      with chosen_to_max show "some_chosen i"
        by (auto simp add: chosen_to_def)
    qed

    fix i
    assume "i < i_max"
    hence lt: "i < length (epochs_to max_chosen_to)" by (simp add: i_max_def)

    from e.element_at [OF lt] epochs_to_max_eq
    have "epoch i = epochs_to' max_chosen_to ! i" by simp

    moreover
    have "epoch' i = ..."
    proof (unfold epoch'_def epochs_to'_def, intro fixedSeqL.element_at, intro_locales)
      from lt epochs_to_max_eq have "i < length (epochs_to' max_chosen_to)" by simp
      thus "i < length (epochs_seq (map value_chosen' [0..<max_chosen_to]))" by (simp add: epochs_to'_def)
    qed

    ultimately show "?thesis i" by simp
  qed

  have "\<And>e. e < e_max \<Longrightarrow> quorum e  = quorum' e"
  proof -
    have quorums_to_max_eq: "quorums_to max_chosen_to = quorums_to' max_chosen_to"
    proof (unfold q.sequence_to_def quorums_to'_def, intro cong [OF refl, where f = quorums_seq] map_ext impI value_chosen'_eq, simp)
      fix i
      assume "i < max_chosen_to"
      with chosen_to_max show "some_chosen i"
        by (auto simp add: chosen_to_def)
    qed

    fix e
    assume "e < e_max"
    hence lt: "e < length (quorums_to max_chosen_to)" by (simp add: e_max_def)

    from q.element_at [OF lt] quorums_to_max_eq
    have "quorum e = quorums_to' max_chosen_to ! e" by simp

    moreover
    have "quorum' e = ..."
    proof (unfold quorum'_def quorums_to'_def, intro fixedSeqL.element_at, intro_locales)
      from lt quorums_to_max_eq have "e < length (quorums_to' max_chosen_to)" by simp
      thus "e < length (quorums_seq (map value_chosen' [0..<max_chosen_to]))" by (simp add: quorums_to'_def)
    qed

    ultimately show "?thesis e" by simp
  qed

  hence read_quorums_eq_e_max:  "\<And>e. e < e_max \<Longrightarrow> read_quorum e  = read_quorum'  e"
    and write_quorums_eq_e_max: "\<And>e. e < e_max \<Longrightarrow> write_quorum e = write_quorum' e"
    by (auto simp add: read_quorum_def read_quorum'_def write_quorum_def write_quorum'_def)

  have epoch'_mono: "\<And>i1 i2. i1 \<le> i2 \<Longrightarrow> i2 < i_max' \<Longrightarrow> epoch' i1 \<le> epoch' i2"
    by (unfold epoch'_def epochs_to'_def, intro topologyL.epoch_mono [OF topologyL], auto simp add: i_max'_def epochs_to'_def)

  show ?thesis
  apply (unfold isConsistent_def)
  apply unfold_locales
  apply (fold value_chosen'_def some_chosen'_def s)
  apply (fold s max_chosen_to'_def i_max'_def read_quorum'_def promised_def forced_def)
  apply (fold s write_quorum'_def)
  proof -
    fix i
    from all_proposed_finite show "finite {(i,p). proposed i p}" .
  next
    fix i j a p0 p1
    assume "multi_promised j a p0" "accepted i a p1" "j \<le> i"
    with multi_promised show "p0 \<preceq> p1" by metis
  next
    fix i a p0 p1
    assume "promised_free i a p0" "accepted i a p1"
    with promised_free show "p0 \<preceq> p1" by metis
  next
    fix i a p0 p1
    assume "promised_prev i a p0 p1"
    thus "accepted i a p1" "p1 \<prec> p0"
      by (metis promised_prev_accepted, metis promised_prev_prev)
  next
    fix i a p0 p1 p2
    assume "promised_prev i a p0 p1" "accepted i a p2" "p2 \<prec> p0"
    thus "p2 \<preceq> p1" by (metis promised_prev_max)
  next
    fix i a p
    assume "accepted i a p" thus "proposed i p" by (metis accepts_proposed)
  next
    fix i assume "some_chosen' i"
    hence "some_chosen i \<or> i = i0" by (auto simp add: some_chosen'_def some_chosen_def chosen'_def)
    with some_chosen_i_max i0_max have "i < i_max" by auto
    also note i_max_le
    finally show "i < i_max'" .
  next
    note i_max_positive also note i_max_le
    finally show "0 < i_max'" .
  next
    fix i p
    assume proposed: "proposed i p"
    from proposed_quorum [OF this]
    obtain S where S_quorum: "read_quorum (prop_topology_version p) S"
               and S_promised: "\<forall>a\<in>S. promised i a p"
               and S_value: "(forced i p S = {} \<or> value_proposed i p = value_proposed i (max_of (forced i p S)))"
               by auto
    show "\<exists>S. read_quorum' (prop_topology_version p) S \<and> (\<forall>a\<in>S. promised i a p) \<and> (forced i p S = {} \<or> value_proposed i p = value_proposed i (max_of (forced i p S)))"
    proof (intro exI [of _ S] conjI S_promised S_value)

      have "read_quorum (prop_topology_version p) = read_quorum' (prop_topology_version p)"
      proof (intro read_quorums_eq_e_max)
        from S_quorum S_promised obtain a where "promised i a p" by (auto simp add: read_quorum_def)
        hence "prop_topology_version p \<le> epoch (instance_with_epoch i)" by (metis promised_topology)

        also have "... < e_max"
          by (intro epoch_defined_i_max instance_with_epoch_lt)

        finally show "prop_topology_version p < e_max" .
      qed

      with S_quorum show "read_quorum' (prop_topology_version p) S" by simp
    qed
  next
    fix i a p
    assume promised: "promised i a p"
    note promised_topology [OF this]
    also have "epoch (instance_with_epoch i) = epoch' (instance_with_epoch i)"
      by (intro epochs_eq_i_max instance_with_epoch_lt)
    also have "... \<le> epoch' (instance_with_epoch' i)"
    proof (intro epoch'_mono)
      show "instance_with_epoch i \<le> instance_with_epoch' i"
      proof (unfold instance_with_epoch'_def, intro Greatest_le_nat allI impI conjI instance_with_epoch_le)
        note instance_with_epoch_lt also note i_max_le
        finally show "instance_with_epoch i < i_max'" .
      qed auto

      have "instance_with_epoch' i \<le> i \<and> instance_with_epoch' i < i_max'"
      proof (unfold instance_with_epoch'_def, intro GreatestI_nat conjI)
        note i_max_positive also note i_max_le finally show "0 < i_max'" .
      qed auto
      thus "instance_with_epoch' i < i_max'" by simp
    qed
    finally show "prop_topology_version p \<le> epoch' (instance_with_epoch' i)" .
  next
    fix i p
    assume "chosen' i p"
    hence c: "(i,p) = (i0,p0) \<or> chosen i p" by (auto simp add: chosen'_def)

    from c have lt: "i < i_max"
    proof (elim disjE)
      assume "(i, p) = (i0, p0)" with i0_max show ?thesis by simp
    next
      assume "chosen i p"
      thus ?thesis by (intro some_chosen_i_max, auto simp add: some_chosen_def)
    qed

    have epochs_eq: "epoch' i = epoch i"
      by (intro sym [OF epochs_eq_i_max] lt)

    have quorums_eq: "write_quorum' (epoch i) = write_quorum (epoch i)"
      by (intro sym [OF write_quorums_eq_e_max] epoch_defined_i_max lt)

    from c have "(\<exists>S. write_quorum (epoch i) S \<and> (\<forall>a\<in>S. accepted i a p)) \<and> (epoch i \<le> Suc (prop_topology_version p))"
    proof (elim disjE)
      assume "chosen i p"
      from chosen_quorum [OF this] chosen_topology [OF this] show ?thesis by simp
    next
      assume "(i, p) = (i0, p0)"
      with quorum_S accepted_S topo_version show ?thesis by auto
    qed

    thus "\<exists>S. write_quorum' (epoch' i) S \<and> (\<forall>a\<in>S. accepted i a p)"
          "epoch' i \<le> Suc (prop_topology_version p)"
          by (unfold epochs_eq quorums_eq, simp_all)
  qed simp
qed

lemma (in paxosL) multiPaxos_add_multi_promise_:
  fixes p0

  assumes "\<And>p j. i0 \<le> j \<Longrightarrow> \<not>accepted j a0 p"
          "prop_topology_version p0 \<le> epoch (instance_with_epoch i0)"

  defines "multi_promised' == (\<lambda> i a p. (i, a, p) = (i0, a0, p0) \<or> multi_promised i a p)"
  shows "isConsistent multi_promised' promised_free promised_prev proposed accepted chosen value_proposed"
using assms
apply (unfold multi_promised'_def)
  by (rule multiPaxos_add_multi_promise)

lemma (in paxosL) multiPaxos_add_promise_free_:
  fixes p0

  assumes "\<And>p. \<not>accepted i0 a0 p"
          "prop_topology_version p0 \<le> epoch (instance_with_epoch i0)"

  defines "promised_free' == (\<lambda> i a p. (i, a, p) = (i0, a0, p0) \<or> promised_free i a p)"
  shows "isConsistent multi_promised promised_free' promised_prev proposed accepted chosen value_proposed"
using assms
apply (unfold promised_free'_def)
  by (rule multiPaxos_add_promise_free)

lemma (in paxosL) multiPaxos_add_promise_prev_:

  assumes "accepted i0 a0 p'0"
          "\<And>p2. accepted i0 a0 p2 \<Longrightarrow> p2 \<preceq> p'0"
          "p'0 \<prec> p0"
          "prop_topology_version p0 \<le> epoch (instance_with_epoch i0)"

  defines "promised_prev' == (\<lambda> i a p p'. (i,a,p,p') = (i0, a0, p0, p'0) \<or> promised_prev i a p p')"
  shows "isConsistent multi_promised promised_free promised_prev' proposed accepted chosen value_proposed"
using assms
apply (unfold promised_prev'_def)
  by (rule multiPaxos_add_promise_prev)

lemma (in paxosL) multiPaxos_add_proposal_:

  assumes "read_quorum (prop_topology_version p0) S"
          "\<And>a. a \<in> S \<Longrightarrow> promised i0 a p0"
          "\<not> proposed i0 p0"

  fixes free_value
  defines "value_proposed' == \<lambda> i p. if (i, p) = (i0, p0) then (if forced i0 p0 S = {} then free_value else value_proposed i0 (max_of (forced i0 p0 S))) else value_proposed i p"
  defines "proposed' == \<lambda> i p. (i, p) = (i0, p0) \<or> proposed i p"
  shows "isConsistent multi_promised promised_free promised_prev proposed' accepted chosen value_proposed'"
using assms
apply (unfold proposed'_def value_proposed'_def)
  by (rule multiPaxos_add_proposal)

lemma (in paxosL) multiPaxos_add_accepted_:

  assumes "proposed i0 p0"
          "\<And>j p1.    multi_promised j a0 p1    \<Longrightarrow> j \<le> i0 \<Longrightarrow> p1 \<preceq> p0"
          "\<And>  p1.    promised_free i0 a0 p1               \<Longrightarrow> p1 \<preceq> p0"
          "\<And>  p1 p2. promised_prev i0 a0 p1 p2            \<Longrightarrow> p1 \<preceq> p0"

  defines "accepted' == (\<lambda>i a p. (i,a,p) = (i0, a0, p0) \<or> accepted i a p)"
  shows "isConsistent multi_promised promised_free promised_prev proposed accepted' chosen value_proposed"
using assms
apply (unfold accepted'_def)
  by (rule multiPaxos_add_accepted)

lemma (in paxosL) multiPaxos_add_choice_:

  assumes "write_quorum (epoch i0) S"
          "\<And>a. a \<in> S \<Longrightarrow> accepted i0 a p0"
          "epoch i0 \<le> Suc (prop_topology_version p0)"
          "i0 < i_max"

  defines "chosen' == (\<lambda>i p. (i, p) = (i0, p0) \<or> chosen i p)"
  shows "isConsistent multi_promised promised_free promised_prev proposed accepted chosen' value_proposed"
using assms
apply (unfold chosen'_def)
  by (rule multiPaxos_add_choice)

end
