theory FixedSeq
  imports Main
begin

locale appendOnlyL =
  fixes sequence :: "'value list \<Rightarrow> 'x list"
  fixes property :: "'x \<Rightarrow> 'x \<Rightarrow> bool"
  assumes sequence_snoc_only: "\<exists> appended. sequence (vs @ [v]) = sequence vs @ appended"
  assumes property_reflexive: "x \<in> set (sequence vs) \<Longrightarrow> property x x"
  assumes property_adjacent: "Suc n < length (sequence vs) \<Longrightarrow> property (sequence vs ! n) (sequence vs ! Suc n)"

lemma (in appendOnlyL) sequence_append_only: "\<exists> appended. sequence (vs0 @ vs1) = sequence vs0 @ appended"
proof (induct vs1 rule: List.rev_induct)
  case (snoc v vs)
  then obtain appended1 where a1: "sequence (vs0 @ vs) = sequence vs0 @ appended1" by auto

  from sequence_snoc_only
  obtain appended2 where a2: "sequence ((vs0 @ vs) @ [v]) = sequence (vs0 @ vs) @ appended2"
    by blast

  from a1 a2 show ?case by simp
qed simp

lemma (in appendOnlyL) append_only_length_mono: "length (sequence vs0) \<le> length (sequence (vs0 @ vs1))"
proof -
  from sequence_append_only
  obtain appended where app: "sequence (vs0 @ vs1) = sequence vs0 @ appended" by auto
  thus ?thesis by auto
qed

lemma (in appendOnlyL) append_only_take:
  assumes n: "n \<le> length (sequence vs0)"
  shows "take n (sequence (vs0 @ vs1)) = take n (sequence vs0)"
proof -
  from sequence_append_only
  obtain appended where app: "sequence (vs0 @ vs1) = sequence vs0 @ appended" by auto

  have "take n (sequence (vs0 @ vs1)) = take n (sequence vs0) @ take (n - length (sequence vs0)) appended"
    by (metis app take_append)
  also from n have "... = take n (sequence vs0)" by simp
  finally show ?thesis .
qed

lemma (in appendOnlyL) append_only_initial:
  assumes n: "n \<le> length (sequence vs0)"
  assumes ex1: "\<exists> vs_new. vs1 = vs0 @ vs_new"
  assumes ex2: "\<exists> vs_new. vs2 = vs0 @ vs_new"
  shows "take n (sequence vs1) = take n (sequence vs2)"
proof -
  from ex1 obtain vs1' where vs1: "vs1 = vs0 @ vs1'" by auto
  from ex2 obtain vs2' where vs2: "vs2 = vs0 @ vs2'" by auto

  have "take n (sequence vs1) = take n (sequence vs0)"
    by (unfold vs1, simp add: append_only_take [OF n])
  also have "... = take n (sequence vs2)"
    by (unfold vs2, simp add: append_only_take [OF n])
  finally show ?thesis .
qed

locale fixedSeqL
  = appendOnlyL sequence property
  for sequence :: "'value list \<Rightarrow> 'x list"
    and property :: "'x \<Rightarrow> 'x \<Rightarrow> bool"
    +
    (* the infinite list of all values that will ever be chosen *)
  fixes all_values :: "nat \<Rightarrow> 'value"
    (* the first n values to be chosen defines a finite sequence *)
  fixes sequence_to :: "nat \<Rightarrow> 'x list"
  defines "sequence_to == \<lambda>n. sequence (map all_values [0..<n])"
    (* the nth element in the sequence, assuming it ever gets that long  *)
  fixes element_at :: "nat \<Rightarrow> 'x"
  defines "element_at == \<lambda>i. sequence_to (SOME n. i < length (sequence_to n)) ! i"
    (* whether the sequence ever gets long enough *)
  fixes valid_index :: "nat \<Rightarrow> bool"
  defines "valid_index == \<lambda>i. \<exists> n. i < length (sequence_to n)"

lemma (in fixedSeqL)
  assumes long_enough: "i \<le> length (sequence_to m)"
    and mn: "m \<le> n"
  shows take_le_sequence_to: "take i (sequence_to m) = take i (sequence_to n)"
proof -
  from mn
  have n_seq: "[0..<n] = [0..<m] @ [m..<n]"
  proof (induct n arbitrary: m)
    case (Suc n)
    hence "m \<le> n \<or> m = Suc n" by auto
    with Suc.hyps show ?case by auto
  qed simp

  have "take i (sequence_to n) = take i (sequence (map all_values [0..<m] @ map all_values [m..<n]))"
    by (simp add: sequence_to_def n_seq)
  also from long_enough have "... = take i (sequence_to m)"
    by (unfold sequence_to_def, intro append_only_take)
  finally show ?thesis ..
qed

lemma (in fixedSeqL)
  assumes mn: "m \<le> n"
  shows sequence_to_initial: "sequence_to m = take (length (sequence_to m)) (sequence_to n)"
proof -
  have "sequence_to m = take (length (sequence_to m)) (sequence_to m)"
    by (intro sym [OF take_all], simp)
  also have "... = take (length (sequence_to m)) (sequence_to n)"
    by (intro take_le_sequence_to mn, simp)
  finally show ?thesis .
qed

lemma (in fixedSeqL)
  assumes mn: "m \<le> n"
  shows length_sequence_to_mono: "length (sequence_to m) \<le> length (sequence_to n)"
proof -
  have "length (sequence_to m) = length (take (length (sequence_to m)) (sequence_to n))"
    by (intro cong [OF refl, where f = length] sequence_to_initial mn)
  also have "... = min (length (sequence_to n)) (length (sequence_to m))" by simp
  also have "... \<le> length (sequence_to n)" by simp
  finally show ?thesis .
qed

lemma (in fixedSeqL)
  assumes long_enough: "i < length (sequence_to n)"
  shows element_at: "element_at i = sequence_to n ! i"
proof (unfold element_at_def, intro someI2 [where Q = "\<lambda>m. sequence_to m ! i = sequence_to n ! i"])
  from long_enough show "i < length (sequence_to n)".
  hence inp1: "i+1 \<le> length (sequence_to n)" by simp
  fix m
  assume long_enough': "i < length (sequence_to m)"
  hence imp1: "i+1 \<le> length (sequence_to m)" by simp

  have "m \<le> n \<or> n \<le> m" by auto
  hence take_eq: "take (i+1) (sequence_to m) = take (i+1) (sequence_to n)"
  proof (elim disjE)
    assume "m \<le> n"
    from take_le_sequence_to [OF imp1 this] show ?thesis .
  next
    assume "n \<le> m"
    from take_le_sequence_to [OF inp1 this] show ?thesis by simp
  qed

  have "sequence_to m ! i = take (i+1) (sequence_to m) ! i"
    by (intro sym [OF nth_take], simp)
  also from take_eq have "... = take (i+1) (sequence_to n) ! i" by simp
  also have "... = sequence_to n ! i" by (intro nth_take, simp)
  finally show "sequence_to m ! i = sequence_to n ! i" .
qed

lemma (in fixedSeqL)
  assumes valid_index: "valid_index i"
  shows property_at_reflexive: "property (element_at i) (element_at i)"
proof -
  from valid_index obtain n where long_enough: "i < length (sequence_to n)"
    by (auto simp add: valid_index_def)

  show ?thesis
  proof (intro property_reflexive)

    have "element_at i = sequence_to n ! i"
      by (intro element_at long_enough)
    also from long_enough have "... \<in> set (sequence (map all_values [0..<n]))"
      by (unfold sequence_to_def, intro nth_mem)
    finally show "element_at i \<in> ..." .
  qed
qed

lemma (in fixedSeqL)
  assumes valid_index: "valid_index (Suc i)"
  shows property_at_Suc: "property (element_at i) (element_at (Suc i))"
proof -
  from valid_index obtain n where long_enough: "Suc i < length (sequence_to n)"
    by (auto simp add: valid_index_def)

  from long_enough have long_enough': "i < length (sequence_to n)" by simp

  from long_enough
  have p: "property (sequence_to n ! i) (sequence_to n ! Suc i)"
    by (unfold sequence_to_def, intro property_adjacent)
  thus ?thesis
    by (simp add: element_at [OF long_enough] element_at [OF long_enough'])
qed

end
