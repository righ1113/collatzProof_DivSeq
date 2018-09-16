theory InfiniteDescent
imports Main
begin


theorem infinite_descent [simp]:
  "\<forall>P. (\<forall>n. P n  \<longrightarrow> (\<exists>m. m<n \<and> P m)) \<longrightarrow> (\<forall>n::nat. \<not>P n)"
  (* sledgehammer *)
  apply (metis ex_least_nat_le gr_implies_not0)
  done

theorem infinite_descent2 [simp]:
  "\<forall>P. (\<forall>n. P(n+1) \<longrightarrow> (\<exists>m::nat. m<n+1 \<and> P m)) \<longrightarrow> \<not>P 0 \<longrightarrow> (\<forall>n::nat. \<not>P n)"
  (* sledgehammer *)
  apply (metis Suc_eq_plus1 Suc_leI ex_least_nat_less not_le)
  done


term "[]"
term "(#)"
term False
term fst
term "(@)"
term "-1"
value "add (Suc (Suc 0)) (Suc 0)"

primrec any :: "('a\<Rightarrow>bool) \<Rightarrow> 'a list \<Rightarrow> bool" where
  "any p [] = False" |
  "any p (x # xs) = (p x | any p xs)"

lemma any1 [simp]:
  "\<forall>P. any P (xs@ys) \<longrightarrow> (any P xs) | (any P ys)"
  apply (induction xs)
  apply simp
  apply simp
  done

end
