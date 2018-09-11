theory InfiniteDescent
imports Main
begin

theorem infinite_descent [simp]:
  "(\<forall>n. P(n) \<longrightarrow> (\<exists>m. m<n\<and>P(m))) \<longrightarrow> (\<forall>n::nat. \<not>P(n))"
    apply (metis ex_least_nat_le gr_implies_not0)
    done

theorem infinite_descent2 [simp]:
  "(\<forall>P. (\<forall>n. P(n+1) \<longrightarrow> (\<exists>m::nat. m<n+1 \<and> P(m))) \<longrightarrow> \<not>P(0) \<longrightarrow> (\<forall>n::nat. \<not>P(n)))"
    (* sledgehammer *)
    apply (metis Suc_eq_plus1 Suc_leI ex_least_nat_less not_le)
    done


end

