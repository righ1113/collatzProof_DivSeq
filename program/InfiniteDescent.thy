theory InfiniteDescent
imports Main
begin

theorem infinite_descent [simp]:
  "(\<forall>n::nat. P(n) \<longrightarrow> (\<exists>m::nat. m<n\<and>P(m))) \<longrightarrow> (\<forall>n::nat. \<not>P(n))"
    apply (metis ex_least_nat_le gr_implies_not0)
    done

theorem infinite_descent2 [simp]:
  "(\<forall>P::nat\<Rightarrow>bool. (\<forall>n::nat. P(n+1) \<longrightarrow> (\<exists>m::nat. m<(n+1)\<and>P(m))) \<longrightarrow> \<not>P(0) \<longrightarrow> (\<forall>n::nat. \<not>P(n)))"
    (* sledgehammer *)
    apply (smt discrete ex_least_nat_le ex_least_nat_less nat_less_le)
    done


end

