theory InfiniteDescent
imports Main
begin


theorem infiniteDescent0 []: 
  "[| P 0; !!n. n>0 ==> \<not> P n ==> (\<exists>m::nat. m < n \<and> \<not>P m) |] ==> P n"
  (* sledgehammer *)
  using infinite_descent0
  apply blast
  done


end
