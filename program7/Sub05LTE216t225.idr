module Sub05LTE216t225

import ProofColDivSeqPostulate

%default total


-- 6(36t+37)+3 --FE[5,0,-4]--> 6(8t+7)+3
export
lte216t225 : (m : Nat) -> LTE (S (S (S (S (S (S (S (S (m+m+m+m)+(m+m+m+m)))))))))
  (S (((S (S ((S (S (m+m+m)))+(S (S (m+m+m))))))+(S (S ((S (S (m+m+m)))+(S (S (m+m+m))))))) + ((S (S ((S (S (m+m+m)))+(S (S (m+m+m))))))+(S (S ((S (S (m+m+m)))+(S (S (m+m+m))))))) + ((S (S ((S (S (m+m+m)))+(S (S (m+m+m))))))+(S (S ((S (S (m+m+m)))+(S (S (m+m+m)))))))))
lte216t225 Z     = (lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc) LTEZero
lte216t225 (S m) =
  let lemma = lte216t225 m in

  rewrite (sym (plusSuccRightSucc m m)) in

  rewrite (sym (plusSuccRightSucc (plus m m) m)) in

  rewrite (sym (plusSuccRightSucc (plus (plus m m) m) m)) in

  rewrite (sym (plusSuccRightSucc (plus (plus (plus m m) m) m)
                                  (S (S (S (plus (plus (plus m m) m) m)))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus m m) m) m)
                                     (S (S (plus (plus (plus m m) m) m))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus m m) m) m)
                                        (S (plus (plus (plus m m) m) m)))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus m m) m) m)
                                           (plus (plus (plus m m) m) m))) in

  rewrite (sym (plusSuccRightSucc (plus (plus m m) m) (S (S (S (S (plus (plus m m) m))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus m m) m)    (S (S (S (plus (plus m m) m)))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus m m) m)       (S (S (plus (plus m m) m))))) in

  rewrite (sym (plusSuccRightSucc (plus (plus (plus m m) m) (S (S (plus (plus m m) m))))
                  (S (S (S (S (S (S (S (S (S (plus (plus (plus m m) m) (S (S (plus (plus m m) m))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus m m) m) (S (S (plus (plus m m) m))))
                     (S (S (S (S (S (S (S (S (plus (plus (plus m m) m) (S (S (plus (plus m m) m)))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus m m) m) (S (S (plus (plus m m) m))))
                        (S (S (S (S (S (S (S (plus (plus (plus m m) m) (S (S (plus (plus m m) m))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus m m) m) (S (S (plus (plus m m) m))))
                           (S (S (S (S (S (S (plus (plus (plus m m) m) (S (S (plus (plus m m) m)))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus m m) m) (S (S (plus (plus m m) m))))
                              (S (S (S (S (S (plus (plus (plus m m) m) (S (S (plus (plus m m) m))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus m m) m) (S (S (plus (plus m m) m))))
                                 (S (S (S (S (plus (plus (plus m m) m) (S (S (plus (plus m m) m)))))))))) in

  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (S (S (plus (plus m m) m))))
                        (S (S (S (S (plus (plus (plus m m) m) (S (S (plus (plus m m) m)))))))))
                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                              (S (S (plus (plus m m) m))))
                                                                        (S (S (S (S (plus (plus (plus m m) m)
                                                                                          (S (S (plus (plus m m)
                                m)))))))))))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (S (S (plus (plus m m) m))))
                        (S (S (S (S (plus (plus (plus m m) m) (S (S (plus (plus m m) m)))))))))
                     (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                              (S (S (plus (plus m m) m))))
                                                                        (S (S (S (S (plus (plus (plus m m) m)
                                                                                          (S (S (plus (plus m m)
                                m))))))))))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (S (S (plus (plus m m) m))))
                        (S (S (S (S (plus (plus (plus m m) m) (S (S (plus (plus m m) m)))))))))
                        (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                              (S (S (plus (plus m m) m))))
                                                                        (S (S (S (S (plus (plus (plus m m) m)
                                                                                          (S (S (plus (plus m m)
                                m)))))))))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (S (S (plus (plus m m) m))))
                        (S (S (S (S (plus (plus (plus m m) m) (S (S (plus (plus m m) m)))))))))
                           (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                              (S (S (plus (plus m m) m))))
                                                                        (S (S (S (S (plus (plus (plus m m) m)
                                                                                          (S (S (plus (plus m m)
                                m))))))))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (S (S (plus (plus m m) m))))
                        (S (S (S (S (plus (plus (plus m m) m) (S (S (plus (plus m m) m)))))))))
                              (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                              (S (S (plus (plus m m) m))))
                                                                        (S (S (S (S (plus (plus (plus m m) m)
                                                                                          (S (S (plus (plus m m)
                                m)))))))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (S (S (plus (plus m m) m))))
                        (S (S (S (S (plus (plus (plus m m) m) (S (S (plus (plus m m) m)))))))))
                                 (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                              (S (S (plus (plus m m) m))))
                                                                        (S (S (S (S (plus (plus (plus m m) m)
                                                                                          (S (S (plus (plus m m)
                                m))))))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (S (S (plus (plus m m) m))))
                        (S (S (S (S (plus (plus (plus m m) m) (S (S (plus (plus m m) m)))))))))
                                    (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                              (S (S (plus (plus m m) m))))
                                                                        (S (S (S (S (plus (plus (plus m m) m)
                                                                                          (S (S (plus (plus m m)
                                m)))))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (S (S (plus (plus m m) m))))
                        (S (S (S (S (plus (plus (plus m m) m) (S (S (plus (plus m m) m)))))))))
                                       (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                              (S (S (plus (plus m m) m))))
                                                                        (S (S (S (S (plus (plus (plus m m) m)
                                                                                          (S (S (plus (plus m m)
                                m))))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (S (S (plus (plus m m) m))))
                        (S (S (S (S (plus (plus (plus m m) m) (S (S (plus (plus m m) m)))))))))
                                          (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                              (S (S (plus (plus m m) m))))
                                                                        (S (S (S (S (plus (plus (plus m m) m)
                                                                                          (S (S (plus (plus m m)
                                m)))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (S (S (plus (plus m m) m))))
                        (S (S (S (S (plus (plus (plus m m) m) (S (S (plus (plus m m) m)))))))))
                                             (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                              (S (S (plus (plus m m) m))))
                                                                        (S (S (S (S (plus (plus (plus m m) m)
                                                                                          (S (S (plus (plus m m)
                                m))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (S (S (plus (plus m m) m))))
                        (S (S (S (S (plus (plus (plus m m) m) (S (S (plus (plus m m) m)))))))))
                                                (S (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                              (S (S (plus (plus m m) m))))
                                                                        (S (S (S (S (plus (plus (plus m m) m)
                                                                                          (S (S (plus (plus m m)
                                m)))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus m m) m) (S (S (plus (plus m m) m))))
                        (S (S (S (S (plus (plus (plus m m) m) (S (S (plus (plus m m) m)))))))))
                                                   (S (S (S (S (plus (plus (plus (plus m m) m)
                                                                              (S (S (plus (plus m m) m))))
                                                                        (S (S (S (S (plus (plus (plus m m) m)
                                                                                          (S (S (plus (plus m m)
                                m))))))))))))))) in

  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                    (S (S (plus (plus m m) m))))
                              (S (S (S (S (plus (plus (plus m m) m)
                                                (S (S (plus (plus m m) m)))))))))  
                        (S (S (S (S (plus (plus (plus (plus m m) m)
                                                (S (S (plus (plus m m) m))))       
                                          (S (S (S (S (plus (plus (plus m m) m)    
                                                            (S (S (plus (plus m m) 
                                                                        m))))))))))))))
                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                           (S (S (plus (plus m m) m))))
                           (S (S (S (S (plus (plus (plus m m) m)
                           (S (S (plus (plus m m)
                   m)))))))))))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                    (S (S (plus (plus m m) m))))
                              (S (S (S (S (plus (plus (plus m m) m)
                                                (S (S (plus (plus m m) m)))))))))  
                        (S (S (S (S (plus (plus (plus (plus m m) m)
                                                (S (S (plus (plus m m) m))))       
                                          (S (S (S (S (plus (plus (plus m m) m)    
                                                            (S (S (plus (plus m m) 
                                                                        m))))))))))))))
                     (S (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                           (S (S (plus (plus m m) m))))
                           (S (S (S (S (plus (plus (plus m m) m)
                           (S (S (plus (plus m m)
                   m))))))))))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                    (S (S (plus (plus m m) m))))
                              (S (S (S (S (plus (plus (plus m m) m)
                                                (S (S (plus (plus m m) m)))))))))  
                        (S (S (S (S (plus (plus (plus (plus m m) m)
                                                (S (S (plus (plus m m) m))))       
                                          (S (S (S (S (plus (plus (plus m m) m)    
                                                            (S (S (plus (plus m m) 
                                                                        m))))))))))))))
                        (S (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                           (S (S (plus (plus m m) m))))
                           (S (S (S (S (plus (plus (plus m m) m)
                           (S (S (plus (plus m m)
                   m)))))))))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                    (S (S (plus (plus m m) m))))
                              (S (S (S (S (plus (plus (plus m m) m)
                                                (S (S (plus (plus m m) m)))))))))
                        (S (S (S (S (plus (plus (plus (plus m m) m)
                                                (S (S (plus (plus m m) m))))
                                          (S (S (S (S (plus (plus (plus m m) m)
                                                            (S (S (plus (plus m m)
                                                                        m))))))))))))))
                           (S (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                           (S (S (plus (plus m m) m))))
                           (S (S (S (S (plus (plus (plus m m) m)
                           (S (S (plus (plus m m)
                   m))))))))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                    (S (S (plus (plus m m) m))))
                              (S (S (S (S (plus (plus (plus m m) m)
                                                (S (S (plus (plus m m) m)))))))))  
                        (S (S (S (S (plus (plus (plus (plus m m) m)
                                                (S (S (plus (plus m m) m))))       
                                          (S (S (S (S (plus (plus (plus m m) m)    
                                                            (S (S (plus (plus m m) 
                                                                        m))))))))))))))
                              (S (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                           (S (S (plus (plus m m) m))))
                           (S (S (S (S (plus (plus (plus m m) m)
                           (S (S (plus (plus m m)
                   m)))))))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                    (S (S (plus (plus m m) m))))
                              (S (S (S (S (plus (plus (plus m m) m)
                                                (S (S (plus (plus m m) m)))))))))  
                        (S (S (S (S (plus (plus (plus (plus m m) m)
                                                (S (S (plus (plus m m) m))))       
                                          (S (S (S (S (plus (plus (plus m m) m)    
                                                            (S (S (plus (plus m m) 
                                                                        m))))))))))))))
                                 (S (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                           (S (S (plus (plus m m) m))))
                           (S (S (S (S (plus (plus (plus m m) m)
                           (S (S (plus (plus m m)
                   m))))))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                    (S (S (plus (plus m m) m))))
                              (S (S (S (S (plus (plus (plus m m) m)
                                                (S (S (plus (plus m m) m)))))))))  
                        (S (S (S (S (plus (plus (plus (plus m m) m)
                                                (S (S (plus (plus m m) m))))       
                                          (S (S (S (S (plus (plus (plus m m) m)    
                                                            (S (S (plus (plus m m) 
                                                                        m))))))))))))))
                                    (S (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                           (S (S (plus (plus m m) m))))
                           (S (S (S (S (plus (plus (plus m m) m)
                           (S (S (plus (plus m m)
                   m)))))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                    (S (S (plus (plus m m) m))))
                              (S (S (S (S (plus (plus (plus m m) m)
                                                (S (S (plus (plus m m) m)))))))))  
                        (S (S (S (S (plus (plus (plus (plus m m) m)
                                                (S (S (plus (plus m m) m))))       
                                          (S (S (S (S (plus (plus (plus m m) m)    
                                                            (S (S (plus (plus m m) 
                                                                        m))))))))))))))
                                       (S (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                           (S (S (plus (plus m m) m))))
                           (S (S (S (S (plus (plus (plus m m) m)
                           (S (S (plus (plus m m)
                   m))))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                    (S (S (plus (plus m m) m))))
                              (S (S (S (S (plus (plus (plus m m) m)
                                                (S (S (plus (plus m m) m)))))))))  
                        (S (S (S (S (plus (plus (plus (plus m m) m)
                                                (S (S (plus (plus m m) m))))       
                                          (S (S (S (S (plus (plus (plus m m) m)    
                                                            (S (S (plus (plus m m) 
                                                                        m))))))))))))))
                                          (S (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                           (S (S (plus (plus m m) m))))
                           (S (S (S (S (plus (plus (plus m m) m)
                           (S (S (plus (plus m m)
                   m)))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                    (S (S (plus (plus m m) m))))
                              (S (S (S (S (plus (plus (plus m m) m)
                                                (S (S (plus (plus m m) m)))))))))  
                        (S (S (S (S (plus (plus (plus (plus m m) m)
                                                (S (S (plus (plus m m) m))))       
                                          (S (S (S (S (plus (plus (plus m m) m)    
                                                            (S (S (plus (plus m m) 
                                                                        m))))))))))))))
                                             (S (S (S (S (S (S (plus (plus (plus (plus m m) m)
                           (S (S (plus (plus m m) m))))
                           (S (S (S (S (plus (plus (plus m m) m)
                           (S (S (plus (plus m m)
                   m))))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                    (S (S (plus (plus m m) m))))
                              (S (S (S (S (plus (plus (plus m m) m)
                                                (S (S (plus (plus m m) m)))))))))  
                        (S (S (S (S (plus (plus (plus (plus m m) m)
                                                (S (S (plus (plus m m) m))))       
                                          (S (S (S (S (plus (plus (plus m m) m)    
                                                            (S (S (plus (plus m m) 
                                                                        m))))))))))))))
                                                (S (S (S (S (S (plus (plus (plus (plus m m) m)
                           (S (S (plus (plus m m) m))))
                           (S (S (S (S (plus (plus (plus m m) m)
                           (S (S (plus (plus m m)
                   m)))))))))))))))) in
  rewrite (sym (plusSuccRightSucc (plus (plus (plus (plus (plus m m) m)
                                    (S (S (plus (plus m m) m))))
                              (S (S (S (S (plus (plus (plus m m) m)
                                                (S (S (plus (plus m m) m)))))))))  
                        (S (S (S (S (plus (plus (plus (plus m m) m)
                                                (S (S (plus (plus m m) m))))       
                                          (S (S (S (S (plus (plus (plus m m) m)    
                                                            (S (S (plus (plus m m) 
                                                                        m))))))))))))))
                                                   (S (S (S (S (plus (plus (plus (plus m m) m)
                           (S (S (plus (plus m m) m))))
                           (S (S (S (S (plus (plus (plus m m) m)
                           (S (S (plus (plus m m)
                   m))))))))))))))) in

    (lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . lteSuccRight . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc . LTESucc) lemma



