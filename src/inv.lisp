(in-package "ACL2")

;; ===================================================================
;;
;; A multiplicative implementation of modular inverse.
;;
;; ===================================================================

(include-book "quotient")

;; ===================================================================
;;
;; inv
;;
;; ===================================================================

(defun inv (d p)
  (declare (type (integer 1 *) d p)
	   (xargs :guard (inv-guard d p)
		  :measure (nfix d)))
  (let ((d (mbe :logic (nfix d) :exec d))
	(p (mbe :logic (nfix p) :exec p)))
    (if (or (<= d 1) (not (mbt (inv-guard d p)))) d
      (let ((q (quotient p d)))
	(int-mod (* q (inv (int-mod (* q d) p) p)) p)))))

(defthm natp-inv
  (implies
   (natp d)
   (natp (inv d p)))
  :rule-classes (:rewrite
		 (:forward-chaining :trigger-terms ((inv d p)))))

(defthm inv-works
  (implies
   (inv-guard d p)
   (equal (int-mod (* d (inv d p)) p) 1))
  :hints (("Goal" :in-theory (enable NONNEG-INT-GCD-DROP-INT-MOD)
	   :induct (inv d p))
	  (and stable-under-simplificationp
	       '(:in-theory (enable NATP-FROM-POSNATP)))))
