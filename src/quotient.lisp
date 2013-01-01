(in-package "ACL2")

;; ===================================================================
;;
;; A multiplicative implementation of modular inverse.
;;
;; ===================================================================

(include-book "aux")

;; ===================================================================
;;
;; function abbreviations
;;
;; ===================================================================

(defun ndiv (n d)
  (declare (type (integer 0 *) n)
	   (type (integer 1 *) d))
  (nonnegative-integer-quotient n d))

(defun nmod (n d)
  (declare (type (integer 0 *) n)
	   (type (integer 1 *) d))
  (nonneg-int-mod n d))

(defun ngcd (n d)
  (declare (type (integer 0 *) n)
	   (type (integer 0 *) d))
  (nonneg-int-gcd n d))

;; ===================================================================
;;
;; inv-guard: guard for the inv function
;;
;; ===================================================================

(defun inv-guard (d p)
  (declare (type t d p))
  (and
   (posnatp d)
   (pnunitp p)
   (< d p)
   (equal (nonneg-int-gcd d p) 1)))

(defthm inv-guard-implies
  (implies
   (inv-guard d p)
   (and
    (posnatp d)
    (pnunitp p)
    (< d p)
    (equal (nonneg-int-gcd d p) 1)))
  :rule-classes (:forward-chaining))

(defthm implies-inv-guard
  (implies
   (and
    (equal (nonneg-int-gcd d p) 1)
    (posnatp d)
    (pnunitp p)
    (< d p))
   (inv-guard d p))
  :rule-classes (:rewrite :forward-chaining))

(in-theory (disable inv-guard))

;; ===================================================================
;;
;; quotient-rec-guard: guard for quotient-rec
;;
;; ===================================================================

(defun quotient-rec-guard (n d p)
  (declare (type t n d p))
  (and (inv-guard d p)
       (< 1 d)
       (integerp n)
       (<= p n)
       (equal (nmod n p) 0)
       (<= (ndiv n p) (ideal-k d p))
       ))

(defun quotient-guard (p d)
  (declare (type t d p))
  (and (inv-guard d p)
       (< 1 d)))

(defthm quotient-guard-implies
  (implies
   (quotient-guard p d)
   (and (inv-guard d p)
	(< 1 d)))
  :rule-classes (:forward-chaining))

(defthm implies-quotient-guard
  (implies
   (and
    (inv-guard d p)
    (< 1 d))
   (quotient-guard p d))
  :rule-classes (:rewrite :forward-chaining))

(defthm quotient-guard-implies-quotient-rec-guard
  (implies
   (quotient-guard p d)
   (quotient-rec-guard p d p))
  :rule-classes (:forward-chaining))

(in-theory (disable quotient-guard))

;; ===================================================================
;;
;; quotient-rec-measure
;;
;; ===================================================================

(defun quotient-rec-measure (n d p)
  (abs (- (ideal-k d p) (ndiv n p))))

(defthm natp-quotient-rec-measure
  (natp (quotient-rec-measure n d p))
  :rule-classes (:type-prescription))

(defthm quotient-rec-guard-implies-quotient-measure-decreases
  (implies
   (and
    (quotient-rec-guard n d p)
    (not (equal (ngcd (+ (ndiv n d) 1) p) 1)))
   (< (quotient-rec-measure (+ n p) d p)
      (quotient-rec-measure n d p)))
  :hints (("Goal" ;;:in-theory (enable inv-guard posnatp pnunitp natp)
	   :do-not-induct t)))

(in-theory (disable quotient-rec-measure))

;; ===================================================================
;;
;; quotient-rec
;;
;; ===================================================================

(defun quotient-rec (n d p)
  (declare (type (integer 1 *) n d p)
	   (xargs :measure (quotient-rec-measure n d p)
		  :guard   (quotient-rec-guard n d p)
		  :guard-hints (("Goal" :in-theory (enable quotient-rec-guard)))))
  (if (not (mbt (quotient-rec-guard n d p))) 1
    (let ((q (ndiv n d)))
      (if (= (ngcd q p) 1) (- p q)
	(let ((q (1+ q)))
	  (if (= (ngcd q p) 1) q
	    (quotient-rec (+ n p) d p)))))))

(defthm integerp-quotient-rec
  (integerp (quotient-rec n d p))
  :rule-classes (:rewrite :type-prescription
			  (:forward-chaining :trigger-terms ((quotient-rec n d p)))))

(defthm posnatp-quotient-rec
  (implies
   (quotient-rec-guard n d p)
   (posnatp (quotient-rec n d p)))
  :hints (("Goal" :in-theory (enable quotient-rec-guard)))
  :rule-classes (:rewrite :type-prescription
			  (:forward-chaining :trigger-terms ((quotient-rec n d p)))))

(defthm quotient-rec-product-upper-bound
  (implies
   (quotient-rec-guard n d p)
   (< (int-mod (* d (quotient-rec n d p)) p)
      d))
  :rule-classes (:rewrite
		 :linear
		 (:forward-chaining :trigger-terms ((quotient-rec n d p)))))

(defthm quotient-rec-product-lower-bound
  (implies
   (quotient-rec-guard n d p)
   (< 0 (int-mod (* d (quotient-rec n d p)) p)))
  :rule-classes (:linear
		 :rewrite
		 (:forward-chaining :trigger-terms ((quotient-rec n d p))))
  :hints (("Goal" :in-theory 
	   (enable 
	    NONNEG-INT-MOD-AS-INT-MOD
	    equal-int-mod-to-int-mod-equivp
	    NONNEGATIVE-INTEGER-QUOTIENT-TO-NONNEG-INT-MOD))))


(defthm quotient-rec-is-relatively-prime
  (implies
   (quotient-rec-guard n d p)
   (equal (nonneg-int-gcd (quotient-rec n d p) p) 1)))

(in-theory (disable quotient-rec-guard))

;; ===================================================================
;;
;; quotient
;;
;; ===================================================================

(defun quotient-exec (p d)
  (declare (xargs :guard (quotient-guard p d)))
  (quotient-rec p d p))

(encapsulate
    (
     (quotient (p d) t :guard (quotient-guard p d))
     )
  
  (local
   (defun quotient (p d)
     (declare (xargs :guard (quotient-guard p d)))
     (quotient-exec p d)))
  
  (defthm integerp-quotient
    (integerp (quotient p d))
    :rule-classes (:rewrite
		   (:forward-chaining
		    :trigger-terms ((quotient p d)))))
  
  (defthm posnatp-quotient
    (implies
     (quotient-guard p d)
     (posnatp (quotient p d)))
    :rule-classes (:rewrite
		   (:forward-chaining
		    :trigger-terms ((quotient p d)))))
  
  (defthm quotient-product-upper-bound
    (implies
     (quotient-guard p d)
     (< (int-mod (* d (quotient p d)) p)
	d))
    :rule-classes (:rewrite :linear))

  (defthm quotient-product-lower-bound
    (implies
     (quotient-guard p d)
     (< 0 (int-mod (* d (quotient p d)) p)))
    :rule-classes (:linear :rewrite))

  (defthm quotient-is-relatively-prime
    (implies
     (quotient-guard p d)
     (equal (nonneg-int-gcd (quotient p d) p) 1)))

  )
