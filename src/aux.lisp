(in-package "ACL2")

;;(INCLUDE-BOOK "misc/beta-reduce" :DIR :SYSTEM)
(include-book "coi/util/skip-rewrite" :dir :system)
(include-book "prime-fac")
(include-book "arithmetic-5/top" :dir :system)

(in-theory 
 (disable 
  POS::PRIME-DIVISOR-OF-PRODUCT-DIVIDES-FACTOR
  POS::NONNEG-INT-GCD=>NONNEG-INT-MOD
  POS::PRIMEP=>NONNEG-INT-GCD=1
  POS::PRIMEP
  POS::DIVIDESP
  ))

;; ===================================================================
;; useful types
;; ===================================================================

(defthm natp-implies
  (implies
   (natp x)
   (and (integerp x)
	(<= 0 x)))
  :rule-classes (:forward-chaining))

(defthm implies-natp
  (implies
   (and (integerp x)
	(<= 0 x))
   (natp x))
  :rule-classes (:rewrite :forward-chaining))

(in-theory (disable natp))

(defun posnatp (x)
  (declare (type t x))
  (and (integerp x)
       (< 0 x)))

(defthm not-posnatp-implies
  (implies
   (and
    (not (posnatp x))
    (integerp x))
   (not (< 0 x)))
  :rule-classes (:forward-chaining))

(defthm posnatp-implies
  (implies
   (posnatp x)
   (and (integerp x)
	(< 0 x)))
  :rule-classes (:forward-chaining))

(defthm implies-posnatp
  (implies
   (and (< 0 x)
	(integerp x))
   (posnatp x))
  :rule-classes (:rewrite :forward-chaining))

(in-theory (disable posnatp))

;; A positive non-unit integer
(defun pnunitp (x)
  (declare (type t x))
  (and (posnatp x)
       (< 1 x)))

(defthm pnunitp-implies
  (implies
   (pnunitp x)
   (and (posnatp x)
	(< 1 x)))
  :rule-classes (:forward-chaining))

(defthm implies-pnunitp
  (implies
   (and (< 1 x)
	(posnatp x))
   (pnunitp x))
  :rule-classes (:rewrite :forward-chaining))

(defthm not-pnunitp-implication
  (implies
   (not (pnunitp x))
   (or (not (posnatp x))
       (not (< 1 x))))
  :rule-classes (:forward-chaining))

(in-theory (disable pnunitp))

(defthm posnatp-implication-2
  (implies
   (posnatp x)
   (not (equal x 0)))
  :rule-classes (:forward-chaining))

(defthm pnuntip-implication-2
  (implies
   (pnunitp x)
   (not (equal x 1)))
  :rule-classes (:forward-chaining))

(defthm inequality-strengthens-natp
  (implies
   (and
    (natp x)
    (not (equal x 0)))
   (posnatp x))
  :rule-classes (:forward-chaining))

(defthm inequality-strengthens-posnatp
  (implies
   (and
    (posnatp x)
    (not (equal x 1)))
   (pnunitp x))
  :rule-classes (:forward-chaining))

(defthm bounded-integer-1
  (implies
   (and
    (not (< 1 p))
    (integerp p)
    (< 0 p))
   (equal p 1))
  :rule-classes (:forward-chaining))

;; ===================================================================
;; integer properties
;; ===================================================================

(defthm equal-product-zero
  (implies
   (and
    (integerp x)
    (integerp y))
   (equal (equal (* x y) 0)
	  (or (equal x 0)
	      (equal y 0)))))

(encapsulate
    ()

  (local
   (defthm product-bound
     (implies
      (and
       (integerp x)
       (integerp y)
       (< 1 (abs x))
       (< 1 (abs y)))
      (and (< (abs x) (abs (* x y)))
	   (< (abs y) (abs (* x y)))))))

  (defthm equal-product-one
    (implies
     (and
      (integerp x)
      (integerp y))
     (equal (equal (* x y) 1)
	    (or (and (equal x -1) (equal y -1))
		(and (equal x 1) (equal y 1)))))
    :hints (("Goal" :cases ((= x 0)
			    (= x 1)
			    (= x -1)
			    (= y 0)
			    (= y 1)
			    (= y -1)))
	    (and stable-under-simplificationp
		 '(:use product-bound))))

  )

(defthm equal-product-one-instance
  (implies
   (and
    (integerp x)
    (integerp y)
    (integerp r))
   (equal (equal (+ (* x r) (* y r)) 1)
	  (let ((x r)
		(y (+ x y)))
	    (or (and (equal x -1) (equal y -1))
		(and (equal x 1) (equal y 1))))))
  :hints (("Goal" :use (:instance equal-product-one
				  (x r)
				  (y (+ x y)))
	   :in-theory (disable equal-product-one))))
	      
(defthm equal-sum-zero
  (implies
   (and
    (natp x)
    (natp y))
   (equal (equal (+ x y) 0)
	  (and (equal x 0) (equal y 0)))))

(defthm equal-sum-one
  (implies
   (and
    (natp x)
    (natp y))
   (equal (equal (+ x y) 1)
	  (or (and (equal x 0) (equal y 1))
	      (and (equal y 0) (equal x 1))))))

(defthm equal-product-reduction
  (implies
   (and
    (posnatp x)
    (posnatp g)
    (<= g x)
    (integerp r))
   (equal (equal g (* x r))
	  (and (equal g x) (equal r 1))))
  :hints (("Goal" :in-theory (enable posnatp))))

(defthm natp-times
  (implies
   (and
    (natp x)
    (natp y))
   (natp (* x y)))
  :rule-classes (:rewrite
		 (:forward-chaining :trigger-terms ((binary-* x y)))))

;; ===================================================================
;; nonneg-int-mod and nonnegative-integer-quotient
;; ===================================================================

(defthm divide-by-one
  (implies
   (natp x)
   (equal (nonnegative-integer-quotient x 1) x)))

(defthm nonnegative-integer-quotient-identity
  (implies
   (posnatp p)
   (equal (nonnegative-integer-quotient p p) 1)))

(defun nat-induction (x)
  (if (zp x) 0
    (nat-induction (1- x))))

(defthm nonnegative-integer-quotient-plus-denominator
  (implies
   (and
    (natp n)
    (posnatp p))
   (equal (nonnegative-integer-quotient (+ n p) p)
	  (1+ (nonnegative-integer-quotient n p)))))

(defthm nonnegative-integer-quotient-identity-n
  (implies
   (and
    (posnatp n)
    (posnatp p))
   (equal (nonnegative-integer-quotient (* n p) p) n))
  :hints (("Goal" :induct (nat-induction n))))

(defthm mod-multiple-of-modulus-is-zero
  (implies
   (and
    (posnatp x)
    (posnatp d))
   (equal (nonneg-int-mod (* d x) d) 0)))

(defthm nonneg-int-mod-less-than-modulus
  (implies
   (< x p)
   (equal (nonneg-int-mod x p) (nfix x))))

(defthm nonneg-int-mod-identity
  (implies
   (natp p)
   (equal (nonneg-int-mod p p) 0)))

(defthm nonneg-int-mod-fixedpoint
  (equal
   (nonneg-int-mod (nonneg-int-mod y n) n)
   (nonneg-int-mod y n))
  :hints (("Goal" :induct (nonneg-int-mod y n))))

(defthm nonneg-int-mod-+-elimination
  (implies
   (and
    (natp x)
    (natp y))
   (equal
    (nonneg-int-mod (+ x (nonneg-int-mod y n)) n)
    (nonneg-int-mod (+ x y) n)))
  :hints (("Goal" :induct (nonneg-int-mod y n))))

(defthmd nonneg-int-mod-+-introduction-1
  (implies
   (and
    (natp x)
    (natp y)
    (syntaxp (not (equal (car y) 'nonneg-int-mod))))
   (equal
    (nonneg-int-mod (+ y x) n)
    (nonneg-int-mod (+ (nonneg-int-mod y n) x) n))))

(defthmd nonneg-int-mod-+-introduction-2
  (implies
   (and
    (natp x)
    (natp y)
    (syntaxp (not (equal (car y) 'nonneg-int-mod))))
   (equal
    (nonneg-int-mod (+ x y) n)
    (nonneg-int-mod (+ x (nonneg-int-mod y n)) n))))

(encapsulate
    ()

  (local
   (defun nmul (x y)
     (if (zp x) 0
       (if (= x 1) y
	 (+ y (nmul (1- x) y))))))
  
  (local
   (defthm natp-nmul
     (implies
      (natp y)
      (natp (nmul x y)))
     :rule-classes (:rewrite (:forward-chaining :trigger-terms ((nmul x y))))))

  (local
   (defthm nmul-is-times
     (implies
      (and
       (natp x)
       (integerp y))
      (equal (* x y) (nmul x y)))))
  
  (defthm nonneg-int-mod-*-elimination
    (implies
     (and
      (natp x)
      (natp y))
     (equal
      (nonneg-int-mod (* x (nonneg-int-mod y n)) n)
      (nonneg-int-mod (* x y) n)))
    :hints (("Goal" :do-not-induct t
	     :induct (nmul x y))
	    (and stable-under-simplificationp
		 '(:in-theory (e/d (nonneg-int-mod-+-introduction-1
				    nonneg-int-mod-+-introduction-2
				    ) 
				   (nonneg-int-mod-+-elimination))))))
  
  )

(defthmd nonneg-int-mod-to-nonnegative-integer-quotient
  (implies
   (and
    (natp x)
    (natp n))
   (equal (nonneg-int-mod x n) (- x (* n (nonnegative-integer-quotient x n))))))

(defthmd nonnegative-integer-quotient-to-nonneg-int-mod
  (implies
   (and
    (natp x)
    (natp n))
   (equal (* n (nonnegative-integer-quotient x n)) (- x (nonneg-int-mod x n))))
  :hints (("Goal" :in-theory (enable nonneg-int-mod-to-nonnegative-integer-quotient))))

(defthm common-factors-are-factors-of-gcd
  (implies
   (and
    (natp x)
    (natp y)
    (natp a)
    (equal (nonneg-int-mod x a) 0)
    (equal (nonneg-int-mod y a) 0))
   (equal (nonneg-int-mod (nonneg-int-gcd x y) a) 0))
  :hints (("Goal" :in-theory (enable nonneg-int-mod-to-nonnegative-integer-quotient)
	   :restrict ((nonneg-int-mod-to-nonnegative-integer-quotient ((x x)))
		      (nonneg-int-mod-to-nonnegative-integer-quotient ((x y)))))))

;; ===================================================================
;; gcd common factor
;; ===================================================================

(defthm nonneg-int-gcd-lower-bound
  (implies
   (and
    (posnatp x)
    (posnatp y))
   (<= 1 (nonneg-int-gcd x y)))
  :rule-classes :linear)

(defthmd multiple-of-nonneg-int-mod
  (implies
   (and
    (natp g)
    (natp x)
    (natp y))
   (equal (* g (nonneg-int-mod x y))
	  (nonneg-int-mod (* g x) (* g y))))
  :hints (("Goal" :expand (nonneg-int-mod (* g x) (* g y))
	   :induct (nonneg-int-mod x y))))

(defthm gcd-of-common-factor
  (implies
   (and
    (natp x)
    (natp y)
    (natp g))
   (equal (nonneg-int-gcd (* g x) (* g y))
	  (* g (nonneg-int-gcd x y))))
  :hints (("Goal" 
	   :in-theory (enable multiple-of-nonneg-int-mod)
	   :expand (NONNEG-INT-GCD (* G X) (* G Y))
	   :induct (nonneg-int-gcd x y))))

;; ===================================================================
;; g-c-d
;; ===================================================================

(defun g-c-d (x y)
  (declare (xargs :measure (nfix (+ x y))))
  (if (zp x)
      y
    (if (zp y)
	x
      (if (<= x y)
	  (g-c-d x (- y x))
	(g-c-d (- x y) y)))))

(defthm g-c-d-0
  (and (equal (g-c-d 0 y) y)
       (equal (g-c-d x 0) (nfix x))))

(defthm force-proof
  (implies (not (zp x))
	   (equal (g-c-d x x) x))
  :hints (("goal" :expand ((g-c-d x x)))))

(defthmd g-c-d-commute
  (implies
   (and
    (natp x)
    (natp y))
   (equal (g-c-d x y)
	  (g-c-d y x))))

(defthm g-c-d-type
  (implies 
   (and (natp x)
	(natp y))
   (natp (g-c-d x y)))
  :rule-classes (:rewrite
		 :type-prescription
		 (:forward-chaining :trigger-terms ((g-c-d x y)))))

(defthm g-c-d-bound
  (implies
   (and
    (posnatp x)
    (posnatp y))
   (and (< 0 (g-c-d x y))
	(<= (g-c-d x y) x)
	(<= (g-c-d x y) y)))
  :rule-classes (:linear
		 (:forward-chaining :trigger-terms ((g-c-d x y)))))

(defthm g-c-d-zero
  (implies
   (natp x)
   (and (equal (g-c-d x 0) x)
	(equal (g-c-d 0 x) x))))

;; ===================================================================
;; r and s
;; ===================================================================

(mutual-recursion
 
 (defun r (x y)
   (declare (type (integer 0 *) x y)
	    (xargs :measure (nfix (+ x y))))
   (if (zp x)
       0
     (if (zp y)
	 1
       (if (<= x y)
	   (- (r x (- y x)) (s x (- y x)))
	 (r (- x y) y)))))

 (defun s (x y)
   (declare (type (integer 0 *) x y)
	    (xargs :measure (nfix (+ x y))))
   (if (zp x)
       1
     (if (zp y)
	 0
       (if (<= x y)
	   (s x (- y x))
	 (- (s (- x y) y) (r (- x y) y))))))
 )

(defthmd r-s-lemma
  (implies (and (natp x)
		(natp y))
	   (equal (g-c-d x y)
		  (+ (* (r x y) x)
		     (* (s x y) y))
		  )))

(defthmd s=0-prop
  (implies
   (and
    (natp x)
    (natp y)
    (equal (s x y) 0))
   (equal (r x y) 1))
  :hints (("Goal" :cases ((= x 0) (= y 0))
	   :use (r-s-lemma))))

(defthmd r=0-prop
  (implies
   (and
    (natp x)
    (natp y)
    (equal (r x y) 0))
   (equal (s x y) 1))
  :hints (("Goal" :cases ((= x 0) (= y 0))
	   :use (r-s-lemma))))

(defthm s-of-1
  (equal (s 1 y) 0)
  :hints (("Goal" :induct (nat-induction y))))

(defthm r-of-1
  (equal (r 1 y) 1)
  :hints (("Goal" :induct (nat-induction y))))

(defthm r-of-1-2
  (equal (r x 1) (if (zp x) 0 1))
  :hints (("Goal" :induct (nat-induction x))))

(defthm s-of-1-2
  (equal (s x 1) (if (zp x) 1 (- (- x 1))))
  :hints (("Goal" :induct (nat-induction x))))

(defun sign (x)
  (if (<= x 0) -1 1))

(defthmd r-s-sign
  (implies
   (and
    (natp x)
    (natp y))
   (equal (sign (r x y)) (- (sign (s x y)))))
  :hints (("Goal" :induct (g-c-d x y))))

(defthm r-s-sign-implication-1
  (implies
   (and
    (natp x)
    (natp y)
    (<= (r x y) 0))
   (< 0 (s x y)))
  :rule-classes (:linear
		 (:forward-chaining :trigger-terms ((r x y) (s x y))))
  :hints (("Goal" :use r-s-sign)))

(defthm r-s-sign-implication-2
  (implies
   (and
    (natp x)
    (natp y)
    (<= (s x y) 0))
   (< 0 (r x y)))
  :rule-classes (:linear
		 (:forward-chaining :trigger-terms ((r x y) (s x y))))
  :hints (("Goal" :use r-s-sign)))

(defthm r-s-sign-implication-3
  (implies
   (and
    (natp x)
    (natp y)
    (< 0 (s x y)))
   (<= (r x y) 0))
  :rule-classes (:linear
		 (:forward-chaining :trigger-terms ((r x y) (s x y))))
  :hints (("Goal" :use r-s-sign)))

(defthm r-s-sign-implication-4
  (implies
   (and
    (natp x)
    (natp y)
    (< 0 (r x y)))
   (<= (s x y) 0))
  :rule-classes (:linear
		 (:forward-chaining :trigger-terms ((r x y) (s x y))))
  :hints (("Goal" :use r-s-sign)))

(defthm r-s-differ
  (implies
   (and
    (natp x)
    (natp y))
   (not (equal (r x y) (s x y))))
  :rule-classes ((:forward-chaining :trigger-terms ((r x y) (s x y))))
  :hints (("Goal" :use r-s-sign)))

(defthm r=0-implies-p=0
  (implies
   (and
    (natp p)
    (natp d))
   (equal (equal (r p d) 0)
	  (equal p 0)))
  :hints (("Goal" :expand (r p d)
	   :induct (nonneg-int-mod p d))))

(defthm s=0-implies-d>=p
  (implies
   (and
    (equal (s p d) 0)
    (posnatp p)
    (posnatp d))
   (<= p d))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :expand (s p d)
	   :induct (nonneg-int-mod p d))))

(defthm r-s-property
  (implies
   (and
    (equal (g-c-d x y) 1)
    (pnunitp x)
    (pnunitp y))
   (and (not (equal (r x y) 0))
	(not (equal (s x y) 0))))
  :rule-classes ((:forward-chaining :trigger-terms ((g-c-d x y)
						    (r x y)
						    (s x y))))
  :hints (("Goal" :in-theory (enable r-s-lemma))))

(defthmd r-s-bounds
  (implies
   (and
    (pnunitp x)
    (pnunitp y))
   (and (< (abs (s x y)) x)
	(< (abs (r x y)) y)))
  :hints (("Goal" 
	   :induct (g-c-d x y)
	   :expand ((s x y)
		    (r x y))
	   :do-not-induct t)
	  (and stable-under-simplificationp
	       '(:in-theory (enable pnunitp posnatp natp)
			    :cases ((equal x y))))))

;; ===================================================================
;; mapping g-c-d between nonneg-int-gcd
;; ===================================================================

(defthmd step-0
  (implies
   (not (zp y))
   (equal (g-c-d x y)
	  (g-c-d y (nonneg-int-mod x y))))
  :hints (("Goal" :induct (nonneg-int-mod x y)
	   :expand (G-C-D X Y)
	   :in-theory (enable g-c-d-commute)
	   :do-not-induct t)))

(in-theory (disable g-c-d))

(defthmd nonneg-int-gcd-to-g-c-d
  (implies
   (and
    (natp x)
    (natp y))
   (equal (nonneg-int-gcd x y)
	  (g-c-d x y)))
  :hints (("Goal" :in-theory (enable step-0)
	   :induct (nonneg-int-gcd x y))))

;; ===================================================================
;; ideal-k and cheat-i
;; ===================================================================

(defun ideal-k (d p)
  (declare (type (integer 1 *) p)
	   (type (integer 1 *) d))
  (let ((d (ifix d))
	(p (ifix p)))
    (let ((k (r p d)))
      (if (< 0 k)  (- d k) (- k)))))

(defthm integerp-ideal-k
  (integerp (ideal-k d p))
  :rule-classes ((:forward-chaining :trigger-terms ((ideal-k d p)))))

(defthm natp-ideal-k
  (implies
   (and
    (posnatp d)
    (posnatp p))
   (natp (ideal-k d p)))
  :hints ((and stable-under-simplificationp
	       '(:in-theory (enable pnunitp)
                            :use (:instance r-s-bounds
                                            (x p)
                                            (y d)))))
  :rule-classes (:rewrite
		 (:forward-chaining :trigger-terms ((ideal-k d p)))))

(defthm ideal-k-bounds
  (implies
   (and
    (pnunitp d)
    (pnunitp p))
   (and (< 0 (ideal-k d p))
	(< (ideal-k d p) d)))
  :hints ((and stable-under-simplificationp
	       '(:use (:instance r-s-bounds
				 (x p)
				 (y d)))))
  :rule-classes (:rewrite
		 :linear
		 (:forward-chaining :trigger-terms ((ideal-k d p)))))

(defun cheat-i (d p)
  (declare (type (integer 1 *) p)
	   (type (integer 1 *) d))
  (let ((p (ifix p))
	(d (ifix d)))
    (let ((i (s p d)))
      (if (<= i 0) (+ p i) i))))

(defthm integerp-cheat-i
  (integerp (cheat-i d p))
  :rule-classes ((:forward-chaining :trigger-terms ((cheat-i d p)))))

(defthm natp-cheat-i
  (implies
   (and
    (posnatp d)
    (posnatp p))
   (natp (cheat-i d p)))
  :hints ((and stable-under-simplificationp
	       '(:in-theory (enable pnunitp)
                            :use (:instance r-s-bounds
				 (x p)
				 (y d)))))
  :rule-classes (:rewrite
		 (:forward-chaining :trigger-terms ((cheat-i d p)))))

(defthm cheat-i-bounds
  (implies
   (and
    (pnunitp d)
    (pnunitp p)
    (< d p))
   (and (< 0 (cheat-i d p))
	(< (cheat-i d p) p)))
  :hints ((and stable-under-simplificationp
	       '(:use (:instance r-s-bounds
				 (x p)
				 (y d)))))
  :rule-classes (:rewrite
		 :linear
		 (:forward-chaining :trigger-terms ((cheat-i d p)))))

(defthmd nonneg-int-gcd-to-bezouts-identity
  (implies
   (and
    (natp d)
    (natp p))
   (equal (nonneg-int-gcd d p) (+ (* d (cheat-i d p)) (* p (- (ideal-k d p))))))
  :hints (("Goal" :do-not-induct t
	   :in-theory (enable nonneg-int-gcd-to-g-c-d g-c-d-commute)
	   :use (:instance r-s-lemma
			   (x p)
			   (y d)))))

(defthmd cheat-product-to-nonneg-int-gcd
  (implies
   (and
    (natp d)
    (natp p))
   (equal (* d (cheat-i d p)) (+ (* p (ideal-k d p)) (nonneg-int-gcd d p))))
  :hints (("Goal" :in-theory (enable nonneg-int-gcd-to-bezouts-identity))))

(defthmd ideal-product-to-nonneg-int-gcd
  (implies
   (and
    (natp d)
    (natp p))
   (equal (* p (ideal-k d p)) (- (* d (cheat-i d p)) (nonneg-int-gcd d p))))
  :hints (("Goal" :in-theory (enable nonneg-int-gcd-to-bezouts-identity))))

(in-theory (disable ideal-k cheat-i))

(encapsulate
    ()
  
  (local
   (encapsulate
       ()

     (defun product-reduction (x y)
       (* (nonneg-int-gcd x y) (nonnegative-integer-quotient x (nonneg-int-gcd x y))))

     (defthm equal-product-one-instance-2
       (implies
	(and
	 (integerp x)
	 (integerp y)
	 (integerp a)
	 (integerp b)
	 (integerp g))
	(equal (equal (+ (* a g x) (* b g y)) 1)
	       (let ((x g)
		     (y (+ (* a x) (* b y))))
		 (or (and (equal x -1) (equal y -1))
		     (and (equal x  1) (equal y  1))))))
       :hints (("Goal" :in-theory (disable equal-product-one)
		:use (:instance equal-product-one
				(x g)
				(y (+ (* a x) (* b y)))))))
     
     (defthmd existence-implies-gcd-helper
       (implies
	(and
	 (integerp a)
	 (integerp b)
	 (natp x)
	 (natp y)
	 (equal (+ (* a (product-reduction x y)) (* b (product-reduction y x))) 1))
	(equal (nonneg-int-gcd (product-reduction x y) (product-reduction y x)) 1))
       :hints (("Goal" :in-theory (e/d (COMMUTATIVITY-OF-NONNEG-INT-GCD) 
				       (NONNEGATIVE-INTEGER-QUOTIENT-GCD)))))
     
     (defthmd existence-implies-gcd
       (implies
	(and
	 (integerp a)
	 (integerp b)
	 (natp x)
	 (natp y)
	 (equal (+ (* a x) (* b y)) 1))
	(equal (nonneg-int-gcd x y) 1))
       :hints (("Goal" :use existence-implies-gcd-helper)))
     
     (defthmd simple-product-helper
       (implies
	(and
	 (equal a x)
	 (equal b y))
	(equal (* a b) (* x y))))
     
     (defthmd relatively-prime-factors-imply-relatively-prime-product-helper
       (implies
	(and
	 (natp y)
	 (natp x)
	 (natp p)
	 (equal (* x (cheat-i x p)) (+ (* p (ideal-k x p)) 1))
	 (equal (* y (cheat-i y p)) (+ (* p (ideal-k y p)) 1))
	 )
	(equal (nonneg-int-gcd p (* y x)) 1))
       :hints (("Goal" :use ((:instance simple-product-helper
					(a (* x (cheat-i x p)))
					(b (* y (cheat-i y p)))
					(x (+ (* p (ideal-k x p)) 1))
					(y (+ (* p (ideal-k y p)) 1)))
			     (:instance existence-implies-gcd
					(a (- (+ (IDEAL-K X P)
						 (IDEAL-K Y P)
						 (* P
						    (IDEAL-K X P)
						    (IDEAL-K Y P)))))
					(x p)
					(b (* (CHEAT-I X P) (CHEAT-I Y P)))
					(y (* x y)))))))

     ))
  
  (defthmd relatively-prime-factors-imply-relatively-prime-product
    (implies
     (and
      (natp y)
      (natp x)
      (natp p)
      (equal (nonneg-int-gcd x p) 1)
      (equal (nonneg-int-gcd y p) 1)
      )
     (equal (nonneg-int-gcd (* y x) p) 1))
    :hints (("Goal" :in-theory (enable ideal-product-to-nonneg-int-gcd
				       COMMUTATIVITY-OF-NONNEG-INT-GCD)
	     :use relatively-prime-factors-imply-relatively-prime-product-helper)))

  )
  
(encapsulate
    ()

  (local
   (defthmd relatively-prime-product-implies-relatively-prime-factors-helper
     (implies
      (and
       (natp y)
       (natp x)
       (natp p)
       (equal (nonneg-int-gcd p (* y x)) 1))
      (equal (nonneg-int-gcd p x) 1))
     :hints (("Goal" :do-not-induct t
	      :use (:instance  gcd-of-common-factor
			       (g (NONNEG-INT-GCD P X))
			       (x (NONNEGATIVE-INTEGER-QUOTIENT P (NONNEG-INT-GCD P X)))
			       (y (* Y (NONNEGATIVE-INTEGER-QUOTIENT X (NONNEG-INT-GCD P X)))))
	      )))
   )

  (defthmd relatively-prime-product-implies-relatively-prime-factors
    (implies
     (and
      (equal (nonneg-int-gcd (* x y) p) 1)
      (natp y)
      (natp x)
      (natp p))
     (and (equal (nonneg-int-gcd x p) 1)
	  (equal (nonneg-int-gcd y p) 1)))
    :hints (("Goal" :in-theory (enable COMMUTATIVITY-OF-NONNEG-INT-GCD)
	     :use ((:instance relatively-prime-product-implies-relatively-prime-factors-helper
			      (x x)
			      (y y))
		   (:instance relatively-prime-product-implies-relatively-prime-factors-helper
			      (x y)
			      (y x))))))

  )

(defthm nonneg-int-gcd-product-reduction
  (implies
   (and
    (natp x)
    (natp y)
    (natp p))
   (equal (equal (nonneg-int-gcd (* x y) p) 1)
	  (and (equal (nonneg-int-gcd x p) 1)
	       (equal (nonneg-int-gcd y p) 1))))
  :hints (("Goal" :use (relatively-prime-product-implies-relatively-prime-factors
			relatively-prime-factors-imply-relatively-prime-product
			))))

(defthm multiple-of-p-plus-one-is-relatively-prime-to-p
  (implies
   (and
    (natp n)
    (posnatp p))
   (equal (nonneg-int-gcd (+ 1 (* p n)) p) 1))
  :hints (("goal" :in-theory (e/d (commutativity-of-nonneg-int-gcd) (nonneg-int-gcd-abs))
	   :use (:instance nonneg-int-gcd-abs
			   (n p)
			   (j n)
			   (x 1)))))

;; I think d is relatively prime with ideal-k
;;         p is relatively prime with cheat-i

(defthm cheat-i-relatively-prime-to-p
  (implies
   (and
    (posnatp d)
    (posnatp p)
    (equal (nonneg-int-gcd d p) 1))
   (equal (nonneg-int-gcd (cheat-i d p) p) 1))
  :hints (("Goal" :do-not-induct t
	   :in-theory (e/d (cheat-product-to-nonneg-int-gcd)
			   (nonneg-int-gcd-product-reduction))
	   :use (:instance nonneg-int-gcd-product-reduction
			   (p p)
			   (x d)
			   (y (cheat-i d p))))))

;; ===================================================================
;; int-mod characterization
;; ===================================================================

(defun int-mod (n d)
  (declare (type integer n)
	   (type (integer 1 *) d))
  (let ((n (ifix n))
	(d (nfix d)))
    (if (zp d) (ifix n)
      (if (< n 0) 
	  (let ((r (nonneg-int-mod (- n) d)))
	    (if (= r 0) 0 (- d r)))
	(nonneg-int-mod n d)))))

(defthm int-mod-less-than-modulus
  (implies
   (and
    (posnatp p)
    (natp x)
    (< (abs x) p))
   (equal (int-mod x p) x))
  :hints (("Goal" :in-theory (enable int-mod))))

(defthm int-mod-zero
  (equal (int-mod 0 d) 0))

(defthmd nonneg-int-mod-as-int-mod
  (implies
   (natp x)
   (equal (nonneg-int-mod x n)
	  (int-mod x n)))
  :hints (("Goal" :in-theory (enable int-mod))))

(defthm natp-int-mod
  (implies
   (posnatp d)
   (natp (int-mod n d)))
  :rule-classes ((:forward-chaining :trigger-terms ((int-mod n d)))))

(defthm int-mod-bound
  (implies
   (posnatp d)
   (and (<= 0 (int-mod w d))
	(< (int-mod w d) d)))
  :rule-classes (:linear
		 (:forward-chaining :trigger-terms ((int-mod w d)))))

(defthm int-mod-fixedpoint
  (equal (int-mod (int-mod x n) n)
	 (int-mod x n)))

(defun int-mod-measure (x n)
  (let ((x (ifix x))
	(n (nfix n)))
    (if (< x 0) (- n x)
      x)))

(defun int-mod-induction (x n)
  (declare (xargs :measure (int-mod-measure x n)))
  (let ((x (ifix x))
	(n (nfix n)))
    (if (zp n) (ifix x)
      (if (< x 0) (int-mod-induction (+ x n) n)
	(if (<= n x) (int-mod-induction (- x n) n)
	  x)))))

(defthmd int-mod-to-int-mod-induction
  (equal (int-mod x n)
	 (int-mod-induction x n))
  :hints (("Goal" :do-not-induct t
	   :induct (int-mod-induction x n))
	  (and stable-under-simplificationp
	       '(:expand (NONNEG-INT-MOD (- X) N)))))

(defthmd int-mod---elimination-weak
  (implies
   (integerp x)
   (equal (int-mod (- (int-mod x n)) n)
	  (int-mod (- (nfix n) x) n)))
  :hints (("Goal" :induct (int-mod-induction x n)
	   :in-theory (e/d (int-mod-to-int-mod-induction) (int-mod)))))

(defthm int-mod-+-elimination
  (implies
   (and
    (integerp x)
    (integerp y))
   (equal
    (int-mod (+ x (int-mod y n)) n)
    (int-mod (+ x y) n)))
  :hints (("Goal" :in-theory (e/d (int-mod-to-int-mod-induction) (int-mod)))
	  (and stable-under-simplificationp
	       '(:do-not-induct t :induct (int-mod-induction y n)
				:expand (INT-MOD-INDUCTION (+ X Y) N)))))

(defthm int-mod-n-n
  (implies
   (natp n)
   (equal (int-mod n n) 0))
  :hints (("Goal" :in-theory (enable int-mod))))

(in-theory (disable int-mod))

(defthmd int-mod-+-introduction-2
  (implies
   (and
    (integerp x)
    (integerp y)
    (syntaxp (not (equal (car y) 'int-mod))))
   (equal
    (int-mod (+ x y) n)
    (int-mod (+ x (int-mod y n)) n))))

(defthmd int-mod-+-introduction-1
  (implies
   (and
    (integerp x)
    (integerp y)
    (syntaxp (not (equal (car y) 'int-mod))))
   (equal
    (int-mod (+ y x) n)
    (int-mod (+ (int-mod y n) x) n))))

(defthm int-mod---elimination
  (implies
   (integerp x)
   (equal (int-mod (- (int-mod x n)) n)
	  (int-mod (- x) n)))
  :hints (("Goal" :in-theory (e/d (int-mod---elimination-weak
				   int-mod-+-introduction-1
				   int-mod-+-introduction-2)
				  (int-mod-+-elimination))
	   :do-not-induct t)))

(defthmd int-mod---introduction
  (implies
   (and
    (integerp x)
    (syntaxp (not (equal (car x) 'int-mod))))
   (equal (int-mod (- x) n)
	  (int-mod (- (int-mod x n)) n))))

;; DAG -- I'm not sure about the rest of this ..

(encapsulate
    ()

  (local
   (defun imul (x y)
     (declare (xargs :measure (abs (ifix x))))
     (let ((x (ifix x)))
       (if (= x 0) 0
	 (if (= x 1) y
	   (if (= x -1) (- y)
	     (if (< x 0) (+ (imul (1+ x) y) (- y))
	       (+ (imul (1- x) y) y))))))))
   
  (local
   (defthm integerp-imul
     (implies
      (integerp y)
      (integerp (imul x y)))
     :rule-classes (:rewrite (:forward-chaining :trigger-terms ((imul x y))))))

  (local
   (defthm imul-is-times
     (implies
      (and
       (integerp x)
       (integerp y))
      (equal (* x y) (imul x y)))))

  (defthm int-mod-*-elimination
    (implies
     (and
      (integerp x)
      (integerp y))
     (equal
      (int-mod (* x (int-mod y n)) n)
      (int-mod (* x y) n)))
    :hints (("Goal" :do-not-induct t
	     :do-not '(generalize eliminate-destructors)
	     :induct (imul x y))
	    (and stable-under-simplificationp
		 '(:in-theory (e/d (int-mod---introduction
				    int-mod-+-introduction-1
				    int-mod-+-introduction-2
				    ) 
				   (int-mod---elimination
				    int-mod-+-elimination))))))

  )

(defthmd nonneg-int-mod-*-introduction-1
  (implies
   (and
    (natp x)
    (natp y)
    (syntaxp (not (equal (car y) 'nonneg-int-mod))))
   (equal
    (nonneg-int-mod (* y x) n)
    (nonneg-int-mod (* (nonneg-int-mod y n) x) n))))

(defthmd nonneg-int-mod-*-introduction-2
  (implies
   (and
    (natp x)
    (natp y)
    (syntaxp (not (equal (car y) 'nonneg-int-mod))))
   (equal
    (nonneg-int-mod (* x y) n)
    (nonneg-int-mod (* x (nonneg-int-mod y n)) n))))

(defthmd int-mod-*-introduction-1
  (implies
   (and
    (integerp x)
    (integerp y)
    (syntaxp (not (equal (car y) 'int-mod))))
   (equal
    (int-mod (* y x) n)
    (int-mod (* (int-mod y n) x) n))))

(defthmd int-mod-*-introduction-2
  (implies
   (and
    (integerp x)
    (integerp y)
    (syntaxp (not (equal (car y) 'int-mod))))
   (equal
    (int-mod (* x y) n)
    (int-mod (* x (int-mod y n)) n))))

(include-book "coi/nary/nary" :dir :system)
(include-book "coi/util/good-rewrite-order" :dir :system)

;; ==================================================================
;;
;; nonneg-int-mod congruence
;;
;; ==================================================================

(defun nni-mod-equivp (x y n)
  (equal (nonneg-int-mod x n)
	 (nonneg-int-mod y n)))

(defequiv+ (nni-mod-equivp x y n)
  :lhs x
  :rhs y
  :equiv   nni-mod-equiv
  :context nni-mod-ctx
  :keywords t
  )

(defthm nni-mod-cong
  (implies
   (bind-contextp (x (equal y (nni-mod-ctx x :n n))))
   (equal (nonneg-int-mod x n)
	  (nonneg-int-mod y n))))

(defthm nni-mod-equivp-cong
  (implies
   (bind-contextp ((x (equal a (nni-mod-ctx x :n n)))
		  (y (equal b (nni-mod-ctx y :n n)))))
   (equal (nni-mod-equivp x y n)
	  (nni-mod-equivp a b n))))

(defthm nni-mod-elimination
  (nni-mod-equiv :lhs (nonneg-int-mod x n)
		 :rhs x
		 :n n))

(defthm order-nni-mod-equivp
  (implies
   (syntaxp (good-rewrite-order x y))
   (equal (nni-mod-equivp y x n)
	  (nni-mod-equivp x y n)))
  :rule-classes ((:rewrite :loop-stopper nil)))

(defthm nni-mod-equivp-rewrite
  (implies
   (nni-mod-equivp x y n)
   (nni-mod-equiv :lhs x
		  :rhs y
		  :n n)))

;; ==================================================================
;;
;; int-mod congruence
;;
;; ==================================================================

(defun int-mod-equivp (x y n)
  (equal (int-mod x n)
	 (int-mod y n)))

(defthmd equal-int-mod-to-int-mod-equivp
  (implies
   (posnatp n)
   (equal (equal (int-mod x n) z)
	  (and (integerp z)
	       (<= 0 z)
	       (< z n)
	       (int-mod-equivp x z n))))
  :hints (("Goal" :in-theory (enable int-mod int-mod-equivp))))

(defthm int-mod-equivp-1-0
  (equal (int-mod-equivp 1 0 n) (equal n 1))
  :hints (("Goal" :in-theory (enable int-mod))))

(defthm int-mod-equivp-1
  (int-mod-equivp x y 1))

(defthm int-mod-equivp-identity
  (int-mod-equivp x x p))

(defequiv+ (int-mod-equivp x y n)
  :lhs x
  :rhs y
  :equiv   int-mod-equiv
  :context int-mod-ctx
  :keywords t
  )

(defthm int-mod-cong
  (implies
   (bind-contextp (x (equal y (int-mod-ctx x :n n))))
   (equal (int-mod x n)
	  (int-mod y n))))

(defthm int-mod-equivp-cong
  (implies
   (bind-contextp ((x (equal a (int-mod-ctx x :n n)))
		  (y (equal b (int-mod-ctx y :n n)))))
   (equal (int-mod-equivp x y n)
	  (int-mod-equivp a b n))))

(defthm int-mod-elimination
  (int-mod-equiv :lhs (int-mod x n)
		 :rhs x
		 :n n))

(defthm order-int-mod-equivp
  (implies
   (syntaxp (good-rewrite-order x y))
   (equal (int-mod-equivp y x n)
	  (int-mod-equivp x y n)))
  :rule-classes ((:rewrite :loop-stopper nil)))

(defthm int-mod-equivp-rewrite
  (implies
   (int-mod-equivp x y n)
   (int-mod-equiv :lhs x
		  :rhs y
		  :n n)))

(defthm nni-mod-of-modulus
  (nni-mod-equiv :lhs n
		 :rhs 0
		 :n n))

(defthm int-mod-of-modulus
  (implies
   (natp n)
   (int-mod-equiv :lhs n
		  :rhs 0
		  :n n))
  :hints (("Goal" :in-theory (enable int-mod))))

;; ==================================================================
;;
;; ==================================================================

(defthm nni-mod-+-cong
  (implies
   (and
    (natp x)
    (natp y)
    (bind-contextp ((x (equal a (nni-mod-ctx x :n n)))
		    (y (equal b (nni-mod-ctx y :n n)))))
    (natp a)
    (natp b))
   (nni-mod-equiv :lhs (+ x y)
		  :rhs (+ a b)
		  :n n))
  :hints (("Goal" :do-not-induct t
	   :in-theory (e/d (nonneg-int-mod-+-introduction-1
			    nonneg-int-mod-+-introduction-2
			    ) 
			   (nonneg-int-mod-+-elimination)))))
	   
(defthm int-mod-+-cong
  (implies
   (and
    (integerp x)
    (integerp y)
    (bind-contextp ((x (equal a (int-mod-ctx x :n n)))
		    (y (equal b (int-mod-ctx y :n n)))))
    (integerp a)
    (integerp b))
   (int-mod-equiv :lhs (+ x y)
		  :rhs (+ a b)
		  :n n))
  :hints (("Goal" :do-not-induct t
	   :in-theory (e/d (int-mod-+-introduction-1
			    int-mod-+-introduction-2
			    ) 
			   (int-mod-+-elimination)))))
	   
;; ==================================================================
;;
;; ==================================================================

(defthm nni-mod-*-cong
  (implies
   (and
    (natp x)
    (natp y)
    (bind-contextp ((x (equal a (nni-mod-ctx x :n n)))
		   (y (equal b (nni-mod-ctx y :n n)))))
    (natp a)
    (natp b))
   (nni-mod-equiv :lhs (* x y)
		  :rhs (* a b)
		  :n n))
  :hints (("Goal" :do-not-induct t
	   :in-theory (e/d (nonneg-int-mod-*-introduction-1
			    nonneg-int-mod-*-introduction-2
			    ) 
			   (nonneg-int-mod-*-elimination)))))

(defthm int-mod-*-cong
  (implies
   (and
    (integerp x)
    (integerp y)
    (bind-contextp ((x (equal a (int-mod-ctx x :n n)))
		   (y (equal b (int-mod-ctx y :n n)))))
    (integerp a)
    (integerp b))
   (int-mod-equiv :lhs (* x y)
		  :rhs (* a b)
		  :n n))
  :hints (("Goal" :do-not-induct t
	   :in-theory (e/d (int-mod-*-introduction-1
			    int-mod-*-introduction-2
			    ) 
			   (int-mod-*-elimination)))))

;; ==================================================================
;;
;; ==================================================================

(defthm int-mod---cong
  (implies
   (and
    (integerp x)
    (bind-contextp (x (equal a (int-mod-ctx x :n n))))
    (integerp a))
   (int-mod-equiv :lhs (- x)
		  :rhs (- a)
		  :n n))
  :hints (("Goal" :do-not-induct t
	   :in-theory (e/d (int-mod---introduction
			    ) 
			   (int-mod---elimination)))))

;; ==================================================================
;;
;; ==================================================================

;; This isn't saying anything about ideal-k
(defthm gcd-ideal-k-construction
  (implies
   (and
    (posnatp p)
    (posnatp d))
   (equal (nonneg-int-gcd (+ 1 (* p (ideal-k d p))) p) 1)))

;; ==================================================================
;; push back
;; ==================================================================

(in-theory (disable nonneg-int-gcd))

(defthm int-mod--1
  (implies
   (posnatp d)
   (equal (int-mod -1 d)
	  (- d 1)))
  :hints (("Goal" :expand ((nonneg-int-mod 1 d))
	   :in-theory (enable nonneg-int-mod int-mod))))

(defthmd introduce-product-equality
  (implies
   (and
    (posnatp y)
    (integerp z))
   (equal (equal (nonnegative-integer-quotient x y) z)
	  (equal (* y (nonnegative-integer-quotient x y)) (* y z)))))

(defthmd introduce-product-<
  (implies
   (and
    (posnatp y)
    (integerp z))
   (equal (< z (nonnegative-integer-quotient x y))
	  (< (* y z) (* y (nonnegative-integer-quotient x y))))))

(defthm divide-one-less-than-perfect-product
  (implies
   (and
    (posnatp d)
    (posnatp i))
   (equal (nonnegative-integer-quotient (+ -1 (* d i)) d)
	  (- i 1)))
  :hints (("Goal" :in-theory (enable introduce-product-equality
				     NONNEG-INT-MOD-AS-INT-MOD
				     NONNEGATIVE-INTEGER-QUOTIENT-TO-NONNEG-INT-MOD))))


(defthm nonnegative-integer-quotient-to-cheat-i
  (implies
   (and
    (equal (nonneg-int-gcd d p) 1)
    (equal n (* p (ideal-k d p)))
    (pnunitp d)
    (pnunitp p)
    (< d p))
   (equal (nonnegative-integer-quotient n d)
	  (1- (cheat-i d p))))
  :hints (("Goal" :do-not-induct t
	   :in-theory (enable IDEAL-PRODUCT-TO-NONNEG-INT-GCD))))

(defthm answer-the-equality-question
  (implies
   (and
    (equal (ideal-k d p) (nonnegative-integer-quotient n p))
    (equal (nonneg-int-mod n p) 0)
    (natp n)
    (natp d)
    (natp p))
   (equal (* p (ideal-k d p)) n))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" :in-theory (enable NONNEG-INT-MOD-TO-NONNEGATIVE-INTEGER-QUOTIENT))))

;; In order to use this we may need to know something
;; about the case when (EQUAL (IDEAL-K D P) 1)

(in-theory (disable ideal-k))
(in-theory (disable nonnegative-integer-quotient))
(in-theory (disable nonneg-int-mod))
(in-theory (disable nonneg-int-mod-nonnegative-integer-quotient))

(defthm ideal-k-zero
  (equal (ideal-k x 0) 0)
  :hints (("Goal" :in-theory (enable ideal-k))))

(encapsulate
    ()
  
  (local
   (set-default-hints '((nonlinearp-default-hint++ 
 			 id stable-under-simplificationp
 			 hist nil))))
  
  (defthm answer-the-in-equality-question
    (implies
     (and
      (< (nonnegative-integer-quotient n p) (ideal-k d p))
      (equal (nonneg-int-mod n p) 0)
      (natp n)
      (natp d)
      (natp p))
     (< n (* p (ideal-k d p))))
    :rule-classes (:linear
 		   :rewrite
 		   (:forward-chaining 
 		    :trigger-terms 
 		    ((< (nonnegative-integer-quotient n p) (ideal-k d p)))))
    :hints (("Goal" :in-theory (enable NONNEG-INT-MOD-TO-NONNEGATIVE-INTEGER-QUOTIENT))))
  
  )

(encapsulate
    ()

  (local
   (encapsulate
       ()

     (defthmd introduce-product-helper
       (implies
	(and (integerp x) (integerp y) (posnatp z))
	(equal (< x y)
	       (< (* z x) (* z y)))))
     
     (local
      (set-default-hints '((nonlinearp-default-hint++ 
			    id stable-under-simplificationp
			    hist nil))))
     
     (defthm product-upper-bound-<
       (implies
	(and
	 (< n (* p ideal))
	 (< ideal d)
	 (natp d)
	 (natp ideal)
	 (natp p))
	(< n (* p d)))
       :rule-classes (:rewrite :forward-chaining :linear))
     
     (defthmd <-nonnegative-integer-quotient-from-<-product
       (implies
	(and
	 (natp n)
	 (natp d)
	 (natp p)
	 (< n (* p d)))
	(< (nonnegative-integer-quotient n d) p))
       :hints (("Goal" :in-theory (enable NONNEGATIVE-INTEGER-QUOTIENT-TO-NONNEG-INT-MOD)
		:use ((:instance introduce-product-helper
				 (x n)
				 (y (* p d))
				 (z d))
		      (:instance introduce-product-helper
				 (x (nonnegative-integer-quotient n d))
				 (y p)
				 (z d))))))
     
     )
   )
  
  (defthm bound-nonnegative-integet-quotient-by-product
    (implies
     (and
      (integerp d)
      (< 1 d)
      (integerp p)
      (< 1 p)
      (natp n)
      (equal (nonneg-int-gcd d p) 1)
      (equal (nonneg-int-mod n p) 0)
      (< n (* p (ideal-k d p))))
     (< (nonnegative-integer-quotient n d) p))
    :hints (("Goal" :in-theory (enable <-nonnegative-integer-quotient-from-<-product)))
    :rule-classes (:linear :rewrite))
  
  )

(defthm nonnegative-integer-quotient-n-d-upper-bound
  (implies (and (pnunitp d)
		(pnunitp p)
		(< d p)
		(equal (nonneg-int-gcd d p) 1)
		(integerp n)
		(<= p n)
		(equal (nonneg-int-mod n p) 0)
		(<= (nonnegative-integer-quotient n p)
		    (ideal-k d p))
		)
	   (< (nonnegative-integer-quotient n d) p))
  :hints (("goal" :cases ((equal (nonnegative-integer-quotient n p) 
				 (ideal-k d p))))))

(defthm negation-of-quotient-decreases-d
  (implies
   (and
    (posnatp n)
    (pnunitp p)
    (pnunitp d)
    (< d p)
    (equal (nonneg-int-mod n p) 0))
   (< (int-mod (- (* d (nonnegative-integer-quotient n d))) p)
      d))
  :rule-classes (:rewrite :linear)
  :hints (("goal" :in-theory (enable 
			      equal-int-mod-to-int-mod-equivp
			      nonneg-int-mod-as-int-mod
			      nonnegative-integer-quotient-to-nonneg-int-mod))))

(defthmd nested-ideal-product-to-nonneg-int-gcd
  (implies
   (and
    (natp d)
    (natp p)
    (natp q))
   (equal (* p (* (ideal-k d p) q))
	  (* (- (* d (cheat-i d p)) (nonneg-int-gcd d p)) q)))
  :hints (("Goal" :use ideal-product-to-nonneg-int-gcd)))

(defun a-posnat (n p d)
  (- (* (cheat-i d p) (NONNEGATIVE-INTEGER-QUOTIENT N P))
     (* (ideal-k d p) (NONNEGATIVE-INTEGER-QUOTIENT N D))))

(defthm d-is-less-than-multiples-of-p
  (implies
   (and
    (< d p)
    (equal (nonneg-int-mod n p) 0)
    (posnatp p)
    (integerp d)
    (posnatp n))
   (< d n)))

(encapsulate
    ()
  
  (local
   (encapsulate
       ()

     (defun mul3 (a b c)
       (* a b c))
     
     (defthmd introduce-product-lemma
       (implies
	(and
	 (integerp I)
	 (integerp C)
	 (integerp Qd)
	 (integerp Qp)
	 (posnatp p)
	 (posnatp d))
	(equal (< (* I Qd) (* C Qp))
	       (< (mul3 I p (* d Qd)) (mul3 C d (* p Qp))))))
     
     (defthmd introduce-multiple-product
       (implies
	(and
	 (integerp i)
	 (integerp c)
	 (natp n)
	 (posnatp d)
	 (posnatp p))
	(equal (< (* I (NONNEGATIVE-INTEGER-QUOTIENT N D))
		  (* C (NONNEGATIVE-INTEGER-QUOTIENT N P)))
	       (< (* I P (+ N (- (NONNEG-INT-MOD N D))))
		  (* C D (+ N (- (NONNEG-INT-MOD N P)))))))
       :hints (("Goal" :do-not '(preprocess)
		:in-theory (e/d (NONNEGATIVE-INTEGER-QUOTIENT-TO-NONNEG-INT-MOD)
				nil)
		:use (:instance introduce-product-lemma
				(Qd (NONNEGATIVE-INTEGER-QUOTIENT N D))
				(Qp (NONNEGATIVE-INTEGER-QUOTIENT N P))))))
     
     (defthm mod-is-less-than-sum
       (implies
	(and
	 (natp n)
	 (natp a)
	 (posnatp d)
	 (< D A))
	(< (NONNEG-INT-MOD A D) (+ A N))))
     
     ))

  (defthm posnatp-a-posnat
    (implies
     (and
      (posnatp a)
      (posnatp p)
      (posnatp d)
      (< d p)
      (equal (nonneg-int-mod a p) 0)
      (equal (nonneg-int-gcd d p) 1))
     (posnatp (a-posnat A p d)))
    :rule-classes (:rewrite
		   (:forward-chaining :trigger-terms ((a-posnat a p d))))
    :hints (("Goal" :do-not-induct t
	     :in-theory (e/d (ideal-product-to-nonneg-int-gcd
			      nested-ideal-product-to-nonneg-int-gcd
			      introduce-multiple-product)
			     (REMOVE-WEAK-INEQUALITIES)))))

  )
     
(encapsulate
    ()

  (local
   (defthmd n-divisible-by-p-and-d-implication
     (implies
      (and
       (natp n)
       (natp p)
       (natp d)
       (equal (nonneg-int-mod n p) 0)
       (equal (nonneg-int-mod n d) 0))
      (equal (* (* d (nonnegative-integer-quotient n d)) (ideal-k d p))
	     (* (* p (nonnegative-integer-quotient n p)) (ideal-k d p))))
     :hints (("Goal" :in-theory (enable NONNEGATIVE-INTEGER-QUOTIENT-TO-NONNEG-INT-MOD)))))

  (defthmd express-nonnegative-integer-quotient-as-a-multiple-of-d
    (implies
     (and
      (equal (nonneg-int-gcd d p) 1)
      (equal (nonneg-int-mod n d) 0)
      (equal (nonneg-int-mod n p) 0)
      (natp n)
      (natp p)
      (natp d))
     (equal (nonnegative-integer-quotient n p) (* d (a-posnat n p d))))
    :hints (("Goal" :do-not-induct t
	     :use n-divisible-by-p-and-d-implication
	     :in-theory (enable nested-ideal-product-to-nonneg-int-gcd))))
   
  )

(in-theory (disable a-posnat))

(encapsulate
    ()

  (local 
   (set-default-hints '((nonlinearp-default-hint++ 
			 id stable-under-simplificationp
			 hist nil))))
  
  (defthm ideal-k-product-bound
    (implies
     (and
      (pnunitp d)
      (pnunitp p)
      (posnatp I))
     (< (IDEAL-K D P) (* D I)))
    :rule-classes (:rewrite :linear))
  
  )

(defthm quotient-less-than-ideal-is-not-divisible
  (implies
   (and
    (<= (nonnegative-integer-quotient n p) (ideal-k d p))
    (pnunitp p)
    (pnunitp d)
    (posnatp n)
    (< d p)
    (equal (nonneg-int-gcd d p) 1)
    (equal (nonneg-int-mod n p) 0))
   (not (equal (nonneg-int-mod n d) 0)))
  :hints (("Goal" :in-theory (enable express-nonnegative-integer-quotient-as-a-multiple-of-d)
	   :do-not-induct t)))

(defthm quotient-less-than-ideal-is-not-divisible-int-mod-equivp
  (implies
   (and
    (<= (nonnegative-integer-quotient n p) (ideal-k d p))
    (pnunitp p)
    (pnunitp d)
    (posnatp n)
    (< d p)
    (equal (nonneg-int-gcd d p) 1)
    (int-mod-equivp n 0 p))
   (not (int-mod-equivp n 0 d)))
  :hints (("Goal" :use quotient-less-than-ideal-is-not-divisible
	   :in-theory (e/d (NONNEG-INT-MOD-AS-INT-MOD
			    equal-int-mod-to-int-mod-equivp)
			   (quotient-less-than-ideal-is-not-divisible)))))

(defthm plus-one-of-quotient-decreases-d
  (implies
   (and
    (natp n)
    (pnunitp p)
    (pnunitp d)
    (< d p)
    (not (equal (nonneg-int-mod n d) 0))
    (equal (nonneg-int-mod n p) 0))
   (< (int-mod (+ d (* d (NONNEGATIVE-INTEGER-QUOTIENT N D))) p)
      d))
  :hints (("Goal" :do-not-induct t
	   :in-theory (enable 
		       equal-int-mod-to-int-mod-equivp
		       NONNEG-INT-MOD-AS-INT-MOD
		       NONNEGATIVE-INTEGER-QUOTIENT-TO-NONNEG-INT-MOD)
	   )))

(defthm nonneg-int-gcd-nonneg-int-mod
  (implies
   (posnatp p)
   (equal (nonneg-int-gcd (nonneg-int-mod x p) p)
	  (nonneg-int-gcd x p)))
  :hints (("Goal" :expand (NONNEG-INT-GCD X P)
	   :in-theory (enable COMMUTATIVITY-OF-NONNEG-INT-GCD))))

(defthm nonneg-int-gcd-int-mod
  (implies
   (and
    (natp x)
    (posnatp p))
   (equal (nonneg-int-gcd (int-mod x p) p)
	  (nonneg-int-gcd x p)))
  :hints (("Goal" :use nonneg-int-gcd-nonneg-int-mod
	   :in-theory (enable NONNEG-INT-MOD-AS-INT-MOD))))

(defund pm1 (p)
  (- p 1))

(defthmd gcd-p-minus-1-to-gcd-int-mod-pm1
  (implies
   (and
    (natp p)
    (natp x)
    (< x p))
   (equal (nonneg-int-gcd (+ p (- x)) p)
	  (nonneg-int-gcd (int-mod (* (pm1 p) x) p) p)))
  :hints (("Goal" :in-theory (e/d (NONNEG-INT-MOD-AS-INT-MOD)
				  nil)
	   :expand ((nonneg-int-gcd (+ p (- x)) p)
		    (nonneg-int-gcd x p)))
	  (and stable-under-simplificationp
	       '(:in-theory (enable COMMUTATIVITY-OF-NONNEG-INT-GCD pm1)))))

(defthm natp-pm1
  (implies
   (posnatp p)
   (natp (pm1 p)))
  :hints (("Goal" :in-theory (enable pm1))))

(defthm nonneg-int-gcd-pm1
  (implies
   (posnatp p)
   (equal (nonneg-int-gcd (pm1 p) p) 1))
  :hints (("Goal" :expand ((nonneg-int-gcd (+ -1 p) p)
			   (NONNEG-INT-GCD P (+ -1 P))
			   (NONNEG-INT-MOD P (+ -1 P))
			   (NONNEG-INT-MOD 1 (+ -1 P)))
	   :in-theory (enable pm1))))

;; This opens the door for some congruence proofs ..
(defthmd nonneg-int-gcd-drop-int-mod
  (implies
   (and
    (natp n)
    (not (zp p)))
   (equal (nonneg-int-gcd (int-mod n p) p)
	  (nonneg-int-gcd n p)))
  :hints (("Goal" :in-theory (enable NONNEG-INT-MOD-AS-INT-MOD)
	   :expand ((nonneg-int-gcd (int-mod n p) p)
		    (nonneg-int-gcd n p)))))

(defthm gcd-p-minus-1-to-gcd-pm1
  (implies
   (and
    (natp p)
    (natp x)
    (< x p))
   (equal (nonneg-int-gcd (+ p (- x)) p)
	  (nonneg-int-gcd (* x (pm1 p)) p)))
  :hints (("Goal" :in-theory (enable 
			      gcd-p-minus-1-to-gcd-int-mod-pm1
			      nonneg-int-gcd-drop-int-mod
			      ))))

