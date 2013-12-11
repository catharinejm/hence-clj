(ns hence-clj.core
  (:require [clojure.tools.reader :as r]
            [clojure.set :as set]
            [clojure.pprint :as pp]
            [clojure.repl :as repl :refer [doc]])
  (:refer-clojure :exclude [cons atom? list? pop])
  (:alias core clojure.core)
  (:import [java.io Writer]))

(declare pair?)

(defprotocol IPair
  (car [p])
  (cdr [p])
  (internalString [p]))

(defmacro caar [p]
  `(car (car ~p)))
(defmacro cadr [p]
  `(car (cdr ~p)))
(defmacro cdar [p]
  `(cdr (car ~p)))
(defmacro cddr [p]
  `(cdr (cdr ~p)))

(defrecord Pair [a d]
  IPair
  (car [p] a)
  (cdr [p] d)
  (internalString [p]
    (let [str-a (if (nil? a) "nil" (str a))]
      (cond
       (nil? d) str-a
       (pair? d) (str str-a " " (internalString d))
       :else (str str-a " . " d))))

  Object
  (toString [p]
    (str "(" (internalString p) ")")))

(defmethod core/print-method Pair
  [p ^Writer w]
  p(.write w (str p)))

(defn pair? [f]
  (satisfies? IPair f))
(defmacro atom? [f]
  `(not (pair? ~f)))

(defmulti eq? (fn [x _] (type x)))
(defmethod eq? clojure.lang.Symbol
  [x y]
  (= x y))

(defmethod eq? :default
  [x y]
  (identical? x y))

(defn list? [f]
  (cond
   (nil? f) true
   (pair? f) (recur (cdr f))
   :else false))

(def registers (atom {}))

(add-watch registers :trace
           (fn [k r os ns]
             (pp/with-pprint-dispatch print (pp/pprint ns))))

(def reg-name? keyword?)

(defn reg
  ([] (reg (gensym)))
  ([n] (-> n name keyword)))

(def sp :sp)

(defn reg-vals*
  ([regs]
     (reg-vals* @registers regs))
  ([reg-map regs]
     (map reg-map regs)))

(defmacro update-reg [regs r v]
  `(if (and (nil? ~v))
     (dissoc ~regs ~r)
     (assoc ~regs ~r ~v)))

(defn swap* [regs r1 r2]
  (assert (not (eq? r1 r2)) "Cannot swap a register with itself")
  (let [[v1 v2] (reg-vals* regs [r1 r2])]
    (-> regs
        (update-reg r1 v2)
        (update-reg r2 v1))))

(defn swap [r1 r2]
  (swap! registers swap* r1 r2))

(defn swap-car* [regs r1 r2]
  (assert (not (eq? r1 r2)) "Cannot swap a register with itself")
  (let [[v1 v2] (reg-vals* regs [r1 r2])]
    (assert (pair? v2) "Second argument must be a pair")
    (let [new-pair (->Pair v1 (cdr v2))]
      (-> regs
          (update-reg r1 (car v2))
          (assoc r2 new-pair)))))
 
(defn swap-car [r1 r2]
  (swap! registers swap-car* r1 r2))

(defn swap-cdr* [regs r1 r2]
  (assert (not (eq? r1 r2)) "Cannot swap a register with itself")
  (let [[v1 v2] (reg-vals* regs [r1 r2])]
    (assert (pair? v2) "Second argument must be a pair")
    (let [new-pair (->Pair (car v2) v1)]
      (-> regs
          (update-reg r1 (cdr v2))
          (assoc r2 new-pair)))))

(defn swap-cdr [r1 r2]
  (swap! registers swap-cdr* r1 r2))

(defn sreg-to-val* [regs r1 val]
  (assert (atom? val) "Cannot assign a non-atom directly")
  (let [old-val (regs r1)]
    (assert (atom? old-val) "Cannot overwrite a register referencing a pair")
    (update-reg regs r1 val)))

(defn sreg-to-reg* [regs r1 r2]
  (let [v2 (regs r2)]
    (sreg-to-val* regs r1 v2)))

(defn sreg [r1 val]
  (let [swap-fn (if (reg-name? val)
                  sreg-to-reg*
                  sreg-to-val*)]
    (swap! registers swap-fn r1 val)))

(defn cons* [regs r1 r2]
  (assert (not (eq? r1 r2)) "Cannot cons a register to itself")
  (let [[v1 v2] (reg-vals* [r1 r2])]
    (assert (or (nil? v2) (pair? v2)) "Second argument must be a pair or null")
    (-> regs
        (assoc r2 (->Pair v1 v2))
        (dissoc r1))))

(defn cons [r1 r2]
  (swap! registers cons* r1 r2))
(def push cons)

(defn pop* [regs r1 r2]
  (let [[v1 v2] (reg-vals* regs [r1 r2])]
    (assert (nil? v1) "Register to pop into must be null")
    (assert (pair? v2) "Register to pop from must be a pair")
    (-> regs
        (update-reg r1 (car v2))
        (update-reg r2 (cdr v2)))))

(defn pop [r1 r2]
  (swap! registers pop* r1 r2))

(defn free* [regs r1]
  (let [v1 (regs r1)]
    (if-not (nil? v1)
      (if (atom? v1)
        (sreg* regs r1 nil)
        (let [t1 :t1]
          (push* regs t1 sp) (pop* regs t1 r1)
          (free* regs r1)
          (swap* regs t1 r1) (free* regs r1)
          (pop* regs t1 sp))))))

(defn free [r1]
  (swap! registers free* r1))

(defn copy* [regs r1 r2]
  (let [[v1 v2] (reg-vals* regs [r1 r2])]
    (assert (nil? v2) "Cannot copy into populated register")
    (if (atom? v1)
      (sreg* regs r2 r1)
      (let [t1 :t1
            t2 :t2]
        (-> regs
            (push* t1 sp) (push* t2 sp)
            (pop* t1 r1) (copy* r1 r2)
            (swap* t1 r1) (swap* t2 r2) (copy* r1 r2)
            (swap* t1 r1) (swap* t2 r2) (push* t1 r1) (push* t2 r2)
            (pop* t2 sp) (pop* t1 sp))))))

(defn copy [r1 r2]
  (swap! registers copy* r1 r2))

(defmacro prog1 [form & forms]
  `(let [ret# ~form]
     ~@forms
     ret#))

(defn equal? [r1 r2]
  (or (and (atom? r1) (atom? r2) (eq? r1 r2))
      (and (not (atom? r1)) (not (atom? r2))
           (let [t1 (reg "t1")
                 t2 (reg "t2")]
             (push t1 sp) (push t2 sp) (pop t1 r1) (pop t2 r2)
             (prog1 (and (equal? r1 r2)
                         (do (swap t1 r1) (swap t2 r2)
                             (prog1 (equal? r1 r2)
                                    (swap t1 r1) (swap t2 r2))))
                    (push t1 r1) (push t2 r2) (pop t2 sp) (pop t2 sp))))))
