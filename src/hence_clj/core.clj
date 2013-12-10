(ns hence-clj.core
  (:require [clojure.tools.reader :as r]
            [clojure.set :as set]
            [clojure.pprint :as pp]
            [clojure.repl :as repl :refer [doc]])
  (:refer-clojure :exclude [cons atom? list?])
  (:alias core clojure.core)
  (:import [java.io Writer]))

(declare pair? null?)

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
    (cond
     (null? d) (str a)
     (pair? d) (str a " " (internalString d))
     :else (str a " . " d)))

  Object
  (toString [p]
    (str "(" (internalString p) ")")))

(defmethod core/print-method Pair
  [p ^Writer w]
  (.write w (str p)))
(defmethod core/print-method :free-list
  [p ^Writer w]
  (.write w "([free list] ...)"))

(declare alloc-obj)
(defn cons [a d]
  (let [d (if (and (core/list? d) (empty? d)) nil d)]
    (alloc-obj (->Pair a d))))

(defn pair? [f]
  (satisfies? IPair f))
(defmacro atom? [f]
  `(not (pair? ~f)))
(def null? nil?)

(defmulti eq? (fn [x _] (type x)))
(defmethod eq? clojure.lang.Symbol
  [x y]
  (= x y))

(defmethod eq? :default
  [x y]
  (identical? x y))

(defn list? [f]
  (cond
   (null? f) true
   (pair? f) (recur (cdr f))
   :else false))

(defn free-list []
  (with-meta
    (reify IPair
      (car [p] nil)
      (cdr [p] (free-list)))
    {:type :free-list}))

(def registers (atom {:fr (free-list)
                      :sp nil}))

(def obj-space (atom #{}))

(defn alloc-obj* [os o]
  (assert (not (contains? os o)) "Object already exists!")
  (conj os 1))

(defn alloc-obj [o]
  (swap! obj-space alloc-obj* o)
  o)

(defn free-obj* [os o]
  (assert (contains? os o) "Object does not exist!")
  (set/difference os #{o}))

(defn free-obj [o]
  (swap! obj-space free-obj* o))

(def reg-name? keyword?)

(defn reg-vals*
  ([regs]
     (reg-vals* @registers regs))
  ([reg-map regs]
     (map reg-map regs)))

(defn swap* [regs r1 r2]
  (let [[v1 v2] (reg-vals* regs [r1 r2])]
    (assert (not (eq? v1 v2) "Cannot swap a value with itself"))
    (assoc regs r1 v2 r2 v1)))

(defn swap [r1 r2]
  (swap! registers swap* r1 r2))

(defn swap-car* [regs r1 r2]
  (let [[v1 v2] (reg-vals* regs [r1 r2])]
    (assert (not (eq? v1 v2)) "Cannot swap a value with itself")
    (assert (pair? v2) "Second argument must be a pair")
    (let [new-list (cons v1 (cdr v2))]
      (assoc regs r1 (car v2) r2 new-list))))
 
(defn swap-car [r1 r2]
  (swap! registers swap-car* r1 r2))

(defn swap-cdr* [regs r1 r2]
  (let [[v1 v2] (reg-vals* regs [r1 r2])]
    (assert (not (eq? v1 v2)) "Cannot swap a value with itself")
    (assert (pair? v2) "Second argument must be a pair")
    (let [new-pair (cons (car v2) v1)]
      (assoc regs r1 (cdr v2) r2 new-pair))))

(defn swap-cdr [r1 r2]
  (swap! registers swap-cdr* r1 r2))

(defn sreg-to-val* [regs r1 val]
  (assert (atom? val) "Cannot assign a non-atom directly")
  (let [old-val (regs r1)]
    (assert (atom? old-val) "Cannot overwrite a list register")
    (assoc regs r1 val)))

(defn sreg-to-reg* [regs r1 r2]
  (let [v2 (regs r2)]
    (sreg-to-val* regs r1 v2)))

(defn sreg [r1 val]
  (let [swap-fn (if (reg-name? val)
                  sreg-to-reg*
                  sreg-to-val*)]
    (swap! registers swap-fn r1 val)))
