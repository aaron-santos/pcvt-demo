(ns los.core
  (:require clojure.pprint
            clojure.set
            [clojure.walk :as w]
            [clojure.zip :as z]
            [quil.core :as q]
            [quil.middleware :as m]))

(def ^:dynamic *width* 600)
(def ^:dynamic *height* 600)
(def ^:dynamic *cell-width* 10)
(def ^:dynamic *cell-height* 10)

(def center [(/ *width* 2) (/ *height* 2)])
(def cell-center [(/ *width* 2 *cell-width*) (/ *height* 2 *cell-height*)])

(defmacro log-time
  "Log the time it takes to execute body."
  [msg & body]
  `(time
     (let [result# (do ~@body)]
       (println ~msg)
       result#)))

(defn setup []
  (q/smooth)
  (q/frame-rate 60)
  (vec (repeat (/ *height* *cell-height*) (vec (repeat (/ *width* *cell-width*) false)))))

(defn draw-grid [size]
  (q/stroke 80)
  (q/stroke-weight 1)
  ;; draw vertical lines
  (doseq [x (range 0 *width* size)]
    (q/line x 0 x *height*))
  ;; draw horizontal lines
  (doseq [y (range 0 *height* size)]
    (q/line 0 y *width* y))
  nil)

(def line-segment (memoize
  (fn
   [start end]
   (if (= start end)
      []
      (let [[x1 y1] start
            [x2 y2] end
            xdiff (- x2 x1)
            ydiff (- y2 y1)
            maxdiff (max (Math/abs xdiff) (Math/abs ydiff))
            dx (/ xdiff maxdiff)
            dy (/ ydiff maxdiff)]
        (map (fn [i] [(Math/round (double (+ x1 (* i dx)))) (Math/round (double (+ y1 (* i dy))))])
            (range (inc maxdiff))))))))


(def line-segment-fast-without-endpoints (memoize
  (fn [start end]
    "(line-segment-fast [1 1] [5 4])"
    (let [[ox oy] start
          [dx dy] end]
      (rest
        (butlast
          (map (fn [[x y]] [(+ ox x) (+ oy y)])
               (line-segment [0 0] [(- dx ox) (- dy oy)]))))))))

(defn circle-points [x0 y0 radius]
  (letfn [(points [x y m]
            (let [x+   (+ x0 x)
                  x-   (- x0 x)
                  y+   (+ y0 y)
                  y-   (- y0 y)
                  x0y+ (+ x0 y)
                  x0y- (- x0 y)
                  xy0+ (+ y0 x)
                  xy0- (- y0 x)
                  xys  [[x+ y+]
                        [x+ y-]
                        [x- y+]
                        [x- y-]
                        [x0y+ xy0+]
                        [x0y+ xy0-]
                        [x0y- xy0+]
                        [x0y- xy0-]]
                  [y m] (if (pos? m)
                            [(dec y) (- m (* 8 y))]
                            [y m])]
                (if (<= x y)
                 (concat xys
                         (points (inc x)
                                 y
                                 (+ m 4 (* 8 x))))
                 xys)))]
    (points 0 radius (- 5 (* 4 radius)))))

(defn square-points [x0 y0 radius]
  (letfn [(points [x y m]
            (let [x+   (+ x0 x)
                  x-   (- x0 x)
                  y+   (+ y0 y)
                  y-   (- y0 y)
                  x0y+ (+ x0 y)
                  x0y- (- x0 y)
                  xy0+ (+ y0 x)
                  xy0- (- y0 x)
                  xys  [[x+ y+]
                        [x+ y-]
                        [x- y+]
                        [x- y-]
                        [x0y+ xy0+]
                        [x0y+ xy0-]
                        [x0y- xy0+]
                        [x0y- xy0-]]
                  oy    y
                  om    m
                  [y m] (if (pos? m)
                            [(dec y) (- m (* 8 y))]
                            [y m])]
                (if (<= x y)
                 (concat xys
                         (points (if (pos? om)
                                   x
                                   (inc x))
                                 (if (pos? m)
                                   y
                                   oy)
                                 (+ m 4 (* 8 x))))
                 xys)))]
    (points 0 radius (- 5 (* 4 radius)))))

;(defn add-points [x0 y0 points]
;  (reduce (fn [[x y]]
;            (if (not-any? adjacent? points)

(defn distance-sq
  [p1 p2]
  (let [sq (fn [x] (* x x))]
  (+ (sq (- (:x p1) (:x p2)))
     (sq (- (:y p1) (:y p2))))))

(defn farther-than?
  "Are the two points farther in distance than l?"
  ([p1 p2 l]
  (> (distance-sq p1 p2) (* l l)))
  ([x1 y1 x2 y2 l]
  (if (or (> (Math/abs (- x1 x2)) l)
          (> (Math/abs (- y1 y2)) l))
    true
    (> (distance-sq {:x x1 :y y1} {:x x2 :y y2}) (* l l)))))

(defn points-in-circle [x0 y0 radius]
  (let [min-x (- x0 radius)
        max-x (+ x0 radius)
        min-y (- y0 radius)
        max-y (+ y0 radius)]
    (remove (fn [[x y]] (farther-than? x0 y0 x y radius))
            (for [x (range min-x max-x)
                  y (range min-y max-y)]
              [x y]))))


(defn remove-points-beyond-radius
  [x0 y0 r segments]
  (map (fn [segment]
         (remove (fn [[x y]]
                   (farther-than? x0 y0 x y r))
                 segment))
       segments))

(defn paths->trie [segments]
  (reduce (fn [tree segment]
            (assoc-in tree segment {}))
          {}
          segments))


(defn trie->paths [trie]
  (reduce
    (fn [paths [k subtree]]
      (if (empty? subtree)
        (conj paths (list k))
        (concat
          paths
          (map (fn [path]
                 (cons k path))
                 (trie->paths subtree)))))
    (list)
    trie))

(defn replace-vals [kvs m]
  (reduce-kv (fn [r k v]
               (assoc r k (get kvs k v)))
             {}
             m))

;; cull subtries with parent keys in the set `exclude`.
(defn cull-trie [exclude trie]
  (let [replacement-nodes (zipmap exclude (repeat {}))]
    (w/prewalk (fn [m] (if (and (map? m)
                                (some #(contains? replacement-nodes %) (keys m)))
                         (replace-vals replacement-nodes m)
                         m))
               trie)))

(defn trie->keys [trie]
  (loop [t  (z/zipper map? vals #(zipmap (keys %1) %2) trie)
         ks #{}]
    (cond
      (z/end? t) ks
      (empty? (z/node t)) (recur (z/next t) ks)
      (z/branch? t) (let [new-keys (set (keys (z/node t)))]
        (recur (z/next t) (clojure.set/union new-keys ks)))
      :leaf
      (println "got leaf" (z/node t)))))

;;(println "(trie->paths {:a {}})")
;;(println (trie->paths {:a {}}))
;;(println "(trie->paths {:a {:b {}}})")
;;(println (trie->paths {:a {:b {}}}))
;;(println "(trie->paths {:a {:b {:c {}}}})")
;;(println (trie->paths {:a {:b {:c {}}}}))
;;(println "(trie->paths {:a {:b {:c {} :d {}} :e { :f {} :g {}} :f {}}})")
;;(println (trie->paths {:a {:b {:c {} :d {}} :e { :f {} :g {}} :f {}}}))

;(println (segments->tree (trie->paths {:a {:b {:c {} :d {}} :e { :f {} :g {}} :f {}}})))

(def r->c-points
  (apply hash-map (mapcat (fn [k] [k (circle-points 0 0 k)]) (range 30))))

(def r->trie
  (apply hash-map (mapcat (fn [k]
                         (let [c-points (square-points 0 0 k)
                               segments     (remove empty?
                                              (map #(line-segment [0 0] %)
                                                   c-points))
                               ;; truncate segments to radius
                               segments (remove-points-beyond-radius 0 0 k segments)
                               ;_ (println "segments")
                               ;_ (clojure.pprint/pprint segments)
                               num-segments (count segments)
                               trie         (paths->trie segments)]
                            [k trie]))
                        (range 30))))
                                   
(defn collision-point-set [state]
  (set
    (filter (complement nil?)
            (for [y (range (count state))
                  x (range (count (first state)))]
              (when (get-in state [y x])
                [x y])))))

(defn draw [state]
  (q/color-mode :rgb 255 255 255)
  (q/background 10)
  (draw-grid 10)
  (q/stroke 0)
  (q/stroke-weight 0)

  (let [diam 300
       [cx cy] center
       [ccx ccy] cell-center]
    ;; color middle cell red
    (q/fill 200 0 0)
    (q/rect cx cy 8 8)
    ;; draw fine red circle over shaded cells
    (q/stroke 200 0 0)
    (q/fill 0 0 0 0)
    (q/ellipse (+ 5 cx) (+ cy 5) diam diam)
    (let [;c-points (points-in-circle ccx ccy 25)
          r (mod (int (/ (q/frame-count) 10)) 30)
          r 20
          ;c-points (circle-points ccx ccy (mod (int (/ (q/frame-count) 10)) 25))
          c-points (get r->c-points r)
          ;_ (println "points-in-circle" c-points)
          ;_ (println "circle-points" cc-points)
          segments    (remove empty?
                         (map (fn [[x y]]
                                (line-segment [ccx ccy] [(+ x ccx) (+ y ccy)]))
                              c-points))
          trie         (get r->trie r)
          ;_ (println "trie")
          ;_ (clojure.pprint/pprint trie)
          collision-points (set (map (fn [[x y]] [(- x ccx) (- y ccy)])
                                     (collision-point-set state)))
          ;_ (println "collision-points" collision-points)
          trie         (log-time "cull-trie" (cull-trie collision-points trie))
          segments (trie->paths trie)
          num-segments (count segments)
          ;_ (println "culled-trie" trie)
          visible-points (remove nil? (trie->keys trie))]
      ;(println "visible points" visible-points)
      ;; print visible cells
      (q/fill 90 90 90 255)
      (doseq [[x y] visible-points]
          ;(println "visible-point" x y)
          (q/rect (* (+ x ccx) *cell-width*) (* (+ y ccy) *cell-height*) *cell-width* *cell-height*))
      ;; shade cells to form circle
      (q/fill 90 180 90 255)
      (doseq [[x y] c-points]
        ;(println "perimeter cell" x y)
        (q/rect (+ (* (+ x ccx) *cell-width*) 1)  (+ (* (+ y ccy) *cell-height*) 1)  9 9))

      ;; draw blocking cells
      (q/fill 190 190 190 255)
      (doseq [[y line] (map-indexed vector state)]
        (doseq [[x cell] (map-indexed vector line)]
          (when cell
            ;(println "Drawing rect" (* x *cell-width*) (* y *cell-height*) *cell-width* *cell-height* "for cell" cell)
            (q/rect (* x *cell-width*) (* y *cell-height*) *cell-width* *cell-height*))))
    
        
      ;; print line segments
      ;(println "segments")
      ;(clojure.pprint/pprint (segments->tree segments))
      (q/stroke-weight 2)
      (q/color-mode :hsb num-segments 1.0 1.0)
      (doseq [[idx segment] (map-indexed vector segments)]
        (doseq [[[x0 y0] [x1 y1]]  (partition 2 (-> (interleave segment segment) rest butlast))]
          (q/stroke idx 1.0 0.7)
          (q/line (+ (* 10 x0) 5 cx)
                  (+ (* 10 y0) 5 cy)
                  (+ (* 10 x1) 5 cx)
                  (+ (* 10 y1) 5 cy)))))))

(defn on-click [state event]
  (let [{x :x y :y} event
        cellx (int (/ x *cell-width*))
        celly (int (/ y *cell-height*))
        new-state (update-in state [celly cellx] not)]
    (println "click @" x y cellx celly)
    (print "collision-point-set" (collision-point-set new-state))
    new-state))
    

(q/defsketch example
  :title "Oh so many grey circles"
  :middleware [m/fun-mode]
  :setup setup
  :draw draw
  :mouse-clicked on-click
  :size [*width* *height*])

(defn -main [] nil)
