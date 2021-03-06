(ns los.core
  (:require clojure.pprint
            clojure.set
            [clojure.walk :as w]
            [clojure.zip :as z]
            [quil.core :as q]
            [quil.middleware :as m])
  (:import [javax.swing JOptionPane]))

(def ^:dynamic *width* 600)
(def ^:dynamic *height* 600)
(def ^:dynamic *cell-width* 10)
(def ^:dynamic *cell-height* 10)

(def ^:dynamic *cells-width* (/ *width* *cell-width*))
(def ^:dynamic *cells-height* (/ *height* *cell-height*))

(def radius (atom 20))
; one of :hide :show :strobe
(def path-mode (atom :hide :validator #(contains? #{:hide :show :strobe} %)))
(def next-path-mode {:hide :show
                     :show :strobe
                     :strobe :hide})
;; gold/brown theme
;(def background-rgb           [ 10  10 10 255])
;(def grid-rgb                 [ 80  80 80 255])
;(def center-cell-rgb          [200   0  0 255])
;(def visible-non-blocking-rgb [101 100 20 255])
;(def visible-blocking-rgb     [158 158 86 255])
;(def invisible-blocking-rgb   [ 66  66 66 255])

;; light theme
(def background-rgb           [255 255 255 255])
(def grid-rgb                 [210 210 250 255])
(def center-cell-rgb          [  0  20  90 255])
(def visible-non-blocking-rgb [181 190 220 255])
(def visible-blocking-rgb     [118 118 146 255])
(def invisible-blocking-rgb   [ 46  46  76 255])

(def center [(/ *width* 2) (/ *height* 2)])
(def cell-center [(/ *width* 2 *cell-width*) (/ *height* 2 *cell-height*)])

(defmacro log-time
  "Log the time it takes to execute body."
  [msg & body]
  `(time
     (let [result# (do ~@body)]
       (println ~msg)
       result#)))

(def empty-grid
  (vec (repeat (/ *height* *cell-height*) (vec (repeat (/ *width* *cell-width*) false)))))
  
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
        (map (fn [i]
          (let [x (double (+ x1 (* i dx)))
                y (double (+ y1 (* i dy)))]
          [(if (pos? x)
              (Math/round x)
              (- (Math/round (- x))))
           (if (pos? y)
              (Math/round y)
              (- (Math/round (- y))))]))
            (range (inc maxdiff))))))))

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

(defn trie->zipper [exclude-subtrie? trie]
  (z/zipper ; branch?
             map?
             ; children
             (fn [node]
               (reduce-kv (fn [children k subtree]
                            (if (exclude-subtrie? k)
                              children
                              (conj children subtree)))
                          []
                          node))
             ; make node
             #(zipmap (keys %1) %2)
             ; root
             trie))

(defn trie->zipper-ext [exclude-subtrie? trie]
  (z/zipper
    ; branch?
    (fn [x] (or (map? x) (map? (second x))))
    ; children
    (fn [x] (seq 
              (reduce (fn [children [k subtree]]
                           (if (exclude-subtrie? k)
                                          (conj children [k {}])
                                          (conj children [k subtree])))
                         []
                         (if (map? x)
                              (map vec x)
                              (second x)))))
    ; make node
    (fn [x children]
      (if (map? x)
        (into {} children)
        (assoc x 1 (into {} children))))
    trie))

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

;;;;;;;;;;;;;;;;;
;; No trie-zipper->paths. It is not possible/sane to do this.
;;;;;;;;;;;;;;;;;

(defn trie-zipper-ext->paths [trie-zipper]
  (loop [t     (z/next trie-zipper)
         paths #{}]
    (cond
      (z/end? t)
         paths
      (empty? (z/node t))
        (recur (z/next t) paths)
      (z/branch? t)
        (if (empty? (second (z/node t)))
          (let [path (->> t z/path rest (map first))]
            (recur (z/next t) (conj paths (conj (vec path) (first (z/node t))))))
          (recur (z/next t) paths))
      :leaf
        (println "got leaf" (z/node t)))))

(defn trie-zipper->keys [trie-zipper]
  (loop [t  trie-zipper
         ks #{}]
    (cond
      (z/end? t) ks
      (empty? (z/node t)) (recur (z/next t) ks)
      (z/branch? t) (let [new-keys (keys (z/node t))]
        (recur (z/next t) (reduce conj ks new-keys)))
      :leaf
      (println "got leaf" (z/node t)))))

(defn trie-zipper-ext->keys [trie-zipper]
  (loop [t  (z/next trie-zipper)
         ks #{}]
    (cond
      (z/end? t) ks
      (empty? (z/node t)) (recur (z/next t) ks)
      (z/branch? t) (let [new-key (first (z/node t))]
        (recur (z/next t) (conj ks new-key)))
      :leaf
      (println "got leaf" (z/node t)))))

(def r->trie
  (apply hash-map (mapcat (fn [k]
                         (let [c-points (square-points 0 0 k)
                               segments     (remove empty?
                                              (map (fn [[x y]] (line-segment [0 0] [x y]))
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

(defn draw-grid [size]
  (apply q/stroke grid-rgb)
  (q/stroke-weight 1.0)
  ;; draw vertical lines
  (doseq [x (range 0 *width* size)]
    (q/line x 0 x *height*))
  ;; draw horizontal lines
  (doseq [y (range 0 *height* size)]
    (q/line 0 y *width* y))
  nil)

(defn center-on-screen [points]
  (let [[center-x center-y] cell-center]
    (map (fn [[x y]] [(+ x center-x) (+ y center-y)]) points)))

(defn draw-cells [xys color]
  (apply q/fill color)
  (doseq [[x y] xys]
    (q/rect (* x *cell-width*) (* y *cell-height*) *cell-width* *cell-height*)))

(defn setup []
  (q/smooth)
  (q/frame-rate 60)
  empty-grid)

(defn draw [state]
  (q/color-mode :rgb 255 255 255)
  (apply q/background background-rgb)
  (let [;; center of screen in pixels
        [cx cy] center
        ;; center of screen in cell-space
        [ccx ccy] cell-center
        ;; view distance
        r @radius
        ;; unculled visibility trie
        trie   (get r->trie r)
        #_#_ _ (println "trie")
        #_#_ _ (clojure.pprint/pprint trie)
        ;; collision points in player-cell-space
        collision-points (set (map (fn [[x y]] [(- x ccx) (- y ccy)])
                                   (collision-point-set state)))
        #_#_ _ (println "collision-points" collision-points)
        ;; culled visibility trie zipper
        tz     (case @path-mode
                 :hide   (trie->zipper     (fn [xy] (contains? collision-points xy)) trie)
                 :show   (trie->zipper-ext (fn [xy] (contains? collision-points xy)) trie)
                 :strobe (trie->zipper-ext (fn [xy] (contains? collision-points xy)) trie))
        #_#_ _ (println "culled-trie" tz)
        visible-points (set (remove nil? (case @path-mode
                                           :hide   (trie-zipper->keys tz)
                                           :show   (trie-zipper-ext->keys tz)
                                           :strobe (trie-zipper-ext->keys tz))))]
    ;; print visible cells
    (draw-cells (center-on-screen visible-points) visible-non-blocking-rgb)

    ;; color middle cell red
    (apply q/fill center-cell-rgb)
    (q/rect cx cy 8 8)

    ;; draw blocking cells
    (doseq [[y line] (map-indexed vector state)]
      (doseq [[x cell] (map-indexed vector line)]
        (when cell
          (if (contains? visible-points [(- x ccx) (- y ccy)])
            (apply q/fill visible-blocking-rgb)
            (apply q/fill invisible-blocking-rgb))
          ;(println "Drawing rect" (* x *cell-width*) (* y *cell-height*) *cell-width* *cell-height* "for cell" cell)
          (q/rect (* x *cell-width*) (* y *cell-height*) *cell-width* *cell-height*))))
    
    (draw-grid 10)
    (q/stroke 0.1 0.2 0.3)
    (q/stroke-weight 1.5)
      
    ;; print line segments
    (when (contains? #{:show :strobe} @path-mode)
      (let [;; culled trie segments in player-cell-space
            segments (trie-zipper-ext->paths tz)
            num-segments (count segments)]
        (q/color-mode :hsb num-segments 1.0 1.0)
        (doseq [[idx segment] (map-indexed vector segments)]
          (when (or (= @path-mode :show)
                    (and (= (@path-mode :strobe))
                         (= idx (mod (long (/ (q/frame-count) 10)) num-segments))))
            (doseq [[[x0 y0] [x1 y1]]  (partition 2 (-> (interleave segment segment) rest butlast))]
              (q/line (+ (* 10 x0) 5 cx)
                      (+ (* 10 y0) 5 cy)
                      (+ (* 10 x1) 5 cx)
                      (+ (* 10 y1) 5 cy)))))))))

(defn on-click [state event]
  (let [{x :x y :y} event
        cellx (int (/ x *cell-width*))
        celly (int (/ y *cell-height*))
        new-state (update-in state [celly cellx] not)]
    (println "click @" x y cellx celly)
    (print "collision-point-set" (collision-point-set new-state))
    new-state))
    
(def pillar-near
  (let [[x y] cell-center]
    (assoc-in empty-grid [y (inc x)] true)))

(def pillar-away
  (let [[x y] cell-center]
    (assoc-in empty-grid [(inc y) (+ x 3)] true)))

(def corner-peeking
  (let [[cx cy] cell-center]
  (as-> empty-grid state
    (reduce (fn [state x] (assoc-in state [(dec cy) x] true))
            state
            (range *cells-width*))
    (reduce (fn [state x] (assoc-in state [(inc cy) x] true))
            state
            (range cx))
    (reduce (fn [state x] (assoc-in state [(inc cy) x] true))
            state
            (range (inc cx) *cells-width*)))))

(def diagonal-walls
  (reduce (fn [state x]
            (assoc-in state [(inc x) x] true))
          empty-grid
          (range *cells-width*)))

(defn random []
  (let [random-grid (reduce (fn [state [x y]]
                              (if (zero? (rand-int 10))
                                (assoc-in state [y x] true)
                                state))
                            empty-grid
                            (for [x (range *cells-width*)
                                  y (range *cells-height*)]
                              [x y]))
        random-grid (assoc-in random-grid (reverse cell-center) false)]
    random-grid))

(defn visible-points [state trie [x y]]
  "Set of points visible from [x y]"
  (if (get-in state [y x])
    nil
    (let [cx x
          cy y
          collision-points (set (map (fn [[x y]]
                                       [(- x cx) (- y cy)])
                                     (collision-point-set state)))
          tz       (trie->zipper (fn [xy] (contains? collision-points xy)) trie)
          ;; culled trie segments in player-cell-space
          visible-points (set (remove nil? (trie-zipper->keys tz)))]
      visible-points)))

(defn print-symmetry [state]
  (let [r       @radius
        trie    (get r->trie r)
        [ccx ccy] cell-center
        ; visible points in trie-space
        visible-pts (visible-points state trie cell-center)
        ; hidden-points (clojure.set/difference ks visible-points)
        groups     (->> visible-pts
                     ; remove blocking cells from test
                     ; comvert trie-space to grid-space
                     (remove (fn [[x y]] (get-in state [(+ y ccy) (+ x ccx)])))
                     ; Is cell-center visible from trie-space point [x y]?
                     ; group the number of symmetric and asymmetric results
                     (group-by (fn [[x y]]
                                 (let [transitive-visible-points (visible-points state trie [(+ x ccx) (+ y ccy)])]
                                   (contains? transitive-visible-points [(- x) (- y)])))))
        {sym  true
         asym false
         :or {sym  []
              asym []}} groups
        n-sym   (count (get groups true))
        n-asym  (count (get groups false))
        pct-sym (* 100.0 (/ n-asym (+ n-sym n-asym)))]
    (println "testing visible points" visible-points)
    (println "cell-center" cell-center)
    (println "sym" (get groups true))
    (println "asym" (get groups false))
    (println "num symmetric-cells" n-sym)
    (println "num asymmetric-cells" n-asym)
    (println "Symmetry error" pct-sym "%")
    (JOptionPane/showMessageDialog
      nil
      (str "Symmetry error " pct-sym "%"))
  pct-sym))

(defn print-multi-random-symmetry [state]
  (let [iterations 100
        errors (map (fn [i]
                      (println "Calculating symmetry for iteration" i)
                      (print-symmetry (random)))
                    (range iterations))
        error-avg (/ (reduce + errors) iterations)
        msg (format "Iterations %d\nAverageError %f"
              iterations
              error-avg)]
    (JOptionPane/showMessageDialog nil msg)))

(defn on-key [state event]
  (case (get event :key)
    :n pillar-near
    :a pillar-away
    :c corner-peeking
    :d diagonal-walls
    :r (random)
    :s (do (print-symmetry state)
           state)
    :S (do (print-multi-random-symmetry state)
           state)
    :+ (do (swap! radius inc)
           (println "New Radius" @radius)
           state)
    :- (do (swap! radius dec)
           (println "New Radius" @radius)
           state)
    :p (do (swap! path-mode (fn [path-mode] (get next-path-mode path-mode)))
           (println "New path mode" @path-mode)
           state)
    state))

(q/defsketch example
  :title "Pre-computed visibility tries demo"
  :middleware [m/fun-mode]
  :setup setup
  :draw draw
  :mouse-clicked on-click
  :key-typed on-key
  :size [*width* *height*])

(defn -main [] nil)
