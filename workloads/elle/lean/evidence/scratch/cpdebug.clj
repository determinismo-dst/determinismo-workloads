(require '[elle.closed-predicate :as cp] '[jepsen.history :as h] '[clojure.edn :as edn] '[elle.core :as elle])
(let [c (first (edn/read-string (slurp "results/closed-predicate-2.cases.edn")))
      hist (h/client-ops (h/history (:history c)))
      av (cp/all-versions hist)
      vs (cp/version-sets av hist)
      ew (cp/ext-writes hist)
      an {:all-versions av :vsets vs :ext-writes ew}
      {:keys [graph explainer]} (cp/graph an hist)]
  (prn :all-versions av)
  (prn :vsets vs)
  (prn :version< (cp/version< av 0 :elle/unborn 0) (cp/version< av 1 :elle/dead 0))
  (prn :explain (elle/explain-pair-data explainer (nth hist 5) (nth hist 1))))
