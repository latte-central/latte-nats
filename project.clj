(defproject latte-nats "0.1.0-SNAPSHOT"
  :description "A formalization of natural numbers in LaTTe."
  :url "https://github.com/latte-central/latte-nats.git"
  :license {:name "MIT Licence"
            :url "http://opensource.org/licenses/MIT"}
  :dependencies [[org.clojure/clojure "1.10.1"]
                 [latte-sets "1.0b8-SNAPSHOT"]]
  :main latte-integers.main
  :aliases {"certify" ["run" ":certify"]
            "clear-cert" ["run" ":clear-cert"]}
  :codox {:output-path "docs/"
          :metadata {:doc/format :markdown}
          :namespaces [latte-nats.core]}
  :plugins [[lein-codox "0.10.7"]])
