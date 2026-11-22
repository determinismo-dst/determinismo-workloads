;; SPDX-License-Identifier: MIT
;; This platform's libhegel, from the jar (fetch.sh put them there), into the build's output.
(require '[babashka.fs :as fs]
         '[jank.build.util :as util])

(let [{:keys [src-dir out-dir]} *input*
      os (System/getProperty "os.name")
      arch (if (#{"aarch64" "arm64"} (System/getProperty "os.arch")) "arm64" "amd64")
      macos? (.startsWith os "Mac")
      platform (str (if macos? "darwin-" "linux-") arch)
      library (if macos? "libhegel.dylib" "libhegel.so")
      from (fs/path src-dir "lib" platform library)]
  (when-not (fs/exists? from)
    (throw (ex-info (str "libhegel: " from " missing (no prebuilt library for " os " " arch
                         ", or hegel-sys/fetch.sh not run before packaging)") {})))
  (fs/create-dirs (fs/path out-dir "lib"))
  (fs/create-dirs (fs/path out-dir "include"))
  (fs/copy from (fs/path out-dir "lib" library) {:replace-existing true})
  (fs/copy (fs/path src-dir "include" "hegel.h") (fs/path out-dir "include" "hegel.h") {:replace-existing true})
  (util/include-dir "include")
  (util/link-dir "lib")
  (util/link-library "hegel"))
