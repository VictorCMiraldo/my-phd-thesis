\section{Source-Code}

  The easiest way to obtain the source is through either
GitHub or Hackage. The source code for the different projects
discussed throughout this dissertation is publicly
available as Haskell packages, on Hackage:

\begin{itemize}
  \item \url{hackage.haskell.org/package/generics-mrsop}
  \item \url{hackage.haskell.org/package/simplistic-generics}
  \item \url{hackage.haskell.org/package/generics-mrsop-gdiff}
  \item \url{hackage.haskell.org/package/hdiff}
\end{itemize}

  The actual version of \texttt{hdiff} that we have documented
and used to obtain the results presented in this dissertation
has been archived on Zenodo~\cite{Miraldo2020_hdiff}.

\section{Dataset}

  The dataset~\cite{Miraldo2020_Dataset} was obtained by running the
data collection script (\Cref{sec:eval:collection}) over the repositories
listed in \Cref{tbl:repos}, on the 16$^{th}$ of January of 2020.
It is also available in Zenodo for download.

\let\oldarraystretch\arraystretch
\renewcommand{\arraystretch}{1.1}
\begin{center}
\footnotesize
\begin{longtable}{lllll}
\caption{Repositories used for data collection.} \label{tbl:repos} \\ \toprule
Language & Repository & Conflicts & Commits & Forks \\ \midrule \endfirsthead
\caption{Repositories used for data collection (continued).} \label{tbl:repos} \\ \toprule
Language & Repository & Conflicts & Commits & Forks \\ \midrule \endhead
Clojure & metabase/metabase & 411 & 18697 & 25 \\
Clojure & onyx-platform/onyx & 189 & 6828 & 209 \\
Clojure & incanter/incanter & 96 & 1593 & 286 \\
Clojure & nathanmarz/cascalog & 68 & 1366 & 181 \\
Clojure & overtone/overtone & 65 & 3070 & 413 \\
Clojure & technomancy/leiningen & 46 & 4736 & 15 \\
Clojure & ring-clojure/ring & 44 & 1027 & 441 \\
Clojure & ztellman/aleph & 43 & 1398 & 213 \\
Clojure & pedestal/pedestal & 35 & 1581 & 248 \\
Clojure & circleci/frontend & 33 & 18857 & 170 \\
Clojure & arcadia-unity/Arcadia & 25 & 1716 & 95 \\
Clojure & walmartlabs/lacinia & 19 & 991 & 105 \\
Clojure & clojure/clojurescript & 18 & 5706 & 730 \\
Clojure & oakes/Nightcode & 17 & 1914 & 119 \\
Clojure & weavejester/compojure & 16 & 943 & 245 \\
Clojure & boot-clj/boot & 12 & 1331 & 169 \\
Clojure & clojure-liberator/liberator & 12 & 406 & 144 \\
Clojure & originrose/cortex & 11 & 1045 & 103 \\
Clojure & dakrone/clj-http & 9 & 1198 & 368 \\
Clojure & bhauman/lein-figwheel & 9 & 1833 & 221 \\
Clojure & jonase/kibit & 9 & 436 & 124 \\
Clojure & riemann/riemann & 7 & 1717 & 512 \\
Clojure & korma/Korma & 7 & 491 & 232 \\
Clojure & clojure/core.async & 4 & 564 & 181 \\
Clojure & status-im/status-react & 3 & 5224 & 723 \\
Clojure & cemerick/friend & 2 & 227 & 122 \\
Clojure & LightTable/LightTable & 1 & 1265 & 927 \\
Clojure & krisajenkins/yesql & 1 & 285 & 112 \\
Clojure & cgrand/enlive & 1 & 321 & 144 \\
Clojure & plumatic/schema & 1 & 825 & 244 \\
\midrule
Java & spring-projects/spring-boot & 760 & 24545 & 284 \\
Java & elastic/elasticsearch & 746 & 49920 & 158 \\
Java & apereo/cas & 363 & 15834 & 31 \\
Java & jenkinsci/jenkins & 296 & 29141 & 6 \\
Java & xetorthio/jedis & 147 & 1610 & 32 \\
Java & google/ExoPlayer & 133 & 7694 & 44 \\
Java & apache/storm & 117 & 10204 & 4 \\
Java & junit-team/junit4 & 77 & 2427 & 29 \\
Java & skylot/jadx & 52 & 1165 & 24 \\
Java & naver/pinpoint & 51 & 10931 & 3 \\
Java & apache/beam & 34 & 25062 & 22 \\
Java & baomidou/mybatis-plus & 31 & 3640 & 21 \\
Java & mybatis/mybatis-3 & 21 & 3164 & 83 \\
Java & dropwizard/dropwizard & 20 & 5229 & 31 \\
Java & SeleniumHQ/selenium & 18 & 24627 & 54 \\
Java & code4craft/webmagic & 11 & 1015 & 37 \\
Java & aws/aws-sdk-java & 7 & 2340 & 24 \\
Java & spring-projects/spring-security & 7 & 8339 & 36 \\
Java & eclipse/deeplearning4j & 6 & 572 & 48 \\
Java & square/okhttp & 5 & 4407 & 78 \\
\midrule
JavaScript & meteor/meteor & 1208 & 22501 & 51 \\
JavaScript & adobe/brackets & 699 & 17782 & 66 \\
JavaScript & mrdoob/three.js & 403 & 31473 & 22 \\
JavaScript & moment/moment & 141 & 3724 & 65 \\
JavaScript & RocketChat/Rocket.Chat & 125 & 17445 & 55 \\
JavaScript & serverless/serverless & 118 & 12278 & 39 \\
JavaScript & nodejs/node & 99 & 29302 & 159 \\
JavaScript & twbs/bootstrap & 86 & 19261 & 679 \\
JavaScript & photonstorm/phaser & 80 & 13958 & 61 \\
JavaScript & emberjs/ember.js & 76 & 19460 & 42 \\
JavaScript & atom/atom & 63 & 37335 & 137 \\
JavaScript & TryGhost/Ghost & 50 & 10374 & 7 \\
JavaScript & jquery/jquery & 44 & 6453 & 19 \\
JavaScript & mozilla/pdf.js & 41 & 12132 & 69 \\
JavaScript & Leaflet/Leaflet & 37 & 6810 & 44 \\
JavaScript & expressjs/express & 36 & 5558 & 79 \\
JavaScript & hexojs/hexo & 27 & 3146 & 38 \\
JavaScript & videojs/video.js & 17 & 3509 & 63 \\
JavaScript & facebook/react & 10 & 12732 & 273 \\
JavaScript & jashkenas/underscore & 8 & 2447 & 55 \\
JavaScript & lodash/lodash & 8 & 7992 & 46 \\
JavaScript & axios/axios & 8 & 900 & 6 \\
JavaScript & select2/select2 & 3 & 2573 & 58 \\
JavaScript & chartjs/Chart.js & 3 & 2966 & 101 \\
JavaScript & facebook/jest & 2 & 4595 & 41 \\
JavaScript & vuejs/vue & 1 & 3076 & 234 \\
JavaScript & nwjs/nw.js & 1 & 3913 & 38 \\
\midrule
Lua & Kong/kong & 209 & 5494 & 31 \\
Lua & hawkthorne/hawkthorne-journey & 155 & 5538 & 370 \\
Lua & snabbco/snabb & 119 & 9456 & 295 \\
Lua & tarantool/tarantool & 54 & 13542 & 224 \\
Lua & luarocks/luarocks & 45 & 2325 & 296 \\
Lua & luakit/luakit & 28 & 4186 & 219 \\
Lua & pkulchenko/ZeroBraneStudio & 20 & 3945 & 447 \\
Lua & CorsixTH/CorsixTH & 16 & 3355 & 250 \\
Lua & OpenNMT/OpenNMT & 14 & 1684 & 455 \\
Lua & koreader/koreader & 14 & 7256 & 710 \\
Lua & bakpakin/Fennel & 12 & 689 & 59 \\
Lua & Olivine-Labs/busted & 9 & 950 & 139 \\
Lua & Element-Research/rnn & 8 & 622 & 318 \\
Lua & lcpz/awesome-copycats & 8 & 821 & 412 \\
Lua & Tieske/Penlight & 6 & 743 & 190 \\
Lua & yagop/telegram-bot & 5 & 729 & 519 \\
Lua & awesomeWM/awesome & 5 & 9990 & 360 \\
Lua & torch/nn & 4 & 1839 & 967 \\
Lua & luvit/luvit & 4 & 2897 & 330 \\
Lua & GUI/lua-resty-auto-ssl & 3 & 318 & 119 \\
Lua & alexazhou/VeryNginx & 3 & 604 & 810 \\
Lua & sailorproject/sailor & 2 & 640 & 128 \\
Lua & leafo/moonscript & 2 & 738 & 162 \\
Lua & nrk/redis-lua & 1 & 327 & 193 \\
Lua & skywind3000/z.lua & 1 & 367 & 59 \\
Lua & rxi/json.lua & 1 & 46 & 144 \\
Lua & luafun/luafun & 1 & 55 & 88 \\
\midrule
Python & python/cpython & 891 & 106167 & 131 \\
Python & sympy/sympy & 864 & 41009 & 29 \\
Python & matplotlib/matplotlib & 515 & 32949 & 47 \\
Python & home-assistant/home-assistant & 496 & 23812 & 91 \\
Python & bokeh/bokeh & 326 & 18196 & 32 \\
Python & certbot/certbot & 272 & 9524 & 28 \\
Python & scikit-learn/scikit-learn & 192 & 25044 & 19 \\
Python & explosion/spaCy & 163 & 11141 & 27 \\
Python & docker/compose & 129 & 5590 & 29 \\
Python & scrapy/scrapy & 74 & 7705 & 83 \\
Python & keras-team/keras & 70 & 5342 & 176 \\
Python & tornadoweb/tornado & 60 & 4144 & 51 \\
Python & pallets/flask & 56 & 3799 & 132 \\
Python & ipython/ipython & 51 & 24203 & 39 \\
Python & pandas-dev/pandas & 48 & 21596 & 92 \\
Python & quantopian/zipline & 45 & 6032 & 31 \\
Python & Theano/Theano & 44 & 28099 & 25 \\
Python & psf/requests & 32 & 5927 & 75 \\
Python & ansible/ansible & 29 & 48864 & 18 \\
Python & nvbn/thefuck & 11 & 1555 & 26 \\
Python & waditu/tushare & 8 & 407 & 35 \\
Python & facebook/prophet & 4 & 445 & 26 \\
Python & jakubroztocil/httpie & 3 & 1145 & 29 \\
Python & binux/pyspider & 1 & 1174 & 34 \\
Python & Jack-Cherish/python-spider & 1 & 279 & 39 \\
Python & zulip/zulip & 1 & 34149 & 35 \\
\bottomrule
\end{longtable}
\end{center}

\renewcommand{\arraystretch}{\oldarraystretch}