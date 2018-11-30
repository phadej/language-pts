build :
	cabal new-build

build-all : build
	cabal new-build --project-file=cabal.project.empty --enable-tests all --builddir=dist-newstyle-nat       --constraint='language-pts +nat -nat-prim -bool -bool-prim'
	cabal new-build --project-file=cabal.project.empty --enable-tests all --builddir=dist-newstyle-bool      --constraint='language-pts +nat +nat-prim -bool -bool-prim'
	cabal new-build --project-file=cabal.project.empty --enable-tests all --builddir=dist-newstyle-nat-prim  --constraint='language-pts -nat -nat-prim +bool -bool-prim'
	cabal new-build --project-file=cabal.project.empty --enable-tests all --builddir=dist-newstyle-bool-prim --constraint='language-pts -nat -nat-prim +bool +bool-prim'
	cabal new-build --project-file=cabal.project.empty --enable-tests all --builddir=dist-newstyle-sigma     --constraint='language-pts -nat -nat-prim -bool -bool-prim +sigma'
	cabal new-build --project-file=cabal.project.empty --enable-tests all --builddir=dist-newstyle-equality  --constraint='language-pts -nat -nat-prim -bool -bool-prim +equality'
	cabal new-build --project-file=cabal.project.empty --enable-tests all --builddir=dist-newstyle-prop      --constraint='language-pts -nat -nat-prim -bool -bool-prim +prop'
	cabal new-build --project-file=cabal.project.empty --enable-tests all --builddir=dist-newstyle-labels    --constraint='language-pts -nat -nat-prim -bool -bool-prim +labels'

test : build doctest
	cabal new-test

test-all : build-all doctest-all
	cabal new-test

haddock : 
	cabal new-haddock --with-compiler=ghc-8.4.4 --haddock-hyperlink-source

doctest :
	doctest -XCPP -DLANGUAGE_PTS_HAS_NAT -DLANGUAGE_PTS_HAS_NAT_PRIM -DLANGUAGE_PTS_HAS_BOOL -DLANGUAGE_PTS_HAS_BOOL_PRIM -DLANGUAGE_PTS_HAS_SIGMA -DLANGUAGE_PTS_HAS_EQUALITY -DLANGUAGE_PTS_HAS_PROP -DLANGUAGE_PTS_HAS_QUARKS --fast src/

doctest-all : doctest
	doctest -XCPP --fast src/
	doctest -XCPP -DLANGUAGE_PTS_HAS_NAT --fast src/
	doctest -XCPP -DLANGUAGE_PTS_HAS_BOOL --fast src/
	doctest -XCPP -DLANGUAGE_PTS_HAS_ETA --fast src/
	doctest -XCPP -DLANGUAGE_PTS_HAS_SIGMA --fast src/
	doctest -XCPP -DLANGUAGE_PTS_HAS_EQUALITY --fast src/
	doctest -XCPP -DLANGUAGE_PTS_HAS_PROP --fast src/
	doctest -XCPP -DLANGUAGE_PTS_HAS_QUARKS --fast src/
	doctest -XCPP -DLANGUAGE_PTS_HAS_NAT -DLANGUAGE_PTS_HAS_BOOL -DLANGUAGE_PTS_HAS_QUARKS --fast src/

ghcid :
	ghcid -c 'cabal new-repl' --restart=language-pts.cabal
