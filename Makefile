build :
	cabal new-build

build-all : build
	cabal new-build --project-file=cabal.project.empty --enable-tests all --builddir=dist-newstyle-nat       --constraint='language-pts +nat -nat-prim -bool -bool-prim'
	cabal new-build --project-file=cabal.project.empty --enable-tests all --builddir=dist-newstyle-bool      --constraint='language-pts +nat +nat-prim -bool -bool-prim'
	cabal new-build --project-file=cabal.project.empty --enable-tests all --builddir=dist-newstyle-nat-prim  --constraint='language-pts -nat -nat-prim +bool -bool-prim'
	cabal new-build --project-file=cabal.project.empty --enable-tests all --builddir=dist-newstyle-bool-prim --constraint='language-pts -nat -nat-prim +bool +bool-prim'

haddock : 
	cabal new-haddock --with-compiler=ghc-8.4.4 --haddock-hyperlink-source

doctest :
	doctest -XCPP -DLANGUAGE_PTS_HAS_NAT -DLANGUAGE_PTS_HAS_NAT_PRIM -DLANGUAGE_PTS_HAS_BOOL -DLANGUAGE_PTS_HAS_BOOL_PRIM --fast src/

doctest-all : doctest
	doctest -XCPP --fast src/
	doctest -XCPP -DLANGUAGE_PTS_HAS_NAT --fast src/
	doctest -XCPP -DLANGUAGE_PTS_HAS_BOOL --fast src/
	doctest -XCPP -DLANGUAGE_PTS_HAS_ETA --fast src/
	doctest -XCPP -DLANGUAGE_PTS_HAS_NAT -DLANGUAGE_PTS_HAS_BOOL -DLANGUAGE_PTS_HAS_ETA --fast src/

ghcid :
	ghcid -c 'cabal new-repl' --restart=language-pts.cabal
