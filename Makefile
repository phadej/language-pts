build :
	cabal new-build

haddock : 
	#  haddock_api_datadir=/home/ogre/Documents/other-haskell/haddock/haddock-api/resources
	cabal new-haddock --with-compiler=ghc-8.4.2 --with-haddock=haddock-2.19 --haddock-hyperlink-source

doctest :
	doctest -XCPP -DLANGUAGE_PTS_HAS_NAT -DLANGUAGE_PTS_HAS_BOOL --fast src/

doctest-all : doctest
	doctest -XCPP --fast src/
	doctest -XCPP -DLANGUAGE_PTS_HAS_NAT --fast src/
	doctest -XCPP -DLANGUAGE_PTS_HAS_BOOL --fast src/
	doctest -XCPP -DLANGUAGE_PTS_HAS_ETA --fast src/
	doctest -XCPP -DLANGUAGE_PTS_HAS_NAT -DLANGUAGE_PTS_HAS_BOOL -DLANGUAGE_PTS_HAS_ETA --fast src/

ghcid :
	ghcid -c 'cabal new-repl' --restart=language-pts.cabal
