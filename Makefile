

all: rebuild_metabuild
	./_build/bin/metabuild

clean: rebuild_metabuild
	./_build/bin/metabuild clean

run: all
	./_build/bin/lambdac

rebuild_metabuild: _build/bin/metabuild
	./_build/bin/metabuild metabuild

_build/bin/metabuild:
	cd buildsystem/MetaBuilder; \
	stack install --local-bin-path=../../_build/bin

.PHONY: all clean run rebuild_metabuild

