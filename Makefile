
NPROC ?= $(shell nproc)
TLC_JAVA_OPTS ?= -XX:+UseParallelGC
TLC_OPTS ?= -workers $(NPROC)
	# -debug -coverage 1

.PHONY: all clean

all: build/report.txt

build/report.txt: build/backpressure.tla build/backpressure.cfg
	TLC_JAVA_OPTS="$(TLC_JAVA_OPTS)" tlc $(TLC_OPTS) \
		$(abspath $<) -config $(abspath $(word 2,$^)) \
		| tee $@

build/backpressure.tla: backpressure.tla backpressure.cfg
	mkdir -p build
	cp -f backpressure.tla backpressure.cfg build/

clean:
	rm -rf build/
