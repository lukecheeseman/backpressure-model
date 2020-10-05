
NPROC ?= $(shell nproc)
TLC_JAVA_OPTS ?= -XX:+UseParallelGC
TLC_OPTS ?= -workers $(NPROC)
	# -debug -coverage 1

.PHONY: all clean

all: build/report.txt build/backpressure.pdf

build/report.txt: build/backpressure.tla build/backpressure.cfg
	TLC_JAVA_OPTS="$(TLC_JAVA_OPTS)" tlc $(TLC_OPTS) \
		$(abspath $<) -config $(abspath $(word 2,$^)) \
		| tee $@

build/backpressure.pdf: build/backpressure.tla
	$(shell cd build && tla2tex backpressure.tla && pdflatex backpressure.tex)

build/backpressure.tla: backpressure.tla
	mkdir -p build
	cp -f $< build/

build/backpressure.cfg: backpressure.cfg
	mkdir -p build
	cp -f $< build/

clean:
	rm -rf build/
