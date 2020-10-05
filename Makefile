
NPROC ?= $(shell nproc)
TLC_JAVA_OPTS ?= -XX:+UseParallelGC
TLC_OPTS ?= -workers $(NPROC)
	# -debug -coverage 1

.PHONY: all clean

all: build/report.txt backpressure.pdf

build/report.txt: build/backpressure.tla build/backpressure.cfg
	TLC_JAVA_OPTS="$(TLC_JAVA_OPTS)" tlc $(TLC_OPTS) \
		$(abspath $<) -config $(abspath $(word 2,$^)) \
		| tee $@

backpressure.pdf: build/backpressure.tla
	cd build && tla2tex backpressure.tla && pdflatex backpressure.tex
	cp build/backpressure.pdf .

build/backpressure.tla: backpressure.tla
	mkdir -p build
	cp -f $< build/

build/backpressure.cfg: backpressure.cfg
	mkdir -p build
	cp -f $< build/

clean:
	rm -rf build/
