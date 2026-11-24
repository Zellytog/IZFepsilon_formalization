all: RocqMakefile
	$(MAKE) -f RocqMakefile

RocqMakefile: _RocqProject
	rocq makefile -f _RocqProject -o RocqMakefile

clean:
	if [ -f RocqMakefile ]; then $(MAKE) -f RocqMakefile clean; fi
	rm -f RocqMakefile RocqMakefile.conf .RocqMakefile.d

.PHONY: all clean
