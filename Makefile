COQFILES = $(wildcard coq/*.v)
COQEXAMPLES = $(wildcard coq/Examples/*.v)

all:
	coqc $(COQFILES)
	@for f in $(COQEXAMPLES); do coqc $$f; done

clean:
	rm -f coq/*.vo coq/*.glob coq/Examples/*.vo coq/Examples/*.glob
