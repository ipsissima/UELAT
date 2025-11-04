COQ_SRC_DIR := Coq
COQPROJECT := $(COQ_SRC_DIR)/_CoqProject
COQMAKEFILE := Makefile.coq
COQFILES := $(shell find $(COQ_SRC_DIR) -type f -name '*.v')

.PHONY: all coq clean

all: coq

ifeq ($(wildcard $(COQPROJECT)),)
coq:
	@echo "Warning: $(COQPROJECT) not found; compiling files directly"
	@set -e; for f in $(COQFILES); do \
		echo "coqc $$f"; \
		coqc $$f; \
	done

clean:
	@echo "Removing Coq build artifacts"
	@find $(COQ_SRC_DIR) -type f \( -name '*.vo' -o -name '*.glob' \) -print0 | xargs -0 -r rm -f
else
coq:
	coq_makefile -f $(COQPROJECT) -o $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE)

clean:
	@if [ -f $(COQMAKEFILE) ]; then \
		$(MAKE) -f $(COQMAKEFILE) cleanall; \
	else \
		echo "No $(COQMAKEFILE); nothing to clean."; \
	fi
endif
