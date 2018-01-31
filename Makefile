COQMAKEFILE = coq_makefile
CODE_DIR = src
LATEX_DIR = latex

default: library latex/rules.pdf

.PHONY: library clean doc

src/Makefile: src/_CoqProject
	cd src && $(COQMAKEFILE) -f _CoqProject -o Makefile

latex/rules.pdf:
	$(MAKE) -C $(LATEX_DIR) rules.pdf

latex/rulesParanoid.pdf:
	$(MAKE) -C $(LATEX_DIR) rulesParanoid.pdf

library: src/Makefile
	$(MAKE) -C $(CODE_DIR)

doc:
	$(MAKE) -C $(CODE_DIR) html

clean: src/Makefile
	$(MAKE) -C $(LATEX_DIR) clean
	$(MAKE) -C $(CODE_DIR) clean
