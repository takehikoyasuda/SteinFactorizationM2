# Build the package documentation and leave it at a fixed path, so that a
# browser tab opened on it once can be reloaded after every edit.
DOCDIR := doc-build
DOCINDEX := $(DOCDIR)/share/doc/Macaulay2/SteinFactorization/html/index.html

# No RerunExamples and no RemakeAllDocumentation on purpose: M2 hashes each
# example block and reruns only the ones whose input changed, so an edit to the
# prose alone reruns none of them.  That saves little today -- the whole suite of
# examples is about 1.5s of the 12s this takes, the rest being page generation --
# but it is what keeps the loop usable if an example ever costs what the
# twisted-cubic benchmark costs.  `make docs-all` is the build that assumes
# nothing is cached.
#
# IgnoreExampleErrors is off so that an example which stops working fails the
# build here rather than being written to a log nobody reads.  Examples are the
# one part of the documentation that cannot be wrong quietly, and that is worth
# keeping.
M2DOC = M2 --no-readline --no-debug -q -e

# Built up in pieces, and each recipe passes one unbroken line to the shell.
# A backslash-newline inside the single-quoted M2 expression is not portable:
# GNU make 3.81, as shipped on macOS, joins those lines before handing the
# recipe to the shell, while make 4.x leaves the backslash in place, where
# single quotes stop the shell from removing it and M2 reports
# "syntax error at '\'".  That is how this first failed on an Ubuntu runner
# while working locally.
INSTALL_ARGS = FileName => "SteinFactorization.m2", InstallPrefix => "$(CURDIR)/$(DOCDIR)/", IgnoreExampleErrors => false, MakeInfo => false
REMAKE_ARGS = RerunExamples => true, RemakeAllDocumentation => true

docs:
	$(M2DOC) 'installPackage("SteinFactorization", $(INSTALL_ARGS)); exit 0' < /dev/null
	@echo
	@echo "file://$(CURDIR)/$(DOCINDEX)"

# Everything from scratch: every example rerun, every page regenerated.  Use it
# after changing the code the examples call, or before a release.
docs-all:
	rm -rf $(DOCDIR)
	$(M2DOC) 'installPackage("SteinFactorization", $(INSTALL_ARGS), $(REMAKE_ARGS)); exit 0' < /dev/null
	@echo
	@echo "file://$(CURDIR)/$(DOCINDEX)"

# Separate from clean, because $(DOCDIR) holds the cached example output that
# makes `make docs` fast.  Removing it is a deliberate act, not housekeeping.
docs-clean:
	rm -rf $(DOCDIR)

.PHONY: docs docs-all docs-clean
