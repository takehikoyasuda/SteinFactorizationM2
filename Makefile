# Build the technical note.
#
# SOURCE_DATE_EPOCH and FORCE_SOURCE_DATE stop pdflatex from stamping the build
# time into the file, so identical input gives a byte-identical PDF.  That makes
# the note reproducible: a reader who runs `make` on a given revision of the tex
# gets exactly the PDF that CI published from it, not a file that differs only
# in its timestamp.
#
# Bump the date when the note is substantively revised; it is what the PDF
# reports as its creation date.
SOURCE_DATE_EPOCH := 1782864000		# 2026-07-01

PDFLATEX = SOURCE_DATE_EPOCH=$(SOURCE_DATE_EPOCH) FORCE_SOURCE_DATE=1 \
	   pdflatex -interaction=nonstopmode -halt-on-error

# Twice: the first pass writes the cross-references, the second resolves them.
IMPLEMENTATION.pdf: IMPLEMENTATION.tex
	$(PDFLATEX) $<
	$(PDFLATEX) $<

clean:
	rm -f IMPLEMENTATION.aux IMPLEMENTATION.log IMPLEMENTATION.out \
	      IMPLEMENTATION.toc

.PHONY: clean
