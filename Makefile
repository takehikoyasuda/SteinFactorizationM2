# Build the technical note.
#
# SOURCE_DATE_EPOCH and FORCE_SOURCE_DATE stop pdflatex from stamping the build
# time into the file, so identical input gives a byte-identical PDF.  Without
# them every rebuild produces a different file and shows up as a git change even
# when nothing was edited -- and since a PDF is already compressed, git cannot
# delta it, so each of those non-changes would cost a full copy in the history.
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
