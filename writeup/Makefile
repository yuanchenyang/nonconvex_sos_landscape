files = writeup.tex
styfiles = mymacros.sty mytheorems.sty
figures =
bibfile = MyLibraryTEX.bib

output = $(files:.tex=.pdf)

all: $(output)

%.pdf: %.tex $(styfiles) $(bibfile) $(figures)
	rubber --pdf --synctex $*

clean:
	echo $(files) | xargs -n 1 rubber --clean

watch:  ## Recompile on updates to the source files
	while true; do inotifywait -e modify $(files) ; sleep 0.01 ; make all ; done
