target = report
source = report
camera = final-report

deps := $(source).tex ./*.tex ./images/*.*
 
build_dir = _build

all: $(target).pdf

# %.pdf: $(build_dir) %.tex $(wildcard $(deps)) 
# 	@latexmk -bibtex -pdf -jobname=$(build_dir)/$(basename $@) $(basename $@) 
# 	@cp $(build_dir)/$@ $@

$(target).pdf: $(build_dir) $(target).tex $(wildcard $(deps)) 
	latexmk -bibtex -pdf -jobname=$(build_dir)/$(target) $(target)
	cp $(build_dir)/$(target).pdf $(target).pdf

$(build_dir): 
	@mkdir $(build_dir)

$(camera).pdf: $(build_dir) camera_expand $(wildcard $(deps))
	latexmk -bibtex -pdf -jobname=$(build_dir)/$(camera) $(camera)
	cp $(build_dir)/$(camera).pdf $(camera).pdf

camera_expand: $(target).tex $(wildcard $(deps))
	@latexpand $(target).tex > $(camera).tex

camera: $(camera).pdf
	cp $(build_dir)/$(camera).bbl $(camera).bbl
	@zip $(camera)-source.zip $(camera).tex \
		$(camera).bbl ref.bib *.cls *.sty images/*

clean:
	@rm -rf $(build_dir)
