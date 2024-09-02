target = report
source = report

deps := $(source).tex ./*.tex
 
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

clean:
	@rm -rf $(build_dir)
