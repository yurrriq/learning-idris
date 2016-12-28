pandoc       ?= pandoc
pandoc_flags := -f markdown_github+lhs -t markdown_github

sed      ?= sed
sed_hack := sed 's/ sourceCode/idris/'

srcs    := $(notdir $(wildcard src/*.lidr))
outputs := $(addprefix out/,${srcs:.lidr=.md})

all: ${outputs}

out/%.md: src/%.lidr
	${pandoc} ${pandoc_flags} $< | ${sed_hack} >$@
