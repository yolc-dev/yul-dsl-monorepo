########################################################################################################################
## VARIABLES
########################################################################################################################

# Output directories
BUILD_DIR ?= $(PWD)/build

# Cabal general options
CABAL ?= cabal
CABAL_OPTIONS ?= -v1 -O0 -j

# Cabal build options

CABAL_BUILD_OPTIONS ?=

# Cabal test options
CABAL_TEST_SHOW_DETAILS_MODE ?= direct # alternatively: always | failure | never
CABAL_TEST_PROP_NUM_RUNS ?= 1000
CABAL_TEST_OPTIONS ?= \
    --test-show-details=$(CABAL_TEST_SHOW_DETAILS_MODE) \
    --test-options="--maximum-generated-tests=$(CABAL_TEST_PROP_NUM_RUNS)"

# Cabal paths

CABAL_PATH= $(CABAL) -v0 --builddir=$(BUILD_DIR)/cabal-path path --output-format=json

GHC = $(shell $(CABAL_PATH) | jq -r .compiler.path)
GHC_ID = $(shell $(GHC) --info | ghci -e 'readFile "/dev/stdin" >>= putStrLn . snd . last . filter ((== "Project Unit Id") . fst) . (read :: String -> [(String, String)])')
CABAL_COMPILER_ID = $(shell $(CABAL_PATH) | jq -r .compiler.id)

CABAL_WITH_OPTIONS = $(CABAL) $(CABAL_OPTIONS) --project-file=cabal.$(CABAL_COMPILER_ID).project

# Cabal commands

CABAL_DEFAULT_BUILD_DIR  ?= $(BUILD_DIR)/yolc/$(GHC_ID)-dist
CABAL_DOCS_BUILD_DIR     ?= $(BUILD_DIR)/yolc/$(GHC_ID)-docs
CABAL_COVERAGE_BUILD_DIR ?= $(BUILD_DIR)/yolc/$(GHC_ID)-coverage

CABAL_BUILD    = $(CABAL_WITH_OPTIONS) --builddir=$(CABAL_DEFAULT_BUILD_DIR) build $(CABAL_BUILD_OPTIONS)
CABAL_REPL     = $(CABAL_WITH_OPTIONS) --builddir=$(CABAL_DEFAULT_BUILD_DIR) repl  $(CABAL_BUILD_OPTIONS)
CABAL_TEST     = $(CABAL_WITH_OPTIONS) --builddir=$(CABAL_DEFAULT_BUILD_DIR) test  $(CABAL_TEST_OPTIONS)

CABAL_DOCS     = $(CABAL_WITH_OPTIONS) --builddir=$(CABAL_DOCS_BUILD_DIR) haddock

CABAL_COVERAGE = $(CABAL_WITH_OPTIONS) --builddir=$(CABAL_COVERAGE_BUILD_DIR) coverage

# Yolc options

export YOLC_DEBUG_LEVEL = 0
export YOLC_PACKAGE_DB = $(CABAL_DEFAULT_BUILD_DIR)/packagedb/$(CABAL_COMPILER_ID)

# Forge options

FORGE_TEST_OPTIONS ?= -vv

# Other configurations

LINEAR_SMC_VERSION = 2.2.3
LINEAR_SMC_PATH_FILE = 3rd-parties/linear-smc-$(LINEAR_SMC_VERSION).patch

########################################################################################################################
# TARGETS
########################################################################################################################

ALL_YULDSL_MODULES = simple-sop eth-abi yul-dsl yul-dsl-pure yul-dsl-linear-smc yol-suite

DEV_TARGETS = build-all test-all test-yol-suite test-demo-foundry lint

all: lint build test

lint:
	hlint --ignore-glob=hs-pkgs/yol-suite/templates/*.hs hs-pkgs/
	hlint examples/

freeze:
	$(CABAL_WITH_OPTIONS) freeze

build: build-dist build-docs

build-all: build-dist
	$(CABAL_BUILD) all

build-dist:
	$(CABAL_BUILD) $(ALL_YULDSL_MODULES)

	@cd $(CABAL_DEFAULT_BUILD_DIR); find build -path '*/t' -prune -o -type f -print \
		| xargs tar c \
		| md5sum > $(CABAL_DEFAULT_BUILD_DIR)/dist.md5sum.new
	@cd $(CABAL_DEFAULT_BUILD_DIR); if ! diff dist.md5sum.new dist.md5sum &>/dev/null; then \
		echo "!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!"; \
		echo "!! WARNING: Yolc dist changed. To force rebuilding yol projects."; \
		echo "!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!"; \
		mv dist.md5sum.new dist.md5sum; \
		rm -rf $(BUILD_DIR)/yol; \
	fi

build-module-%:
	$(CABAL_BUILD) $*

build-docs:
	$(CABAL_DOCS) $(ALL_YULDSL_MODULES)

build-docs-display:
	for i in $(ALL_YULDSL_MODULES); do \
		xdg-open $(CABAL_DOCS_BUILD_DIR)/build/*/*/$${i}-*/noopt/doc/html/$${i}/index.html; \
  done

build-docs-and-display: build-docs build-docs-display

build-patches: $(LINEAR_SMC_PATH_FILE)

clean: clean-all

# This clean up all the yolsuite built projects.
# If you experience weird build errors while developing yolc, this can help.
clean-yol:
	rm -rf build/yol

clean-all:
	rm -rf build cache out dist-*

test: build-dist test-all test-yol-suite test-demo

test-all:
	$(CABAL_TEST) all

test-module-%:
	$(CABAL_TEST) $*

test-yol-suite:
	yolc -m yul hs-pkgs/yol-suite/testsuite
	cd hs-pkgs/yol-suite/testsuite && forge test -vvv

test-demo: test-demo-show test-demo-yul test-demo-foundry

test-demo-show:
	time yolc -m show "examples/demo:ERC20"

test-demo-yul:
	time yolc -m yul "examples/demo:ERC20"

test-demo-foundry:
	time yolc -m yul "examples/demo"
	cd examples/demo && forge test $(FORGE_TEST_OPTIONS)

dev:
	nodemon -w hs-pkgs -w yol-demo -w examples -e "hs sol cabal" -i "#.*" -x "make $(DEV_TARGETS) || exit 1"

repl-%:
	$(CABAL_REPL) $*

.PHONY: all lint freeze build build-* clean clean-* test test-* dev repl-*

$(LINEAR_SMC_PATH_FILE):
	[ -d 3rd-parties/linear-smc ] || exit 1
	diff -ur -p2 3rd-parties/linear-smc-"$(LINEAR_SMC_VERSION)" 3rd-parties/linear-smc | tee "$(LINEAR_SMC_PATH_FILE)"
# delete the patch if empty
	[[ -s "$(LINEAR_SMC_PATH_FILE)" ]] & rm -f "$(LINEAR_SMC_PATH_FILE)"
