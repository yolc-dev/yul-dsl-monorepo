########################################################################################################################
## VARIABLES
########################################################################################################################

# Project Configurations
LINEAR_SMC_VERSION = 2.2.3
LINEAR_SMC_PATH_FILE = 3rd-parties/linear-smc-$(LINEAR_SMC_VERSION).patch

# Output directories
DEFAULT_BUILDDIR ?= $(PWD)/build/default
CABAL_TEST_COVERAGE_BUILDDIR ?= $(PWD)/build/dist-coverage

# Build options
BUILD_OPTIONS ?=

# Test options
CABAL_TEST_SHOW_DETAILS_MODE ?= direct # alternatively: always | failure | never
CABAL_TEST_PROP_NUM_RUNS ?= 1000
CABAL_TEST_OPTIONS ?= \
    --test-show-details=$(CABAL_TEST_SHOW_DETAILS_MODE) \
    --test-options="--maximum-generated-tests=$(CABAL_TEST_PROP_NUM_RUNS)"

FORGE_TEST_OPTIONS ?= -vv

# Cabal flavors
CABAL_VERBOSITY ?= 1

CABAL ?= cabal -v$(CABAL_VERBOSITY)

CABAL_PACKAGE_DB = $(shell $(CABAL) -v0 --builddir=$(DEFAULT_BUILDDIR) path --output-format=json | \
										 jq -r '."store-dir" + "/" + .compiler.id + "-inplace/package.db"')

CABAL_BUILD    = $(CABAL) --builddir=$(DEFAULT_BUILDDIR) -O0 -j build
CABAL_TEST     = $(CABAL) --builddir=$(DEFAULT_BUILDDIR) -O0 -j test $(CABAL_TEST_OPTIONS)
CABAL_DOCS     = $(CABAL) --builddir=$(DEFAULT_BUILDDIR) -O0 -j haddock
CABAL_COVERAGE = $(CABAL) --builddir=$(CABAL_TEST_COVERAGE_BUILDDIR) -O0 -j coverage

# Yolc Options

export YOLC_DEBUG_LEVEL ?= 0

# Misc
DEV_TARGETS = build-all test-all test-demo-foundry lint

########################################################################################################################
# TARGETS
########################################################################################################################

ALL_YULDSL_MODULES = simple-sop eth-abi yul-dsl yul-dsl-pure yul-dsl-linear-smc yol-suite

all: lint build test

lint:
	hlint --ignore-glob=hs-pkgs/yol-suite/templates/*.hs hs-pkgs/
	hlint examples/

build: build-all build-docs

build-all:
	$(CABAL_BUILD) $(BUILD_OPTIONS) all

build-module-%:
	$(CABAL_BUILD) $(BUILD_OPTIONS) $*

build-docs:
	$(CABAL_DOCS) $(ALL_YULDSL_MODULES)

build-display-docs:
	for i in $(ALL_YULDSL_MODULES); do \
		xdg-open $(DEFAULT_BUILDDIR)/build/*/*/$${i}-*/noopt/doc/html/$${i}/index.html; \
  done

build-docs-and-display: build-docs build-display-docs

build-patches: $(LINEAR_SMC_PATH_FILE)

clean:
	rm -rf build cache out dist-*

test: test-all test-yol-suite test-demo

test-all:
	$(CABAL_TEST) all

test-module-%:
	$(CABAL_TEST) $*

test-yol-suite:
	yolc -fm yul hs-pkgs/yol-suite/testsuite
	cd hs-pkgs/yol-suite/testsuite && forge test -vvv

test-demo: test-demo-show test-demo-yul test-demo-foundry

test-demo-show:
	time yolc -fm show "examples/demo:ERC20"

test-demo-yul:
	time yolc -fm yul "examples/demo:ERC20"

test-demo-foundry:
	time yolc -fm yul "examples/demo"
	cd examples/demo && forge test $(FORGE_TEST_OPTIONS)

dev:
	nodemon -w hs-pkgs -w yol-demo -w examples -e "hs sol cabal" -i "#.*" -x "make $(DEV_TARGETS) || exit 1"

repl-eth-abi:
	$(CABAL) --builddir=$(DEFAULT_BUILDDIR) repl eth-abi

.PHONY: all lint build build-* clean install-* test test-* dev repl-eth-abi

$(LINEAR_SMC_PATH_FILE):
	[ -d 3rd-parties/linear-smc ] || exit 1
	diff -ur -p2 3rd-parties/linear-smc-"$(LINEAR_SMC_VERSION)" 3rd-parties/linear-smc | tee "$(LINEAR_SMC_PATH_FILE)"
# delete the patch if empty
	[[ -s "$(LINEAR_SMC_PATH_FILE)" ]] & rm -f "$(LINEAR_SMC_PATH_FILE)"
