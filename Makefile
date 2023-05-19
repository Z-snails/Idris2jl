export IDRIS2_JL := $(PWD)/build/exec/idris2jl
IDRIS2 := idris2

.PHONY: build
build:
	$(IDRIS2) --build idris2jl.ipkg

.PHONY: install-support
install-support:
	$(MAKE) -C support/julia install

.PHONY: uninstall-support
uninstall-support:
	$(MAKE) -C support/julia uninstall

.PHONY: test
test:
	$(MAKE) -C tests test

.PHONY: bench
bench:
	cd bench && nu run.nu $(IDRIS2_JL)

.PHONY: clean
clean:
	rm -r build
