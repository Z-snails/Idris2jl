./build/exec/test: Main.idr
	$(IDRIS2) -p contrib -p test -o test Main.idr

.PHONY: test
test: ./build/exec/test
	./build/exec/test $(IDRIS2_JL)
