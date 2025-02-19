# Directories
INCLUDE_DIR = .

# Executables
FSTAR = fstar.exe
KRML = krml

TARGET = exe/Impl.HelloWorld.exe

# Phony targets
.PHONY: all clean krml

# Default target: generate the .krml file
all: $(TARGET)

obj/%.krml: code/%.fst
	$(FSTAR) --z3version 4.13.3 --odir obj --cache_dir obj --include $(INCLUDE_DIR) --codegen krml $< --krmloutput $@

# Generate C code from .krml using krml
$(C_OUTPUT): $(KRML_OUTPUT) 
	$(KRML) -tmpdir dest -no-prefix Impl.HelloWorld $(KRML_OUTPUT)

exe/%.exe: obj/%.krml
	mkdir -p exe
	$(KRML) -tmpdir dest -no-prefix $* -o $@ $<

# Clean up generated files
clean: 
	rm -rf obj internal dest exe
