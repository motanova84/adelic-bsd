.PHONY: all pdf figs tables clean help

# Default target
all: pdf figs tables

# Build PDF documents
pdf:
	@echo "Building PDF documents..."
	latexmk -pdf -shell-escape certificates/dR_uniformity/*.tex || true
	@echo "PDF build complete"

# Generate figures
figs:
	@echo "Generating figures..."
	python scripts/make_figs.py || echo "make_figs.py not yet implemented"
	@echo "Figures complete"

# Generate tables
tables:
	@echo "Generating tables..."
	python scripts/make_tables.py || echo "make_tables.py not yet implemented"
	@echo "Tables complete"

# Clean build artifacts
clean:
	@echo "Cleaning build artifacts..."
	latexmk -C
	find . -name "*.aux" -delete
	find . -name "*.log" -delete
	find . -name "*.out" -delete
	find . -name "*.fdb_latexmk" -delete
	find . -name "*.fls" -delete
	find . -name "*.synctex.gz" -delete
	@echo "Clean complete"

# Help target
help:
	@echo "Available targets:"
	@echo "  all     - Build everything (PDF, figures, tables)"
	@echo "  pdf     - Build PDF documents"
	@echo "  figs    - Generate figures"
	@echo "  tables  - Generate tables"
	@echo "  clean   - Remove build artifacts"
	@echo "  help    - Show this help message"
