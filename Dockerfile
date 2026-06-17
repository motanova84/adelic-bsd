# QCAL Production Docker Image
# Multi-stage build for optimized image size
#
# NOTE: SageMath (sage-all) is NOT available on PyPI and cannot be installed
# via regular pip. For production containers, Python-only dependencies are
# installed from requirements_ci.txt. To use SageMath locally, install the
# system binary first (see README.md) and then run: sage -pip install -r requirements.txt

FROM python:3.11-slim AS builder

# Set working directory
WORKDIR /build

# Install build dependencies
RUN apt-get update && apt-get install -y --no-install-recommends \
    gcc \
    g++ \
    git \
    && rm -rf /var/lib/apt/lists/*

# Copy CI requirements (excludes sage-all which requires the SageMath binary)
COPY requirements_ci.txt .

# Install Python dependencies
RUN pip install --no-cache-dir --user -r requirements_ci.txt

# Production stage
FROM python:3.11-slim

# Install runtime dependencies
RUN apt-get update && apt-get install -y --no-install-recommends \
    libgomp1 \
    && rm -rf /var/lib/apt/lists/*

# Create non-root user
RUN useradd -m -u 1000 qcal && \
    mkdir -p /app && \
    chown -R qcal:qcal /app

# Set working directory
WORKDIR /app

# Copy Python packages from builder
COPY --from=builder --chown=qcal:qcal /root/.local /home/qcal/.local

# Copy application code
COPY --chown=qcal:qcal . .

# Switch to non-root user
USER qcal

# Add local Python packages to PATH
ENV PATH=/home/qcal/.local/bin:$PATH
ENV PYTHONPATH=/app

# Set environment variables for reproducibility
ENV PYTHONHASHSEED=42
ENV PYTHONUNBUFFERED=1

# Health check
HEALTHCHECK --interval=30s --timeout=10s --start-period=5s --retries=3 \
    CMD python3 -c "import sys; sys.exit(0)"

# Default command
CMD ["python3", "validate_v5_coronacion.py", "--precision", "30"]

# Metadata
LABEL maintainer="motanova84"
LABEL description="QCAL Production Container for Adelic-BSD Framework"
LABEL version="1.0"
