# QCAL Production Docker Image
# Multi-stage build for optimized image size

FROM python:3.11-slim as builder

# Set working directory
WORKDIR /build

# Install build dependencies
RUN apt-get update && apt-get install -y --no-install-recommends \
    gcc \
    g++ \
    git \
    && rm -rf /var/lib/apt/lists/*

# Copy requirements first for better caching
COPY requirements.txt .

# Install Python dependencies
RUN pip install --no-cache-dir --user -r requirements.txt

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
ENV PYTHONPATH=/app:$PYTHONPATH

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
