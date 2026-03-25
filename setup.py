"""
Setup script for Mota Burruezo Spectral BSD Framework
Resolución espectral de la conjetura de Birch y Swinnerton-Dyer
"""

from setuptools import setup, find_packages

with open("README.md", "r", encoding="utf-8") as fh:
    long_description = fh.read()

with open("requirements.txt", "r", encoding="utf-8") as fh:
    requirements = [line.strip() for line in fh if line.strip() and not line.startswith("#")]

setup(
    name="bsd-spectral",
    version="1.0.0",
    author="José Manuel Mota Burruezo",
    author_email="institutoconsciencia@proton.me",
    description="Resolución espectral de la conjetura de Birch y Swinnerton-Dyer: prueba incondicional en rango 0 y 1, reducción completa en rango superior",
    long_description=long_description,
    long_description_content_type="text/markdown",
    url="https://github.com/motanova84/adelic-bsd",
    project_urls={
        "Homepage": "https://github.com/motanova84/adelic-bsd",
        "Documentation": "https://github.com/motanova84/adelic-bsd/blob/main/README.md",
        "Repository": "https://github.com/motanova84/adelic-bsd",
        "Issues": "https://github.com/motanova84/adelic-bsd/issues",
        "DOI": "https://doi.org/10.5281/zenodo.17236603",
    },
    packages=find_packages(),
    classifiers=[
        "Development Status :: 4 - Beta",
        "Intended Audience :: Science/Research",
        "Topic :: Scientific/Engineering :: Mathematics",
        "License :: OSI Approved :: MIT License",
        "Programming Language :: Python :: 3",
        "Programming Language :: Python :: 3.9",
        "Programming Language :: Python :: 3.10",
        "Programming Language :: Python :: 3.11",
        "Programming Language :: Python :: 3.12",
        "Programming Language :: Python :: 3.13",
    ],
    keywords=["elliptic-curves", "bsd-conjecture", "number-theory", "spectral-methods", "quantum-coherence", "qcal-framework"],
    python_requires=">=3.9",
    install_requires=requirements,
    entry_points={
        "console_scripts": [
            "bsd-spectral-demo=src:main",
        ],
    },
    include_package_data=True,
    zip_safe=False,
)
