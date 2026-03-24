"""
Setup script for QCAL ∞³ - Adelic BSD Framework

Author: José Manuel Mota Burruezo (JMMB Ψ ✧ ∞³)
Framework: QCAL ∞³ (Quantum Coherence Arithmetic Logic)
Institution: Instituto de Conciencia Cuántica (ICQ)
"""

from setuptools import setup, find_packages

with open("README.md", "r", encoding="utf-8") as fh:
    long_description = fh.read()

with open("requirements.txt", "r", encoding="utf-8") as fh:
    requirements = [line.strip() for line in fh if line.strip() and not line.startswith("#")]

setup(
    name="qcal-adelic-bsd",
    version="1.0.0",
    author="José Manuel Mota Burruezo",
    author_email="institutoconsciencia@proton.me",
    maintainer="José Manuel Mota Burruezo (JMMB Ψ ✧ ∞³)",
    maintainer_email="institutoconsciencia@proton.me",
    description="QCAL ∞³ Framework - Spectral resolution of BSD conjecture via adelic operators at f₀ = 141.7001 Hz",
    long_description=long_description,
    long_description_content_type="text/markdown",
    url="https://github.com/motanova84/adelic-bsd",
    project_urls={
        "Documentation": "https://github.com/motanova84/adelic-bsd/blob/main/README.md",
        "Source": "https://github.com/motanova84/adelic-bsd",
        "Zenodo": "https://doi.org/10.5281/zenodo.17379721",
        "BSD DOI": "https://doi.org/10.5281/zenodo.17236603",
        "ORCID": "https://orcid.org/0009-0002-1923-0773",
    },
    packages=find_packages(),
    classifiers=[
        "Development Status :: 5 - Production/Stable",
        "Intended Audience :: Science/Research",
        "Topic :: Scientific/Engineering :: Mathematics",
        "Topic :: Scientific/Engineering :: Physics",
        "License :: OSI Approved :: MIT License",
        "License :: Other/Proprietary License",
        "Programming Language :: Python :: 3",
        "Programming Language :: Python :: 3.9",
        "Programming Language :: Python :: 3.10",
        "Programming Language :: Python :: 3.11",
        "Programming Language :: Python :: 3.12",
        "Programming Language :: Python :: 3.13",
        "Operating System :: OS Independent",
        "Natural Language :: English",
        "Natural Language :: Spanish",
    ],
    keywords=[
        "qcal",
        "birch-swinnerton-dyer",
        "elliptic-curves",
        "spectral-methods",
        "adelic-operators",
        "mathematical-physics",
        "quantum-coherence",
        "f0-141.7001hz",
        "millennium-problems",
    ],
    python_requires=">=3.9",
    install_requires=requirements,
    entry_points={
        "console_scripts": [
            "qcal-demo=examples.quick_demo:main",
            "spectral-demo=examples.quick_demo:main",
        ],
    },
    include_package_data=True,
    zip_safe=False,
    license="MIT License + CC BY-NC-SA 4.0",
    platforms=["any"],
)
