"""Setup script for the adelic-bsd repository."""

from setuptools import find_packages, setup

with open("README.md", "r", encoding="utf-8") as fh:
    long_description = fh.read()

with open("requirements.txt", "r", encoding="utf-8") as fh:
    requirements = [line.strip() for line in fh if line.strip() and not line.startswith("#")]

setup(
    name="bsd-spectral",
    version="1.0.0",
    author="José Manuel Mota Burruezo",
    author_email="institutoconsciencia@proton.me",
    description="Resolución espectral de la conjetura de Birch y Swinnerton-Dyer",
    long_description=long_description,
    long_description_content_type="text/markdown",
    url="https://github.com/motanova84/adelic-bsd",
    project_urls={
        "Homepage": "https://github.com/motanova84/adelic-bsd",
        "Documentation": "https://github.com/motanova84/adelic-bsd/blob/main/README.md",
        "Repository": "https://github.com/motanova84/adelic-bsd",
        "Issues": "https://github.com/motanova84/adelic-bsd/issues",
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
    keywords=["elliptic-curves", "bsd-conjecture", "number-theory", "spectral-methods"],
    python_requires=">=3.9",
    install_requires=requirements,
    include_package_data=True,
    zip_safe=False,
)
