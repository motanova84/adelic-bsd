"""
Setup script for Mota Burruezo Spectral BSD Framework
"""

from setuptools import setup, find_packages

with open("README.md", "r", encoding="utf-8") as fh:
    long_description = fh.read()

with open("requirements.txt", "r", encoding="utf-8") as fh:
    requirements = [line.strip() for line in fh if line.strip() and not line.startswith("#")]

setup(
    name="algoritmo-spectral",
    version="0.1.0",
    author="Mota Burruezo",
    author_email="",
    description="Spectral finiteness proof for Tate–Shafarevich groups",
    long_description=long_description,
    long_description_content_type="text/markdown",
    url="https://github.com/motanova84/algoritmo",
    packages=find_packages(),
    classifiers=[
        "Development Status :: 3 - Alpha",
        "Intended Audience :: Science/Research",
        "Topic :: Scientific/Engineering :: Mathematics",
        "License :: OSI Approved :: MIT License",
        "Programming Language :: Python :: 3",
        "Programming Language :: Python :: 3.9",
        "Programming Language :: Python :: 3.10",
        "Programming Language :: Python :: 3.11",
    ],
    python_requires=">=3.9",
    install_requires=requirements,
    entry_points={
        "console_scripts": [
            "spectral-demo=examples.quick_demo:main",
        ],
    },
    include_package_data=True,
    zip_safe=False,
)
