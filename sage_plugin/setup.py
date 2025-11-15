from setuptools import setup, find_packages

setup(
    name="adelic_bsd",
    version="0.1.0",
    description="Verificación espectral de la conjetura BSD usando SageMath con QCAL Beacons",
    author="José Manuel Mota Burruezo",
    packages=find_packages(),
    install_requires=[
        "cryptography>=41.0.0,<44.0.0",
    ],
    python_requires=">=3.9",
    classifiers=[
        "Development Status :: 3 - Alpha",
        "Intended Audience :: Science/Research",
        "Topic :: Scientific/Engineering :: Mathematics",
        "Programming Language :: Python :: 3",
        "Programming Language :: Python :: 3.9",
        "Programming Language :: Python :: 3.10",
        "Programming Language :: Python :: 3.11",
        "Programming Language :: Python :: 3.12",
        "Programming Language :: Python :: 3.13",
        "Operating System :: OS Independent",
    ],
)
