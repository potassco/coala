from distutils.core import setup
from distutils.command.install import INSTALL_SCHEMES

for scheme in INSTALL_SCHEMES.values():
    scheme['data'] = scheme['purelib']

setup(
    # Application name:
    name="coala",

    # Version number (initial):
    version="2.432",

    # Application author details:
    author="Christian Schulz-Hanke",
    author_email="Christian.Schulz-Hanke@cs.uni-potsdam.de",

    # Packages
    packages=["coala","coala.parse","coala.bc","coala.bc_legacy","coala.bcLc","coala.b","coala.bcAgent","coala.bcAgent_legacy","ply"],

    #
    scripts=["coala/coala","outputformatclingocoala"],

    # Include additional files into the package
    #include_package_data=True,

    # Details
    url="http://www.cs.uni-potsdam.de/wv/coala2/",

    #
    # license="LICENSE.txt",
    description="coala - Action Language Translation Tool.",

    # long_description=open("README.txt").read(),
    long_description=open("README.txt").read(),

    # Dependent packages (distributions)
    #install_requires=[
    #    "flask",
    #],

    data_files=[('', ['README_BC.txt'])]+ \
             [
            ("encodings",["encodings/base.lp", "encodings/base_translation.lp", \
                "encodings/csp.lp", "encodings/incremental.lp", "encodings/incremental_clingo.lp", "encodings/solve_incremental.lp"]), \
            ("encodings/internal", ["encodings/internal/arithmetic.lp", \
                "encodings/internal/csp.lp", \
                "encodings/internal/fixed.lp", \
                "encodings/internal/fixed_not_decoupled.lp", \
                "encodings/internal/iterative.lp", \
                "encodings/internal/iterative_not_decoupled.lp", \
                "encodings/internal/states.lp", \
                "encodings/internal/states_not_decoupled.lp", \
                "encodings/internal/transitions.lp", \
                "encodings/internal/transitions_not_decoupled.lp"])
            ]
)

# Build: python setup.py sdist
