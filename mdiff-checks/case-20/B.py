# Author: Alexandre Gramfort <alexandre.gramfort@inria.fr>
# License: BSD Style.

import numpy


def configuration(parent_package='', top_path=None):
    from numpy.distutils.misc_util import Configuration
    config = Configuration('cluster', parent_package, top_path)
    config.add_extension('_inertia',
                         sources=['_inertia.c'],
                         include_dirs=[numpy.get_include()])
    config.add_extension('_k_means',
                         sources=['_k_means.c'],
                         include_dirs=[numpy.get_include()]
                         )

    return config

if __name__ == '__main__':
    from numpy.distutils.core import setup
    setup(**configuration(top_path='').todict())
