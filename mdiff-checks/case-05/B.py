 # -*- coding: utf-8 -*-
"""
IPython -- An enhanced Interactive Python

One of Python's nicest features is its interactive interpreter. This allows
very fast testing of ideas without the overhead of creating test files as is
typical in most programming languages. However, the interpreter supplied with
the standard Python distribution is fairly primitive (and IDLE isn't really
much better).

IPython tries to:

  i - provide an efficient environment for interactive work in Python
  programming. It tries to address what we see as shortcomings of the standard
  Python prompt, and adds many features to make interactive work much more
  efficient.

  ii - offer a flexible framework so that it can be used as the base
  environment for other projects and problems where Python can be the
  underlying language. Specifically scientific environments like Mathematica,
  IDL and Mathcad inspired its design, but similar ideas can be useful in many
  fields. Python is a fabulous language for implementing this kind of system
  (due to its dynamic and introspective features), and with suitable libraries
  entire systems could be built leveraging Python's power.

  iii - serve as an embeddable, ready to go interpreter for your own programs.

IPython requires Python 2.4 or newer.
"""

#*****************************************************************************
#       Copyright (C) 2008-2009 The IPython Development Team
#       Copyright (C) 2001-2007 Fernando Perez. <fperez@colorado.edu>
#
#  Distributed under the terms of the BSD License.  The full license is in
#  the file COPYING, distributed as part of this software.
#*****************************************************************************

# Enforce proper version requirements
import sys

if sys.version[0:3] < '2.4':
    raise ImportError('Python Version 2.4 or above is required for IPython.')

# Make it easy to import extensions - they are always directly on pythonpath.
# Therefore, non-IPython modules can be added to extensions directory
import os
sys.path.append(os.path.join(os.path.dirname(__file__), "extensions"))

# Define what gets imported with a 'from IPython import *'
__all__ = ['IPython.core.ipapi','utils.generics','utils.ipstruct',
    'core.release','core.shell']

# Load __all__ in IPython namespace so that a simple 'import IPython' gives
# access to them via IPython.<name>
glob,loc = globals(),locals()
for name in __all__:
    #print 'Importing: ',name # dbg
    __import__(name,glob,loc,[])

from IPython.core import shell
Shell = shell
from IPython.core import ipapi
from IPython.core import iplib

from IPython.lib import (
    enable_wx, disable_wx,
    enable_gtk, disable_gtk,
    enable_qt4, disable_qt4,
    enable_tk, disable_tk,
    set_inputhook, clear_inputhook,
    current_gui, spin,
    appstart_qt4, appstart_wx,
    appstart_gtk, appstart_tk
)

# Release data
from IPython.core import release # do it explicitly so pydoc can see it - pydoc bug
__author__   = '%s <%s>\n%s <%s>\n%s <%s>' % \
               ( release.authors['Fernando'] + release.authors['Janko'] + \
                 release.authors['Nathan'] )
__license__  = release.license
__version__  = release.version
__revision__ = release.revision

# Namespace cleanup
del name,glob,loc
