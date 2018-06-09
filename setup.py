#*****************************************************************************
#
#    Copyright (C) 2009-2018 Christian Nassau <nassau@nullhomotopie.de>
#
#  Distributed under the terms of the GNU General Public License (GPL),
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from distutils.core import setup
from distutils.extension import Extension

#import shutil
#import os
#import subprocess

setup(
  name = "yacop",
  version = "2.0",
  author = "Christian Nassau",
  author_email = "nassau@nullhomotopie.de",
  maintainer = "Christian Nassau", 
  maintainer_email = "nassau@nullhomotopie.de",
  url = "http://nullhomotopie.de",
  description = "Yacop - Steenrod algebra cohomology",
  packages=["yacop","yacop.resolutions","yacop.modules","yacop.utils"],
)
