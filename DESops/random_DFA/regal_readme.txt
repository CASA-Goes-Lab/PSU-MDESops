regal is a c++ program, requires local compilation


For now, need to install regal and its prerequisites, and then compile the executable used to generate random DFA's.

Following these instructions will create a file in the DESops/random_DFA/regal-1.08.0929 directory called "random_DFA"
This is the executable called by the generate_random_DFA python function.

If the installation and compilation of random_DFA is unsuccessful or the file isn't found, an error will be raised
when importing the random_DFA python module

e.g.

>>> desops.random_DFA.generate(...) # Will exit w/ error code if random_DFA not installed

To install regal and DESops script:

0. Install prerequisites for regal
    libxml++-2.4    (this is version 2.6 of libxml++)
    Link: http://ftp.gnome.org/pub/GNOME/sources/libxml++/2.40/

libxml++ also requires:
    libxml2
    Link: http://www.xmlsoft.org/

    glibmm-2.4
    Link: https://www.gtkmm.org/en/


1. Install regal (see README file in the regal directory for more details)

If user:

    make install-user

If root:
    make install

2. Compile random_DFA executable:

    make desops
