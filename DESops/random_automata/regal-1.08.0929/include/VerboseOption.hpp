// VerboseOption.hpp: this file is part of the REGAL project.
//
// REGAL : Random and Exhaustive Generators for Automata - Library
//
// Copyright (C) 2007 Julien DAVID.
//
// This program is free software; you can redistribute it and/or
// modify it under the terms of the GNU General Public License
// as published by the Free Software Foundation; either version 2
// of the License, or (at your option) any later version.
//
// The complete GNU General Public Licence Notice can be found as the
// `COPYING' file in the root directory.
//
//
#ifndef VERBOSEOPTION
#define VERBOSEOPTION

#include<iostream>


/**
   Only used in verbose mode
   Prints an output stream
   @param o stream to print
*/
template<typename T>
void verbose(const T & o){

#ifdef VERBOSE_MODE
  std::cout<<o<<std::endl;
#endif

}






#endif
