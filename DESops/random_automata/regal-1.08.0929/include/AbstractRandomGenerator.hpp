// AbstractRandomGenerator.hpp: this file is part of the REGAL project.
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
#ifndef ABSTRACTRANDOMGENERATOR
#define ABSTRACTRANDOMGENERATOR

namespace regal{

  template<class Type>
  class AbstractRandomGenerator{
  public:
    /**
       Returns an randomly generated element
       @Return an randomly generated element
    */
    virtual Type * random()=0;

    virtual ~AbstractRandomGenerator(){};
  };

}

#endif
