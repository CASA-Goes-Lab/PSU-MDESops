// AbstractExhaustiveGenerator.hpp: this file is part of the REGAL project.
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
#ifndef ABSTRACTEXHAUSTIVEGENERATOR
#define ABSTRACTEXHAUSTIVEGENERATOR

namespace regal{

  template<class Type>
  class AbstractExhaustiveGenerator{
  public:
    /**
       Returns the first generated element
       @Return the first generated element
    */
    virtual Type * first()=0;
    /**
       Returns the next generated element
       @Return the next generated element
    */
    virtual Type * next()=0;
    /**
       Returns an element that indicates the generation is over
       @Return an element that indicates the generation is over
    */
    virtual Type * end()=0;

    virtual ~AbstractExhaustiveGenerator(){}
  };

}


#endif
