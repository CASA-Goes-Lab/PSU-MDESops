// CatalanSuit.hpp: this file is part of the REGAL project.
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
#ifndef CATALANSUIT
#define CATALANSUIT

#include "toolbox/GenericFunction.hpp"
#include "AbstractSuit.hpp"


namespace regal{
  class CatalanSuit: public AbstractSuit{
  private:
    int automatonSize; /*!< Number of state in the automaton */
    int alphabetSize; /*!< Size of the alphabet */

  public:
    int * first();
    int * next();

    /**
       Returns the value of the suit at the position pos if pos is smaller than size
       and automatonSize otherwise.
       @param pos is the position we wants to have an information on
       @Return the value of the suit at the position pos if pos is smaller than size
       and automatonSize otherwise.
    */
    int getMax(const int & pos){return (pos<size)?Min(tab[pos],automatonSize):automatonSize;}

    /**
       Creates a catalen suit
       @param autSize is the states number of the automaton
       @param alphaSize is the size of the alphabet
    */
    CatalanSuit(const int & autSize,const int alphaSize):AbstractSuit::AbstractSuit((alphaSize-1)*autSize+1){
      automatonSize=autSize;
      alphabetSize=alphaSize;
      verbose("Creation of a CatalanSuit");
    }

    /**
       Destroy a CatalanSuit
    */
    virtual ~CatalanSuit(){
      verbose("Destruction of a CatalanSuit");
    }
  };

}

#endif
