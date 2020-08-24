// CompletionSuit.cpp: this file is part of the REGAL project.
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
#include "CompletionSuit.hpp"


namespace regal{

  /**
     Returns the first tabular of integers, which allows us
     to complete the generated automaton. Depends on a list
     of restiction.
     Rule : 1 <= p[i] <= Rule(p[i])
     @Return 1 1 .... 1
  */
  int * CompletionSuit::first(){
    int i;
    for(position=0,i=1;position<size;position++)
      tab[position]=i;
    position--;
    modifiedPosition=0;
    return tab;
  }



  /**
     Returns the first tabular of integers, which allows us
     to complete the generated automaton. Depends on a list
     of restiction.
     Rule : 1 <= p[i] <= Rule(p[i])
     @Return the next tab, according to the construction rule, and NULL if
     the construction is over.
  */
  int * CompletionSuit::next(){
    while(tab[position]++>=catalanSuit->getMax(position)){
      position--;
      if(position<0)
	return NULL;
    }
    modifiedPosition=position;
    for(position++;position<size;position++)
      tab[position]=1;
    position--;
    return tab;
  }

}
