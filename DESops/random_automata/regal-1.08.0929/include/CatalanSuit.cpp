// CatalanSuit.cpp: this file is part of the REGAL project.
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
#include "CatalanSuit.hpp"


namespace regal{

  /**
     Returns the first tabular of integers, which is in bijection
     with paths of Dyck and uncomplete DFA Automaton.
     This is the first step for DFA generation.
     Rule: Max(i,p[i-1]) <= p[i] <= size
     @Return 1 2 3 .... n
  */
  int * CatalanSuit::first(){
    for(position=0;position<(size-1);position++)
      tab[position]=position/(alphabetSize-1)+1;
    tab[position]=automatonSize;
    position--;
    return tab;
  }


  /**
     Returns a tabular of integers, which is in bijection
     with paths of Dyck and uncomplete DFA Automaton.
     This is the first step for DFA generation.
     Rule: Max(i,p[i-1]) <= p[i] <= size
     @Return the next tab, according to the construction rule, and NULL if
     the construction is over.
  */
  int * CatalanSuit::next(){
    while(tab[position]++>=automatonSize){
      position--;
      if(position<0)return NULL;
    }
    for(position++;position<size-1;position++){
      tab[position]=Max(tab[position-1],position+1);
    }
    position--;
    return tab;
  }

}
