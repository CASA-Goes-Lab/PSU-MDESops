// MinimizingAlgorithm.hpp: this file is part of the REGAL project.
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
#ifndef MINIMIZINGALGORITHM
#define MINIMIZINGALGORITHM

#include "AbstractAutomaton.hpp"
#include <iostream>

#include <list>
#include <vector>
#include <deque>

namespace regal{

  template<typename StateLabel_t,typename Sigma,class Automaton_t=AbstractAutomaton<StateLabel_t,Sigma> >
  class MinimizingAlgorithm{
  protected:
    int size;
    int maxClass;
    int * partitionRes;


  public:
    /**
       Minimize an automaton and returns a partition of the states.
       @param a is the automaton to minimize
       @Return partition of the states in the minimized automaton
    */
    virtual int * minimizeToPartition(Automaton_t * a,const int & it=-1)=0;




    virtual unsigned int * minimizeMultipleComplexity(Automaton_t * a)=0;
    MinimizingAlgorithm(){}
    virtual ~MinimizingAlgorithm(){}

  };
}



#endif
