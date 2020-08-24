// RandomCompleteICDFAGenerator.hpp: this file is part of the REGAL project.
//
// REGAL : Random and Exhaustive Generators for Automata - Library
//
// Copyright (C) 2008 Julien DAVID.
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
#ifndef RANDOMCOMPLETEICDFAGENERATOR
#define RANDOMCOMPLETEICDFAGENERATOR

#include "RandomDFAGenerator.hpp"



namespace regal{

  template<typename StateLabel_t,typename Sigma, class Automaton_t=AbstractAutomaton<StateLabel_t,Sigma> >
  class RandomCompleteICDFAGenerator :
    public RandomDFAGenerator<StateLabel_t,Sigma,Automaton_t>{
  public:


    /**
      Facade to create a random generator for complete deterministic accessible automata.
      See RandomDFAGenerator to acces the methods
    */
    RandomCompleteICDFAGenerator(const int & autSize,const Alphabet<Sigma> & alpha,const double & prob=0.5):
      RandomDFAGenerator<StateLabel_t,Sigma,Automaton_t>::RandomDFAGenerator(autSize,alpha,prob,false){};

    ~RandomCompleteICDFAGenerator(){}

  };



}

#endif
