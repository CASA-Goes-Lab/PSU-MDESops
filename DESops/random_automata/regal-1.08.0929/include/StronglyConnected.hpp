// Stronglyconnected.hpp: this file is part of the REGAL project.
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
#ifndef STRONGLYCONNECTED_HPP
#define STRONGLYCONNECTED_HPP

#include<iostream>
#include<list>
#include<deque>
#include "ReverseDFAAlgorithm.hpp"

namespace regal{

  template<typename StateLabel_t,typename Sigma,class Automaton_t=AbstractAutomaton<StateLabel_t,Sigma> >
  class StronglyConnectedTester{

  public:
    static bool testConnectability(Automaton_t * a){
      int n=a->getSize(),i;
      int asize=a->getAlphabetSize();
      std::list<int> * currentList;
      ReverseDFAAlgorithm<StateLabel_t,Sigma,Automaton_t> rda;
      bool * traversedStates=new bool[n];
      bool res=true;
      std::deque<int> stateStack;
      std::list<int> ** reverse=rda.reverseDFA(a);

      for(i=0;i<n;i++)
	traversedStates[i]=false;

      stateStack.push_front(0);
      traversedStates[0]=true;
      while(!stateStack.empty()){
	currentList=reverse[stateStack.front()];
	stateStack.pop_front();
	for(i=0;i<asize;i++){
	  for(std::list<int>::iterator currentInt=currentList[i].begin();currentInt!=currentList[i].end();currentInt++){
	    if(!traversedStates[*currentInt]){
	      traversedStates[*currentInt]=true;
	      stateStack.push_front(*currentInt);
	    }
	  }
	}
      }

      for(i=0;i<n;i++)
	if(traversedStates[i]==false){
	  res=false;
	  break;
	}

      delete [] traversedStates;
      return res;

    }

  };

}

#endif
