// CoAccessible.hpp: this file is part of the REGAL project.
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
#ifndef COACCESSIBLE_HPP
#define COACCESSIBLE_HPP

#include<iostream>
#include<list>
#include<deque>
#include "ReverseDFAAlgorithm.hpp"

namespace regal{

  template<typename StateLabel_t,typename Sigma,class Automaton_t=AbstractAutomaton<StateLabel_t,Sigma> >
  class CoAccessibleTester{

  public:
    static bool testCoAccessibility(Automaton_t * a,const int* states=NULL,const int & num=-1){
      int n=a->getSize(),i;
      int asize=a->getAlphabetSize();
      std::list<int> * currentList;
      ReverseDFAAlgorithm<StateLabel_t,Sigma,Automaton_t> rda;
      bool * traversedStates=new bool[n];
      std::deque<int> stateStack;
      std::list<int> ** reverse=rda.reverseDFA(a);

      for(i=0;i<n;i++){
	if(a->isFinal(a->getRealValue(i))){
	  stateStack.push_front(i);
	  traversedStates[i]=true;
	}
	else
	  traversedStates[i]=false;
      }

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

      if(num==-1){
	for(i=0;i<n;i++)
	  if(traversedStates[i]==false){
	    delete [] traversedStates;
	    return false;
	  }
      }
      else{
	for(i=0;i<num;i++){
	  if(traversedStates[states[i]]==false){
	    delete [] traversedStates;
	    return false;
	}
	}
      }
      delete [] traversedStates;
      return true;
    }


  };

}

#endif
