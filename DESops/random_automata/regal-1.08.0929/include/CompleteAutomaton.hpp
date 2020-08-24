// CompleteAutomaton.hpp: this file is part of the REGAL project.
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
#ifndef COMPLETEAUTOMATON_HPP
#define COMPLETEAUTOMATON_HPP

#include<iostream>



namespace regal{

  template<typename StateLabel_t,typename Sigma,class Automaton_t=AbstractAutomaton<StateLabel_t,Sigma> >
  class CompleteAutomaton{

  public:
    static bool completeAutomaton(Automaton_t * a){
      int n=a->getSize(),i;
      StateLabel_t newState;
      bool incomplete=false;
      Alphabet<Sigma> al=a->getAlphabet();
      std::list<Sigma> listT=al.getList();
      for(i=0;i<n;i++){
	for(typename std::list<Sigma>::iterator l=listT.begin();l!=listT.end();l++){
	  if(a->getArrivalState(a->getRealValue(i),*l)==a->undefinedTransition()){
	    if(!incomplete){
	      incomplete=true;
	      newState=a->addState();
	      for(typename std::list<Sigma>::iterator l2=listT.begin();l2!=listT.end();l2++)
		a->addTransition(newState,newState,*l2);
	    }
	    a->addTransition(a->getRealValue(i),newState,*l);
	  }
	}
      }
      return incomplete;
    }

  };

}

#endif
