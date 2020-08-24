// ReverseDFAAlgorithm.hpp: this file is part of the REGAL project.
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
#ifndef REVERSEDFAALGORITHM
#define REVERSEDFAALGORITHM

#include "Alphabet.hpp"
#include "AbstractAutomaton.hpp"
#include "toolbox/GenericFunction.hpp"

#include <list>
#include <iostream>

using namespace std;

namespace regal{

  template<typename StateLabel_t,typename Sigma,class Automaton_t=AbstractAutomaton<StateLabel_t,Sigma> >
  class ReverseDFAAlgorithm{
  private:
    list<int> ** data;
    int automatonSize;
    int alphabetSize;

    void initMemory(Automaton_t * a){
      freeMemory();
      automatonSize=a->getSize();
      alphabetSize=a->getAlphabet().getSize();
      data=new list<int> *[automatonSize];
      for(int i=0;i<automatonSize;i++)
	data[i]=new list<int>[alphabetSize];
    }


    void freeMemory(){
      if(automatonSize!=0){
	for(int i=0;i<automatonSize;i++)
	  delete [] data[i];
	delete [] data;
      }
    }

  public:

    list<int> ** reverseDFA(Automaton_t * a){
      int i,arrival;
      initMemory(a);
      Alphabet<Sigma> alphabet=a->getAlphabet();
      typename std::list<Sigma> alphabetL=alphabet.getList();
      for(i=0;i<automatonSize;i++){
	for(typename std::list<Sigma>::iterator l=alphabetL.begin();l!=alphabetL.end();l++){
	  arrival=a->getArrivalNumericalState(i,*l);
	  if(arrival!=-1)
	    data[arrival][alphabet.getNumericalValue(*l)].push_back(i);
	}
      }
      return data;
    }



    ReverseDFAAlgorithm(){
      automatonSize=0;
      alphabetSize=0;
      data=NULL;
    }

    ~ReverseDFAAlgorithm(){
      freeMemory();
    }


  };

}


#endif
