// RandomDFAGenerator.hpp: this file is part of the REGAL project.
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
#ifndef RANDOMTREEAUTOMATONGENERATOR
#define RANDOMTREEAUTOMATONGENERATOR

#include "AbstractRandomGenerator.hpp"
#include "AbstractAutomaton.hpp"
#include "toolbox/GenericFunction.hpp"
#include "VerboseOption.hpp"



namespace regal{

  template<typename StateLabel_t,typename Sigma, class Automaton_t=AbstractAutomaton<StateLabel_t,Sigma> >
  class RandomTreeAutomatonGenerator :
    public AbstractRandomGenerator<Automaton_t>{
  private:

    StateLabel_t * randomMap_state;
    Sigma * randomMap_letter;
    int size,asize;
    Alphabet<Sigma> alphabet;
    Automaton_t * result;
    double probability;


    void reinitTransitions(){
      std::list<Sigma> listT=alphabet.getList();
      typename std::list<Sigma>::iterator l;
      for(int i=0;i<size;i++)
	for(l=listT.begin();l!=listT.end();l++)
	  result->addTransition(result->getRealValue(i),result->getRealValue(-1),*l);

    }

    /**
       Randomdly assign the final states on the generated automaton
    */
    void randomFinalization(){
      int i;
      StateLabel_t state;
      for(i=0;i<size;i++){
	state=result->getRealValue(i);

	if(((rand()%RAND_MAX)/(double)RAND_MAX)<probability)
	  result->setStateAsFinal(state,true);
	else
	  result->setStateAsFinal(state,false);
      }
    }

  public:



    Automaton_t * random(){
      std::list<Sigma> listT=alphabet.getList();
      typename std::list<Sigma>::iterator l;
      int randomValue,i,j;

      reinitTransitions();

      for(j=0,l=listT.begin();l!=listT.end();l++,j++){
	randomMap_state[j]=result->getRealValue(0);
	randomMap_letter[j]=*l;
      }

      for(i=1;i<size;i++){
	randomValue=rand()%((asize-1)*i+1);
	result->addTransition(randomMap_state[randomValue],result->getRealValue(i),randomMap_letter[randomValue]);

	l=listT.begin();

	randomMap_state[randomValue]=result->getRealValue(i);
	randomMap_letter[randomValue]=*l;
	for(j=0,l++;l!=listT.end();l++,j++){
	  randomMap_state[(asize-1)*i+1+j]=result->getRealValue(i);
	  randomMap_letter[(asize-1)*i+1+j]=*l;
	}
      }

      randomFinalization();
      return result;
    }

    RandomTreeAutomatonGenerator(const int & autSize,const Alphabet<Sigma> & alpha,
				 const double & prob=0.5):alphabet(alpha){
      int i;
      time_t t;
      srand(time(&t));
      size=autSize;
      probability=prob;
      asize=alphabet.getSize();
      randomMap_state=new StateLabel_t[(asize-1)*size+1];
      randomMap_letter=new Sigma[(asize-1)*size+1];
      result=new Automaton_t(size,alphabet);
      for(i=0;i<size;i++)
	result->addState();
    }

    ~RandomTreeAutomatonGenerator(){
      delete [] randomMap_state;
      delete [] randomMap_letter;
      delete result;
    }


  };

}

#endif
