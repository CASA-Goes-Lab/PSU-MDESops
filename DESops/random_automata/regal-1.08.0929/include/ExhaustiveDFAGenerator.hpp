// ExhaustiveDFAGenerator.hpp: this file is part of the REGAL project.
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
#ifndef EXHAUSTIVEDFAGENERATOR
#define EXHAUSTIVEDFAGENERATOR

#include "AbstractExhaustiveGenerator.hpp"
#include "AbstractDFAGenerator.hpp"
#include "VerboseOption.hpp"
#include "StronglyConnected.hpp"
#include "CoAccessible.hpp"
#include "MooreAlgorithm.hpp"

namespace regal{

  template<typename StateLabel_t,typename Sigma, class Automaton_t=AbstractAutomaton<StateLabel_t,Sigma> >
  class ExhaustiveDFAGenerator :
    public AbstractExhaustiveGenerator<Automaton_t>, AbstractDFAGenerator<StateLabel_t,Sigma,Automaton_t>{
  private:
    CatalanSuit * catS; /*!< Word of Dyck that will be converted into a Trie */
    CompletionSuit *comS; /*!< CompletionSuit that will be used to complete the Trie into a complete DFA */
    int lastFinal; /*!< used for finalization in the exhaustive genneration */
    int finalCounter; /*!< counts how much final state there is in the automaton */

    /**
       Set all states as not final
    */
    bool firstFinalise(){
      for(lastFinal=0;lastFinal<this->result->getSize();lastFinal++)
	this->result->setStateAsFinal(this->result->getRealValue(lastFinal),false);
      lastFinal--;
      finalCounter=0;
      return true;
    }

    /**
       Used to make a finalization of an automaton. Generate successively  all possibility
    */
    bool nextFinalize(){
      while(this->result->isFinal(this->result->getRealValue(lastFinal))){
	lastFinal--;
	if(lastFinal<0)return false;
      }
      this->result->setStateAsFinal(this->result->getRealValue(lastFinal),true);
      finalCounter++;
      for(lastFinal++;lastFinal<this->result->getSize();lastFinal++){
	this->result->setStateAsFinal(this->result->getRealValue(lastFinal),false);
	finalCounter--;
      }
      lastFinal--;
      return true;
    }



  public:

    /**
       Returns the first generated automaton
       @Return the first generated automaton
    */
    Automaton_t * first(){
      catS->first();
      comS->first();
      //cout<<*catS<<" - "<<*comS<<endl;
      this->suitToDFA(catS->getSuit(),comS->getSuit());
      firstFinalise();
      return this->result;
    }

    /**
       Returns the next generated automaton, and NULL if the generation has ended.
       @Return the next generated automaton, and NULL if the generation has ended.
    */
    Automaton_t * next(){
      if(!nextFinalize()){
	if(comS->next()==NULL){
	  if(catS->next()==NULL)
	    return NULL;
	  comS->first();
	  this->suitToDFA(catS->getSuit(),comS->getSuit());
	}
	else
	  this->DFAcompletion(comS->getSuit(),comS->getModifiedPosition());
	firstFinalise();
	//cout<<*catS<<" - "<<*comS<<endl;
      }
      return this->result;
    }


    int getFinalCounter(){return finalCounter;}

    /**
       Returns the next generated automaton, and NULL if the generation has ended.
       This iterator is special because it only doesn't return automata with more than n/2 final states.
       Therefore, only half of the set is generated, and the other half is the complementary of the first.
       @Return the next generated automaton, and NULL if the generation has ended.
    */
    Automaton_t * nextComplementary(){
      bool finalTest;
      int p=this->result->getSize()/2;
      do{
	finalTest=nextFinalize();
      }while(finalTest==true&&finalCounter>p);
      if(!finalTest){
	if(comS->next()==NULL){
	  if(catS->next()==NULL)
	    return NULL;
	  comS->first();
	  this->suitToDFA(catS->getSuit(),comS->getSuit());
	}
	else
	  this->DFAcompletion(comS->getSuit(),comS->getModifiedPosition());
	firstFinalise();
	//cout<<*catS<<" - "<<*comS<<endl;
      }
      return this->result;
    }



    Automaton_t * end(){return NULL;}

    /**
       Create an exhaustive DFA Generator
       @param autSize is the number of states in the generated automatons
       @param alphaSize is the size of the alphabet in the generated automatons
    */
    ExhaustiveDFAGenerator(const int & autSize,const Alphabet<Sigma> & alpha):
      AbstractDFAGenerator<StateLabel_t,Sigma,Automaton_t>::AbstractDFAGenerator(autSize,alpha){

      catS=new CatalanSuit(this->result->getSize(),alpha.getSize());
      comS=new CompletionSuit(catS);
      verbose("Creation of the ExhaustiveDFAGenerator");
    }


    /**
       Destroy the ExhaustiveDFAGenerator
    */
    virtual ~ExhaustiveDFAGenerator(){
      delete catS;
      delete comS;
      verbose("Destruction of the ExhaustiveDFAGenerator");

    }

  };

}

#endif
