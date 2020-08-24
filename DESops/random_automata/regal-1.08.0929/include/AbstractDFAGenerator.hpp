// AbstractDFAAutomaton.hpp: this file is part of the REGAL project.
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
#ifndef ABSTRACTDFAGENERATOR
#define ABSTRACTDFAGENERATOR

#include "CatalanSuit.hpp"
#include "CompletionSuit.hpp"
#include "AbstractAutomaton.hpp"
#include "VerboseOption.hpp"

#include<queue>
#include<stack>
#include<iterator>
#include<map>

namespace regal{

  template<typename StateLabel_t,typename Sigma>
  class DFA_Generator_transition{
  public:
    StateLabel_t state;
    Sigma word;
    DFA_Generator_transition(const StateLabel_t & s,const Sigma & w){
      state=s;
      word=w;
    }
    DFA_Generator_transition(){
    }
  };


  template<typename StateLabel_t,typename Sigma, class Automaton_t=AbstractAutomaton<StateLabel_t,Sigma> >
  class AbstractDFAGenerator{


  protected:
    int stateQueueSize;
    Automaton_t * result; /*!< Value returned by the generator: allocated only once */
    //std::queue<DFA_Generator_transition<StateLabel_t,Sigma> > stateQueue;
    DFA_Generator_transition<StateLabel_t,Sigma> * stateQueue;


    /**
       Checks if a generated suit is a catalan suit
       @param s is the suit to test
       @param incomplete is an heuristic to transform a complete ICDFA generator into a non-complete one
       @Returns true if s is a suit of Catalan, false otherwise
    */
    bool isACatalanSuit(int * s,const int & incomplete=0){
      int i;
      for(i=0;i<(result->getSize()*(result->getAlphabetSize()-1));i++)
	if((s[i]-incomplete)<((i/(result->getAlphabetSize()-1))+1))return false;
      if((s[i]-incomplete)!=result->getSize())
	return false;
      return true;
    }

    /**
       Checks if a generated set partition can be transformed in an automaton
       @param s is the set partition to test
       @param incomplete is an heuristic to transform a complete ICDFA generator into a non-complete one
       @Returns true if s is a valid set partition, false otherwise
    */
    bool isAValidSetPartition(int * s,const int & incomplete=0){
      int i,max=-1;
      int asize=result->getAlphabetSize();
      for(i=incomplete;i<(result->getSize()*asize);i++){
	max=(s[i]>max)?s[i]:max;
	if(i%asize==0 && (max-incomplete)<(i/asize))
	  return false;
      }

      return true;
    }


    /**
       1st part of the Bassino-Nicaud Algorithm
       Build up a trie, using the suit
       @param suit is one of the 2 Integer lists used to build the automaton
    */
    void suitToTrie(int * suit,const int & incomplete=0){
      std::stack<DFA_Generator_transition<StateLabel_t,Sigma> > transitionStack;
      DFA_Generator_transition<StateLabel_t,Sigma> dfagt;
      StateLabel_t tmp=result->getRealValue(0);
      std::list<Sigma> listT=result->getAlphabet().getList();
      int i,j,counter;
      result->setStateAsInitial(tmp,true);

      for(typename std::list<Sigma>::reverse_iterator l=listT.rbegin();l!=listT.rend();l++){
	dfagt.word=*l;
	dfagt.state=tmp;
	transitionStack.push(dfagt);
      }

      for(i=0,counter=1,j=1;i<(result->getSize()*(result->getAlphabetSize()-1));i++){
	while(j<(suit[i]-incomplete)){
	  dfagt=transitionStack.top();
	  transitionStack.pop();
	  tmp=result->getRealValue(j);
	  result->addTransition(dfagt.state,tmp,dfagt.word);

	  for(typename std::list<Sigma>::reverse_iterator l=listT.rbegin();l!=listT.rend();l++){
	    dfagt.word=*l;
	    dfagt.state=tmp;
	    transitionStack.push(dfagt);
	  }
	  counter++;
	  j++;
	}
	stateQueue[i]=transitionStack.top();
	transitionStack.pop();
      }
      stateQueue[i]=transitionStack.top();
      transitionStack.pop();
    }

    /**
       2nd part of the Bassino-Nicaud Algorithm
       Complete the automaton, using the completion suit and a trie
       @param suit is one of the 2 Integer lists used to build the automaton
       @param incomplete is an heuristic to transform a complete ICDFA generator into a non-complete one
    */
    void DFAcompletion(int * completion,const int & modifiedPosition,const int & incomplete=0){
      DFA_Generator_transition<StateLabel_t,Sigma> dfagt;
      int i=modifiedPosition;
      while(i<stateQueueSize){
	dfagt=stateQueue[i];
	result->addTransition(dfagt.state,completion[i]-1-incomplete,dfagt.word);
	i++;
      }
    }

    /**
       Bassino-David-Nicaud Algorithm
       Trandform a set partition directly into an automaton
       @param setPartition is the set partition to tranform
       @param incomplete is an hauristic that allows to genere incomplete automata
    */
    void setToDFA(int * setPartition,const int & incomplete=0){
      std::stack<DFA_Generator_transition<StateLabel_t,Sigma> > transitionStack;
      DFA_Generator_transition<StateLabel_t,Sigma> dfagt;
      StateLabel_t tmp=result->getRealValue(0);
      std::list<Sigma> listT=result->getAlphabet().getList();
      int i,counter;
      result->setStateAsInitial(tmp,true);

      for(typename std::list<Sigma>::reverse_iterator l=listT.rbegin();l!=listT.rend();l++){
	dfagt.word=*l;
	dfagt.state=tmp;
	transitionStack.push(dfagt);
      }



      for(i=1,counter=0;i<(result->getSize()*result->getAlphabetSize()+1);i++){
      	dfagt=transitionStack.top();
	transitionStack.pop();
	tmp=result->getRealValue(setPartition[i]-incomplete);
	result->addTransition(dfagt.state,tmp,dfagt.word);
	//std::cout<<dfagt.state<<"."<<dfagt.word<<"="<<tmp<<std::endl;


	if(tmp==(counter+1)){
	  for(typename std::list<Sigma>::reverse_iterator l=listT.rbegin();l!=listT.rend();l++){
	    dfagt.word=*l;
	    dfagt.state=tmp;
	    transitionStack.push(dfagt);
	  }
	  counter++;
	}
      }
    }

    /**
       Bassino-Nicaud Algorithm
       Fill the automaton result using the suits
       @param catalan is the Catalan suit used to build the Tree automaton
       @param completion is the suit used to complete the filling
    */
    void suitToDFA(int * catalan,int * completion,const int &incomplete=0){
      suitToTrie(catalan,incomplete);
      DFAcompletion(completion,0,incomplete);
    }

    AbstractDFAGenerator(const int & autSize,const Alphabet<Sigma> & alpha){
      result=new Automaton_t(autSize,alpha);
      stateQueueSize=(alpha.getSize()-1)*autSize+1;
      stateQueue=new DFA_Generator_transition<StateLabel_t,Sigma>[stateQueueSize];
      for(int i=0;i<autSize;i++)
	result->addState();
      verbose("Creation of an AbstractDFAGenerator");
    }

    virtual ~AbstractDFAGenerator(){
      delete result;
      delete [] stateQueue;
      verbose("Destruction of an AbstractDFAGenerator");
    }

  public:
    /**
       Returns the size of the generated automatons
       @Return the size of the generated automatons
    */
    int getSize(){return result->getSize();}
    Automaton_t * getDFA(){return result;}



  };

}

#endif
