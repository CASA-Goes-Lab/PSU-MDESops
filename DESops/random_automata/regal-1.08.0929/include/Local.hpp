// Local.hpp: this file is part of the REGAL project.
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
#ifndef LOCAL_HPP
#define LOCAL_HPP

#include<iostream>
#include<list>
#include<deque>
#include "DFAAutomaton.hpp"
#include "ReverseDFAAlgorithm.hpp"
#include "Pair.hpp"


namespace regal{

  template<typename StateLabel_t,typename Sigma,class Automaton_t=AbstractAutomaton<StateLabel_t,Sigma> >
  class LocalTester{
  private:

    static int sum(const int & n){
      int res=0;
      for(int i=1;i<=n;i++){
	res+=i;
      }
      return res;
    }

    static bool testCycleRec(DFAAutomaton<Pair<StateLabel_t,StateLabel_t> ,Sigma> *a,Pair<int,int> p, int * tab){
      std::list<Sigma> listT=a->getAlphabet().getList();
      int tmpState;
      Pair<int,int> tmpPair;
      for(typename std::list<Sigma>::reverse_iterator l=listT.rbegin();l!=listT.rend();l++){
	tmpPair=a->getArrivalState(p,*l);
	tmpState=a->getIntegerValue(tmpPair);
	if(tab[tmpState]==1)
	  return false;
	else if(!tab[tmpState]){
	  tab[tmpState]=1;
	  if(!testCycleRec(a,tmpPair,tab))
	     return false;
	  tab[tmpState]=2;
	}
      }
      return true;
    }

    /*
      Test if there is a cycle in the not-diagonal subset of P(A),
      meaning the states (p,q) such as p!=q.
      If there is no cycle, the automaton A is local.
      @param a the automaton P(A)
      @return true there is no cycle, false therefore
    */
    static bool testCyclesInPairAutomaton(DFAAutomaton<Pair<StateLabel_t,StateLabel_t> ,Sigma> *a){
      Pair<int,int> p;
      int i,size=a->getSize();
      int * tab=new int[size];
      for(i=0;i<size;i++){
	if(!tab[i]){
	  p=a->getRealValue(i);
	  tab[i]=1;
	  if(!testCycleRec(a,p,tab)){
	    delete [] tab;
	    return false;
	  }
	  tab[i]=2;
	}
      }
      delete [] tab;
      return true;
    }


    /* Build the automaton P(A) with the following rules:
       ((p,q),a,(r,s)) is a transition in P(A) if and only if
       (p,a,r) and (q,a,s) are transitions in A.
       The state (p,q) is equal to (q,p) -> we'll sort the values
       in the lexicographic order.
       @param a is the automaton to transform
       @Return P(A).
    */
    static DFAAutomaton<Pair<StateLabel_t,StateLabel_t> ,Sigma> * makePairAutomaton(Automaton_t * a){
      int size=a->getSize();
      int sumA=sum(size);
      std::list<Sigma> listT=a->getAlphabet().getList();
      Pair<StateLabel_t,StateLabel_t> p,p2;
      DFAAutomaton<Pair<StateLabel_t,StateLabel_t> ,Sigma> * pa=
	new DFAAutomaton<Pair<StateLabel_t,StateLabel_t> ,Sigma>(sumA,a->getAlphabet());
      for(p.first=0;p.first<size;p.first++)
 	for(p.second=p.first;p.second<size;p.second++)
 	  pa->addState(p);

      for(p.first=0;p.first<size;p.first++)
 	for(p.second=p.first;p.second<size;p.second++){
	  for(typename std::list<Sigma>::reverse_iterator l=listT.rbegin();l!=listT.rend();l++){
	    p2.first=a->getArrivalState(p.first,*l);
	    p2.second=a->getArrivalState(p.second,*l);
	    pa->addTransition(p,p2,*l);
	  }
	}
      return pa;
    }


  public:

    /*
      Returns true if a is local, false otherwise.
      @param a is the automaton which we want to test
      @Return true if a is local, false otherwise.
    */
    static bool testLocality(Automaton_t * a){
      DFAAutomaton<Pair<StateLabel_t,StateLabel_t> ,Sigma> * pairA=makePairAutomaton(a);
      bool res=testCyclesInPairAutomaton(pairA);
      delete pairA;
      return res;
    }

  };

}

#endif
