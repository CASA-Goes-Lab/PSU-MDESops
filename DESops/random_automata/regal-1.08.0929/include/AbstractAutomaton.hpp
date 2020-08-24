// AbstractAutomaton.hpp: this file is part of the REGAL project.
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
#ifndef ABSTRACTAUTOMATON
#define ABSTRACTAUTOMATON


#include "GasteXConverter.hpp"
#include "DotConverter.hpp"
#include "Converter.hpp"
#include "VerboseOption.hpp"
#include "Alphabet.hpp"

#include<map>

namespace regal{

  struct InvalidStateException : public std::exception {};

  template<typename StateLabel_t,typename Sigma>
  class AbstractAutomaton{
  private:
    std::map<int,StateLabel_t> intTostateMap; /*!< Used to make sure every state is associated to an integer */
    std::map<StateLabel_t,int> stateTointMap; /*!< Used to get the numerical value associated to a state */

    /**
       Adds a State in the Automaton
       @Return the created state
    */
    virtual StateLabel_t createState(const StateLabel_t & value)=0;

  protected:
    Alphabet<Sigma> alphabet;
    int stateNumber; /*!< actual number of states in the automaton */


    /*
      Reduces by one the number of states in the automaton,
      which is the same than deleting the last state.
     */
    void undefineLastState(){
      stateNumber--;
    }


  public:
    /**
       Creates an Abstract Automaton
    */
    AbstractAutomaton(const Alphabet<Sigma> & a):alphabet(a){
      stateNumber=0;
      verbose("Creation of an Automaton");
    }

    /**
       Destroy the current Abstract Automaton
    */
    virtual ~AbstractAutomaton(){
      verbose("Destruction of an Automaton");
    }

    virtual Alphabet<Sigma> getAlphabet()const{return alphabet;}

    virtual StateLabel_t undefinedTransition()const =0;

    virtual int getSize()=0;

    virtual int getAlphabetSize(){return alphabet.getSize();}

    /**
       Returns an integer value associated with the template parameter
       @s is the template parameter
       @Return an integer value associated with the template parameter
    */
    int getIntegerValue(const StateLabel_t & s){
      if(stateTointMap.find(s)==stateTointMap.end())
	return -1;
      return stateTointMap[s];
    }

    /**
       Returns an template parameter associated with the integer value
       @s is the integer value
       @Return an template parameter associated with the integer value
    */
    StateLabel_t getRealValue(const int & ind){
      if(ind<0)
	return undefinedTransition();
      return intTostateMap[ind];
    }

    /**
       Adds a State in the Automaton and associate it to a numerical value
       @Return the created state
    */
    virtual StateLabel_t addState(const StateLabel_t & value=0){
      intTostateMap[stateNumber]=createState(value);
      stateTointMap[getRealValue(stateNumber-1)]=stateNumber-1;
      return getRealValue(stateNumber-1);
    }



    /**
       Adds a Transition in the Automaton

       @param start is the label of the state where the new transition starts
       @param end is the label of the state where the new transition ends
       @param value is the value of the transition
    */
    virtual void addTransition(const StateLabel_t & start,const StateLabel_t & end,const Sigma & value)=0;

    /**
       Tells if a state is final

       @param sl is the label of the state
       @Return True if the state is final, False otherwise
    */
    virtual bool isFinal(const StateLabel_t & sl)=0;

    /**
       Tells if a state is initial

       @param sl is the label of the state
       @Return True if the state is initial, False otherwise
    */
    virtual bool isInitial(const StateLabel_t & sl)=0;

    /**
       Set a state as final
       @param sl is the label of the state
       @param value: if true, s1 is final.
    */
    virtual void setStateAsFinal(const StateLabel_t & sl,const bool & value)=0;
    /**
       Set a state as initial
       @param sl is the label of the state
       @param value, if true, s1 is initial.
    */
    virtual void setStateAsInitial(const StateLabel_t & sl,const bool & value)=0;
  };

}

#endif
