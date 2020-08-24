// Alphabet.hpp: this file is part of the REGAL project.
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
#ifndef ALPHABET
#define ALPHABET

#include "VerboseOption.hpp"
#include <list>
#include <map>
#include <iterator>
#include <algorithm>




namespace regal{

  template<typename Sigma>
  class Alphabet{
  private:
    std::list<Sigma> alphabet; /*!< Generic list of the alphabet */
    std::map<Sigma,int> numericalAlphabet; /*!< Map used to associated a object of the alphabet to an integer */
    int size; /*!< Size of the alphabet */

  public:

    /**
       Adds a letters in the Alphabet
       @param elt is the element to add.
    */
    void insert(const Sigma & elt){
      if(find(alphabet.begin(),alphabet.end(),elt)==alphabet.end()){
	alphabet.push_back(elt);
	numericalAlphabet[elt]=size;
	size++;
      }
    }

    /**
       Returns the current size of the alphabet
       @Return the current size of the alphabet
    */
    int getSize() const{return size;}

    /**
       Since every element is a template parameter, we use a map to associate
       the letters with an integer.
       @param val is a letter already in the alphabet
       @Result is the integer value associated to val
    */
    int getNumericalValue(const Sigma & val){
      return numericalAlphabet[val];
    }

    /**
       Returns the alphabet as a list of template parameters.
       @Return the alphabet as a list of template parameters.
    */
    std::list<Sigma> getList(){return alphabet;}

    /**
       Default constructor of the alphabet
    */
    Alphabet(){
      size=0;
      verbose("Creation of an Alphabet");
    }


    /**
       Build an alphabet with a list of letters.
       @param l is a tabular of template parameters, which is supposed to contain the alphabet
       @param s is the tabular's size.
    */
    Alphabet(Sigma* l,const int & s){
      size=0;
      for(int i=0;i<s;i++)
	insert(l[i]);
    }

    /**
       Destroy the alphabet
    */
    virtual ~Alphabet(){
      verbose("Destruction of an Alphabet");
    }

    friend std::ostream& operator<<(std::ostream& o,const Alphabet<char> & a);


  };


  /**
     Print an Alphabet
     @param o is the stream in which we add the DFA's description
     @param a is the Alphabet we want to print
     @Return the modified stream
  */
  std::ostream& operator<<(std::ostream& o,const Alphabet<char> & a){
    o<<std::endl<<"----------"<<std::endl;
    o<<"Alphabet"<<std::endl;
    o<<"Size = "<<a.size<<std::endl;
    std::list<char> listT=a.alphabet;
    for(std::list<char>::iterator l=listT.begin();l!=listT.end();l++)
      o<<*l<<" ";
    o<<std::endl<<"----------"<<std::endl;
    return o;
  }





}

#endif
