// AbstractSuit.hpp: this file is part of the REGAL project.
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
#ifndef ABSTRACTSUIT
#define ABSTRACTSUIT

#include <iostream>
#include "VerboseOption.hpp"

namespace regal{

  class AbstractSuit{
  protected:
    int * tab; /*!< Numerical suit, allocated only once, size can't be changed */
    int size; /*!< Maximum size of the suit */
    int position; /*!< used for exhaustive suit generation */
  public:
    virtual int * first()=0;
    virtual int * next()=0;


    int getSize(){return size;}
    int * getSuit(){return tab;}

    /**
       Allocates the parameters
       @param s is the size of the partition
    */
    AbstractSuit(const int & s){
      size=s;
      position=0;
      tab=new int[s];
      verbose("Creation of an AbstractSuit");
    }

    /**
       Destroy an instance of a Suit
    */
    virtual ~AbstractSuit(){
      delete [] tab;
      verbose("Destruction of an AbstractSuit");
    }


    /**
       Print a partition as a list of integer
       Returns the modified steam.
    */
    friend std::ostream& operator<<(std::ostream& o,const AbstractSuit & a){
      int i;
      for(i=0;i<a.size;i++)o<<a.tab[i]<<" ";
      return o;
    }

  };

}

#endif
