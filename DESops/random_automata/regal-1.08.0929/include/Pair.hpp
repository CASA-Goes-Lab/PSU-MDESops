// Pair.hpp: this file is part of the REGAL project.
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
#ifndef PAIR_HPP
#define PAIR_HPP

namespace regal{

  template<typename elt1,typename elt2>
  class Pair{
  public:
    elt1 first;
    elt2 second;

    friend bool operator==(Pair<elt1,elt2> p1,Pair<elt1,elt2> p2){
      if(p1.first==p2.first&&p1.second==p2.second)
	return true;
      return false;
    }

    friend bool operator<(Pair<elt1,elt2> p1,Pair<elt1,elt2> p2){
      if(p1.first<p2.first||(p1.first==p2.first&&p1.second<p2.second))
	return true;
      return false;
    }

    Pair(const elt1 & f=0){
      first=f;
      second=f;
    }

    Pair(const elt1 & f,const elt2 & s){
      first=f;
      second=s;
    }

    Pair(const Pair<elt1,elt2> & p){
      first=p.first;
      second=p.second;
    }

    ~Pair(){};

  };

   /**
     Print a pair of integers
     @param o is the stream in which we add the DFA's description
     @param a is the pair we want to print
     @Return the modified stream
  */
  ostream& operator<<(ostream& o,const Pair<int,int> & a){
    o<<"("<<a.first<<", "<<a.second<<")";
    return o;
  }



}

#endif
