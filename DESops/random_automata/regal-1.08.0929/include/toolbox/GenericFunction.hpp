// GenericFunction.hpp: this file is part of the REGAL project.
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
#ifndef GENERICFUNCTION
#define GENERICFUNCTION

#include<math.h>


template<typename T,typename U>
T Max(const T & a,const U & b){
  return ((a)<(b))?(b):(a);
}

template<typename T>
T Min(const T & a,const T & b){
  return ((a)>(b))?(b):(a);
}


template<typename T>
void swapT(T& arg1,T& arg2){
  T tmp;
  tmp=arg1;
  arg1=arg2;
  arg2=tmp;
}



template<typename T>
T getSmallerElement(T * & l,int & size){
  int i;
  T res=0;
  if(size>0)
    for(i=1,res=l[0];i<size;i++)res=Min(res,l[i]);
  return res;
}

#endif
