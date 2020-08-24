// BoltzmannSampler.cpp: this file is part of the REGAL project.
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
#include "BoltzmannSampler.hpp"

namespace regal{

  /**
     Compute DzetaK, a constant which is used to generate partitions.
     In the automaton case, K is the alphabet's size
     @param sum is the mean size of an object
     @param z is the value to compute with the W-Lambert function.
  */
  void BoltzmannSampler::computeDzetaK(long double sum,long double z){
    long double W0=0.,tmp;
    long double facti=1;
    long double precision=1/powl(10,15);
    int i;
    for(i=1;i;i++){
      facti*=i;
      tmp=pow(-i,i-1)*pow(z,i)/facti;
      W0+=tmp;
      //std::cout.precision(20);
      //std::cout<<tmp<<std::endl;
      if(tmp<precision&&tmp>-precision)
	break;
    }
    dzetaK=W0+sum;
    //printf("%d %.20Lf\n",i,dzetaK);
  }


  /**
     Creates a partition, guaranteeing an equiprobability among the results.
     @Return a partition
  */
  int * BoltzmannSampler::sample(){
    int counter=0,i;
    rejectCounter=0;
    //int max=autSize*alphaSize;
#ifdef __REJECTFLAG
    std::cout<<"Entree dans le sampler"<<std::endl;
#endif

    while(counter!=setSize){
      //for(i=0,counter=0;i<autSize;i++){
      for(i=0,counter=0;i<subsetNumber;i++){
	partition[i]=nzpl->randomValue();
	counter+=partition[i];
	if(counter>setSize)
	  break;
      }
      rejectCounter++;
    }



#ifdef __REJECTFLAG
    std::cout<<"Nombre de rejet : "<<rejectCounter<<std::endl;
#endif

    return partition;
  }

}
