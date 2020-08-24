// BoltzmannSampler.hpp: this file is part of the REGAL project.
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
#ifndef BOLTZMANNSAMPLER
#define BOLTZMANNSAMPLER

#include <cmath>
#include<ctime>
#include<cstdlib>
#include "VerboseOption.hpp"
#include "plaws/NonZeroPoissonLaw.hpp"


#include <iostream>


namespace regal{

  using namespace plaws;

  class BoltzmannSampler{
  private:
    DiscreteProbabilityLaw * nzpl;
    long double dzetaK;
    double p;
    int * partition; /*!< value returned by the function "sample". Allocated only once */
    int setSize; /*!< Number of state in the automaton */
    int subsetNumber; /*!< Size of the alphabet */
    long double meanSize; /*!< Mean size of a subset */
    int rejectCounter;


    void computeDzetaK(long double sum,long double z);


  public:
    int getRejectCounter(){return rejectCounter;}
    int * sample();

    /**
       Creates a Boltzmann Sampler
       @param size is the set we wants to generate
       @param subset is the number of subset in the partition
    */
    BoltzmannSampler(const int & size=2,const int & subset=2){
      time_t t;
      partition=new int[subset];
      setSize=size;
      subsetNumber=subset;
      meanSize=size/(long double)subsetNumber;
      computeDzetaK(meanSize,-meanSize*expl(-(long double)meanSize));
      nzpl=new NonZeroPoissonLaw(dzetaK);
      srand(time(&t));
      verbose("Creation of a Boltzmann Sampler");
    }

    /**
       Destroy a BoltzmannSampler
    */
    ~BoltzmannSampler(){
      delete [] partition;
      delete nzpl;
      verbose("Destruction of a Boltzmann Sampler");
    }
  };

}

#endif
