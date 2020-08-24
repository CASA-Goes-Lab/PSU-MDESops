// DiscreteProbabilityLaw.hpp: this file is part of the REGAL project.
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
#ifndef DISCRETEPROBABILITYLAW
#define DISCRETEPROBABILITYLAW


#include <math.h>
#include<time.h>
#include<stdlib.h>
#include "../VerboseOption.hpp"

#include <iostream>

namespace regal{

  namespace plaws{

    class DiscreteProbabilityLaw{
    protected:
      double x,p;

      /**
	 Determines the probability for the next integer to be generated
	 @Return the probability for the next integer to be generated
      */
      virtual void updateProbability(const int & k)=0;

      /**
	 Determines the probability for the minimum integer to be generated
	 @Return the probability for the minimum integer to be generated
      */
      virtual double initProbability()=0;

      /**
	 Determines the minimum integer that can be returned
	 @Return the minimum integer that can be returned
      */
      virtual int initCounter(){return 0;}

    public:


      /**
	 Returns a random generated value, according to a given probability law
	 @Return a random generated value
      */
      int randomValue(){
	int k=initCounter();
	p=initProbability();
	double dice=(rand())/(double)RAND_MAX;
	while(dice>=p){
	  dice-=p;
	  k++;
	  updateProbability(k);
	}
	return k;
      }



      /**
	 Creates a Discrete Probability Law
	 @param x depends on the probability law
      */
      DiscreteProbabilityLaw(const double & param){
	x=param;
	time_t t;
	srand(time(&t));
      }

      /**
	 Destroy a Discrete Probability Law
      */
      virtual ~DiscreteProbabilityLaw(){
	verbose("Destruction of a Discrete Probability Law");
      }
    };

  }

}

#endif
