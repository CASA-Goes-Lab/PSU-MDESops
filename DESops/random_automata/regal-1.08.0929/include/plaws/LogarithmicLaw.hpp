// LogarithmicLaw.hpp: this file is part of the REGAL project.
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
#ifndef LOGARITHMICLAW
#define LOGARITHMICLAW


#include"DiscreteProbabilityLaw.hpp"

namespace regal{

  namespace plaws{

    class LogarithmicLaw: public DiscreteProbabilityLaw{

    private:

      virtual void updateProbability(const int & k){
	this->p=this->x*this->p*((k-1)/k);
      }

      virtual double initProbability(){
	return this->x/(log(1/(1-this->x)));
      }

      int initCounter(){return 1;}

    public:


      /**
	 Creates a generator of integer, according to the Logarithmic law
	 @param lambda
      */
      LogarithmicLaw(const double & lambda):DiscreteProbabilityLaw::DiscreteProbabilityLaw(lambda){
      }

      /**
	 Destroy a BoltzmannSampler
      */
      ~LogarithmicLaw(){
	verbose("Destruction of a Logarithmic Law");
      }
    };

  }

}

#endif
