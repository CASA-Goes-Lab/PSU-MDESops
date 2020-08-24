// NonZeroPoissonLaw.hpp: this file is part of the REGAL project.
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
#ifndef NONZEROPOISSONLAW
#define NONZEROPOISSONLAW

#include"DiscreteProbabilityLaw.hpp"

namespace regal{

  namespace plaws{

    class NonZeroPoissonLaw: public DiscreteProbabilityLaw{
    private:

      void updateProbability(const int & k){
	this->p=this->x*this->p/k;
      }

      double initProbability(){
	return this->x/(expl(this->x)-1);
      }

      int initCounter(){return 1;}


    public:

      /**
	 Creates a generator of integer, according to the Poisson law
	 @param lambda
      */
      NonZeroPoissonLaw(const double & lambda):DiscreteProbabilityLaw::DiscreteProbabilityLaw(lambda){
      }

      /**
	 Destroy a BoltzmannSampler
      */
      ~NonZeroPoissonLaw(){
	verbose("Destruction of a Poisson Law");
      }
    };

  }

}

#endif
