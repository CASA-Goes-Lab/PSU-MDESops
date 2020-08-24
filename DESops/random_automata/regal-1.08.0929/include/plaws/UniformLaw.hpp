// UniformLaw.hpp: this file is part of the REGAL project.
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
#ifndef UNIFORMLAW
#define UNIFORMLAW


#include"DiscreteProbabilityLaw.hpp"

namespace regal{

  namespace plaws{

    class UniformLaw: public DiscreteProbabilityLaw{

    private:

      virtual void updateProbability(const int & k){
      }

      virtual double initProbability(){
	return this->x;
      }

    public:


      /**
	 Creates a generator of integer, according to the Uniform law
	 @param lambda
      */
      UniformLaw(const double & lambda):DiscreteProbabilityLaw::DiscreteProbabilityLaw(lambda){
      }

      /**
	 Destroy a BoltzmannSampler
      */
      ~UniformLaw(){
	verbose("Destruction of a Uniform Law");
      }
    };

  }

}

#endif
