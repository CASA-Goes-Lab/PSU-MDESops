// BernouilliLaw.hpp: this file is part of the REGAL project.
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
#ifndef BERNOUILLILAW
#define BERNOUILLILAW


#include"DiscreteProbabilityLaw.hpp"

namespace regal{

  namespace plaws{

    class BernouilliLaw: public DiscreteProbabilityLaw{

    private:
      int * probabilityTab;

      virtual void updateProbability(const int & k){
	this->p=probabilityTab[k];
      }

      virtual double initProbability(){
	return probability[0];;
      }

    public:


      /**
	 Creates a generator of integer, according to the Bernouilli law
	 @param tab contains the probability for each value to be picked
      */
      BernouilliLaw(const int * tab):DiscreteProbabilityLaw::DiscreteProbabilityLaw(0.){
	probabilityTab=tab;
      }

      /**
	 Destroy a BoltzmannSampler
      */
      ~BernouilliLaw(){
	verbose("Destruction of a Bernouilli Law");
      }
    };

  }

}

#endif
