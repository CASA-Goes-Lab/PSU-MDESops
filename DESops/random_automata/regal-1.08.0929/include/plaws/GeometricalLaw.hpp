// GeometricalLaw.hpp: this file is part of the REGAL project.
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
#ifndef GEOMETRICALLAW
#define GEOMETRICALLAW


#include"DiscreteProbabilityLaw.hpp"

namespace regal{

  namespace plaws{

    class GeometricalLaw: public DiscreteProbabilityLaw{

    private:

      virtual void updateProbability(const int & k){
	this->p=this->x*this->p;
      }

      virtual double initProbability(){
	return 1-this->x;
      }

    public:


      /**
	 Creates a generator of integer, according to the Geometrical law
	 @param lambda
      */
      GeometricalLaw(const double & lambda):DiscreteProbabilityLaw::DiscreteProbabilityLaw(lambda){
      }

      /**
	 Destroy a BoltzmannSampler
      */
      ~GeometricalLaw(){
	verbose("Destruction of a Geometrical Law");
      }
    };

  }

}

#endif
