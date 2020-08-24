// MathStatisticMaker.hpp: this file is part of the REGAL project.
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
#ifndef MATHSTATISTICMAKER
#define MATHSTATISTICMAKER

#include "StatisticMaker.hpp"

namespace regal{

  class MathStatisticMaker{
  private:
    double counter; /*!< Used to count how much values has been added */
    double sum; /*!< Used to sum the added values */
    double sum_sum; /*!< Used to sum the square of added values */

  public:

    /**
       Adds a value to the statistics
       @param value is the value to add
    */
    void addValue(const double & value){
      counter++;
      sum+=value;
      sum_sum+=value*value;
    }

    /**
       Returns the mean of all the added values
       @Return the mean of all the added values
     */
    double getMean(){
      return sum/counter;
    }

    /**
       Returns the variance of all the added values
       @Return the variance of all the added values
     */
    double getVariance(){
      double mean=sum/counter;
      return sum_sum/counter-mean*mean;
    }

    /**
       Returns the standard deviation of all the added values
       @Return the standard deviation of all the added values
     */
    double getStandardDeviation(){
      return sqrt(getVariance());
    }

    /**
       Reset counters in order to compute new statistics.
    */
    void resetCounter(){
      counter=0.;
      sum=0.;
      sum_sum=0.;
    }

    /**
       Creates a MathStatisticMaker
       @param path is the path for the output file
       @param option is the option to open the file : w,w+,a,a+
    */
    MathStatisticMaker(){
      counter=0.;
      sum=0.;
      sum_sum=0.;
    }

    /**
       Destroys a MathStatisticMaker
    */
    ~MathStatisticMaker(){}

  };


}

#endif
