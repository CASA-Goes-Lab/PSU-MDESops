// PlotStatisticMaker.hpp: this file is part of the REGAL project.
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
#ifndef PLOTSTATISTICMAKER
#define PLOTSTATISTICMAKER

#include  <stdio.h>

#include "StatisticMaker.hpp"

namespace regal{

  class PlotStatisticMaker:public StatisticMaker{
  public:

    /**
       Adds a list of values to the statistics
       @param values is the list to add
       @param size is the size of the list
    */
    void addValue(double * values, int size){
      int i;
      for(i=0;i<size;i++)
	fprintf(output,"%f ",values[i]);
      fprintf(output,"\n");
    }

    /**
       Adds 2 value in the statistics
       @param value1 is the first value to add
       @param value2 is the second value to add
    */
    void addValue(int value1, double value2){
      fprintf(output,"%d %f\n",value1,value2);
    }

    /**
       Creates a PlotStatisticMaker
       @param path is the path for the output file
       @param option is the option to open the file : w,w+,a,a+
    */
    PlotStatisticMaker(char * path,char * option):StatisticMaker::StatisticMaker(path,option){
    }

    /**
       Destroys a PlotStatisticMaker
    */
    ~PlotStatisticMaker(){}

  };

}


#endif
