// HistogramMaker.hpp: this file is part of the REGAL project.
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
#ifndef HISTOGRAMMAKER
#define HISTOGRAMMAKER

#include "StatisticMaker.hpp"

namespace regal{


  class HistogramMaker:public StatisticMaker{
  protected:
    int * tab;
    int max;

  public:

    /**
       Creates a HistogramMaker
       @param path is the path of the output file
       @param option is the option to open the file: w,w+,a,a+
       @param maxValue is the maximum value in the histogram
    */
    HistogramMaker(char * path,char * option,const int & maxValue):StatisticMaker::StatisticMaker(path,option){
      tab=NULL;
      max=0;
      resetHistogram(maxValue);
    }

    /**
       Reset the current histogram
       @param maxValue is the maximum value in the histogram
    */
    void resetHistogram(const int & maxValue){
      if(max==maxValue)
	memset(tab,0,max*sizeof(int));
      else{
	if(max!=0)
	  delete [] tab;
	tab=new int[maxValue];
	memset(tab,0,sizeof(int)*maxValue);
	max=maxValue;
      }
    }

    /**
       Increment the value pointed by ind
       @param ind indicates where is the value to increment in the histogram
     */
    void addValue(const int & ind){
      if(ind<max&&ind>=0)
	tab[ind]++;
    }

    /**
       Write the histogram in the output
     */
    void writeHistogram(){
      for(int i=0;i<max;i++)
	fprintf(this->output,"%d %d\n",i,tab[i]);
    }

    /**
       Returns the current histogram
       @Return the current histogram
     */
    int * getHistogram(){
      return tab;
    }

    /**
       Destroy a StathsticMaker
    */
    virtual ~HistogramMaker(){
      if(max!=0)
	delete [] tab;
    }

  };

}


#endif
