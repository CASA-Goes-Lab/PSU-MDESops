// StatisticMaker.hpp: this file is part of the REGAL project.
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
#ifndef STATISTICMAKER
#define STATISTICMAKER

namespace regal{

  struct InvalidStatsFileException : public std::exception {};


  class StatisticMaker{
  protected:
    FILE * output; // Output File for the statistics


  public:

    /**
       Creates a StathiticMaker
       @param path is the path of the output file
       @param option is the option to open the file: w,w+,a,a+
    */
    StatisticMaker(char * path,char * option){
      if((output=fopen(path,option))==NULL)
	throw new InvalidStatsFileException();
    }

    /**
       Creates a StatisticMaker, without an output file
    */
    StatisticMaker(){
      output=NULL;
    }

    /**
       Destroy a StathsticMaker
    */
    virtual ~StatisticMaker(){
      if(output!=NULL)
	fclose(output);
    }

  };

}


#endif
