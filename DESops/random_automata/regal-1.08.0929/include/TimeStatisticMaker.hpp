// TimeStatisticMaker.hpp: this file is part of the REGAL project.
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
#ifndef TIMESTATISTICMAKER
#define TIMESTATISTICMAKER

#include "StatisticMaker.hpp"
#include <sys/timeb.h>
#include <ctime>

namespace regal{

  class TimeStatisticMaker:public StatisticMaker{
  private:
    struct timeb before,after;
    double duration;
  public:

    /**
       Notes time before an action
    */
    void startingTime(){
      ftime(&before);
    }

    /**
       Notes time after an action
    */
    void endingTime(){
      ftime(&after);
      duration=(after.time-before.time)+(after.millitm-before.millitm)/1000.;
    }

    /**
       Returns the action's duration
       @Return the action's duration
    */
    double getDuration(){
      return duration;
    }

    /**
       Write duration in output
    */
    void addValue(){
      fprintf(output,"%f\n",duration);
    }

    /**
       Creates a TimeStatisticMaker
       @param path is the path of the output file
       @param option  is the option to open the file : w,w+,a,a+
    */
    TimeStatisticMaker(char * path,char * option):StatisticMaker::StatisticMaker(path,option){
    }

    /**
       Creates a TimeStatisticMaker
    */
    TimeStatisticMaker(){}

    /**
       Destroys a TimeStatisticMaker
    */
    ~TimeStatisticMaker(){}


  };


}

#endif
