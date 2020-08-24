// DotConverter.hpp: this file is part of the REGAL project.
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
#ifndef DOTCONVERTER
#define DOTCONVERTER

#include <stdio.h>
#include <string.h>
#include "Converter.hpp"

namespace regal{

  class DotConverter:public Converter{
  private:
    char * name;
  public:

    /**
       Print in output the Dot line to draw a node
    */
    void draw_node(char * & name,int posx,int posy,bool initial,bool final){
      if(final)
	fprintf(output,"\"%s\" [shape = doublecircle];\n",name);
      if(initial)
	fprintf(output,"\"%s\" [style=filled,color=lightgrey];\n",name);
    }


    /**
       Print in output the Dot line to draw an egde
       Make a loop if start and end are the same
    */
    void draw_edge(char * & start,char * & end,char * & word){
      fprintf(output,"%s -> %s [ label = \"%s\" ]\n",start,end,word);;
    }


    /**
       Write in output the header to creates a GasteX automaton
       @param sizeX is the max width of the drawning
       @param sizeY is the max height of the drawning
    */
    void beginAutomaton(const int & sizeX,const int & sizeY){
      fprintf(output,"digraph automaton{\n");
      fprintf(output,"graph [label = \"%s\",]\n",name);
    }

    /**
       Write in output that the current automaton's description is finished
    */
    void endAutomaton(){
      fprintf(output,"}\n\n");
    }

    /**
       Creates a DotConverter
       @param path is the path of the output file
    */
    DotConverter(const char *  path){
      if((output=fopen(path,"w"))==NULL)
	throw new InvalidFileException();
      name=(char *)malloc(sizeof(char)*(strlen(path)+1));
      sprintf(name,"%s",path);
      verbose("Creation of a DotConverter");
    }

    /**
       Destroy a DotConverter
    */
    ~DotConverter(){
      fclose(output);
      free(name);
      verbose("Destruction of a DotConverter");
    }

  };

}

#endif
