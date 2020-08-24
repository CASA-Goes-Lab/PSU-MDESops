// GasteXConverter.hpp: this file is part of the REGAL project.
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
#ifndef GASTEXCONVERTER
#define GASTEXCONVERTER

#include <stdio.h>
#include <string.h>
#include "Converter.hpp"

namespace regal{

  class GasteXConverter: public Converter{
  private:

    /**
       Creates the header of a GasteX file
    */
    void beginGasteXDocument(){
      fprintf(output,"\\documentclass{article}\n");
      fprintf(output,"\\usepackage[usenames]{color}\n");
      fprintf(output,"\\usepackage{gastex}\n");
      fprintf(output,"\\begin{document}\n");
    }


    /**
       Close properly a auto-generated GasteX Document
    */
    void endGasteXDocument(){
      fprintf(output,"\n\\end{document}\n");
      fclose(output);
    }

  public:

    /**
       Print in output the GasteX line to draw a node
    */
    void draw_node(char * & name,int posx,int posy,bool initial,bool final){
      fprintf(output,"\\node");
      if(initial==true&&final==false)
	fprintf(output,"[Nmarks=i]");
      else if(initial==false&&final==true)
	fprintf(output,"[Nmarks=f,fangle=270]");
      if(initial==true&&final==true)
	fprintf(output,"[Nmarks=fi,fangle=270]");
      fprintf(output,"(%s)(%d,%d){%s}\n",name,posx,posy,name);
    }


    /**
       Print in output the GasteX line to draw a egde
       Make a loop if start and end are the same
    */
    void draw_edge(char * & start,char * & end,char * & word){
      if(strcmp(start,end)==0)
	fprintf(output,"\\drawloop[loopangle=90](%s){$%s$}\n",start,word);
      else
	fprintf(output,"\\drawedge[linecolor=Red](%s,%s){$%s$}\n",start,end,word);
    }


    /**
       Write in output the header to creates a GasteX automaton
       @param sizeX is the max width of the drawning
       @param sizeY is the max height of the drawning
    */
    void beginAutomaton(const int & sizeX,const int & sizeY){
      fprintf(output,"\n\n\\begin{center}\n");
      fprintf(output,"\\begin{picture}(%d,%d)(-20,-28)\n",sizeX,sizeY);
      fprintf(output,"\\gasset{Nw=5,Nh=5,Nmr=2.5,curvedepth=4}\n");
      fprintf(output,"\\thinlines\n");
      fprintf(output,"\\put(0,0){\n");
    }

    /**
       Write in output that the current automaton's description is finished
    */
    void endAutomaton(){
      fprintf(output,"}\n");
      fprintf(output,"\\end{picture}\n");
      fprintf(output,"\\end{center}\n\n\n");
      fprintf(output,"\\newpage\n\n\n");
    }

    GasteXConverter(const char *  path){
      if((output=fopen(path,"w"))==NULL)
	throw new InvalidFileException();
      beginGasteXDocument();
      verbose("Creation of a GasteXConverter");
    }

    ~GasteXConverter(){
      endGasteXDocument();
      verbose("Destruction of a GasteXConverter");
    }

  };

}

#endif
