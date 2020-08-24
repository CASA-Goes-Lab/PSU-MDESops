// Converter.hpp: this file is part of the REGAL project.
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
#ifndef CONVERTER
#define CONVERTER

#include <iostream>
#include "VerboseOption.hpp"

namespace regal{

  struct InvalidFileException : public std::exception {};

  class Converter{
  protected:
    FILE * output; /*!< Possible output for the converter */

  public:

    /**
       Convert a representation of a node into another one
       @param name is the name of the node
       @param posx is the horizontal position of the node
       @param posy is the vertical position of the node
       @param initial indicates if the states is initial
       @param final indicates if the states is final
    */
    virtual void draw_node(char * & name,int posx,int posy,bool initial,bool final)=0;

    /**
       Convert a representation of an edge/transition into another one
       @param start indicates the name of the starting node
       @param end indicates the name of the ending node
       @param word is the word associated to the edge/transition
    */
    virtual void draw_edge(char * & start,char * & end,char * & word)=0;

    /**
       Write a new declaration of an automaton
       @param sizeX is the width of the graphical output
       @param sizeY is the heigth of the graphical output
    */
    virtual void beginAutomaton(const int & sizeX,const int & sizeY)=0;

    /**
       Indicates the end of the automaton's declaration in the output
    */
    virtual void endAutomaton()=0;

    /**
       Creates a Converter, which translate an automaton into its graphical version,
       such as DoT or GasteX.
    */
    Converter(){}

    /**
     Destroy a Converter
   */
    virtual ~Converter(){}

  };

}

#endif
