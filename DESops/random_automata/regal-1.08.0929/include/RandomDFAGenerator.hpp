// RandomDFAGenerator.hpp: this file is part of the REGAL project.
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
#ifndef RANDOMDFAGENERATOR
#define RANDOMDFAGENERATOR

#include "AbstractRandomGenerator.hpp"
#include "AbstractDFAGenerator.hpp"
#include "BoltzmannSampler.hpp"
#include "toolbox/GenericFunction.hpp"
#include "VerboseOption.hpp"
#include "MyMooreAlgorithm.hpp"
#include "StronglyConnected.hpp"
#include "CoAccessible.hpp"
#include "Local.hpp"



namespace regal{

  template<typename StateLabel_t,typename Sigma, class Automaton_t=AbstractAutomaton<StateLabel_t,Sigma> >
  class RandomDFAGenerator :
    public AbstractRandomGenerator<Automaton_t>, AbstractDFAGenerator<StateLabel_t,Sigma,Automaton_t>{
  private:
    BoltzmannSampler * bs; /*!< Gives a partition that will be converted into an automaton */
    int *partBoltzmann; /*!< Partition given by bs */
    int * partMin; /*!<Used to sort the subset during the generation */
    int * partFinalMemory; /*!< Buffer used to sotck the values of partFinal, allocated only once */
    //int * catS; /*!< CatalanSuit - Word of Dyck : used to create a trie */
    //int * comS; /*!< CompletionSuit : used to complete the trie into a DFA */
    int * permutation; /*!< used to allocate the memory used by random permutations only once */
    int rejectCounters[2];
    double probability;
    int setSize; /*!< Size of the partition we need to generate to create an automaton */
    int subsetNumber; /*!< Number of subsets we need in the set partition to create an automaton */
    int incomplete; /*!< Heuristic to transform a complete ICDFA generator into a non-complete one */

    /**
       Sort sub-sets of a partition according to their smallest element.
    */
    void sortPartition(){
      int i,j;
      for(i=0;i<subsetNumber;i++)partMin[i]=-1;

      for(i=0,j=0;i<setSize;i++){
	if(partMin[partFinalMemory[i]]==-1)partMin[partFinalMemory[i]]=j++;
	partFinalMemory[i]=partMin[partFinalMemory[i]];
      }

    }



    /**
       Prints a partition, which is a 2-dimensional tabular
    */
    void printPartition(){
      int i;
      //std::cout<<"Taille ensemble "<<setSize<<std::endl;
      //std::cout<<"Taille des sous ensembles "<<std::endl;
      /*for(i=0;i<subsetNumber;i++)
	std::cout<<partBoltzmann[i]<<" ";
      std::cout<<std::endl;
      */
      //std::cout<<"Partition"<<std::endl;
      for(i=0;i<setSize;i++)
	std::cout<<partFinalMemory[i]<<" ";
      std::cout<<std::endl;
    }

    /**
       Generate a random permutation
       Note: this function is using permutation to stock the permutation
       and save time with memory allocations.
       @Return the generated permutation
     */
    int * randomPermutation(){
      int i,pos;
      int * l=permutation;
      for(i=0;i<setSize;i++){
	pos=rand()%(i+1);
	if(pos!=i)
	  l[i]=l[pos];
	l[pos]=i+1;
      }
      return l;
    }

    /**
       Part of the Bassino-Nicaud algorithm:
       Generate a random set partition, using a Bolztmann Sampler.
       Note: the 2-dimentionnal buffer partFinalMemory is
       a 1 dimentionnal buffer to reduce memory allocations.
    */
    void randomPartition(){
      int i,j,counter,pos;
      int * l=randomPermutation();

      partBoltzmann=bs->sample();

      for(pos=0,i=0,counter=0;counter<setSize;i++){
	for(j=0;j<partBoltzmann[i];j++,pos++){
	  partFinalMemory[l[pos]-1]=i;
	}
	counter+=partBoltzmann[i];
      }
      sortPartition();
      //Adds the last transition without boltzmann to ensure equiprobability that has been
      //proved for automatonSize*alphabetSize+1

      //if(incomplete)partFinalMemory[setSize]=rand()%subsetNumber;
    }


    /**
       Part of the Bassino-Nicaud algorithm: translate a partition
       into 2 Suits : catS which is a word of Dyck and comS
       which complete catS in the automaton's contruction.
    */
    /*void partitionToSuits(){
      int i,max=-10,pos=0;
      for(i=0;i<setSize;i++){
	if(partFinalMemory[i]>max)max=partFinalMemory[i];
	else{
	  comS[pos]=partFinalMemory[i]+1;
	  catS[pos]=max+1;
	  pos++;
	}
      }

      }*/

    /**
       Randomdly assign the final states on the generated automaton
    */
    void randomFinalization(){
      int i;
      StateLabel_t state;
      for(i=0;i<this->result->getSize();i++){
	state=this->result->getRealValue(i);

	if(((rand()%RAND_MAX)/(double)RAND_MAX)<probability)
	  this->result->setStateAsFinal(state,true);
	else
	  this->result->setStateAsFinal(state,false);
      }
    }


    /**
       Randomdly design a state to be the only final state
    */
    void onlyOneFinalState(){
      int i;
      StateLabel_t state;
      for(i=0;i<this->result->getSize();i++){
	state=this->result->getRealValue(i);
	this->result->setStateAsFinal(state,false);
      }
      this->result->setStateAsFinal(this->result->getRealValue(rand()%this->result->getSize()),true);
    }


    /**
       Generate randomly a DFA, without finalizing it.
    */
    void randomUnfinalizedDFA(){
      rejectCounters[1]=0;
      do{
	randomPartition();
	//partitionToSuits();
	rejectCounters[1]++;
	//printPartition();
      }
      //while(!this->isACatalanSuit(catS,incomplete));
      while(!this->isAValidSetPartition(partFinalMemory,incomplete));
#ifdef __REJECTFLAG
      std::cout<<"Nombre de rejet : "<<rejectCounters[1]<<std::endl;
#endif

      this->setToDFA(partFinalMemory,incomplete);
      //this->suitToDFA(catS,comS,incomplete);
      //std::cout<<*this->result<<std::endl;
    }


    bool isMinimal(Automaton_t * a){
      int i,max=0,size=a->getSize();
      bool zero=false;
      MyMooreAlgorithm<int,char,Automaton_t > ma;
      int * partition=ma.minimizeToPartition(a);
      for(i=0;i<size;i++){
	if(partition[i]>max)
	  max=partition[i];
	zero=(partition[i]==0)?true:false;
      }
      if(max==(size-1)&&zero)
	return true;
      return false;
    }


  public:

    /**
       Returns a randomly generated automaton
       @Return a randomly generated automaton
    */
    Automaton_t * random(){
      randomUnfinalizedDFA();
      randomFinalization();
      return this->result;
    }

    /**
       Returns a randomly generated minimal automaton
       @Return a randomly generated minimal automaton
    */
    Automaton_t * randomMinimal(){
      do{
	random();
      }while(!isMinimal(this->result));
      return this->result;
    }

    /**
       Returns a randomly generated strongly connected automaton
       @Return a randomly generated strongly connected automaton
    */
    Automaton_t * randomStronglyConnected(){
      do{
	random();
      }while(!StronglyConnectedTester<StateLabel_t,Sigma,Automaton_t>::testConnectability(this->result));
      return this->result;
    }

    /**
       Returns a randomly generated local automaton
       @Return a randomly generated local automaton
    */
    Automaton_t * randomLocal(){
      do{
	randomStronglyConnected();
      }while(!LocalTester<StateLabel_t,Sigma,Automaton_t>::locality(this->result));
      return this->result;
    }



    /**
       Returns a randomly generated strongly connected automaton
       @Return a randomly generated strongly connected automaton
    */
    Automaton_t * randomCoAccessible(){
      do{
	random();
      }while(!CoAccessibleTester<StateLabel_t,Sigma,Automaton_t>::testCoAccessibility(this->result));
      return this->result;
    }

    /**
       Returns a randomly generated automaton with only one final state
       @Return a randomly generated automaton with only one final state
    */
    Automaton_t * randomOneFinalState(){
      randomUnfinalizedDFA();
      onlyOneFinalState();
      return this->result;
    }

    /**
       Returns the number of reject used to generate the previous Automaton
       @Return the number of Bolztmann rejects and Dyck rejects.
     */
    int * getRejectCounters(){
      rejectCounters[0]=bs->getRejectCounter();
      return rejectCounters;
    }

    /**
       Create a random DFA Generator
       @param autSize is the number of states in the generated automatons
       @param alphaSize is the size of the alphabet in the generated automatons
       @param prob is the probability for a state to be final
    */
    RandomDFAGenerator(const int & autSize,const Alphabet<Sigma> & alpha,const double & prob=0.5,const bool & c=false):
      AbstractDFAGenerator<StateLabel_t,Sigma,Automaton_t>::AbstractDFAGenerator(autSize,alpha){
      incomplete=(c)?1:0;
      setSize=autSize*alpha.getSize()+1;
      subsetNumber=autSize+incomplete;
      bs=new BoltzmannSampler(setSize,subsetNumber);
      //catS=new int[autSize*(alpha.getSize()-1)+1];
      //comS=new int[autSize*(alpha.getSize()-1)+1];
      permutation=new int[setSize];
      partMin=new int[subsetNumber];
      partFinalMemory=new int[setSize];
      probability=prob;
      verbose("Creation of the RandomDFAGenerator");
    }


    /**
       Destroy the RandomDFAGenerator
    */
    ~RandomDFAGenerator(){
      delete bs;
      //delete [] catS;
      //delete [] comS;
      delete [] permutation;
      delete [] partFinalMemory;
      delete [] partMin;
      verbose("Destruction of the RandomDFAGenerator");

    }

  };

}

#endif
