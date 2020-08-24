// MooreAlgorithm.hpp: this file is part of the REGAL project.
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
#ifndef MOOREALGORITHM
#define MOOREALGORITHM

#include "MinimizingAlgorithm.hpp"
#include "Alphabet.hpp"
#include "toolbox/GenericFunction.hpp"
#include "toolbox/LexicographicalSort.hpp"


namespace regal{

  template<typename StateLabel_t,typename Sigma,class Automaton_t=AbstractAutomaton<StateLabel_t,Sigma> >
  class MooreAlgorithm: public MinimizingAlgorithm<StateLabel_t,Sigma,Automaton_t>{
  private:
    int *partitionTmp;
    int ** partitionWord;
    int complexity; /*!< Used to measure Moore's complexity */
    int * tmpClassNum[2]; /*!< Used to measure how fast the classes are divided */
    bool tmpClassNumFlag;
    int aSize; /*!< Size of the alphabet */
    List_t ** lexicographical;
    List_t * lexicographicalRes;
    List_t * lexicographicalTMP;


    /**
      Used to free the dynamic allocations when the automaton's size has changed
      or when the class is destroyed
     */
    void freeMemory(){
      int i;
      if(this->partitionRes!=NULL)delete [] this->partitionRes;
      if(partitionTmp!=NULL)delete [] partitionTmp;
      if(partitionWord!=NULL){
	for(i=0;i<this->size;i++){
	  delete [] partitionWord[i];
	  destroyList(lexicographical[i]);
	}
	destroyList(lexicographical[i]);
	free(lexicographical);
	destroyList(lexicographicalRes);
	destroyList(lexicographicalTMP);
	delete [] partitionWord;
      }
    }

    /**
      Used to allocate memory space when the class is created or when the automaton's size has changed
    */
    void initPartition(const int & s,const int & as){
      int i;
      if(s!=this->size){
	freeMemory();
	this->size=s;
	aSize=as;
	this->partitionRes=new int[this->size];
	this->partitionTmp=new int[this->size];
	this->partitionWord=new int*[this->size];
	this->lexicographical=(List_t **)malloc(sizeof(List_t *)*(s+1));
	for(i=0;i<this->size;i++){
	  this->partitionWord[i]=new int[as];
	  this->lexicographical[i]=createList();
	}
	this->lexicographical[i]=createList();
	this->lexicographicalTMP=createList();
	this->lexicographicalRes=createList();
      }
    }

    /**
      Sort the states according to the arrival classes of the transition labeled by the
      prof^th letters of the alphabet or according to their classes
      Needs to be executed k+1 times to obtain a sorted list of states
      @param prof is the index of the letter labeling the transition used to sort the states
    */
    void lexicographicalSort(int prof){
      doubleChainedList_t * tmp;
      while(lexicographicalRes->first!=NULL){
	tmp=extractFirstList(&lexicographicalRes);
	if(prof==0)
	  insertNodeLastList(&(lexicographical[this->partitionRes[tmp->val]]),tmp);
	else{
	  if(this->partitionWord[tmp->val][prof-1]!=-1)
	    insertNodeLastList(&(lexicographical[this->partitionWord[tmp->val][prof-1]]),tmp);
	  else
	    insertNodeLastList(&(lexicographical[this->maxClass]),tmp);
	}
      }
      for(int i=0;i<=this->maxClass;i++)
	concatList(&lexicographicalRes,&lexicographical[i]);
    }

    /*
      Launch the function lexicographicalSort k+1 times
      then compares the states in the list two by two.
      If their parameters are still the same, they are still in the same classes.
      Otherwise a new class is created.
    */
    void sortClasses(){
      doubleChainedList_t * tmp,*tmp2;
      if(tmpClassNumFlag==true)
	memset(tmpClassNum[1],0,this->size*sizeof(int));
      for(int i=aSize;i>=0;i--)
	lexicographicalSort(i);
      this->maxClass=1;

      for(tmp=lexicographicalRes->first,tmp2=NULL;tmp!=NULL;tmp2=tmp,tmp=tmp->next){
	if(tmp2!=NULL&&!sameClass(aSize,tmp->val,tmp2->val))
	  this->maxClass++;
	partitionTmp[tmp->val]=this->maxClass-1;
	if(tmpClassNumFlag==true)
	  tmpClassNum[1][this->maxClass]++;
      }
    }

    bool mooreFirstCutting(Automaton_t * a){
      int i;
      bool res=true;
      for(i=0;i<this->size;i++){
	if(a->isFinal(a->getRealValue(i))){
	  this->partitionRes[i]=0;
	  insertLastList(&lexicographicalRes,i);
	}
	else{
	  this->partitionRes[i]=1;
	  insertLastList(&lexicographicalTMP,i);
	}
      }
      if(lexicographicalRes->size==0||lexicographicalTMP->size==0){
	res=false;
	this->maxClass=1;
      }
      else{
	concatList(&lexicographicalRes,&lexicographicalTMP);
	this->maxClass=2;
      }
      return res;
    }

    bool sameClass(const int & alphabetSize,const int & state1,const int & state2){
      int i;
      if(this->partitionRes[state1]!=this->partitionRes[state2])return false;
      for(i=0;i<alphabetSize;i++)
	if(this->partitionWord[state1][i]!=this->partitionWord[state2][i])
	  return false;
      return true;
    }

    bool isPartitionMinimal(){
      int i;
      for(i=0;i<this->size;i++)
	if(this->partitionRes[i]!=this->partitionTmp[i])
	  return false;
      return true;
    }

  public:

    /**
       Minimize an automaton with Moore algorithm and returns a partition of the states.
       @param a is the automaton to minimize
       @param Mit allows to stop the algorithm at a given iteration
       @Return partition of the states, in which i is a states of a and p[i]
       is a state of Moore(a)
    */
    int * minimizeToPartition(Automaton_t * a,const int & Mit=-1){
      int i;
      Alphabet<Sigma> al=a->getAlphabet();
      std::list<Sigma> listT=al.getList();
      complexity=0;
      initPartition(a->getSize(),al.getSize());
      complexity++;
      if(!mooreFirstCutting(a)){
	emptyList(lexicographicalRes);
	return this->partitionRes;
      }
      /*std::cout<<"-----------------------------------"<<std::endl;
      for(i=0;i<this->size;i++)
      std::cout<<this->partitionRes[i]<<" ";
      std::cout<<std::endl;
      */
      //swapT(this->partitionRes,this->partitionTmp);
      while(1){
	complexity++;
	for(i=0;i<this->size;i++){
	  for(std::list<char>::iterator l=listT.begin();l!=listT.end();l++)
	    if(a->getArrivalState((StateLabel_t)i,*l)!=a->undefinedTransition())
	      partitionWord[i][al.getNumericalValue(*l)]=this->partitionRes[a->getArrivalState((StateLabel_t)i,*l)];
	    else
	      partitionWord[i][al.getNumericalValue(*l)]=-1;
	}
	sortClasses();
	if(tmpClassNumFlag==true)
	  tmpClassNum[0][complexity-1]=this->maxClass;

	swapT(this->partitionRes,partitionTmp);
	/*for(i=0;i<this->size;i++)
	  std::cout<<this->partitionRes[i]<<" ";
	std::cout<<std::endl;
	*/
	if(this->maxClass==a->getSize()||isPartitionMinimal()||((complexity-1)==Mit)){
	  emptyList(lexicographicalRes);
	  return this->partitionRes;
	}
      }

    }

    /**
       Minimize an automaton with Moore algorithm and returns the class number at each iteration.
       @param a is the automaton to minimize
       @Return a tabular containing the class number at each iteration (first value is the size of the tabular)
       and the number of states in each classes.
    */
    int ** minimizeSteps(Automaton_t * a,const int & precision=-1){
      if(tmpClassNum[0]!=NULL){
	delete [] tmpClassNum[0];
	delete [] tmpClassNum[1];
      }
      tmpClassNum[0]=new int[a->getSize()];
      tmpClassNum[1]=new int[a->getSize()];
      tmpClassNumFlag=true;
      minimizeToPartition(a,precision);
      tmpClassNumFlag=false;
      tmpClassNum[0][0]=complexity;
      tmpClassNum[1][0]=this->maxClass;
      return tmpClassNum;
    }


    /**
       Minimize an automaton with Moore algorithm and only returns the size of the result.
       @param a is the automaton to minimize
       @Return the size of the result.
    */
    int minimizeSize(Automaton_t * a){
      minimizeToPartition(a);
      return this->maxClass;
    }

    /**
       Returns the complexity of the minimization on a
       @param a is the automaton to minimize
       @Return the complexity of the minimization
    */
    int minimizeComplexity(Automaton_t * a){
      minimizeToPartition(a);
      return complexity;
    }
    unsigned int * minimizeMultipleComplexity(Automaton_t * a){
      return NULL;
    }


    /**
       Minimize an automaton with Moore algorithm
       @param a is the automaton to minimize
       @Return the minimized automaton
    */
    Automaton_t * minimize(Automaton_t * a){
      int i,j;
      Alphabet<Sigma> al=a->getAlphabet();
      std::list<Sigma> listT=al.getList();
      minimizeToPartition(a);

      /*for(i=0;i<a->getSize();i++)
	std::cout<<this->partitionRes[i]<<" ";
      std::cout<<std::endl;
      */
      int * viewed=new int[a->getSize()];
      int count;
      for(i=0;i<a->getSize();i++)
	viewed[i]=-1;
      for(i=0,count=0;i<a->getSize();i++)
	if(viewed[this->partitionRes[i]]==-1)viewed[this->partitionRes[i]]=count++;
      //reorderPartition(a->getSize());

      Automaton_t * res=new Automaton_t(this->maxClass,al);
      //Transform the partition into an Automaton

      for(i=0;i<this->maxClass;i++)
	res->addState();
      for(i=0,j=0;i<this->size;i++){
	j=viewed[this->partitionRes[i]];
	if(a->isInitial(i))
	  res->setStateAsInitial(j,true);
	if(a->isFinal(i))
	  res->setStateAsFinal(j,true);
	for(std::list<char>::iterator l=listT.begin();l!=listT.end();l++)
	  res->addTransition(viewed[this->partitionRes[i]],viewed[this->partitionRes[a->getArrivalState((StateLabel_t)i,*l)]],*l);


      }
      return res;
    }




    /**
       Create a instance of MooreAlgorithm, an optimized class for minimizing automaton
     */
    MooreAlgorithm(){
      this->size=0;
      this->partitionRes=NULL;
      partitionTmp=NULL;
      partitionWord=NULL;
      tmpClassNum[0]=NULL;
      tmpClassNum[0]=NULL;
      tmpClassNumFlag=false;
    }

    /**
       Destroy a MooreAlgorithm instance
     */
    ~MooreAlgorithm(){
      freeMemory();
      if(tmpClassNum[0]!=NULL){delete [] tmpClassNum[0];delete [] tmpClassNum[1];}
    }


  };

}



#endif
