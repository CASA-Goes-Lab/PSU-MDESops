// MyMooreAlgorithm.hpp: this file is part of the REGAL project.
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
#ifndef MYMOOREALGORITHM
#define MYMOOREALGORITHM

#include "MinimizingAlgorithm.hpp"
#include "Alphabet.hpp"
#include "toolbox/GenericFunction.hpp"
#include "toolbox/LexicographicalSort.hpp"


namespace regal{

  template<typename StateLabel_t,typename Sigma,class Automaton_t=AbstractAutomaton<StateLabel_t,Sigma> >
  class MyMooreAlgorithm: public MinimizingAlgorithm<StateLabel_t,Sigma,Automaton_t>{
  private:
    int *partitionTmp;
    int ** partitionWord;
    int complexity; /*!< Used to measure Moore's complexity */
    int aSize; /*!< Size of the alphabet */
    List_t ** lexicographical;
    List_t * lexicographicalRes;
    List_t * lexicographicalTMP;
    List_t * lexicographicalUndividable;

    void freeMemory(){
      if(this->partitionRes!=NULL)delete [] this->partitionRes;
      if(partitionTmp!=NULL)delete [] partitionTmp;
      if(partitionWord!=NULL){
	for(int i=0;i<this->size;i++){
	  delete [] partitionWord[i];
	  destroyList(lexicographical[i]);
	}
	free(lexicographical);
	destroyList(lexicographicalRes);
	destroyList(lexicographicalTMP);
	destroyList(lexicographicalUndividable);
	delete [] partitionWord;
      }
    }

    void initPartition(const int & s,const int & as){
      if(s!=this->size){
	freeMemory();
	this->size=s;
	aSize=as;
	this->partitionRes=new int[this->size];
	partitionTmp=new int[this->size];
	partitionWord=new int*[this->size];
	lexicographical=(List_t **)malloc(sizeof(List_t *)*s);
	for(int i=0;i<this->size;i++){
	  partitionWord[i]=new int[as];
	  lexicographical[i]=createList();
	}
	lexicographicalTMP=createList();
	lexicographicalRes=createList();
	lexicographicalUndividable=createList();
      }
    }

    void lexicographicalSort(const int & prof){
      doubleChainedList_t * tmp;
      while(lexicographicalRes->first!=NULL){
	tmp=extractFirstList(&lexicographicalRes);
	if(prof==0)
	  insertNodeLastList(&lexicographical[this->partitionRes[tmp->val]],tmp);
	else
	  insertNodeLastList(&lexicographical[this->partitionWord[tmp->val][prof-1]],tmp);
      }
      for(int i=0;i<this->maxClass;i++)
	concatList(&lexicographicalRes,&lexicographical[i]);
    }

    void sortClasses(){
      doubleChainedList_t * tmp,*tmp2;
      for(int i=aSize;i>=0;i--)
	lexicographicalSort(i);
      this->maxClass=0;

      for(tmp=lexicographicalUndividable->first;tmp!=NULL;tmp=tmp->next)
	partitionTmp[tmp->val]=this->maxClass++;

      tmp2=extractFirstList(&lexicographicalRes);

      partitionTmp[tmp2->val]=this->maxClass++;
      insertNodeLastList(&lexicographicalUndividable,tmp2);

      while(lexicographicalRes->first!=NULL){
	tmp=extractFirstList(&lexicographicalRes);
	if(!sameClass(aSize,tmp->val,tmp2->val)){
	  partitionTmp[tmp->val]=this->maxClass++;
	  insertNodeLastList(&lexicographicalUndividable,tmp);
	}
	else{
	  partitionTmp[tmp->val]=partitionTmp[tmp2->val];
	  if(lexicographicalUndividable->last!=NULL&&lexicographicalUndividable->last->val==tmp2->val)
	    insertNodeLastList(&lexicographicalTMP,extractLastList(&lexicographicalUndividable));
	  insertNodeLastList(&lexicographicalTMP,tmp);
	}
	tmp2=tmp;
      }

      concatList(&lexicographicalRes,&lexicographicalTMP);

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
      if(lexicographicalRes->size==0||lexicographicalTMP->size==0)
	res=false;
      else if(lexicographicalRes->size==1){
	concatList(&lexicographicalUndividable,&lexicographicalRes);
	concatList(&lexicographicalRes,&lexicographicalTMP);
      }
      else if(lexicographicalTMP->size==1)
	concatList(&lexicographicalUndividable,&lexicographicalTMP);
      else
	concatList(&lexicographicalRes,&lexicographicalTMP);
      this->maxClass=2;

      return res;
    }

    bool sameClass(const int & alphabetSize,const int & state1,const int & state2){
      int i;
      if(this->partitionRes[state1]!=this->partitionRes[state2])return false;
      for(i=0;i<alphabetSize;i++)
	if(partitionWord[state1][i]!=partitionWord[state2][i])
	  return false;
      return true;
    }

    bool isPartitionMinimal(){
      int i;
      for(i=0;i<this->size;i++)
	if(this->partitionRes[i]!=partitionTmp[i])
	  return false;
      return true;
    }

  public:

    /**
       Minimize an automaton with MyMoore algorithm and returns a partition of the states.
       @param a is the automaton to minimize
       @Return partition of the states, in which i is a states of a and p[i]
       is a state of MyMoore(a)
    */
    int * minimizeToPartition(Automaton_t * a,const int & it=-1){
      doubleChainedList_t * tmp;
      Alphabet<Sigma> al=a->getAlphabet();
      std::list<Sigma> listT=al.getList();
      initPartition(a->getSize(),al.getSize());
      complexity++;
      if(!mooreFirstCutting(a)){
	emptyList(lexicographicalRes);
	emptyList(lexicographicalTMP);
	return this->partitionRes;
      }
      while(1){
	complexity++;
	for(tmp=lexicographicalRes->first;tmp!=NULL;tmp=tmp->next){
	  for(std::list<char>::iterator l=listT.begin();l!=listT.end();l++)
	    partitionWord[tmp->val][al.getNumericalValue(*l)]=
	      this->partitionRes[a->getArrivalState((StateLabel_t)tmp->val,*l)];
	}

	sortClasses();
	swapT(this->partitionRes,partitionTmp);
	if(lexicographicalRes->size==0||isPartitionMinimal()){
	  emptyList(lexicographicalRes);
	  emptyList(lexicographicalUndividable);
	  return this->partitionRes;
	}

      }

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
      complexity=0;
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
       Create a instance of MyMooreAlgorithm, an optimized class for minimizing automaton
     */
    MyMooreAlgorithm(){
      this->size=0;
      this->partitionRes=NULL;
      partitionTmp=NULL;
      partitionWord=NULL;
    }

    /**
       Destroy a MyMooreAlgorithm instance
     */
    ~MyMooreAlgorithm(){
      freeMemory();
    }


  };

}



#endif
