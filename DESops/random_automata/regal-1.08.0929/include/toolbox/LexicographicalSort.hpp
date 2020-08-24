// LexicographicalSort.hpp: this file is part of the REGAL project.
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
#ifndef LEXICOGRAPHICAL_SORT_H
#define LEXICOGRAPHICAL_SORT_H




typedef struct doubleChainedList_t{
  int val;
  doubleChainedList_t * prev;
  doubleChainedList_t * next;
}doubleChainedList_t;

typedef struct List_t{
  int size;
  doubleChainedList_t * first;
  doubleChainedList_t * last;
};

doubleChainedList_t * createNode(int value){
  doubleChainedList_t * res=(doubleChainedList_t *)malloc(sizeof(doubleChainedList_t));
  res->val=value;
  res->prev=NULL;
  res->next=NULL;
  return res;
}

void destroyChainedList(doubleChainedList_t * dcl){
  if(dcl!=NULL){
    destroyChainedList(dcl->next);
    free(dcl);
  }
}

List_t * createList(){
  List_t * res=(List_t *)malloc(sizeof(List_t));
  res->first=NULL;
  res->last=NULL;
  res->size=0;
  return res;
}

void emptyList(List_t * l){
  if(l!=NULL){
    destroyChainedList(l->first);
    l->first=NULL;
    l->last=NULL;
    l->size=0;
  }
}

void destroyList(List_t * l){
  if(l!=NULL){
    destroyChainedList(l->first);
    free(l);
  }
}

void insertNodeLastList(List_t ** l,doubleChainedList_t * dcl){
  if((*l)->last==NULL){
    (*l)->first=dcl;
    (*l)->last=dcl;
  }
  else{
    (*l)->last->next=dcl;
    dcl->prev=(*l)->last;
    (*l)->last=dcl;
  }
  (*l)->size++;
}



doubleChainedList_t * extractFirstList(List_t ** l){
  doubleChainedList_t * res=(*l)->first;
  if(res!=NULL){
    (*l)->first=(*l)->first->next;
    if((*l)->first!=NULL)
      (*l)->first->prev=NULL;
    else
      (*l)->last=NULL;
    (*l)->size--;
    res->next=NULL;
    res->prev=NULL;
  }
  return res;
}

doubleChainedList_t * extractLastList(List_t ** l){
  doubleChainedList_t * res=(*l)->last;
  if(res!=NULL){
    if((*l)->last!=(*l)->first){
      (*l)->last=(*l)->last->prev;
      (*l)->last->next=NULL;
    }
    else{
      (*l)->first=NULL;
      (*l)->last=NULL;
    }
    (*l)->size--;
    res->next=NULL;
    res->prev=NULL;
  }
  return res;
}


void insertLastList(List_t ** l,int value){
  doubleChainedList_t * dcl=createNode(value);
  insertNodeLastList(l,dcl);
}


void concatList(List_t ** l1,List_t ** l2){
  if((*l1)->last!=NULL){
    if((*l2)->last!=NULL){
      (*l1)->last->next=(*l2)->first;
      (*l2)->first->prev=(*l1)->last;
      (*l1)->last=(*l2)->last;
    }
  }
  else{
    (*l1)->first=(*l2)->first;
    (*l1)->last=(*l2)->last;
    (*l1)->size=(*l2)->size;
  }
  (*l2)->first=NULL;
  (*l2)->last=NULL;
  (*l1)->size+=(*l2)->size;
  (*l2)->size=0;

}



#endif
