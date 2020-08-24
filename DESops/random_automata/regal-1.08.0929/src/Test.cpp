#include <iostream>
#include <vector>
#include <string>
#include <list>
#include <map>
#include <iterator>


#include "../include/ExhaustiveDFAGenerator.hpp"
#include "../include/RandomCompleteICDFAGenerator.hpp"
#include "../include/RandomIncompleteICDFAGenerator.hpp"
#include "../include/DFAAutomaton.hpp"
#include "../include/GasteXConverter.hpp"
#include "../include/DotConverter.hpp"
#include "../include/Alphabet.hpp"
#include "../include/PlotStatisticMaker.hpp"
#include "../include/TimeStatisticMaker.hpp"
#include "../include/MathStatisticMaker.hpp"

#include "../include/MooreAlgorithm.hpp"

using namespace regal;
using namespace std;

#define AUTOMATON_NUMBER_FOR_TEST 10.00


int main(int argc, char ** argv){
  if(argc!=3){
    cout<<"Use: ./test [Size] [alph size]"<<endl;
    exit(0);
  }
  int counter=0,j;
  long size=atol(argv[1]);
  char letters[26];
  Alphabet<char> alpha;
  DFAAutomaton<int,char> * a;
  RandomDFAGenerator<int,char,DFAAutomaton<int,char> > *  rg;
  cout<<"Generating "<<AUTOMATON_NUMBER_FOR_TEST<<" automata of size "<<size<<endl;

  for(j=0;j< atol(argv[2]); j++){
    letters[j]='a'+j;
    alpha.insert(letters[j]);
  }

  rg=new RandomCompleteICDFAGenerator<int,char,DFAAutomaton<int,char> >(size,alpha);
  for(counter=0;counter<AUTOMATON_NUMBER_FOR_TEST;counter++){
    a=rg->random();
    cout<<*a<<endl;
  }
  delete rg;

  rg=new RandomIncompleteICDFAGenerator<int,char,DFAAutomaton<int,char> >(size,alpha);
  for(counter=0;counter<AUTOMATON_NUMBER_FOR_TEST;counter++){
    a=rg->random();
    cout<<*a<<endl;
  }
  delete rg;





  cout<<"Number of automata "<<counter<<endl;
  return 0;
}
