
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

int main(int argc, char ** argv) {
    if(argc!=4){
        cout<<"Use: ./test [Size] [alph size] [num_auto]"<<endl;
        exit(0);
    }


    long num_vert = atol(argv[1]);
    long size_alphabet = atol(argv[2]);
    long num_automata = atol(argv[3]);

    Alphabet<long> alpha;

    DFAAutomaton<int, long> * a;

    RandomDFAGenerator<int, long, DFAAutomaton<int,long> > *  rg;

    for(long j=0; j < size_alphabet; j++){
        //  letters[j] = 'a' + j;
        alpha.insert(j);
    }

    rg = new RandomIncompleteICDFAGenerator<int,long,DFAAutomaton<int,long> >(num_vert,alpha);
    for(long counter=0; counter< num_automata; counter++){
        a=rg->random();

        cout << *a << endl;

    }
    delete rg;
    return 0;
}
