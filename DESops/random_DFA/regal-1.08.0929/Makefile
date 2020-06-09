SHELL=/bin/sh
.SUFFIXES:
.SUFFIXES: .cpp .o
CC= g++

exec_prefix=/usr/local
regaldir=$(exec_prefix)/regal
libdir=$(regaldir)/lib
includedir=$(regaldir)/include
bindir=bin

regaldir-user=regal
libdir-user=$(regaldir-user)/lib
includedir-user=$(regaldir-user)/include

CPPFLAGS= -g -Wall --ansi --pedantic -O3

LIB_OUTPUT=$(libdir)/libregal.a
LIB_OUTPUT_USER=$(libdir-user)/libregal.a


LIB_FILE_O=BoltzmannSampler.o CatalanSuit.o CompletionSuit.o
LIB_FILE_BIN=$(bindir)/BoltzmannSampler.o $(bindir)/CatalanSuit.o $(bindir)/CompletionSuit.o

all:install



test:Test.o
	$(CC) $(CPPFLAGS) -o test src/Test.o -L$(libdir-user) -lregal

desops:desops.o
	$(CC) $(CPPFLAGS) -o random_DFA src/desops.o -L$(libdir-user) -lregal


clean:
	rm -rf *.o

mrproper: clean
	rm -f lib/libregal.a

dist:


doc:
	echo "Go to  http://igm.univ-mlv.fr/~jdavid01/REGAL/"

create-dir:
	mkdir $(regaldir)
	mkdir $(libdir)
	mkdir $(includedir)

create-dir-user:
	mkdir $(regaldir-user)
	mkdir $(libdir-user)
	mkdir $(includedir-user)



install:create-dir $(LIB_FILE_O)
	ar r $(LIB_OUTPUT) $(LIB_FILE_BIN)
	cp include/*.hpp $(includedir)/.

install-user:create-dir-user $(LIB_FILE_O)
	ar r $(LIB_OUTPUT_USER) $(LIB_FILE_BIN)
	cp include/*.hpp $(includedir-user)/.


uninstall:
	rm -f $(LIB_FILE_BIN)
	rm -rf $(regaldir)

uninstall-user:
	rm -f $(LIB_FILE_BIN)
	rm -rf $(regaldir-user)



desops.o:
	$(CC) $(CPPFLAGS) -c src/desops.cpp -o src/desops.o

Test.o:
	$(CC) $(CPPFLAGS) -c src/Test.cpp -o src/Test.o
BoltzmannSampler.o:
	$(CC) $(CPPFLAGS) -c -fpic include/BoltzmannSampler.cpp -o bin/BoltzmannSampler.o
CatalanSuit.o:
	$(CC) $(CPPFLAGS) -c -fpic include/CatalanSuit.cpp -o bin/CatalanSuit.o
CompletionSuit.o:
	$(CC) $(CPPFLAGS) -c -fpic include/CompletionSuit.cpp -o bin/CompletionSuit.o




#export LD_LIBRARY_PATH=/home/mif001/jdavid01/regal-1.0.0/lib/
