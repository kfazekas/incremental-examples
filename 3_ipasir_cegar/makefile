FLAGS := -Wall -Wextra -DNDEBUG -O3

STANDARD := -std=c++11

CADICAL_INC := ../cadical/src/
CADICAL_LIB_DIR := ../cadical/build/
CADICAL_LIB := -lcadical

all: hcp2cegar

hcp2cegar: main.o
	g++ $(FLAGS) main.o -L$(CADICAL_LIB_DIR) $(CADICAL_LIB) -o hcp2cegar

main.o : hcp_ipasir_cegar.cpp 
	g++ $(FLAGS) $(STANDARD) -I$(CADICAL_INC) -c $< -o $@
	
#.PHONY : clean
clean:
	rm -f *.a *.o *~ *.out  hcp2cegar
