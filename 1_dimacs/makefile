FLAGS := -Wall -Wextra -DNDEBUG -O3

STANDARD := -std=c++11

all: hcp2dimacs

hcp2dimacs: main.o
	g++ $(FLAGS) main.o -o hcp2dimacs

main.o : hcp_dimacs_generator.cpp 
	g++ $(FLAGS) $(STANDARD) -c $< -o $@
	

#.PHONY : clean
clean:
	rm -f *.a *.o *~ *.out  hcp2dimacs
