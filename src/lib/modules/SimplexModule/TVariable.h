#include <stack>
#include "../../Common.h"
#include "Bound.h"
#include <limits>


namespace smtrat
{

        class TVariable{
			
			
			private:
				
				int id;
				
				carl::Variable original;
				
				double value = 0;
				
				//Is stored after succesfull check, to reset for backtrace
				double lastValue = 0;
				
				
				Bound upperBound;
				
				Bound lowerBound;
				
				std::stack<Bound> stackUpperBound;
			
				std::stack<Bound> stackLowerBound;
				
				bool isBasic;
				
				bool isSlack;
				
				//used in the method that finds the "problem set" of formulas
				//helps to create the sets N- and N+ as described in the paper
				int positionAsNonbasic;
				
			
	public:
			
				TVariable();
				
				TVariable(int pId, bool pIsBasic);
				
				TVariable(carl::Variable pOriginal, int pId, bool pIsBasic);
			
				void changeUpperBound(Bound b);
				
				void changeLowerBound(Bound b);
				
				//reset bounds, loads old value
				void backtrack();
				
				int getId() { return id; };
				
				double getValue() { return value; };
				
				Bound getUpperBound() { return upperBound; };
				Bound getLowerBound() { return lowerBound; };
				
				std::string getName();
		};
}