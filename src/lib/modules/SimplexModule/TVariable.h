#include <stack>
#include "../../Common.h"

namespace smtrat
{

        class TVariable{
			
			
	private:
				
				int id;
				
				Variable original;
				
				value double;
				
				//Is stored after succesfull check, to reset for backtrace
				lastValue double;
				
				
				Bound upperBound;
				
				Bound lowerBound;
				
				std::stack<Bound> stackUpperBound;
			
				std::stack<Bound> stackLowerBound;
				
				bool isBasic;
				
				//used in the method that finds the "problem set" of formulas
				//helps to create the sets N- and N+ as described in the paper
				int positionAsNonbasic;
				
			
			public:
			
				void changeUpperBound(Bound b);
				
				void changeLowerBound(Bound b);
				
				//reset bounds, loads old value
				void backtrack();
		}
}