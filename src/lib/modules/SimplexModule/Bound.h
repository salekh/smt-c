#include "../../Common.h"

namespace smtrat
{
	struct Bound
	{
		enum State { none, infinity, minus_infinity };
		
		public:
			bool upperBound;
			Rational value;
			State state = none;
			
			Bound(){}
			
			Bound(Rational boundValue, bool isUpperBound){
				upperBound = isUpperBound;
				value = boundValue;
			}
			
	};
}