#include "../../Common.h"

namespace smtrat
{
	struct Bound
	{
		public:
			bool upperBound;
			Rational value;
			
			Bound(){}
			
			Bound(Rational boundValue, bool isUpperBound){
				upperBound = isUpperBound;
				value = boundValue;
			}
	};
}