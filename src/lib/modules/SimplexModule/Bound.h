#include "../../Common.h"
#include "TRational.h"

namespace smtrat
{
	struct Bound
	{
		enum State { none, pos_infinity, neg_infinity };
		
		public:
			bool upperBound;
			TRational value;
			State state = none;
			
			Bound(){}
			
			Bound(TRational boundValue, bool isUpperBound){
				upperBound = isUpperBound;
				value = boundValue;
			}
			
	};
}
