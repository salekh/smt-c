#include "../../Common.h"
#include "TRational.h"

namespace smtrat
{
	struct Bound
	{
		
		public:
			bool upperBound;
			TRational value;
			
			Bound(){}
			
			Bound(TRational boundValue, bool isUpperBound){
				upperBound = isUpperBound;
				value = boundValue;
			}
			
	};
}
