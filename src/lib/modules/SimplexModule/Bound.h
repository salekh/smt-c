namespace smtrat
{
	struct Bound
	{
		public:
			bool upperBound;
			double value;
			
			Bound(){}
			
			Bound(double boundValue, bool isUpperBound){
				upperBound = isUpperBound;
				value = boundValue;
			}
	};
}