#include "Tableau.h"

namespace smtrat
{
	TVariable::TVariable(){}
	
	TVariable::TVariable(int pId, bool pIsBasic){
		id = pId;
		isBasic = pIsBasic;
		
		upperBound = Bound(std::numeric_limits<double>::infinity(), true);
		lowerBound = Bound(-std::numeric_limits<double>::infinity(), true);
	}
				
	TVariable::TVariable(carl::Variable pOriginal, int pId, bool pIsBasic){
		original = pOriginal;
		id = pId;
		isBasic = pIsBasic;
		
		upperBound = Bound(std::numeric_limits<double>::infinity(), true);
		lowerBound = Bound(-std::numeric_limits<double>::infinity(), true);
		
	}
	
	
	void TVariable::changeUpperBound(Bound b){
		
	}
	
	void TVariable::changeLowerBound(Bound b){
		
	}
	
	void TVariable::backtrack(){
		
	}
}