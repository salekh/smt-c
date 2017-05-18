#include "Tableau.h"

namespace smtrat
{
	TVariable::TVariable(){}
	
	//Constructor for slack variables
	TVariable::TVariable(int pId, bool pIsBasic){
		id = pId;
		isBasic = pIsBasic;
		
		upperBound = Bound(std::numeric_limits<double>::infinity(), true);
		lowerBound = Bound(-std::numeric_limits<double>::infinity(), true);
		
		isSlack = true;
	}
	
	//Constructor for existing variables
	TVariable::TVariable(carl::Variable pOriginal, int pId, bool pIsBasic){
		original = pOriginal;
		id = pId;
		isBasic = pIsBasic;
		
		upperBound = Bound(std::numeric_limits<double>::infinity(), true);
		lowerBound = Bound(-std::numeric_limits<double>::infinity(), true);
		
		isSlack=false;
	}
	
	
	void TVariable::changeUpperBound(Bound b){
		
	}
	
	void TVariable::changeLowerBound(Bound b){
		
	}
	
	void TVariable::backtrack(){
		
	}
	
	std::string TVariable::getName(){
		if(isSlack == false){
			return original.getName();
		}
		std::ostringstream oss;
		oss << "s" << id;
		return oss.str();
	}
}