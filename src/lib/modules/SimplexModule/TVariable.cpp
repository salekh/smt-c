#include "Tableau.h"

namespace smtrat
{
	TVariable::TVariable(){}
	
	//Constructor for slack variables
	TVariable::TVariable(FormulaT form, int pId, bool pIsBasic){
		id = pId;
		isBasic = pIsBasic;
		formula = form;
		
		upperBound = Bound(TRational(10000000), true);   //TODO real Infinity
		lowerBound = Bound(TRational(-10000000), false);
		
		isSlack = true;
	}
	
	//Constructor for existing variables
	TVariable::TVariable(carl::Variable pOriginal, int pId, bool pIsBasic){
		original = pOriginal;
		id = pId;
		isBasic = pIsBasic;
		
		upperBound = Bound(TRational(10000000), true);   //TODO real Infinity
		lowerBound = Bound(TRational(-10000000), false);
		
		isSlack=false;
	}
	
	void TVariable::saveValue(){ 
		lastValue = value;
	}
	
	void TVariable::saveBounds(){ 
		stackUpperBound.push(upperBound);
		stackLowerBound.push(lowerBound);
	}
		
	void TVariable::load(){ 
		value = lastValue; 
		
		if(stackUpperBound.empty() || stackLowerBound.empty() ){
			SMTRAT_LOG_ERROR("smtrat.my","TVariable, cant pop empty stack!");
		}
			
		upperBound = stackUpperBound.top();
		stackUpperBound.pop();
		
		lowerBound = stackLowerBound.top();
		stackLowerBound.pop();
					
	}
	
	void TVariable::changeUpperBound(Bound b){
		upperBound = b;
	}
	
	void TVariable::changeLowerBound(Bound b){
		lowerBound = b;
	}
	
	Rational TVariable::calculateDelta(Bound b){
		if(value.getRationalPart() != b.value.getRationalPart() && value.getDeltaPart() != b.value.getDeltaPart()){
			Rational top = value.getRationalPart() - b.value.getRationalPart();
			Rational bottom = value.getDeltaPart() - b.value.getDeltaPart();
			return abs(top)/abs(bottom);
		}
		return 1;
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