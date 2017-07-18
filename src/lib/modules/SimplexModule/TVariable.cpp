#include "Tableau.h"

namespace smtrat
{
	TVariable::TVariable(){}
	
	//Constructor for slack variables
	TVariable::TVariable(FormulaT form, int pId, bool pIsBasic){
		id = pId;
		isBasic = pIsBasic;
		formula = form;
		
		upperBound = TRational(0,1);   
		lowerBound = TRational(0,-1);
		
		isSlack = true;
	}
	
	//Constructor for existing variables
	TVariable::TVariable(carl::Variable pOriginal, int pId, bool pIsBasic){
		original = pOriginal;
		id = pId;
		isBasic = pIsBasic;
		
		upperBound = TRational(0,1); 
		lowerBound = TRational(0,-1);
		
		isSlack=false;
	}
	
	void TVariable::saveValue(){ 
		lastValue = value;
	}
	
	//used for checkpointing
	void TVariable::load(){ 
		value = lastValue; 
	}
	
	void TVariable::changeUpperBound(TRational b){
		upperBound = b;
	}
	
	void TVariable::changeLowerBound(TRational b){
		lowerBound = b;
	}
	
	Rational TVariable::calculateDelta(TRational b){
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