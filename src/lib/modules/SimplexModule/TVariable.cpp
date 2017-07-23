#include "Tableau.h"

namespace smtrat
{
	TVariable::TVariable(){}
	
	//Constructor for slack variables
	TVariable::TVariable(FormulaT form, int pId, bool pIsBasic){
		id = pId;
		isBasic = pIsBasic;
		formula = form;
		
		upperBound = TRational(0,0,1);   
		lowerBound = TRational(0,0,-1);
		
		isSlack = true;
	}
	
	//Constructor for existing variables
	TVariable::TVariable(carl::Variable pOriginal, int pId, bool pIsBasic){
		original = pOriginal;
		id = pId;
		isBasic = pIsBasic;
		
		upperBound = TRational(0,0,1); 
		lowerBound = TRational(0,0,-1);
		
		isSlack=false;
	}
	
	void TVariable::saveValue(){ 
		lastValue = value;
	}
	
	//used for checkpointing
	void TVariable::loadValue(){ 
		value = lastValue; 
	}
	
	void TVariable::activateUpperBound(bool value){
		if(value){
			upperBound = *upperBoundFormula;
		}else{
			upperBound = TRational(0,0,1); 
		}
	};
	
	
	void TVariable::activateLowerBound(bool value){
		if(value){
			lowerBound = *lowerBoundFormula;
		}else{
			lowerBound = TRational(0,0,-1); 
		}
	};
	
	Rational TVariable::calculateDelta(TRational b){
		if(b.getInfPart() == 0 && ( value.getRationalPart() != b.getRationalPart() && value.getDeltaPart() != b.getDeltaPart())){
			Rational top = value.getRationalPart() - b.getRationalPart();
			Rational bottom = value.getDeltaPart() - b.getDeltaPart();
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