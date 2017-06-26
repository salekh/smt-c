#include "../../Common.h"

namespace smtrat
{

		/**
		 * @class NeqHelper
		 * @author osboxes.org
		 * @date 24/06/17
		 * @file NeqHelper.h
		 * @brief This class helps to decide whether checkCore needs to be aborted because of a neq formula
		 */
	class NeqHelper
	{
		
		
	private:
				//for each neq formula, the integer is <= 0 for ok, or 1 for error
		carl::FastMap<FormulaT, int> neqStatus;
		
				//maps the < and > to the neq formula
		carl::FastMap<FormulaT,FormulaT> neqMap;
		
				//number of formulas where neqStatus is 1
		int numberErrorFormulas = 0;
		
	public:
		
				//add the formulas to the maps
		void informNeq(FormulaT neq, FormulaT smaler, FormulaT larger){
			neqStatus[neq] = 0;
			neqMap[smaler] = neq;
			neqMap[larger] = neq;
		}
		
				//recalculates the neqStatus and the numberErrorFormulas value
				//returns true if it is a neq formula
		bool addFormula(FormulaT formula){
			
			if(formula.constraint().relation() == carl::Relation::NEQ){
				
				neqStatus[formula] = neqStatus[formula] + 1;
				
				if(neqStatus[formula] == 1){numberErrorFormulas++;}
				
				return true;
				
			}else if (neqMap.count(formula)){
				FormulaT neqFormula = neqMap[formula];
				neqStatus[neqFormula] = neqStatus[neqFormula] - 1;
				
				if(neqStatus[neqFormula] == 0){numberErrorFormulas--;}
			}
			
			return false;
		}
		
				//recalculates the neqStatus and the numberErrorFormulas value
				//returns true if it is a neq formula
		bool removeForumula(FormulaT formula){
			
			if(formula.constraint().relation() == carl::Relation::NEQ){
				neqStatus[formula] = neqStatus[formula] - 1;
				
				if(neqStatus[formula] == 0){numberErrorFormulas--;}
				return true;
			}else if (neqMap.count(formula)){
				FormulaT neqFormula = neqMap[formula];
				neqStatus[neqFormula] = neqStatus[neqFormula] + 1;
				
				if(neqStatus[neqFormula] == 1){numberErrorFormulas++;}
			}
			return false;
		}
		
				//Called in checkCore, returns true when need to abort
		bool containsProblemFormula(){
			return numberErrorFormulas!=0;
		}
		
	};
	
	
}