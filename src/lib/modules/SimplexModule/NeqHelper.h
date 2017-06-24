#include "../../Common.h"

namespace smtrat
{

        class NeqHelper
        {
			
			
			private:
				carl::FastMap<FormulaT, int> neqStatus;
				carl::FastMap<FormulaT,FormulaT> neqMap;
			
				int numberErrorFormulas = 0;
			
			public:
				
				void informNeq(FormulaT neq, FormulaT smaler, FormulaT larger){
					neqStatus[neq] = 0;
					neqMap[smaler] = neq;
					neqMap[larger] = neq;
				}
				
				bool addFormula(FormulaT formula){
					
					if(formula.constraint().relation() == carl::Relation::NEQ){
						
						std::cout << "ERROR HERE?";
						neqStatus[formula] = neqStatus[formula] + 1;
						
						std::cout << "Essssssssssssssssss";
						
						if(neqStatus[formula] == 1){numberErrorFormulas++;}
						
						return true;
						
					}else if (neqMap.count(formula)){
						FormulaT neqFormula = neqMap[formula];
						neqStatus[neqFormula] = neqStatus[neqFormula] - 1;
						
						if(neqStatus[neqFormula] == 0){numberErrorFormulas--;}
					}
					
					return false;
				}
				
				void removeForumula(FormulaT formula){
					
					if(formula.constraint().relation() == carl::Relation::NEQ){
						neqStatus[formula] = neqStatus[formula] - 1;
						
						if(neqStatus[formula] == 0){numberErrorFormulas--;}
					}else if (neqMap.count(formula)){
						FormulaT neqFormula = neqMap[formula];
						neqStatus[neqFormula] = neqStatus[neqFormula] + 1;
						
						if(neqStatus[neqFormula] == 1){numberErrorFormulas++;}
					}
				}
				
				bool containsProblemFormula(){
					return numberErrorFormulas!=0;
				}
		
		};
		
		
}