#include <Eigen/Dense>
#include <list>
#include "../../Common.h"
#include "TVariable.h"

namespace smtrat
{

        class Tableau
        {
			
			
			private:
			
				Eigen::MatrixXd matrix;
				
				//which rows were actiavted by adding/removing formulas
				std::vector<bool> rowActive;
				
				//Position vector of the nonbasic variables
				std::vector<TVariable> row;
				
				
				//Position vector of the basic variables
				std::vector<TVariable> column;
				
				
				//Stores the bound for the "s" variable of the formula
				carl::FastMap<FormulaT,Bound> formulaToBound;
				
				//Which formula is assigned to which matrix row
				carl::FastMap<FormulaT,int> formulaToRow;
				
				//The "s" variable created for the formula
				carl::FastMap<FormulaT,TVariable> formToVar;
				
				//Mapper between Formula and Tableau Variables
				carl::FastMap<carl::Variable,TVariable> varToTVar;
				
				
				
				
			public:
					
					Tableau(const std::list<FormulaT*>& formulas);
					
					//methods as described in the paper
					void pivotAndUpdate(TVariable v1, TVariable v2, double);
					
					void update(TVariable v, Bound b);
					
					
					//used by insertCore
					void activateRow(FormulaT formula);
					
					//used by removeCore
					void deactivateRow(FormulaT formula);
					
					
					//used as helper for checkCore
					TVariable findSmallestVariable(bool isBasic);
					
					
					//Helper function to convert
					TVariable convertVar(carl::Variable var);
		};
}