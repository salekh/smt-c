#include <list>
#include <algorithm>
#include <functional>
#include "../../Common.h"
#include <Eigen/Dense>
#include "TVariable.h"

namespace smtrat
{

        class Tableau
        {
			
			
		private:
			
				// (Basic aka rows, NonBasic aka columns)
				Eigen::Matrix<Rational, Eigen::Dynamic, Eigen::Dynamic> matrix;
				
				//which rows were actiavted by adding/removing formulas
				std::vector<bool> rowActive;
				
				//Position vector of the nonbasic variables
				std::vector<TVariable*> rowVars;
				
				
				//Position vector of the basic variables
				std::vector<TVariable*> columnVars;
				
				
				//Stores the bound for the "s" variable of the formula
				carl::FastMap<FormulaT,Bound> formulaToBound;
				
				//Which formula is assigned to which matrix row
				carl::FastMap<FormulaT,int> formulaToRow;
				
				//The "s" variable created for the formula
				carl::FastMap<FormulaT,TVariable*> formToVar;
				
				//Mapper between Formula and Tableau Variables
				carl::FastMap<carl::Variable,TVariable*> varToTVar;
				
				
				
				
				public:
					
					Tableau();
					
					Tableau(std::list<FormulaT> formulas);
					
					//methods as described in the paper
					void pivotAndUpdate(TVariable* v1, TVariable* v2, Rational r);
					
					void pivot(int rowPos, int columnPos);
					
					void update(TVariable* v, Bound b);
					
					
					//used by insertCore
					bool activateRow(FormulaT formula);
					
					//used by removeCore
					void deactivateRow(FormulaT formula);
					
					
					//used as helper for checkCore, find smallest Variable that fullfills the function f.
					// function f takes a TVariable and returns a bool
					TVariable* findSmallestVariable(std::function<bool(TVariable*,Rational)> func, int helper, bool isBasic);
					
					
					//Helper function to convert
					TVariable convertVar(carl::Variable var);
					
					//Prints the tableau on the screen
					void print();
		};
}