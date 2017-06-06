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
				
				
				//Stores the bound for the "s" variable of the formula (vector, because "=" needs uper and lower bound)
				carl::FastMap<FormulaT,std::vector<Bound>> formulaToBound;
				
				//Which formula is assigned to which matrix row
				carl::FastMap<FormulaT,int> formulaToRow;
				
				//The "s" variable created for the formula
				carl::FastMap<FormulaT,TVariable*> formToVar;
				
				//Mapper between Formula and Tableau Variables
				carl::FastMap<carl::Variable,TVariable*> varToTVar;
				
				
				bool assertUpper(TVariable* x, Bound c);
				
				bool assertLower(TVariable* x, Bound c);
				
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
					
					//Used by check, used for Backtracking described in the paper
					void createCheckpoint();
					
					void checkTest();
					
					
					//used as helper function for checkCore, finds smallest Variable that fullfills the function f.
					//isBasic: weather the function is called on all basic or all nonbasic variables.
					// function f takes a TVariable, a matrix value and returns a bool
					// returns a TVariable if found, otherwise a nullpointer
					TVariable* findSmallestVariable(std::function<bool(TVariable*,Rational)> func, int helper, bool isBasic);
					
					
					//Gets a map with the variables and keys to be inserted into the model
					carl::FastMap<carl::Variable,Rational> getModelValues() const;
					
					//Prints the tableau on the screen
					void print();
		};
}