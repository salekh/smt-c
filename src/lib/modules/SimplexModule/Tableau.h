/**
 * @file Tableau.h
 * @author Sanchit Alekh <sanchit.alekh@rwth-aachen.de>
 * @author Karsten Jungnitsch <karsten.jungnitsch@rwth-aachen.de>
 * @author Alexander Reeh <alexander.reeh@rwth-aachen.de>
 *
 */

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
		
				//which rows were actiavted by adding/removing formulas, only for printing matrix
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
		
		
		
	private:
				//Helper function that checks whether the tableau matrix is correct when using the values of the variables
		void checkTest();
		
			//Methods as described in the paper
		bool assertUpper(TVariable* x, TRational c);
		
		bool assertLower(TVariable* x, TRational c);
		
	public:
		
		Tableau();
		
		Tableau(std::list<FormulaT> formulas);
		
					//methods as described in the paper
		void pivotAndUpdate(TVariable* v1, TVariable* v2, TRational r);
		
		void pivot(int rowPos, int columnPos);
		
		void update(TVariable* v, TRational b);
		
					//used by insertCore
		bool activateRow(FormulaT formula);
		
					//used by removeCore
		void deactivateRow(FormulaT formula);
		
					//Called everytime after succesfull checkCore happend to store values for Backtracking as described in the paper
		void createCheckpointValue();
		
					//Created everytime befor assertUpper/assertLower is called for Backtracking as described in the paper
		void createCheckpointBounds();
		
		void loadCheckpoint();
		
		
		void checkAndUpdateNonBasic();
		
		
					//used as helper function for checkCore, finds smallest Variable that fullfills the function f.
					//isBasic: weather the function is called on all basic or all nonbasic variables.
					// function f takes a TVariable, a matrix value and returns a bool
					// returns a TVariable if found, otherwise a nullpointer
		TVariable* findSmallestBasicVariable();
		
		TVariable* findSmallestNonBasicVariable(int posBasic, bool upperBound);
		
		
		std::set<TVariable*> findConflictVariables(TVariable* v);
		
					//Gets a map with the variables and keys to be inserted into the model
		carl::FastMap<carl::Variable,Rational> getModelValues() const;
		
					//Prints the tableau on the screen
		void print();
	};
}