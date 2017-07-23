/**
 * 
 * The tableau takes the formulas and creates the TVariables and the matrix
 * It contains all the necessary methods for the SimplexModule
 * 
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
		bool assertUpper(TVariable* x);
		
		bool assertLower(TVariable* x);
		
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
		
				//Called in removecore to reset variable values
		void loadCheckpoint();
		
			/*
			 * Because the order of addCore and removeCore can be arbitrary (for example add(a), add(b), remove(a), remove(b))
			 * this method guarantees that all nonBasic variables are in their bounds
			 * This is a change to the algorithm in the paper (where a strict order is assumed) and it happens in the assert method.
			 * 
			 */
		 void checkAndUpdateNonBasic();
		
		
			/*
			 * Finds the smallest Basic Variable that does not fullfill it bounds
			 */
		TVariable* findSmallestBasicVariable();
		
			/*
			 * For a given position of a basic Variable that does not fullfill a bound and whether the bounds is upper:
			 * Finds a NonBasic variable that can be changed so that the basicVariable can fullfill it bounds.
			 */
		TVariable* findSmallestNonBasicVariable(int posBasic, bool upperBound);
		
		
			//Used in createInfisibleSubset to find all Variables that affect the given TVariable
		std::set<TVariable*> findConflictVariables(TVariable* v);
		
				//Gets a map with the variables and keys to be inserted into the model
		carl::FastMap<carl::Variable,Rational> getModelValues() const;
		
				//Prints the whole tableau and varialbe informations
		void print();
	};
}