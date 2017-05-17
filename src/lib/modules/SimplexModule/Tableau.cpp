#include "Tableau.h"
#include "carl/core/logging.h"

namespace smtrat
{
	
	Tableau::Tableau(){}
	
	Tableau::Tableau(std::list<FormulaT> formulas){
		std::set<carl::Variable> variablesInFormula;
		unsigned long number_of_formulas = formulas.size();

		SMTRAT_LOG_ERROR("smtrat.my", number_of_formulas << " elements present in the formula");
		for(auto form : formulas)
		{
			//Get the variables in the formula
			std::set<carl::Variable> x = form.variables();
			variablesInFormula.insert(x.begin(),x.end());
			SMTRAT_LOG_ERROR("smtrat.my", "Constraint Value " << form.constraint().lhs().toString());
			SMTRAT_LOG_ERROR("smtrat.my", "TABLEAU CREATE " << form.toString());
		}
		for(auto var : variablesInFormula){
			SMTRAT_LOG_ERROR("smtrat.my","Variables in Formulae " << var);
		}
		unsigned long number_of_variables = variablesInFormula.size();
		matrix.setConstant(number_of_formulas,number_of_variables,0);
		SMTRAT_LOG_ERROR("smtrat.my", "Matrix: " << endl << matrix);
	}
	
	void Tableau::pivotAndUpdate(TVariable v1, TVariable v2, double d)
	{
	}
	
	void Tableau::update(TVariable v, Bound b)
	{
	}
	
	void Tableau::activateRow(FormulaT formula)
	{
	}
	
	
	void Tableau::deactivateRow(FormulaT formula)
	{
	}
	
	
	TVariable Tableau::findSmallestVariable(bool isBasic)
	{
		TVariable t;
		return t;
	}
	
	
	TVariable Tableau::convertVar(carl::Variable var)
	{
		TVariable t;
		return t;
	}
	
}