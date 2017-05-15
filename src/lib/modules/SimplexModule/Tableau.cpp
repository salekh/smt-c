#include "Tableau.h"
#include "carl/core/logging.h"

namespace smtrat
{
	
	Tableau(const std::list<FormulaT*>& formulas){
		for(auto form : formulas)
		{
			SMTRAT_LOG_ERROR("smtrat.my", "TABLEAU CREATE " << form.toString());
		}
	}
	
	void Tableau::pivotAndUpdate(TVariable v1, TVariable v2, double);
	{
	}
	
	void Tableau::update(TVariable v, Bound b);
	{
	}
	
	void Tableau::activateRow(FormulaT formula);
	{
	}
	
	
	void Tableau::deactivateRow(FormulaT formula);
	{
	}
	
	
	VariableT Tableau::findSmallestVariable(bool isBasic);
	{
		return -1;
	}
	
	
	TVariable Tableau::convertVar(carl::Variable var);
	{
		return -1;
	}
	
}