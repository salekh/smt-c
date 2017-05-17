#include "Tableau.h"
#include "carl/core/logging.h"

namespace smtrat
{
	
	Tableau::Tableau(){}
	
	Tableau::Tableau(std::list<FormulaT> formulas){
		for(auto form : formulas)
		{
			SMTRAT_LOG_ERROR("smtrat.my", "TABLEAU CREATE " << form.toString());
		}
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