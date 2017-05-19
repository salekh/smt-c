#include "Tableau.h"
#include "carl/core/logging.h"

namespace smtrat
{
	
	Tableau::Tableau(){}
	
	Tableau::Tableau(std::list<FormulaT> formulas){
		
		int VariableId = 0;
		
		//accumulator set for all the variables in the formulae 
		std::set<carl::Variable> variablesInFormula;
		unsigned long number_of_formulas = formulas.size();

		SMTRAT_LOG_ERROR("smtrat.my", number_of_formulas << "Formulas");
		
		for(auto form : formulas)
		{
			//Get the variables in the formula
			std::set<carl::Variable> vs = form.variables();
			//adding the variables into the accumulator set
			variablesInFormula.insert(vs.begin(),vs.end());

			/*
			SMTRAT_LOG_ERROR("smtrat.my", "Constraint Value " << form.constraint().lhs().toString());
			SMTRAT_LOG_ERROR("smtrat.my", "Value " << form.constraint().constantPart());
			SMTRAT_LOG_ERROR("smtrat.my", "TABLEAU CREATE " << form.toString());
			*/
			//Create Slack TVariable
			TVariable tVar(VariableId , true);
			VariableId ++;
			
			ConstraintT constraint = form.constraint();
			
			//Ceck the constraint weather it is >= or <= to create upper or lower Bound
			bool isUpperBound;
			switch( constraint.relation() )
            {
				case carl::Relation::GEQ:
                {
					isUpperBound = false;
				}
				case carl::Relation::LEQ:
				{
					isUpperBound = true;
				}
			}
			
			Bound b(form.constraint().constantPart(),isUpperBound); 
			cout << "Created Bound " << form.constraint().constantPart() << " isUpperBound: " << isUpperBound << endl; 
			
			formulaToBound[form] = b;
			formToVar[form] = tVar;
		}
		
		//Create TVariable for existing variables
		for(auto var : variablesInFormula){
			TVariable tVar(var,VariableId ,false);
			varToTVar[var] = tVar;
			VariableId ++;
		}
		
		unsigned long number_of_variables = variablesInFormula.size();
		matrix.setConstant(number_of_formulas,number_of_variables,Rational(0));
		
		//Set correct size of vectors
		row.resize(number_of_formulas);
		rowActive.resize(number_of_formulas);
		column.resize(number_of_formulas);
		
		//now row is active at init
		std::fill(rowActive.begin(), rowActive.end(), false);

		//get the coefficients of each variable in each formula
		int x=0;int y=0;
		
		for(auto formula : formulas){
			x=0;
			row[y] = formToVar[formula];
			
			for(auto var : variablesInFormula){
				
				column[x] = varToTVar[var];
				
				if(formula.constraint().hasVariable(var)){
					carl::MultivariatePolynomial<smtrat::Rational> coeff = formula.constraint().coefficient(var,1);
					Rational _coeffValue = Rational( coeff.lcoeff() );
					
					cout << coeff << "\t"; 
					matrix(y,x) = _coeffValue;
				}
				else{
					cout << "0" <<  "\t";
				}
				
				x++;
			}
			
			y++;
			cout << endl;
		}	
		
		//SMTRAT_LOG_ERROR("smtrat.my", "Matrix: " << endl << matrix);
		
		//Print the Tableau
		print();
	}
	
	void Tableau::pivotAndUpdate(TVariable v1, TVariable v2, Rational r)
	{
	}
	
	void Tableau::update(TVariable v, Bound b)
	{
	}
	
	bool Tableau::activateRow(FormulaT formula)
	{
		Bound c = formulaToBound[formula];
		TVariable x = formToVar[formula];
		int row = formulaToRow[formula];
		rowActive[row] = true;
		
		if(c.upperBound){
			//AssertUpper
			if(c.value >= x.getUpperBound().value){return true;}
			if(c.value < x.getUpperBound().value){return false;}
			x.getUpperBound().value = c.value;
			//.....TODO add UPDATE
			
		}else{
			//AssertLower
			
		}
		
		return true;
	}
	
	
	void Tableau::deactivateRow(FormulaT formula)
	{
	}
	
	
	
	TVariable* Tableau::findSmallestVariable(std::function<bool(TVariable)> func, bool isBasic)
	{
		int smallestId = -1;
		TVariable* t = nullptr;
		
		if(isBasic){
			
			for(auto r : row){
				if(func(r)){
					if(r.getId() < smallestId){
						smallestId = r.getId();
						t = &r;
					}
						
				}
			}
			
		}else{
			
			for(auto c : column){
				if(func(c)){
					if(c.getId() < smallestId){
						smallestId = c.getId();
						t = &c;
					}
						
				}
			}
			
		}
		
		return t;
	}
	
	
	TVariable Tableau::convertVar(carl::Variable var)
	{
		TVariable t;
		return t;
	}
	
	
	void Tableau::print(){
		
		cout << "\t";
		for(auto c : column){
			cout << c.getName() << "\t";
		}
		cout << endl;
		cout << "\t--------------" << endl;
		
		int a=0;
		for(auto r : row){
			cout <<  r.getName() << "|";
			
			for(int i=0; i< matrix.cols();i++){
				cout << "\t" << matrix(a,i);
			}
			
			cout << endl;
			a++;
		}
		
		cout << endl;
		
		//Print Variables with value and bounds
		for (auto const& x : formToVar)
		{
			TVariable v = x.second;
			cout << v.getName() << " v:" << v.getValue() << " l:" << v.getLowerBound().value << " u:" << v.getUpperBound().value << endl;
		}
		//Print Variables with value and bounds
		for (auto const& x : varToTVar)
		{
			TVariable v = x.second;
			cout << v.getName() << " v:" << v.getValue() << " l:" << v.getLowerBound().value << " u:" << v.getUpperBound().value << endl;
		}
	}
}