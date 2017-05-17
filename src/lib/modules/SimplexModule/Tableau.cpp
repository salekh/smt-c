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
			TVariable tVar(VariableId ,false);
			VariableId ++;
			Bound b(0,true); // <----------------------- TODO: Add the correct Bounds!!!
			
			formulaToBound[form] = b;
			formToVar[form] = tVar;
		}
		
		//Create TVariable for existing variables
		for(auto var : variablesInFormula){
			TVariable tVar(var,VariableId ,true);
			varToTVar[var] = tVar;
			VariableId ++;
		}
		
		unsigned long number_of_variables = variablesInFormula.size();
		matrix.setConstant(number_of_formulas,number_of_variables,0);
		
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
					cout << coeff << "\t"; 
					matrix(y,x) = 0; //coeff; // <----------------------- TODO: Convert coeff to double!!!
				}
				else{
					cout << "0" <<  "\t";
				}
				
				x++;
			}
			
			y++;
			cout << endl;
		}	
		
		SMTRAT_LOG_ERROR("smtrat.my", "Matrix: " << endl << matrix);
		
		//Print the Tableau
		print();
	}
	
	void Tableau::pivotAndUpdate(TVariable v1, TVariable v2, double d)
	{
	}
	
	void Tableau::update(TVariable v, Bound b)
	{
	}
	
	bool Tableau::activateRow(FormulaT formula)
	{
		Bound c = formulaToBound[formula];
		TVariable x = formToVar[formula];
		
		//AssertUpper
		
		return true;
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
	
	
	void Tableau::print(){
		
		cout << "\t";
		for(auto c : column){
			cout << "v" << c.getId() << "\t";
		}
		cout << endl;
		cout << "--------------" << endl;
		
		int a=0;
		for(auto r : row){
			cout << "v" << r.getId() << "|";
			
			for(int i=0; i< matrix.cols();i++){
				cout << "\t" << matrix(i,a);
			}
			
			cout << endl;
			a++;
		}
	}
}