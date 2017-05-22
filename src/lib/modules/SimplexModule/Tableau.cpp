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
			cout << "Loading " << form.constraint() << " l " << form.constraint().lhs().constantPart() <<  endl;
			//Get the variables in the formula
			std::set<carl::Variable> vs = form.variables();
			//adding the variables into the accumulator set
			variablesInFormula.insert(vs.begin(),vs.end());

			//Create Slack TVariable
			TVariable* tVar = new TVariable(VariableId , true);
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
			
			Bound b(-constraint.constantPart(),isUpperBound); 
			cout << "Created Bound " << -constraint.constantPart() << " isUpperBound: " << isUpperBound << endl; 
			
			formulaToBound[form] = b;
			formToVar[form] = tVar;
		}
		
		//Create TVariable for existing variables
		for(auto var : variablesInFormula){
			TVariable* tVar = new TVariable(var,VariableId ,false);
			varToTVar[var] = tVar;
			VariableId ++;
		}
		
		unsigned long number_of_variables = variablesInFormula.size();
		matrix.setConstant(number_of_formulas,number_of_variables,Rational(0));
		
		//Set correct size of vectors
		rowVars.resize(number_of_formulas);
		rowActive.resize(number_of_formulas);
		columnVars.resize(number_of_formulas);
		
		//now row is active at init
		std::fill(rowActive.begin(), rowActive.end(), false);

		//get the coefficients of each variable in each formula
		int x=0;int y=0;
		
		for(auto formula : formulas){
			x=0;
			rowVars[y] = formToVar[formula];
			rowVars[y]->setPositionMatrixY(y);
			
			for(auto var : variablesInFormula){
				
				columnVars[x] = varToTVar[var];
				columnVars[x]->setPositionMatrixX(x);
				
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
	
	
	void Tableau::pivot(int rowPos, int columnPos)
	{
		cout << "pivot!" << endl;
		
		//Swap variables in row and column vector
		TVariable* v = rowVars[rowPos];
		rowVars[rowPos] = columnVars[columnPos];
		columnVars[columnPos] = v;
		
		
		//Change isBasic and position in TVariable
		rowVars[rowPos]->setIsBasic(true);
		columnVars[columnPos]->setIsBasic(false);
		rowVars[rowPos]->setPositionMatrixY(columnVars[columnPos]->getPositionMatrixY());
		columnVars[columnPos]->setPositionMatrixX(rowVars[rowPos]->getPositionMatrixX());
		
		//Change values in matrix
		Rational factor = Rational(matrix(rowPos,columnPos));
		
		for(int y=0;y<matrix.rows();y++){
			
			//For the row where the variable is swapped
			if(rowPos == y){ 
				for(int x=0;x<matrix.cols();x++){
			
					if(columnPos == x){
						matrix(y,x) = Rational(1/factor);
					}else{
						matrix(y,x) /= Rational(-factor);
					}
					
				}
				
			//For all other rows
			}else{
				
				Rational factorRow = Rational(matrix(y,columnPos));
				
				for(int x=0;x<matrix.cols();x++){
					
					if(columnPos == x){
						matrix(y,x) = Rational((1/factor)*factorRow);
					}else{
						matrix(y,x) -= Rational( (matrix(rowPos,x)/factor)*factorRow);
					}
				}
			}
			
		}
		
	}
	
	
	void Tableau::pivotAndUpdate(TVariable* xi, TVariable* xj, Rational v)
	{
		cout << "pivotAndUpdate xi " << xi->getName() << " xj " << xj->getName() << " v " << v << endl;
		
		int i = xi->getPositionMatrixY();
		int j = xj->getPositionMatrixX();
		
		cout << "i " << i << " j " << j;
		cout << " aij " << matrix(j,i) << " " << matrix(i,j) << endl;
		
		
		Rational theta = Rational(v)-xi->getValue()/matrix(i, j); //Sure i j?
		xi->setValue(Rational(v));
		xj->setValue(xj->getValue()+theta);
		
		cout <<  "theta " << theta << endl;
		cout << xi->getName() << " = " << xi->getValue() << endl;
		cout << xj->getName() << " = " << xj->getValue() << endl;
		
		for(int k=0;k<matrix.rows();k++){
			if(k != i){
				rowVars[k]->setValue(rowVars[k]->getValue()+theta*matrix(k,j));
			}
		}
		
		pivot(i,j);
	}
	
	void Tableau::update(TVariable* x, Bound b)
	{
		cout << "Update" << endl;
		
		int column = x->getPositionMatrixX();
		for(auto basic : rowVars){
			int row = basic->getPositionMatrixY(); 
			basic->setValue(basic->getValue() + matrix(column,row)*(b.value-x->getValue()));
		}
		
		x->setValue(b.value);
	}
	
	bool Tableau::activateRow(FormulaT formula)
	{
		Bound c = formulaToBound[formula];
		TVariable* x = formToVar[formula];
		int row = formulaToRow[formula];
		rowActive[row] = true;
		
		if(c.upperBound){
			//AssertUpper
			cout << "activateRow AssertUpper" << endl;
			
			if(c.value >= x->getUpperBound().value){return true;}
			if(c.value < x->getLowerBound().value){return false;}
			cout << "Stayed in" << endl;
			
			x->changeUpperBound(Bound(c.value, true));
			
			if(x->getIsBasic()==false && x->getValue() > c.value){
				update(x, c);
			}
			
		}else {
			//AssertLower
			cout << "activateRow AssertLower" << endl;
			
			if(c.value <= x->getLowerBound().value){return true;}
			if(c.value > x->getUpperBound().value){return false;}
			cout << "Stayed in" << endl;
			
			x->changeLowerBound(Bound(c.value, false));
			
			if(x->getIsBasic()==false && x->getValue() < c.value){
				update(x, c);
			}
		}
		
		return true;
	}
	
	
	void Tableau::deactivateRow(FormulaT formula)
	{
	}
	
	
	
	TVariable* Tableau::findSmallestVariable(std::function<bool(TVariable*, Rational)> func, int pos, bool isBasic)
	{
		//TODO only check rows that are activated!!!
		int smallestId = INT_MAX;
		TVariable* t = nullptr;
		
		if(isBasic){
			
			int i=0;
			for(auto r : rowVars){
				cout << "Check Variable " << r->getName() << " v:" << r->getValue() << " l:" << r->getLowerBound().value << " u:" << r->getUpperBound().value << endl;
				if(func(r, matrix(i, pos))){
					cout << "Fullfills basic" << endl;
					if(r->getId() < smallestId){
						smallestId = r->getId();
						t = r;
					}
						
				}
				i++;
			}
			
		}else{
			
			int i=0;
			for(auto c : columnVars){
				if(func(c, matrix(pos, i))){
					if(c->getId() < smallestId){
						smallestId = c->getId();
						t = c;
					}
						
				}
				i++;
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
		for(auto c : columnVars){
			cout << c->getName() << "\t";
		}
		cout << endl;
		cout << "\t--------------" << endl;
		
		int a=0;
		for(auto r : rowVars){
			cout <<  r->getName() << "|";
			
			for(int i=0; i< matrix.cols();i++){
				cout << "\t" << matrix(a,i);
			}
			
			cout << endl;
			a++;
		}
		
		cout << endl;
		
		//Print Basic Variables with value and bounds
		for (auto const x : formToVar)
		{
			TVariable* v = x.second;
			cout << v->getName() << " v:" << v->getValue() << " l:" << v->getLowerBound().value << " u:" << v->getUpperBound().value << " isBasic " << v->getIsBasic() << " pos " << v->getPositionMatrixY() << endl;
		}
		//Print Nonbasic Variables with value and bounds
		for (auto const x : varToTVar)
		{
			TVariable* v = x.second;
			cout << v->getName() << " v:" << v->getValue() << " l:" << v->getLowerBound().value << " u:" << v->getUpperBound().value << " isBasic " << v->getIsBasic() << " pos " << v->getPositionMatrixX() << endl;
		}
	}
}