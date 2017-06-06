/**
 * @file Tableau.cpp
 * @author Sanchit Alekh <sanchit.alekh@rwth-aachen.de>
 * @author Karsten Jungnitsch <karsten.jungnitsch@rwth-aachen.de>
 * @author Alexander Reeh <alexander.reeh@rwth-aachen.de>
 *
 */

#include "Tableau.h"
#include "carl/core/logging.h"

 namespace smtrat
 {
 	
 	Tableau::Tableau(){}

 	/* Method to create Tableau
	*  Receives a list of formulas from the SAT Solver
	*  
	*  The tableau has the following structure:
	*  Each formula accumulates one row
	*  One column for each variable in the set of formulas
	*/
 	
 	Tableau::Tableau(std::list<FormulaT> formulaList)
 	{
 		
 		int VariableId = 0;

		//accumulator set for all the variables in the formulas 		
 		std::set<carl::Variable> variablesInFormula;
 		unsigned long number_of_formulas = formulaList.size();

 		SMTRAT_LOG_INFO("smtrat.my", number_of_formulas << " Formulas");
 		
 		for(auto formula : formulaList)
 		{
 			SMTRAT_LOG_INFO("smtrat.my", "Loading " << formula.constraint() << " l " << formula.constraint().lhs().constantPart());
 			//cout << "Loading " << formula.constraint() << " l " << formula.constraint().lhs().constantPart() <<  endl;
			//Get the variables in the formula
 			std::set<carl::Variable> varList = formula.variables();
			//adding the variables into the accumulator set
 			variablesInFormula.insert(varList.begin(),varList.end());

 			//TODO Why "Slack" ?!
			//Create Slack Variable of TVariable class
 			TVariable* tVar = new TVariable(VariableId , true);
 			VariableId ++;
 			
 			ConstraintT constraint = formula.constraint();
			
			//Assure we have a linear formula
			assert(constraint.lhs().isLinear());
 			
			//Check the constraint whether it is >= (lower bound) or <= (upper bound) 
			
			std::vector<Bound> boundSet;
 			
 			switch( constraint.relation() )
 			{
				case carl::Relation::EQ:
				{
					Bound bound1(-constraint.constantPart(),false);
					Bound bound2(-constraint.constantPart(),true);
					boundSet = {bound1, bound2};
					break;
				}
				
 				case carl::Relation::GEQ:
 				{
					Bound bound(-constraint.constantPart(),false);
					boundSet = {bound};
					break;
					
 				}
 				case carl::Relation::LEQ:
 				{
					Bound bound(-constraint.constantPart(),true);
					boundSet = {bound};
					break;
 					
 				}
				default:
				{
					assert(false);
					break;
				}
             

				
 			}

 			//Create Bound as the negative constant part of the formula.
 			//E.g x + y -5 <= 0
 			//Bound is +5
 			 
 			
 			SMTRAT_LOG_INFO("smtrat.my", "Created Bound " << -constraint.constantPart() );
 			//cout << "Created Bound " << -constraint.constantPart() << " isUpperBound: " << isUpperBound << endl; 
 			
 			formulaToBound[formula] = boundSet;
 			formToVar[formula] = tVar;
 		}
 		
		//Create TVariable for existing variables
 		for(auto variable : variablesInFormula){
 			TVariable* tVar = new TVariable(variable,VariableId ,false);
 			varToTVar[variable] = tVar;
 			VariableId ++;
 		}
 		
 		unsigned long number_of_variables = variablesInFormula.size();
 		matrix.setConstant(number_of_formulas,number_of_variables,Rational(0));
 		
		//Set correct size of vectors
 		rowVars.resize(number_of_formulas);
 		rowActive.resize(number_of_formulas);
 		columnVars.resize(number_of_variables);
 		
		//make sure the row is active at init
 		std::fill(rowActive.begin(), rowActive.end(), false);

		//get the coefficients of each variable in each formula
 		int x=0;int y=0;

 		//Create Tableau
 		//For each formula add the coefficient of each variable 
 		
 		for(auto formula : formulaList){
 			x=0;
 			rowVars[y] = formToVar[formula];
 			rowVars[y]->setPositionMatrixY(y);
			formulaToRow[formula] = y;
 			
 			for(auto var : variablesInFormula){
 				
 				columnVars[x] = varToTVar[var];
 				columnVars[x]->setPositionMatrixX(x);
 				
 				//If the formula contains the variable, set the Tableau entry to the coefficient
 				//If not, set entry to 0
 				if(formula.constraint().hasVariable(var)){
 					carl::MultivariatePolynomial<smtrat::Rational> coeff = formula.constraint().coefficient(var,1);
 					Rational _coeffValue = Rational( coeff.lcoeff() );
 					
 					//cout << coeff << "\t"; 
 					//SMTRAT_LOG_INFO("smtrat.my",coeff << "\t");
 					matrix(y,x) = _coeffValue;
 				} else {
 					//cout << "0" <<  "\t";
 					//SMTRAT_LOG_INFO("smtrat.my", "0" <<  "\t");
 				}
 				
 				x++;
 			}
 			
 			y++;
			//cout << endl;
 		}	
 		
		SMTRAT_LOG_INFO("smtrat.my", "Print Matrix");
		//Print the Tableau
		#if defined LOGGING
			print();
		#endif
 	}
 	
 	/* This function swaps a basic variable with a non basic variable
 	*  It swaps the positions and updates the
 	*  new coefficients of the rearranged formulas
 	*  Example:
 	*  
 	*  1*x + 1*y = s1
 	*  Row: (1,1)
	*
 	*  Pivot x with s1
	*
 	*  x = s1 - 1*y
 	*  Row: (1,-1)
 	*/
 			void Tableau::checkTest()
	{
						for(int i=0;i<rowVars.size();i++){
							
							if(rowActive[i]){
								Rational sum = 0;
								for(int a=0;a<columnVars.size();a++){
									sum += matrix(i, a)*columnVars[a]->getValue();
								}
								if(sum != rowVars[i]->getValue()){
									SMTRAT_LOG_WARN("smtrat.my", "Value Error in Matrix Row " << i << " (starting with 0)");
								}
							
							}
						}
	}
	
	
 	void Tableau::pivot(int rowPos, int columnPos)
 	{
 		//cout << "Pivoting Starts!" << endl;
 		SMTRAT_LOG_INFO("smtrat.my", "Pivoting Starts!");

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
 		checkTest();
 	}
 	
 	
	/**
	 * pivotAndUpdate: Auxiliary Procedure
	 * Paper Reference: A fast Linear-Arithmetic Solver for DPLL(T)
	 * Bruno Duterte and Leonardo de Moura
	 */
	 
	 void Tableau::pivotAndUpdate(TVariable* xi, TVariable* xj, Rational v)
	 {
	 	//cout << "pivotAndUpdate xi " << xi->getName() << " xj " << xj->getName() << " v " << v << endl;
	 	SMTRAT_LOG_INFO("smtrat.my", "PivotAndUpdate xi: " << xi->getName() << " xj: " << xj->getName() << " v: " << v)

	 	int i = xi->getPositionMatrixY();
	 	int j = xj->getPositionMatrixX();
	 	
		Rational theta = (Rational(v)-xi->getValue())/matrix(i, j); 
		xi->setValue(Rational(v));
		xj->setValue(xj->getValue()+theta);
		
		SMTRAT_LOG_INFO( "smtrat.my","theta " << theta );
		SMTRAT_LOG_INFO("smtrat.my", xi->getName() << " = " << xi->getValue() );
		SMTRAT_LOG_INFO("smtrat.my", xj->getName() << " = " << xj->getValue() );
		
		for(int k=0;k<matrix.rows();k++){
			if(k != i){
				SMTRAT_LOG_INFO("smtrat.my", rowVars[k]->getName() << " = " << rowVars[k]->getValue() << "+" << theta << "*" <<  matrix(k,j) << "=" << (rowVars[k]->getValue()+theta*matrix(k,j)));
				rowVars[k]->setValue(rowVars[k]->getValue()+theta*matrix(k,j));
			}
		}
		
		checkTest();
		SMTRAT_LOG_INFO( "smtrat.my","do swap");
		
		pivot(i,j);
	}
	
	

	/**
	 * pivotAndUpdate: Auxiliary Procedure
	 * Paper Reference: A fast Linear-Arithmetic Solver for DPLL(T)
	 * Bruno Duterte and Leonardo de Moura
	 */
	 
	 void Tableau::update(TVariable* x, Bound b)
	 {
	 	SMTRAT_LOG_INFO("smtrat.my", "Update");
	 	
	 	int column = x->getPositionMatrixX();
	 	for(auto basic : rowVars){
	 		int row = basic->getPositionMatrixY(); 
	 		basic->setValue(basic->getValue() + matrix(column,row)*(b.value-x->getValue()));
	 	}
	 	
	 	x->setValue(b.value);
		
		checkTest();
	 }
	 
	 bool Tableau::activateRow(FormulaT formula)
	 {
	 	std::vector<Bound> boundSet = formulaToBound[formula];
	 	TVariable* x = formToVar[formula];
	 	int row = formulaToRow[formula];
	 	
		//IMPORTANT Question: update on first assertUpper/Lower can change variable values via update and second assert return false. Is this a problem?
	 	bool result = true;
		SMTRAT_LOG_INFO("smtrat.my","Activate Row with basic = " << x->getIsBasic() );
		
		for(auto c: boundSet){
			
			if(c.upperBound){
				//AssertUpper (for upper bounds)
				result = result & assertUpper(x,c);
				
			}else {
				//AssertLower (for lower bounds)
				result = result & assertLower(x,c);
			}
		}
		
		//Only activate the row when all asserts were true
		if(result){
			rowActive[row] = true;
		}
		
	 	return result;
	 }
	 
	 
	 bool Tableau::assertUpper(TVariable* x, Bound c){
		 SMTRAT_LOG_INFO("smtrat.my","activateRow AssertUpper Bound:" << c.value << " "  << x->getValue());
				
		if(c.value >= x->getUpperBound().value){return true;}
		if(c.value < x->getLowerBound().value){return false;}
				
			x->changeUpperBound(Bound(c.value, true));
				
			if(x->getIsBasic()==false && x->getValue() > c.value){
				update(x, c);
		}
		return true;
	 }
	 
	 bool Tableau::assertLower(TVariable* x, Bound c){
		SMTRAT_LOG_INFO("smtrat.my","activateRow AssertLower Bound:" << c.value);
				
		if(c.value <= x->getLowerBound().value){return true;}
		if(c.value > x->getUpperBound().value){return false;}
				
		x->changeLowerBound(Bound(c.value, false));
				
		if(x->getIsBasic()==false && x->getValue() < c.value){
			update(x, c);
		}
		return true;
	 }
	 
	 
	 void Tableau::createCheckpoint(){
		 for(auto r : rowVars){
			 r->save();
		 }
		 
		 for(auto c : columnVars){
			 c->save();
		 }
	 }
	 
	 
	 void Tableau::deactivateRow(FormulaT formula)
	 {
		 int row = formulaToRow[formula];
		 rowActive[row] = false;
		 
		 //rowVars[row]->resetBounds();
		 
		 //Load the variable values of the last succesfull sat test (checkpoint)
		 for(auto r : rowVars){
			 r->load();
		 }
		 
		 for(auto c : columnVars){
			 c->load();
		 }
	 }
	 
	 
	 
	 TVariable* Tableau::findSmallestVariable(std::function<bool(TVariable*, Rational)> func, int pos, bool isBasic)
	 {
		//TODO only check rows that are activated!!!
	 	int smallestId = INT_MAX;
	 	TVariable* t = nullptr;
	 	
	 	if(isBasic){
	 		
			for(int i=0;i<rowVars.size();i++){
				if(rowActive[i]){
					TVariable* r = rowVars[i];
					
					if( func(r, matrix(i, pos))){
						SMTRAT_LOG_INFO("smtrat.my","Check Variable succ " << r->getName() << " v:" << r->getValue() << " l:" << r->getLowerBound().value << " u:" << r->getUpperBound().value);
						if(r->getId() < smallestId){
							smallestId = r->getId();
							t = r;
						}
	 				
					}
				}
	 		}
	 		
	 	}else{
	 		
			for(int i=0;i<columnVars.size();i++){
				TVariable* c = columnVars[i];
	 			if(func(c, matrix(pos, i))){
	 				if(c->getId() < smallestId){
	 					smallestId = c->getId();
	 					t = c;
	 				}
	 				
	 			}
	 		}
	 		
	 		
	 	}
	 	
	 	return t;
	 }
	 
	 
	 carl::FastMap<carl::Variable,Rational> Tableau::getModelValues() const
	 {
		carl::FastMap<carl::Variable,Rational> map;
		
		
		for (auto const x : varToTVar){
			carl::Variable origVar = x.first;
			TVariable* v = x.second;
			map[origVar] = v->getValue();
		}
		
	 	return map;
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
			
			if(rowActive[a]){
				cout << "-";
			}else{
				cout << " ";
			}
			
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
			int pos = v->getIsBasic() ? v->getPositionMatrixY() : v->getPositionMatrixX();
	 		cout << v->getName() << " v:" << v->getValue() << " l:" << v->getLowerBound().value << " u:" << v->getUpperBound().value << " isBasic " << v->getIsBasic() << " pos " << pos << endl;
	 	}
		//Print Nonbasic Variables with value and bounds
	 	for (auto const x : varToTVar)
	 	{
	 		TVariable* v = x.second;
			int pos = v->getIsBasic() ? v->getPositionMatrixY() : v->getPositionMatrixX();
	 		cout << v->getName() << " v:" << v->getValue() << " l:" << v->getLowerBound().value << " u:" << v->getUpperBound().value << " isBasic " << v->getIsBasic() << " pos " << pos << endl;
	 	}
	 }
	}