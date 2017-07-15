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

			//Create Slack Variable of TVariable class
 			TVariable* tVar = new TVariable(formula, VariableId , true);
 			VariableId ++;
 			
 			ConstraintT constraint = formula.constraint();
			
			//Assure we have a linear formula
			assert(constraint.lhs().isLinear());
 			
			//Create Bound as the negative constant part of the formula.
 			//E.g x + y -5 <= 0
 			//Bound is +5
			std::vector<Bound> boundSet;
 			
 			switch( constraint.relation() )
 			{
				case carl::Relation::EQ:
				{
					//Eq is handled as both >= and <=
					Bound bound1(TRational(-constraint.constantPart()),false);
					Bound bound2(TRational(-constraint.constantPart()),true);
					boundSet = {bound1, bound2};
					break;
				}
				
 				case carl::Relation::GEQ:
 				{
					Bound bound(TRational(-constraint.constantPart()),false);
					boundSet = {bound};
					break;
					
 				}
 				case carl::Relation::LEQ:
 				{
					Bound bound(TRational(-constraint.constantPart()),true);
					boundSet = {bound};
					break;
 					
 				}
 				case carl::Relation::GREATER:
 				{
					//Greater uses the delta part of the TRational
 					Bound bound(TRational(-constraint.constantPart(),1),false);
					boundSet = {bound};
 					break;
 				}
 				case carl::Relation::LESS:
 				{
					//Less uses the delta part of the TRational
 					Bound bound(TRational(-constraint.constantPart(),-1),true);
					boundSet = {bound};
 					break;
 				}
 			}


 			 for(Bound b : boundSet){
				 SMTRAT_LOG_INFO("smtrat.my", "Created Bound " << b.value << " isUpperBound: " << b.upperBound);
			 }

 			
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
 		
 		
		//make sure no row is active
		rowActive.resize(number_of_formulas);
 		std::fill(rowActive.begin(), rowActive.end(), false);


		//Create Tableau columnVars vector
		columnVars.resize(number_of_variables);
		
 		int x=0;
		for(auto var : variablesInFormula){
			columnVars[x] = varToTVar[var];
			columnVars[x]->setPositionMatrixX(x);
			x++;
		}
		
		
		//Create Tableau rowVars vector
		rowVars.resize(number_of_formulas);
		
		int y=0;
		for(auto formula : formulaList){
 			rowVars[y] = formToVar[formula];
 			rowVars[y]->setPositionMatrixY(y);
			formulaToRow[formula] = y;
			y++;
		}
		
 		//Create Tableau matrix
		y=0;
		matrix.setConstant(number_of_formulas,number_of_variables,Rational(0));
		
 		for(auto formula : formulaList){
 			
			for(const auto& t: formula.constraint().lhs()){
				if(t.isSingleVariable()){
					carl::Variable var = t.getSingleVariable();
					Rational coeff = t.coeff();
					int x = varToTVar[var]->getPositionMatrixX();
					
					matrix(y,x) = coeff;
				}
			}
 			
 			y++;
 		}	
 		
		SMTRAT_LOG_INFO("smtrat.my", "Print Matrix");
		//Print the Tableau
		#if defined LOGGING
			print();
		#endif
 	}
 	

	void Tableau::checkTest()
	{
		for(int i=0;i<rowVars.size();i++){
							
			TRational sum = TRational(0);
			for(int a=0;a<columnVars.size();a++){
				sum += columnVars[a]->getValue()*matrix(i, a);
			}
			if(sum != rowVars[i]->getValue()){
				SMTRAT_LOG_WARN("smtrat.my", "VALUE ERROR in Matrix Row " << i << " (starting with 0)");
			}
		}
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
 		Rational factor = matrix(rowPos,columnPos);
 		
 		for(int y=0;y<matrix.rows();y++){
 			
			//For the row where the variable is swapped
 			if(rowPos != y){ 
 				
 				Rational factorRow = matrix(y,columnPos);
 				
				if(factorRow != 0){
					for(int x=0;x<matrix.cols();x++){
						
						if(columnPos == x){
							matrix(y,x) = (1/factor)*factorRow;
						}else{
							matrix(y,x) -= (matrix(rowPos,x)/factor)*factorRow;
						}
					}
				}
 			}
 		}
		
		//Extra loop is needed, because otherwise matrix values are overwritten
		int y = rowPos;
		for(int x=0;x<matrix.cols();x++){
 					
			if(columnPos == x){
				matrix(y,x) = 1/factor;
			}else{
				matrix(y,x) /= -factor;
			}
 					
 		}
		
		#if defined DEVELOPPER
			checkTest();
		#endif
 	}
 	
 	
	/**
	 * pivotAndUpdate: Auxiliary Procedure
	 * Paper Reference: A fast Linear-Arithmetic Solver for DPLL(T)
	 * Bruno Duterte and Leonardo de Moura
	 */
	 
	 void Tableau::pivotAndUpdate(TVariable* xi, TVariable* xj, TRational v)
	 {
	 	//cout << "pivotAndUpdate xi " << xi->getName() << " xj " << xj->getName() << " v " << v << endl;
	 	SMTRAT_LOG_INFO("smtrat.my", "PivotAndUpdate xi: " << xi->getName() << " xj: " << xj->getName() << " v: " << v)
		
		#if defined DEVELOPPER
			checkTest();
		#endif

	 	int i = xi->getPositionMatrixY();
	 	int j = xj->getPositionMatrixX();
	 	
		TRational theta = (v-xi->getValue())/matrix(i, j); 
		xi->setValue(v);
		xj->setValue(xj->getValue()+theta);
		
		SMTRAT_LOG_INFO( "smtrat.my","theta " << theta );
		SMTRAT_LOG_INFO("smtrat.my", xi->getName() << " = " << xi->getValue() );
		SMTRAT_LOG_INFO("smtrat.my", xj->getName() << " = " << xj->getValue() );
		
		for(int k=0;k<matrix.rows();k++){
			if(k != i){
				SMTRAT_LOG_INFO("smtrat.my", rowVars[k]->getName() << " = " << rowVars[k]->getValue() << "+" << theta << "*" <<  matrix(k,j) << "=" << (rowVars[k]->getValue()+theta*matrix(k,j)));
				//rowVars[k]->setValue(rowVars[k]->getValue()+theta*matrix(k,j));
				TRational t = TRational(theta);
				t *= matrix(k,j);
				rowVars[k]->getValue() += t;
			}
		}
		
		#if defined DEVELOPPER
			checkTest();
		#endif
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
			TRational t = TRational(b.value);
			t-=x->getValue();
			t*=matrix(row,column);
			basic->getValue() += t;
	 		//basic->setValue(basic->getValue() + (b.value-x->getValue())*matrix(row,column));
	 	}
	 	
	 	x->setValue(b.value);
		
		#if defined DEVELOPPER
			checkTest();
		#endif
	 }
	 
	 bool Tableau::activateRow(FormulaT formula)
	 {
	 	std::vector<Bound> boundSet = formulaToBound[formula];
	 	TVariable* x = formToVar[formula];
	 	int row = formulaToRow[formula];
	 	
		//TODO IMPORTANT Question: update on first assertUpper/Lower can change variable values via update and second assert return false. Is this a problem?
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
	 
	 
	 /**
	  * Idea: When two formulas are added in a row and after that check is executed
	  * During check there is a pivot (makes slack variable Nonbasic) for the first formula, but the check fails because of the second formula and now the second formula is replaced
	  * 	->  because of remove the variable bounds are reset. This means the slack variable of the first formula is no longer in its bounds
	  * 	-> check in the paper can only handle incorrect bounds for Basic Variables
	  * 	-> This adds to check the feature to handle incorrect Bounds for NonBasic Variables
	  */
	 void Tableau::checkAndUpdateNonBasic(){
		 for(TVariable* x : columnVars){
			 if(x->getValue() > x->getUpperBound().value){
				 update(x, x->getUpperBound());
			 }else if( x->getValue() < x->getLowerBound().value){
				 update(x, x->getLowerBound());
			 }
		 }
	 }
	 
	 
	 bool Tableau::assertUpper(TVariable* x, Bound c){
		 SMTRAT_LOG_INFO("smtrat.my","activateRow AssertUpper Bound:" << c.value << " "  << x->getValue());
				
		if(c.value >= x->getUpperBound().value){return true;}
		if(c.value < x->getLowerBound().value){return false;}
				
			x->changeUpperBound(Bound(c.value, true));
				
			//this is now done by checkAndUpdateNonBasic
			//if(x->getIsBasic()==false && x->getValue() > c.value){
			//	update(x, c);
			//}
		return true;
	 }
	 
	 bool Tableau::assertLower(TVariable* x, Bound c){
		SMTRAT_LOG_INFO("smtrat.my","activateRow AssertLower Bound:" << c.value);
				
		if(c.value <= x->getLowerBound().value){return true;}
		if(c.value > x->getUpperBound().value){return false;}
				
		x->changeLowerBound(Bound(c.value, false));
		
		//this is now done by checkAndUpdateNonBasic
		//if(x->getIsBasic()==false && x->getValue() < c.value){
		//	update(x, c);
		//}
		return true;
	 }
	 
	 //stores value inside saveValue of vars to create a checkpoint value
	 void Tableau::createCheckpointValue(){
		 for(auto r : rowVars){
			 r->saveValue();
		 }
		 
		 for(auto c : columnVars){
			 c->saveValue();
		 }
	 }
	 
	 
	 
	 
	 void Tableau::deactivateRow(FormulaT formula)
	 {
		 int row = formulaToRow[formula];
		 rowActive[row] = false;
		 
		//Replaced the stack for bounds with an activate/deactivate feature
		 formToVar[formula]->changeUpperBound(Bound(TRational(10000000), true));
		 formToVar[formula]->changeLowerBound(Bound(TRational(-10000000), false));
		 
		 //Load the variable values of the last succesfull sat test (checkpoint)

	 }
	 
	 
	 //Loads the values stored in the checkpoint
	 void Tableau::loadCheckpoint(){
		 for(auto r : rowVars){
			 r->load();
		 }
		 
		 for(auto c : columnVars){
			 c->load();
		 }
	 }
	 
	 
	 
	 TVariable* Tableau::findSmallestBasicVariable()
	 {
	 	int smallestId = INT_MAX;
	 	TVariable* t = nullptr;
	 	
		for(int i=0;i<rowVars.size();i++){
				//if(rowActive[i]){
	 		TVariable* r = rowVars[i];
	 		if(r->getId() < smallestId){

	 			if((r->getValue()<r->getLowerBound().value || r->getValue()>r->getUpperBound().value)){

	 				smallestId = r->getId();
	 				t = r;
	 			}

	 		}
	 	}

	 	return t;
	 }
	 		
			
	TVariable* Tableau::findSmallestNonBasicVariable(int pos, bool upperBound)
	{
		int smallestId = INT_MAX;
	 	TVariable* t = nullptr;
		
		if(upperBound==false){
	
			for(int i=0;i<columnVars.size();i++){
				TVariable* c = columnVars[i];
				if(c->getId() < smallestId){
					
					
					if((matrix(pos, i)>0 && c->getValue()<c->getUpperBound().value) 
						|| (matrix(pos, i)<0 && c->getValue()>c->getLowerBound().value))
					{
	 					smallestId = c->getId();
	 					t = c;
	 				}
	 				
	 			}
	 		}
			
	 	}else{
	 		
			for(int i=0;i<columnVars.size();i++){
				TVariable* c = columnVars[i];
				if(c->getId() < smallestId){
					if((matrix(pos, i)<0 && c->getValue()<c->getUpperBound().value) 
							|| (matrix(pos, i)>0 && c->getValue()>c->getLowerBound().value))
					{
	 					smallestId = c->getId();
	 					t = c;
	 				}
	 				
	 			}
	 		}
	 		
	 		
	 	}
	 	
	 	return t;
	 }
	 
	 
	 //Returns a set of conflict variables for a given Nonbasic Var
	 //conflict means that the in the matrix a(x,i) != 0
	 std::set<TVariable*> Tableau::findConflictVariables(TVariable* x){
		 
		 int pos = x->getPositionMatrixY();
		 std::set<TVariable*> returnSet;
		 
		 for(int i=0;i<columnVars.size();i++){
				TVariable* c = columnVars[i];
	 			if(matrix(pos, i) != 0){
	 				returnSet.insert(c);
	 				
	 			}
	 		}
			return returnSet;
	 }
	 
	 
	 carl::FastMap<carl::Variable,Rational> Tableau::getModelValues() const
	 {
		carl::FastMap<carl::Variable,Rational> map;
		
		
		Rational delta = 1;
		
		for(auto c : columnVars){
			delta = min(delta,c->calculateDelta(c->getUpperBound()));
			delta = min(delta,c->calculateDelta(c->getLowerBound()));
		}
		
		for(auto c : rowVars){
			delta = min(delta,c->calculateDelta(c->getUpperBound()));
			delta = min(delta,c->calculateDelta(c->getLowerBound()));
		}
		
		SMTRAT_LOG_INFO("smtrat.my","Delta found is " << delta);
		
		for (auto const x : varToTVar){
			carl::Variable origVar = x.first;
			TVariable* v = x.second;
			map[origVar] = v->getValue().getRationalPart()+v->getValue().getDeltaPart()*delta;
		}
		
	 	return map;
	 }
	 
	 
	 //prints the tableau, i.e. all variables (basic + non-basic) with value and bounds

	 void Tableau::print(){
	 	
		 //Create Vector for formulas
		 std::vector<FormulaT> formulaRow;
		 formulaRow.resize(rowVars.size());
		 for(auto a : formulaToRow){
			 formulaRow[a.second] = a.first;
		 }
		 
		 
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
			
			cout << "\t\t" << formulaRow[a];
	 		
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
