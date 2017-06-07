/**
 * @file Simplex.cpp
 * @author Sanchit Alekh <sanchit.alekh@rwth-aachen.de>
 * @author Karsten Jungnitsch <karsten.jungnitsch@rwth-aachen.de>
 * @author Alexander Reeh <alexander.reeh@rwth-aachen.de>
 *
 * @version 2017-05-08
 * Created on 2017-05-08.
 */

#include "SimplexModule.h"

 namespace smtrat
 {
	template<class Settings>
 	SimplexModule<Settings>::SimplexModule(const ModuleInput* _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* _manager):
 	Module( _formula, _conditionals, _manager )
#ifdef SMTRAT_DEVOPTION_Statistics
 	, mStatistics(Settings::moduleName)
#endif
 	{}

	template<class Settings>
 	SimplexModule<Settings>::~SimplexModule()
 	{}

	template<class Settings>
 	bool SimplexModule<Settings>::informCore( const FormulaT& _constraint )
 	{
 		listFormulas.push_back(_constraint);
		return true; // This should be adapted according to your implementation.
	}
	
	template<class Settings>
	void SimplexModule<Settings>::init()
	{}
	
	template<class Settings>
	bool SimplexModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
	{
		//Checks if tableau is initialized
		//If not initialized, then pass it to tableau class to collect the formulae

		if(tableauInitialized == false){
			tableauInitialized = true;
			tableau = Tableau(listFormulas);
		}
		
		bool result = tableau.activateRow(_subformula->formula());
		
		if(result){
			tableau.createCheckpointBounds();
		}
		SMTRAT_LOG_INFO("smtrat.my","AddCore returns " << result);
		return result;
	}
	
	template<class Settings>
	void SimplexModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
	{
		tableau.deactivateRow(_subformula->formula());
	}
	
	template<class Settings>
	void SimplexModule<Settings>::updateModel() const
	{
		mModel.clear();
		//if solver returns SAT, then get the satisfying model
		if( solverState() == Answer::SAT )
		{
			carl::FastMap<carl::Variable,Rational> map = tableau.getModelValues();
			
			for(auto x : map){
				//mModel.emplace(std::make_pair(x.first, x.second) );
				SMTRAT_LOG_INFO("smtrat.my","\t" << x.first.getName() << " = " << x.second);
			}
			
			mModelComputed = true;
		}
		else{
			SMTRAT_LOG_INFO("smtrat.my","Solver returned UNSAT, model won't be updated");
		}
	}
	
	template<class Settings>
	Answer SimplexModule<Settings>::checkCore()
	{
		//Used only for testing to prevent an infinite loop!
		#if defined DEVELOPER
		int limit = 10;
		#else
		int limit = -1;
		#endif
		
		//Is doing exactly what is described in the paper Check() method
		while(true){
			
			// Print Tableau only if Logging is turned on
			#if defined LOGGING
			tableau.print();
			#endif
			
			std::function<bool(TVariable*,Rational)> func = [](TVariable* v, Rational a)-> bool { return (v->getValue()<v->getLowerBound().value || v->getValue()>v->getUpperBound().value);  };
			TVariable* x = tableau.findSmallestVariable(func, 0, true);
			
			if(x == nullptr){
				SMTRAT_LOG_INFO("smtrat.my","No smallest variable found, create checkpoint and return SAT");
				//Creates Checkpoint, needed for backtracking
				tableau.createCheckpointValue();
				
				return Answer::SAT; // if there is no such xi then return satisfiable
			}else{
				
				
				SMTRAT_LOG_INFO("smtrat.my","Smallest basic var (such that value < l_Bound or value > u_Bound) is " << x->getName() << " with id " << x->getId());
				
				if(x->getValue() < x->getLowerBound().value){
					
					SMTRAT_LOG_INFO("smtrat.my","Condition 1 (value < lowerBound)");
					
					func = [](TVariable* v, Rational a)-> bool { return (a>0 && v->getValue()<v->getUpperBound().value) 
						|| (a<0 && v->getValue()>v->getLowerBound().value);  };
						TVariable* b = tableau.findSmallestVariable(func, x->getPositionMatrixY(), false);

						if(b == nullptr){
							generateTrivialInfeasibleSubset();
							//createInfisibleSubset(x);
							return Answer::UNSAT;
						}
						
						SMTRAT_LOG_INFO("smtrat.my","Smallest nonbasic var (such that (aij > 0 and value < u_Bound) or (aij < 0 and value > l_Bound )) is " << b->getName() << " with id " << b->getId());

						tableau.pivotAndUpdate(x, b, Rational(x->getLowerBound().value));
					}

					if(x->getValue() > x->getUpperBound().value){
						SMTRAT_LOG_INFO("smtrat.my","Condition 2 (value > upperBound)");

						func = [](TVariable* v, Rational a)-> bool { return (a<0 && v->getValue()<v->getUpperBound().value) 
							|| (a>0 && v->getValue()>v->getLowerBound().value);  };
							TVariable* b = tableau.findSmallestVariable(func, x->getPositionMatrixY(), false);

							if(b == nullptr){
								generateTrivialInfeasibleSubset();
								//createInfisibleSubset(x);
								return Answer::UNSAT;
							}
							
							SMTRAT_LOG_INFO("smtrat.my","Smallest nonbasic var (such that (aij < 0 and value < u_Bound) or (aij > 0 and value > l_Bound )) is " << b->getName() << " with id " << b->getId());

							tableau.pivotAndUpdate(x, b, Rational(x->getUpperBound().value));
						}

						//return Answer::UNKNOWN;

						if(limit == 0){
							SMTRAT_LOG_INFO("smtrat.my","WARNING: INFINITE LOOP BREAK");
							break;
						}
						limit--;
					}

				}
				
		return Answer::UNKNOWN; // This should be adapted according to your implementation.
	}



	template<class Settings>
	void SimplexModule<Settings>::createInfisibleSubset(TVariable* x)
	{
		FormulaSetT infSubSet;
		std::function<bool(TVariable*,Rational)> func;



		std::set<TVariable*> conflictVars;

		if(x->getValue() < x->getLowerBound().value){
			func = [](TVariable* v, Rational a)-> bool { return (a != 0);  };
			conflictVars = tableau.findConflictVariables(func, x->getPositionMatrixY());
		}

		if(x->getValue() > x->getUpperBound().value){
			func = [](TVariable* v, Rational a)-> bool { return (a != 0);  };
			conflictVars = tableau.findConflictVariables(func, x->getPositionMatrixY());
		}

		if(conflictVars.size() > 0){

			std::cout << "Added Here";

			infSubSet.insert(x->getFormula());

			for(auto y : conflictVars){
				infSubSet.insert(y->getFormula());
			}


			mInfeasibleSubsets.push_back( infSubSet );
		}else{
			std::cout << "Not Reached!";
		}
	}
}

#include "Instantiation.h"
