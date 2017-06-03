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
		SMTRAT_LOG_INFO("smtrat.my","AddCore returns " << result);
		return result;
	}
	
	template<class Settings>
	void SimplexModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
	{
		// Your code.
	}
	
	template<class Settings>
	void SimplexModule<Settings>::updateModel() const
	{
		mModel.clear();
		if( solverState() == Answer::SAT )
		{
			// Your code.
		}
	}
	
	template<class Settings>
	Answer SimplexModule<Settings>::checkCore()
	{
		//Used only for testing to prevent an infinite loop!
		#if defined DEVELOPPER
			int limit = 10;
		#else
			int limit = -1;
		#endif
		
		//Is doing exactly what is described in the paper Check() method
		while(true){
			
			std::function<bool(TVariable*,Rational)> func = [](TVariable* v, Rational a)-> bool { return (v->getValue()<v->getLowerBound().value || v->getValue()>v->getUpperBound().value);  };
			
			TVariable* x = tableau.findSmallestVariable(func, 0, true);
			
			if(x == nullptr){
				SMTRAT_LOG_INFO("smtrat.my","x is nullptr");
				//Creates Checkpoint, needed for backtracking
				tableau.createCheckpoint();
				
				return Answer::SAT; // if there is no such xi then return satisfiable
			}else{
				
				SMTRAT_LOG_INFO("smtrat.my","Needing change");
				
				if(x->getValue() < x->getLowerBound().value){
					
					SMTRAT_LOG_INFO("smtrat.my","Condition 1");
					
					func = [](TVariable* v, Rational a)-> bool { return (a>0 && v->getValue()<v->getUpperBound().value) 
						|| (a<0 && v->getValue()>v->getLowerBound().value);  };
						TVariable* b = tableau.findSmallestVariable(func, x->getPositionMatrixY(), false);

						if(b == nullptr){
							return Answer::UNSAT;
						}

						SMTRAT_LOG_INFO("smtrat.my","Pivot and Update!");
						tableau.pivotAndUpdate(x, b, Rational(x->getLowerBound().value));
					}

					if(x->getValue() > x->getUpperBound().value){
						SMTRAT_LOG_INFO("smtrat.my","Condition 2");

						func = [](TVariable* v, Rational a)-> bool { return (a<0 && v->getValue()<v->getUpperBound().value) 
							|| (a>0 && v->getValue()>v->getLowerBound().value);  };
							TVariable* b = tableau.findSmallestVariable(func, x->getPositionMatrixY(), false);

							if(b == nullptr){
								return Answer::UNSAT;
							}

							SMTRAT_LOG_INFO("smtrat.my","Pivot and Update!");
							tableau.pivotAndUpdate(x, b, Rational(x->getUpperBound().value));
						}

						#if defined LOGGING
							tableau.print();
						#endif
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
}

#include "Instantiation.h"
