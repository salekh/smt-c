/**
 * @file Simplex.cpp
 * @author YOUR NAME <YOUR EMAIL ADDRESS>
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
		
		tableau.activateRow(_subformula->formula());
		return true; // This should be adapted according to your implementation.
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
		while(true){
			
			std::function<bool(TVariable*,Rational)> func = [](TVariable* v, Rational a)-> bool { return (v->getValue()<v->getLowerBound().value || v->getValue()>v->getUpperBound().value);  };
			
			TVariable* x = tableau.findSmallestVariable(func, 0, true);
			
			if(x == nullptr){
				return Answer::SAT; // if there is no such xi then return satisfiable
			}else{
				
				cout << "Needing change" << endl;
				
				if(x->getValue() < x->getLowerBound().value){
					
					cout << "Condition 1" << endl;
					
					func = [](TVariable* v, Rational a)-> bool { return (a>0 && v->getValue()<v->getUpperBound().value) 
															|| (a<0 && v->getValue()>v->getUpperBound().value);  };
					TVariable* b = tableau.findSmallestVariable(func, x->getPositionMatrixY(), false);
					
					if(b == nullptr){
						return Answer::UNSAT;
					}
					cout << "Pivot and Update" << endl;
					
					tableau.pivotAndUpdate(x, b, x->getLowerBound().value);
				}
				
				if(x->getValue() < x->getUpperBound().value){
					cout << "Condition 2" << endl;
					
					func = [](TVariable* v, Rational a)-> bool { return (a<0 && v->getValue()<v->getUpperBound().value) 
															|| (a>0 && v->getValue()>v->getUpperBound().value);  };
					TVariable* b = tableau.findSmallestVariable(func, x->getPositionMatrixY(), false);
					
					if(b == nullptr){
						return Answer::UNSAT;
					}
					
					cout << "Pivot and Update" << endl;
					tableau.pivotAndUpdate(x, b, x->getUpperBound().value);
				}
				
				tableau.print();
				//return Answer::UNKNOWN;
			}
			
		}
		// Your code.
		return Answer::UNKNOWN; // This should be adapted according to your implementation.
	}
}

#include "Instantiation.h"
