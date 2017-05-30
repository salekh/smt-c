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
		cout << "AddCore returns " << result << endl;
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
		//Used only for testing! To prevent an infinite loop!
		int limit = 10;
		
		//Is doing exactly what is described in the paper Check() method
		while(true){
			
			std::function<bool(TVariable*,Rational)> func = [](TVariable* v, Rational a)-> bool { return (v->getValue()<v->getLowerBound().value || v->getValue()>v->getUpperBound().value);  };
			
			TVariable* x = tableau.findSmallestVariable(func, 0, true);
			
			if(x == nullptr){
				cout << "x is nullptr" << endl;
				//Creates Checkpoint, needed for backtracking
				tableau.createCheckpoint();
				
				return Answer::SAT; // if there is no such xi then return satisfiable
			}else{
				
				cout << "Needing change" << endl;
				
				if(x->getValue() < x->getLowerBound().value){
					
					cout << "Condition 1" << endl;
					
					func = [](TVariable* v, Rational a)-> bool { return (a>0 && v->getValue()<v->getUpperBound().value) 
						|| (a<0 && v->getValue()>v->getLowerBound().value);  };
						TVariable* b = tableau.findSmallestVariable(func, x->getPositionMatrixX(), false);

						if(b == nullptr){
							return Answer::UNSAT;
						}

						cout << "Pivot and Update!" << endl;
						tableau.pivotAndUpdate(x, b, Rational(x->getLowerBound().value));
					}

					if(x->getValue() > x->getUpperBound().value){
						cout << "Condition 2" << endl;

						func = [](TVariable* v, Rational a)-> bool { return (a<0 && v->getValue()<v->getUpperBound().value) 
							|| (a>0 && v->getValue()>v->getLowerBound().value);  };
							TVariable* b = tableau.findSmallestVariable(func, x->getPositionMatrixY(), false);

							if(b == nullptr){
								return Answer::UNSAT;
							}

							cout << "Pivot and Update!" << endl;
							tableau.pivotAndUpdate(x, b, Rational(x->getUpperBound().value));
						}

						tableau.print();
						//return Answer::UNKNOWN;

						if(limit == 0){
							cout << "WARNING: INFINITE LOOP BREAK" << endl;
							break;
						}
						limit--;
					}

				}
				
		return Answer::UNKNOWN; // This should be adapted according to your implementation.
	}
}

#include "Instantiation.h"
