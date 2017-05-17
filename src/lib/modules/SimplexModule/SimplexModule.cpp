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
		// Your code.
		return Answer::UNKNOWN; // This should be adapted according to your implementation.
	}
}

#include "Instantiation.h"
