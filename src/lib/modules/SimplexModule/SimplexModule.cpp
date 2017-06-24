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
		//If the formula contains not equals, do not add it to the tableau and instead create formula > or <
		if( _constraint.constraint().relation() == carl::Relation::NEQ){
			
			FormulaT formulaSmaler = FormulaT(_constraint.constraint().lhs(), carl::Relation::LESS);
			FormulaT formulaLarger = FormulaT(_constraint.constraint().lhs(), carl::Relation::GREATER);
			FormulaT formula = FormulaT(carl::FormulaType::OR, formulaSmaler, formulaLarger );
			addLemma(formula);
			
			neqHelper.informNeq(_constraint, formulaSmaler, formulaLarger);
			
			return true;
		}
		
 		listFormulas.push_back(_constraint);
		return true; // This should be adapted according to your implementation.
	}
	
	template<class Settings>
	void SimplexModule<Settings>::init()
	{}
	
	/** This function is called each iteration of the theory solver
    * The SAT solver passes on a subset of all formulas. This set has to be checked on
    * feasability. Since the theory solver has all formulas, it can work with the subset
    * of these formulas to activate by activating each formula in the Tableau of the
    * theory solver
    *
    * addCore activates a formula
    */

    template<class Settings>
	bool SimplexModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
	{
		
		//Ignore formulas that contain not equals and return true
		//informCore already creates an additional formula via > or <
		//%TODO save this information in variable to speed up next checkCore?
		if(neqHelper.addFormula(_subformula->formula())){
			return true;
		}
		
		//Checks if tableau is initialized
		//If not initialized, then pass it to tableau class to collect the formulas

		tableau.createCheckpointBounds();

		if(tableauInitialized == false){
			tableauInitialized = true;
			tableau = Tableau(listFormulas);
		}
		
		bool result = tableau.activateRow(_subformula->formula());
		
		SMTRAT_LOG_INFO("smtrat.my","AddCore returns " << result);
		return result;
	}

    /** Analogue removeCore deactivates a formula if it has to be
    * removed out of the subset of formulas the theory solver
    * has to check on feasability
    */
	
	template<class Settings>
	void SimplexModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
	{
		//Not equals formulas are ignored
		neqHelper.removeForumula(_subformula->formula());
		
		tableau.deactivateRow(_subformula->formula());
	}
	
	template<class Settings>
	void SimplexModule<Settings>::updateModel() const
	{
		mModel.clear();
		if( solverState() == Answer::SAT )
		{
			carl::FastMap<carl::Variable,Rational> map = tableau.getModelValues();
			
			for(auto x : map){
				mModel.insert(std::make_pair(x.first, x.second) );
				SMTRAT_LOG_INFO("smtrat.my","\t" << x.first.getName() << " = " << x.second);
			}
			
			mModelComputed = true;
		}
	}
	
    /** This functions checks the feasability of the set of formulas
    * if they are satisfiable with the current variable 
    * assignments
    * 
    * If they are SAT, the SAT solver returns SAT
    *
    * If they are UNSAT, the SAT solver recieves the set of
    * unfeasible formulas and continues to start a 
    * new iteration or returns UNSAT
    */

	template<class Settings>
	Answer SimplexModule<Settings>::checkCore()
	{
		if(neqHelper.containsProblemFormula()){
			return Answer::UNKNOWN;
		}
		
		//Used only for testing to prevent an infinite loop!
		#if defined DEVELOPPER
			int limit = 10;
		#else
			int limit = -1;
		#endif
		
		//Is doing exactly what is described in the paper Check() method
		while(true){
			
			#if defined LOGGING
				tableau.print();
			#endif
			
			std::function<bool(TVariable*,TRational)> func = [](TVariable* v, TRational a)-> bool { return (v->getValue()<v->getLowerBound().value || v->getValue()>v->getUpperBound().value);  };
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
					
					func = [](TVariable* v, TRational a)-> bool { return (a>0 && v->getValue()<v->getUpperBound().value) 
						|| (a<0 && v->getValue()>v->getLowerBound().value);  };
						TVariable* b = tableau.findSmallestVariable(func, x->getPositionMatrixY(), false);

						if(b == nullptr){
							createInfisibleSubset(x);
							return Answer::UNSAT;
						}
						
						SMTRAT_LOG_INFO("smtrat.my","Smallest nonbasic var (such that (aij > 0 and value < u_Bound) or (aij < 0 and value > l_Bound )) is " << b->getName() << " with id " << b->getId());

						tableau.pivotAndUpdate(x, b, TRational(x->getLowerBound().value));
					}

					if(x->getValue() > x->getUpperBound().value){
						SMTRAT_LOG_INFO("smtrat.my","Condition 2 (value > upperBound)");

						func = [](TVariable* v, TRational a)-> bool { return (a<0 && v->getValue()<v->getUpperBound().value) 
							|| (a>0 && v->getValue()>v->getLowerBound().value);  };
							TVariable* b = tableau.findSmallestVariable(func, x->getPositionMatrixY(), false);

							if(b == nullptr){
								createInfisibleSubset(x);
								return Answer::UNSAT;
							}
							
							SMTRAT_LOG_INFO("smtrat.my","Smallest nonbasic var (such that (aij < 0 and value < u_Bound) or (aij > 0 and value > l_Bound )) is " << b->getName() << " with id " << b->getId());

							tableau.pivotAndUpdate(x, b, TRational(x->getUpperBound().value));
						}

						//return Answer::UNKNOWN;

						if(limit == 0){
							SMTRAT_LOG_WARN("smtrat.my","WARNING: INFINITE LOOP BREAK");
							break;
						}
						limit--;
					}

				}
				
		return Answer::UNKNOWN; // This should be adapted according to your implementation.
	}

    //TODO
    
	template<class Settings>
	void SimplexModule<Settings>::createInfisibleSubset(TVariable* x)
	{
			SMTRAT_LOG_INFO("smtrat.my","Try to create Infeasible Subset");
			//generateTrivialInfeasibleSubset();
			//return;
			
			std::set<TVariable*> conflictVars = tableau.findConflictVariables(x);
			
			if(conflictVars.size() > 0){
				
				SMTRAT_LOG_INFO("smtrat.my","Added InfSubSet");
				
				FormulaSetT infSubSet;
				infSubSet.insert(x->getFormula());
				
				for(auto y : conflictVars){
					infSubSet.insert(y->getFormula());
				}
				
				mInfeasibleSubsets.push_back( std::move(infSubSet) );
			}else{
				SMTRAT_LOG_INFO("smtrat.my","No InfSubSet found");
			}
	}
}

#include "Instantiation.h"
