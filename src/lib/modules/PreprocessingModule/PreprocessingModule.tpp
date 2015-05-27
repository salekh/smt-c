/**
 * @file   PreprocessingModule.cpp
 * @author: Sebastian Junges
 *
 *
 */

#include "PreprocessingModule.h"
#include "../../../cli/ExitCodes.h"
#include <limits.h>

//#define REMOVE_LESS_EQUAL_IN_CNF_TRANSFORMATION (Not working)
//#define ADDLINEARDEDUCTIONS
//#define PREPROCESSING_DEVELOP_MODE

namespace smtrat {

	template<typename Settings>
	PreprocessingModule<Settings>::PreprocessingModule( ModuleType _type, const ModuleInput* const _formula, RuntimeSettings*, Conditionals& _conditionals, Manager* const _manager ):
        Module( _type, _formula, _conditionals, _manager ),
        newBounds(),
        varbounds(),
        visitor(),
        boolSubs(),
        arithSubs()
    {
		removeFactorsFunction = std::bind(&PreprocessingModule<Settings>::removeFactors, this, std::placeholders::_1);
		checkBoundsFunction = std::bind(&PreprocessingModule<Settings>::checkBounds, this, std::placeholders::_1);
		splitSOSFunction = std::bind(&PreprocessingModule<Settings>::splitSOS, this, std::placeholders::_1);
    }

    /**
     * Destructor:
     */
	template<typename Settings>
    PreprocessingModule<Settings>::~PreprocessingModule(){}

    /**
     * Methods:
     */

    /**
     * Adds a constraint to this module.
     *
     * @param _constraint The constraint to add to the already added constraints.
     *
     * @return true
     */
	template<typename Settings>
    bool PreprocessingModule<Settings>::addCore(ModuleInput::const_iterator _subformula) {
		if (Settings::checkBounds) {
			addBounds(_subformula->formula());
		}
        return true;
    }

    /**
     * Checks the so far received constraints for consistency.
     */
	template<typename Settings>
    Answer PreprocessingModule<Settings>::checkCore( bool _full )
    {
		if (Settings::checkBounds) {
			// If bounds are collected, check if they are conflicting.
			if (varbounds.isConflicting()) {
				mInfeasibleSubsets.push_back(varbounds.getConflict());
				return False;
			}
		}
        auto receivedFormula = firstUncheckedReceivedSubformula();
		SMTRAT_LOG_DEBUG("smtrat.preprocessing", "Bounds are " << varbounds.getEvalIntervalMap());
        while( receivedFormula != rReceivedFormula().end() )
        {
			FormulaT formula = receivedFormula->formula();
			
			if (Settings::checkBounds) {
				// If bounds are collected, check if next subformula is a bound.
				// If so, pass on unchanged.
				auto boundIt = newBounds.find(formula);
				if (boundIt != newBounds.end()) {
					addSubformulaToPassedFormula(formula, receivedFormula->formula());
					++receivedFormula;
					continue;
				}
			}
			
			tmpOrigins.clear();
			tmpOrigins.insert(receivedFormula->formula());
			SMTRAT_LOG_DEBUG("smtrat.preprocessing", "Received        " << formula);
			if (Settings::removeFactors) {
				// Remove redundant or obsolete factors of polynomials.
				formula = visitor.visit(formula, removeFactorsFunction);
			}
			SMTRAT_LOG_DEBUG("smtrat.preprocessing", "Removed factors " << formula);
			if (Settings::checkBounds) {
				// Check if bounds make constraints vanish.
				formula = visitor.visit(formula, checkBoundsFunction);
			}
			SMTRAT_LOG_DEBUG("smtrat.preprocessing", "Checked bounds  " << formula);
			if (Settings::splitSOS) {
				// Check if bounds make constraints vanish.
				formula = visitor.visit(formula, splitSOSFunction);
			}
			SMTRAT_LOG_DEBUG("smtrat.preprocessing", "Split sum-of-square decompositions  " << formula);
			if (Settings::eliminateSubstitutions) {
				// Check if bounds make constraints vanish.
				formula = elimSubstitutions(formula);
			}
			SMTRAT_LOG_DEBUG("smtrat.preprocessing", "Eliminate substitutions  " << formula);
			
			formula = formula.toCNF();
			FormulaT origins(carl::FormulaType::AND, tmpOrigins);
			
			if (formula.getType() == carl::FormulaType::AND) {
				// If formula has multiple clauses, add separately.
				for (const auto& f: formula.subformulas()) {
					addSubformulaToPassedFormula(f, origins);
				}
			} else {
				addSubformulaToPassedFormula(formula, origins);
			}
			++receivedFormula;
        }

        Answer ans = runBackends( _full );
        if (ans == False) {
            getInfeasibleSubsets();
        }
        return ans;
    }

    /**
     * Removes a everything related to a sub formula of the received formula.
     *
     * @param _subformula The sub formula of the received formula to remove.
     */
	template<typename Settings>
    void PreprocessingModule<Settings>::removeCore(ModuleInput::const_iterator _subformula) {
		if (Settings::checkBounds) {
			removeBounds(_subformula->formula());
		}
    }
	
	template<typename Settings>
	void PreprocessingModule<Settings>::updateModel() const {
        clearModel();
        if (solverState() == True) {
            getBackendsModel();
        }
		carl::Variables vars;
		rReceivedFormula().arithmeticVars(vars);
		for (const auto& it: model()) {
			if (!it.first.isVariable()) continue;
			carl::Variable v = it.first.asVariable();
			vars.erase(v);
		}
		for (carl::Variable::Arg v: vars) {
			mModel.emplace(v, vs::SqrtEx());
		}
    }
	
	template<typename Settings>
    void PreprocessingModule<Settings>::addBounds(const FormulaT& formula) {
		switch( formula.getType() )
        {
			case carl::FormulaType::CONSTRAINT:
            {
                if( varbounds.addBound(formula.constraint(), formula) )
                {
                    newBounds.insert(formula);
                }
                break;
            }
			case carl::FormulaType::AND:
            {
				for (const auto& f: formula.subformulas()) addBounds(f);
                break;
			}
			default:
                break;
		}
	}
    
	template<typename Settings>
    void PreprocessingModule<Settings>::removeBounds(const FormulaT& formula) {
		switch (formula.getType()) {
			case carl::FormulaType::CONSTRAINT:
            {
				if( varbounds.removeBound(formula.constraint(), formula) )
                {
                    newBounds.erase(formula);
                }
				break;
            }
			case carl::FormulaType::AND:
				for (const auto& f: formula.subformulas()) removeBounds(f);
				break;
			default:
                break;
		}
	}
	
	template<typename Settings>
    FormulaT PreprocessingModule<Settings>::removeFactors(const FormulaT& formula) {
		if(formula.getType() == carl::CONSTRAINT) {
			auto factors = formula.constraint().factorization();
			SMTRAT_LOG_DEBUG("smtrat.preprocessing", "Factorization of " << formula << " = " << factors);
			for (auto it = factors.begin(); it != factors.end();) {
				auto i = carl::IntervalEvaluation::evaluate(it->first, completeBounds(it->first));
				if (i.isPositive()) {
					it = factors.erase(it);
				} else if (i.isSemiPositive()) {
					it->second = 1;
					++it;
				} else if (i.isNegative()) {
					if (it->second % 2 == 0) it = factors.erase(it);
					else {
						it->second = 1;
						++it;
					}
				} else if (i.isSemiNegative()) {
					if (it->second % 2 == 0) it->second = 2;
					else it->second = 1;
					++it;
				} else if (i.isZero()) {
					return FormulaT(ZERO_POLYNOMIAL, formula.constraint().relation());
				} else ++it;
			}
			Poly p = ONE_POLYNOMIAL;
			for (const auto& it: factors) {
				p *= carl::pow(it.first, it.second);
			}
			return FormulaT(p, formula.constraint().relation());
		}
		return formula;
	}
	
	template<typename Settings>
    FormulaT PreprocessingModule<Settings>::splitSOS(const FormulaT& formula) {
		if(formula.getType() == carl::CONSTRAINT) {
            std::vector<std::pair<Rational,Poly>> sosDec;
            bool lcoeffNeg = carl::isNegative(formula.constraint().lhs().lcoeff());
            if (lcoeffNeg) {
                sosDec = (-formula.constraint().lhs()).sosDecomposition();
            } else {
                sosDec = formula.constraint().lhs().sosDecomposition();
            }
            if (sosDec.size() <= 1) {
                return formula;
            }
			SMTRAT_LOG_DEBUG("smtrat.preprocessing", "Sum-of-squares decomposition of " << formula << " = " << sosDec);
            carl::Relation rel = carl::Relation::EQ;
            carl::FormulaType boolOp = carl::FormulaType::AND;
            switch(formula.constraint().relation()) {
                case carl::Relation::EQ:
                    if (formula.constraint().lhs().hasConstantTerm())
                        return FormulaT(carl::FormulaType::FALSE);
                    break;
                case carl::Relation::NEQ:
                    if (formula.constraint().lhs().hasConstantTerm())
                        return FormulaT(carl::FormulaType::TRUE);
                    rel = carl::Relation::NEQ;
                    boolOp = carl::FormulaType::OR;
                    break;
                case carl::Relation::LEQ:
                    if (lcoeffNeg)
                        return FormulaT(carl::FormulaType::TRUE);
                    else if (formula.constraint().lhs().hasConstantTerm())
                        return FormulaT(carl::FormulaType::FALSE);
                    break;
                case carl::Relation::LESS:
                    if (lcoeffNeg) {
                        if (formula.constraint().lhs().hasConstantTerm())
                            return FormulaT(carl::FormulaType::TRUE);
                        rel = carl::Relation::NEQ;
                        boolOp = carl::FormulaType::OR;
                    }
                    else 
                        return FormulaT(carl::FormulaType::FALSE);
                    break;
                case carl::Relation::GEQ:
                    if (!lcoeffNeg)
                        return FormulaT(carl::FormulaType::TRUE);
                    else if (formula.constraint().lhs().hasConstantTerm())
                        return FormulaT(carl::FormulaType::FALSE);
                    break;
                default:
                    assert(formula.constraint().relation() == carl::Relation::GREATER);
                    if (lcoeffNeg)
                        return FormulaT(carl::FormulaType::FALSE);
                    else {
                        if (formula.constraint().lhs().hasConstantTerm())
                            return FormulaT(carl::FormulaType::TRUE);
                        rel = carl::Relation::NEQ;
                        boolOp = carl::FormulaType::OR;
                    }
            }
            FormulasT subformulas;
			for (auto it = sosDec.begin(); it != sosDec.end(); ++it) {
                subformulas.emplace(it->second, rel);
			}
			return FormulaT(boolOp, subformulas);
		}
		return formula;
	}
	
	template<typename Settings>
    FormulaT PreprocessingModule<Settings>::checkBounds(const FormulaT& formula) {
		if(formula.getType() == carl::CONSTRAINT && newBounds.find(formula) == newBounds.end())
		{
			unsigned result = formula.constraint().evaluate(completeBounds(formula.constraint()));
			if (result == 0) {
				accumulateBoundOrigins(formula.constraint());
				return FormulaT(carl::FormulaType::FALSE);
			}
			if (result == 4) {
				accumulateBoundOrigins(formula.constraint());
				return FormulaT(carl::FormulaType::TRUE);
			}
			/*if (result == 1 || result == 2) {
				if (carl::isZero(formula.constraint().constantPart())) {
					if (formula.constraint().lhs().nrTerms() <= 1) return formula;
					FormulasT monomials;
					carl::Sign sign = carl::sgn(formula.constraint().lhs().lcoeff());
					for (TermT t: formula.constraint().lhs()) {
						auto i = carl::IntervalEvaluation::evaluate(t, varbounds.getEvalIntervalMap());
						if (sign != carl::sgn(i)) return formula;
						monomials.emplace(newConstraint(Poly(t.monomial()), carl::Relation::EQ));
					}
					accumulateOrigins(formula.constraint());
					if (result == 1) {
						return FormulaT(carl::FormulaType::AND, monomials);
					} else if (result == 2) {
						return FormulaT(carl::FormulaType::NOT, FormulaT(carl::FormulaType::AND, monomials));
					}
				}
			}*/
		}
		return formula;
	}
    
    template<typename Settings>
    FormulaT PreprocessingModule<Settings>::elimSubstitutions( const FormulaT& _formula ) 
    {
//        std::cout << __func__ << ": " << _formula << std::endl;
        FormulaT result = _formula;
        switch( _formula.getType() )
        {
            case carl::FormulaType::AND:
            {
                std::vector<std::unordered_map<FormulaT, bool>::const_iterator> addedBoolSubs;
                std::vector<std::map<carl::Variable,Poly>::const_iterator> addedArithSubs;
                FormulasT sfs;
                // Process all equations first.
                for( const auto& sf : result.subformulas() )
                {
                    if( sf.getType() == carl::FormulaType::CONSTRAINT && sf.constraint().relation() == carl::Relation::EQ )
                    {
                        FormulaT tmp = elimSubstitutions( sf );
                        if( tmp.getType() == carl::FormulaType::FALSE )
                        {
                            result = tmp;
                            goto Return;
                        }
                        else if( tmp.getType() != carl::FormulaType::TRUE )
                        {
                            sfs.insert( tmp );
                            carl::Variable subVar;
                            Poly subPoly;
                            if( tmp.constraint().getSubstitution( subVar, subPoly ) )
                            {
//                                std::cout << __LINE__ << "   found substitution [" << subVar << " -> " << subPoly << "]" << std::endl;
//                                if( arithSubs.find( subVar ) != arithSubs.end() )
//                                    exit(1235);
                                assert( arithSubs.find( subVar ) == arithSubs.end() );
                                addedArithSubs.push_back( arithSubs.emplace( subVar, subPoly ).first );
                            }
                        }
                    }
                }
                // Now the other sub-formulas.
                for( const auto& sf : result.subformulas() )
                {
                    if( sf.getType() != carl::FormulaType::CONSTRAINT || sf.constraint().relation() != carl::Relation::EQ )
                    {
                        FormulaT sfSimplified = elimSubstitutions( sf );
                        if( sfSimplified.isFalse() )
                        {
                            result = sfSimplified;
                            goto Return;
                        }
                        else if( !sfSimplified.isTrue() )
                        {
                            sfs.insert( sfSimplified );
                            if( sfSimplified.getType() == carl::FormulaType::NOT )
                            {
                                assert( boolSubs.find( sfSimplified.subformula() ) == boolSubs.end() );
//                                std::cout <<  __LINE__ << "   found boolean substitution [" << sfSimplified.subformula() << " -> false]" << std::endl;
                                addedBoolSubs.push_back( boolSubs.insert( std::make_pair( sfSimplified.subformula(), false ) ).first );
//                                if( std::count( addedBoolSubs.begin(), addedBoolSubs.end(), addedBoolSubs.back() ) != 1 )
//                                {
//                                    exit(1234);
//                                }
                                assert( std::count( addedBoolSubs.begin(), addedBoolSubs.end(), addedBoolSubs.back() ) == 1 );
                            }
                            else
                            {
                                assert( boolSubs.find( sfSimplified ) == boolSubs.end() );
                                addedBoolSubs.push_back( boolSubs.insert( std::make_pair( sfSimplified, true ) ).first );
//                                std::cout <<  __LINE__ << "   found boolean substitution [" << sfSimplified << " -> true]" << std::endl;
//                                if( std::count( addedBoolSubs.begin(), addedBoolSubs.end(), addedBoolSubs.back() ) != 1 )
//                                {
//                                    exit(1234);
//                                }
                                assert( std::count( addedBoolSubs.begin(), addedBoolSubs.end(), addedBoolSubs.back() ) == 1 );
                            }
                        }
                    }
                }
                result = FormulaT( carl::FormulaType::AND, sfs );
//                std::cout << "result: " << result << std::endl;
            Return:
                while( !addedArithSubs.empty() )
                {
                    assert( std::count( addedArithSubs.begin(), addedArithSubs.end(), addedArithSubs.back() ) == 1 );
                    arithSubs.erase( addedArithSubs.back() );
                    addedArithSubs.pop_back();
                }
                while( !addedBoolSubs.empty() )
                {
                    assert( std::count( addedBoolSubs.begin(), addedBoolSubs.end(), addedBoolSubs.back() ) == 1 );
                    boolSubs.erase( addedBoolSubs.back() );
                    addedBoolSubs.pop_back();
                }
                return result;
            }
            case carl::FormulaType::ITE:
            {
                FormulaT cond = elimSubstitutions( _formula.condition() );
                if( cond.getType() == carl::FormulaType::CONSTRAINT )
                {
                    carl::Variable subVar;
                    Poly subPoly;
                    if( cond.constraint().getSubstitution( subVar, subPoly, false ) )
                    {
                        auto addedBoolSub = cond.getType() == carl::FormulaType::NOT ? boolSubs.emplace( cond.subformula(), false ) : boolSubs.emplace( cond, true );
                        assert( addedBoolSub.second );
                        auto iter = arithSubs.emplace( subVar, subPoly ).first;
                        FormulaT firstCaseTmp = elimSubstitutions( _formula.firstCase() );
                        arithSubs.erase( iter );
                        boolSubs.erase( addedBoolSub.first );
                        addedBoolSub = cond.getType() == carl::FormulaType::NOT ? boolSubs.emplace( cond.subformula(), true ) : boolSubs.emplace( cond, false );
                        assert( addedBoolSub.second );
                        FormulaT secondCaseTmp = elimSubstitutions( _formula.secondCase() );
                        boolSubs.erase( addedBoolSub.first );
                        FormulaT result( carl::FormulaType::ITE, cond, firstCaseTmp, secondCaseTmp );
//                        std::cout << "result: " << result << std::endl;
                        return result;
                    }
                    else if( cond.constraint().getSubstitution( subVar, subPoly, true ) )
                    {
                        auto addedBoolSub = cond.getType() == carl::FormulaType::NOT ? boolSubs.emplace( cond.subformula(), false ) : boolSubs.emplace( cond, true );
                        assert( addedBoolSub.second );
                        FormulaT firstCaseTmp = elimSubstitutions( _formula.firstCase() );
                        boolSubs.erase( addedBoolSub.first );
                        addedBoolSub = cond.getType() == carl::FormulaType::NOT ? boolSubs.emplace( cond.subformula(), true ) : boolSubs.emplace( cond, false );
                        assert( addedBoolSub.second );
                        auto iter = arithSubs.emplace( subVar, subPoly ).first;
                        FormulaT secondCaseTmp = elimSubstitutions( _formula.secondCase() );
                        arithSubs.erase( iter );
                        boolSubs.erase( addedBoolSub.first );
                        FormulaT result( carl::FormulaType::ITE, cond, firstCaseTmp, secondCaseTmp );
//                        std::cout << "result: " << result << std::endl;
                        return result;
                    }
                }
                auto addedBoolSub = cond.getType() == carl::FormulaType::NOT ? boolSubs.emplace( cond.subformula(), false ) : boolSubs.emplace( cond, true );
                assert( addedBoolSub.second );
                FormulaT firstCaseTmp = elimSubstitutions( _formula.firstCase() );
                boolSubs.erase( addedBoolSub.first );
                addedBoolSub = cond.getType() == carl::FormulaType::NOT ? boolSubs.emplace( cond.subformula(), true ) : boolSubs.emplace( cond, false );
                assert( addedBoolSub.second );
                FormulaT secondCaseTmp = elimSubstitutions( _formula.secondCase() );
                boolSubs.erase( addedBoolSub.first );
                result = FormulaT( carl::FormulaType::ITE, cond, firstCaseTmp, secondCaseTmp );
//                std::cout << "result: " << result << std::endl;
                return result;
            }
            case carl::FormulaType::OR:
            case carl::FormulaType::IFF:
            case carl::FormulaType::XOR: {
                FormulasT newSubformulas;
                bool changed = false;
                for (const auto& cur: _formula.subformulas()) {
                    FormulaT newCur = elimSubstitutions(cur);
                    if (newCur != cur) changed = true;
                    newSubformulas.insert(newCur);
                }
                if (changed) {
                    return FormulaT(_formula.getType(), newSubformulas);
                }
                return _formula;
            }
            case carl::FormulaType::NOT: {
                FormulaT cur = elimSubstitutions(_formula.subformula());
                if (cur != _formula.subformula()) {
                    return FormulaT(carl::FormulaType::NOT, cur);
                }
                return _formula;
            }
            case carl::FormulaType::IMPLIES: {
                FormulaT prem = elimSubstitutions(_formula.premise());
                FormulaT conc = elimSubstitutions(_formula.conclusion());
                if ((prem != _formula.premise()) || (conc != _formula.conclusion())) {
                    return FormulaT(carl::FormulaType::IMPLIES, prem, conc);
                }
                return _formula;
            }
            case carl::FormulaType::CONSTRAINT: {
                auto iter = boolSubs.find( _formula );
                if( iter != boolSubs.end() )
                {
                    return iter->second ? FormulaT( carl::FormulaType::TRUE ) : FormulaT( carl::FormulaType::FALSE );
                }
                return _formula.substitute( arithSubs );
            }
            case carl::FormulaType::BOOL:
            case carl::FormulaType::BITVECTOR:
            case carl::FormulaType::UEQ: {
                auto iter = boolSubs.find( _formula );
                if( iter != boolSubs.end() )
                {
                    return iter->second ? FormulaT( carl::FormulaType::TRUE ) : FormulaT( carl::FormulaType::FALSE );
                }
                return _formula;
            }
            case carl::FormulaType::TRUE:
            case carl::FormulaType::FALSE:
                return _formula;
            case carl::FormulaType::EXISTS:
            case carl::FormulaType::FORALL: {
                FormulaT sub = elimSubstitutions(_formula.quantifiedFormula());
                if (sub != _formula.quantifiedFormula()) {
                    return FormulaT(_formula.getType(), _formula.quantifiedVariables(), sub);
                }
                return _formula;
            }
        }
    }
}


