/*
 * **************************************************************************************[Solver.cc]
 * Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
 * Copyright (c) 2007-2010, Niklas Sorensson
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
 * associated documentation files (the "Software"), to deal in the Software without restriction,
 * including without limitation the rights to use, copy, modify, merge, publish, distribute,
 * sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or
 * substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
 * NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
 * DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
 * OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */
/**
 * @file SATModule.tpp
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 * @since 2012-01-18
 * @version 2014-10-02
 */

#include "SATModule.h"
#include <iomanip>

/*
#ifdef LOGGING
#define DEBUG_METHODS_SATMODULE
#ifdef DEBUG_METHODS_SATMODULE
#define DEBUG_SATMODULE
#endif
//#define DEBUG_SATMODULE_THEORY_PROPAGATION
//#define DEBUG_SATMODULE_DECISION_HEURISTIC
//#define DEBUG_SATMODULE_LEMMA_HANDLING
#endif
*/

using namespace Minisat;

namespace smtrat
{
    // Options:
    static const char*  _cat = "CORE";
    static DoubleOption opt_var_decay( _cat, "var-decay", "The variable activity decay factor", 0.95, DoubleRange( 0, false, 1, false ) );
    static DoubleOption opt_clause_decay( _cat, "cla-decay", "The clause activity decay factor", 0.999, DoubleRange( 0, false, 1, false ) );
    static DoubleOption opt_random_var_freq( _cat, "rnd-freq", "The frequency with which the decision heuristic tries to choose a random variable",
                                             0, DoubleRange( 0, true, 1, true ) );
    static DoubleOption opt_random_seed( _cat, "rnd-seed", "Used by the random variable selection", 91648253,
                                         DoubleRange( 0, false, HUGE_VAL, false ) );
    static IntOption    opt_ccmin_mode( _cat, "ccmin-mode", "Controls conflict clause minimization (0=none, 1=basic, 2=deep)", 2, IntRange( 0, 2 ) );
    static IntOption    opt_phase_saving( _cat, "phase-saving", "Controls the level of phase saving (0=none, 1=limited, 2=full)", 2, IntRange( 0, 2 ) );
    static BoolOption   opt_rnd_init_act( _cat, "rnd-init", "Randomize the initial activity", false );
    static BoolOption   opt_luby_restart( _cat, "luby", "Use the Luby restart sequence", true );
    static IntOption    opt_restart_first( _cat, "rfirst", "The base restart interval", 25, IntRange( 1, INT32_MAX ) );
    static DoubleOption opt_restart_inc( _cat, "rinc", "Restart interval increase factor", 3, DoubleRange( 1, false, HUGE_VAL, false ) );
    static DoubleOption opt_garbage_frac( _cat, "gc-frac", "The fraction of wasted memory allowed before a garbage collection is triggered", 0.20,
                                          DoubleRange( 0, false, HUGE_VAL, false ) );

    template<class Settings>
    SATModule<Settings>::SATModule( const ModuleInput* _formula, RuntimeSettings*, Conditionals& _foundAnswer, Manager* const _manager ):
        Module( _formula, _foundAnswer, _manager ),
        // Parameters (user settable):
        verbosity( 0 ),
        var_decay( opt_var_decay ),
        clause_decay( opt_clause_decay ),
        random_var_freq( opt_random_var_freq ),
        random_seed( opt_random_seed ),
        luby_restart( opt_luby_restart ),
        ccmin_mode( opt_ccmin_mode ),
        phase_saving( opt_phase_saving ),
        rnd_pol( false ),
        rnd_init_act( opt_rnd_init_act ),
        garbage_frac( opt_garbage_frac ),
        restart_first( opt_restart_first ),
        restart_inc( opt_restart_inc ),
        // Parameters (the rest):
        learntsize_factor( 1 ),
        learntsize_inc( 1.5 ),
        // Parameters (experimental):
        learntsize_adjust_start_confl( 100 ),
        learntsize_adjust_inc( 1.5 ),
        // Statistics: (formerly in 'SolverStats')
        solves( 0 ),
        starts( 0 ),
        decisions( 0 ),
        rnd_decisions( 0 ),
        propagations( 0 ),
        conflicts( 0 ),
        dec_vars( 0 ),
        clauses_literals( 0 ),
        learnts_literals( 0 ),
        max_literals( 0 ),
        tot_literals( 0 ),
        ok( true ),
        cla_inc( 1 ),
        var_inc( 1 ),
        watches( WatcherDeleted( ca ) ),
        qhead( 0 ),
        simpDB_assigns( -1 ),
        simpDB_props( 0 ),
        order_heap( VarOrderLt( activity ) ),
        progress_estimate( 0 ),
        remove_satisfied( Settings::remove_satisfied ),
        // Resource constraints:
        conflict_budget( -1 ),
        propagation_budget( -1 ),
        asynch_interrupt( false ),
        mChangedPassedFormula( false ),
        mComputeAllSAT( false ),
        mFullAssignmentCheckedForConsistency( false ),
        mOptimumComputed( false ),
        mBusy( false ),
        mExcludedAssignments( false ),
        mCurrentAssignmentConsistent( SAT ),
        mNumberOfFullLazyCalls( 0 ),
        mCurr_Restarts( 0 ),
        mNumberOfTheoryCalls( 0 ),
        mReceivedFormulaPurelyPropositional(true),
        mConstraintLiteralMap(),
        mBooleanVarMap(),
        mMinisatVarMap(),
        mFormulaAssumptionMap(),
        mFormulaCNFInfosMap(),
        mClauseInformation(),
        mLiteralClausesMap(),
        mNumberOfSatisfiedClauses( 0 ),
        mChangedBooleans(),
        mAllActivitiesChanged( false ),
        mChangedActivities(),
        mNewSplittingVars(),
        mPropagatedLemmas(),
        mRelevantVariables(),
        mNonTseitinShadowedOccurrences(),
        mTseitinVarShadows(),
        mTseitinVarFormulaMap(),
        mCurrentTheoryConflicts(),
        mCurrentTheoryConflictTypes(),
        mCurrentTheoryConflictEvaluations(),
        mLevelCounter(),
        mTheoryConflictIdCounter( 0 ),
        mUpperBoundOnMinimal( passedFormulaEnd() ),
        mLiteralsClausesMap(),
        mLiteralsActivOccurrences()
    {
        mCurrentTheoryConflicts.reserve(100);
        mCurrentTheoryConflictTypes.reserve(100);
        mTrueVar = newVar();
        uncheckedEnqueue( mkLit( mTrueVar, false ) );
        mBooleanConstraintMap.push( std::make_pair( nullptr, nullptr ) );
        #ifdef SMTRAT_DEVOPTION_Statistics
        stringstream s;
        s << moduleName() << "_" << id();
        mpStatistics = new SATModuleStatistics( s.str() );
        #endif
    }

    template<class Settings>
    SATModule<Settings>::~SATModule()
    {
        while( mBooleanConstraintMap.size() > 0 )
        {
            Abstraction*& abstrAToDel = mBooleanConstraintMap.last().first;
            Abstraction*& abstrBToDel = mBooleanConstraintMap.last().second;
            mBooleanConstraintMap.pop();
            if( abstrAToDel != nullptr )
            {
                assert( abstrBToDel != nullptr );
                delete abstrAToDel;
                delete abstrBToDel;
                abstrAToDel = nullptr;
                abstrBToDel = nullptr;
            }
        }
        #ifdef SMTRAT_DEVOPTION_Statistics
        delete mpStatistics;
        #endif
    }
    
    class ScopedBool
    {
        bool& watch;
        bool oldValue;
        
        public:
            
        ScopedBool( bool& watch, bool newValue ): 
            watch(watch), 
            oldValue(watch)
        {
            watch = newValue;
        }
            
        ~ScopedBool()
        {
            watch = oldValue;
        }
    };

    template<class Settings>
    bool SATModule<Settings>::addCore( ModuleInput::const_iterator _subformula )
    {
        if( _subformula->formula().isFalse() )
        {
            mModelComputed = false;
            mOptimumComputed = false;
            mInfeasibleSubsets.emplace_back();
            mInfeasibleSubsets.back().insert( _subformula->formula() );
            return false;
        }
        else if( !_subformula->formula().isTrue() )
        {
            if( !_subformula->formula().isOnlyPropositional() )
                mReceivedFormulaPurelyPropositional = false;
            mModelComputed = false;
            mOptimumComputed = false;
            //TODO Matthias: better solution?
            cancelUntil( assumptions.size() );
            adaptPassedFormula();
            if( _subformula->formula().propertyHolds( carl::PROP_IS_A_LITERAL ) )
            {
                assumptions.push( createLiteral( _subformula->formula(), _subformula->formula() ) );
                assert( mFormulaAssumptionMap.find( _subformula->formula() ) == mFormulaAssumptionMap.end() );
                mFormulaAssumptionMap.emplace( _subformula->formula(), assumptions.last() );
            }
            else
            {
                addClauses( _subformula->formula(), NORMAL_CLAUSE, 0, _subformula->formula() );
            }
            if ( isLemmaLevel(NORMAL) && decisionLevel() == 0)
            {
                if (_subformula->formula().propertyHolds(carl::PROP_IS_A_LITERAL) && _subformula->formula().propertyHolds(carl::PROP_CONTAINS_BOOLEAN))
                {
                    // Add literal from unary clause to lemmas
                    carl::Variables vars;
                    _subformula->formula().booleanVars(vars);
                    assert(vars.size() == 1);
                    // Get corresponding Minisat variable
                    BooleanVarMap::const_iterator itVar = mBooleanVarMap.find(*vars.begin());
                    assert(itVar != mBooleanVarMap.end());
                    Minisat::Var var = itVar->second;
                    // Insert new propagated lemma
                    mPropagatedLemmas[var].push_back(_subformula->formula());
                }
            }
        }
        if( !ok )
            updateInfeasibleSubset();
        return ok;
    }

    template<class Settings>
    void SATModule<Settings>::removeCore( ModuleInput::const_iterator _subformula )
    {
        if( _subformula->formula().isFalse() || _subformula->formula().isTrue() )
            return;
        cancelUntil( 0, true );  // can we do better than this?
        if( !mReceivedFormulaPurelyPropositional )
            adaptPassedFormula();
        assert( rPassedFormula().empty() );
        for( int i = 0; i < learnts.size(); ++i )
        {
            assert( learnts[i] != CRef_Undef );
            removeClause( learnts[i] );
        }
        learnts.clear();
        ok = true;
        if( _subformula->formula().propertyHolds( carl::PROP_IS_A_LITERAL ) )
        {
            auto iter = mFormulaAssumptionMap.find( _subformula->formula() );
            assert( iter != mFormulaAssumptionMap.end() );
            int i = 0;
            while( assumptions[i] != iter->second ) ++i;
            while( i < assumptions.size() - 1 )
            {
                assumptions[i] = assumptions[i+1];
                ++i;
            }
            assumptions.pop();
            mFormulaAssumptionMap.erase( iter );
            ConstraintLiteralsMap::iterator constraintLiteralPair = mConstraintLiteralMap.find( _subformula->formula() );
            if( constraintLiteralPair != mConstraintLiteralMap.end() )
                removeLiteralOrigin( constraintLiteralPair->second.front(), _subformula->formula() );
        }
        else
        {
            auto cnfInfoIter = mFormulaCNFInfosMap.find( _subformula->formula().removeNegations() );
            assert( cnfInfoIter != mFormulaCNFInfosMap.end() );
            updateCNFInfoCounter( cnfInfoIter, _subformula->formula(), false );
            if( cnfInfoIter->second.mClauses.empty() )
            {
                mFormulaCNFInfosMap.erase( cnfInfoIter );
            }
            std::vector<FormulaT> constraints;
            _subformula->formula().getConstraints( constraints );
            for( const FormulaT& constraint : constraints )
            {
                ConstraintLiteralsMap::iterator constraintLiteralPair = mConstraintLiteralMap.find( constraint );
                if( constraintLiteralPair != mConstraintLiteralMap.end() )
                    removeLiteralOrigin( constraintLiteralPair->second.front(), _subformula->formula() );
                constraintLiteralPair = mConstraintLiteralMap.find( constraint.negated() );
                if( constraintLiteralPair != mConstraintLiteralMap.end() )
                    removeLiteralOrigin( constraintLiteralPair->second.front(), _subformula->formula() );
            }
        }
    }
    
    template<class Settings>
    void SATModule<Settings>::removeLiteralOrigin( Lit _litToRemove, const FormulaT& _origin )
    {
        int abstractionVar = var(_litToRemove);
        auto& abstrPair = mBooleanConstraintMap[abstractionVar];
        assert( abstrPair.first != nullptr && abstrPair.second != nullptr );
        Abstraction& abstr = sign(_litToRemove) ? *abstrPair.second : *abstrPair.first;
        if( abstr.origins != nullptr )
        {
            auto& origs = *abstr.origins;
            auto iter = origs.begin();
            while( iter != origs.end() )
            {
                if( *iter == _origin || (iter->getType() == carl::FormulaType::AND && iter->contains( _origin )) )
                {
                    if (iter != --origs.end())
                    {
                        *iter = origs.back();
                        origs.pop_back();
                    }
                    else
                    {
                        origs.pop_back();
                        break;
                    }
                }
                else
                {
                    ++iter;
                }
            }
            if( origs.empty() )
            {
                abstr.origins = nullptr;
            }
        }
    }

    template<class Settings>
    double SATModule<Settings>::luby( double y, int x )
    {
        // Find the finite subsequence that contains index 'x', and the
        // size of that subsequence:
        int size, seq;
        for( size = 1, seq = 0; size < x + 1; seq++, size = 2 * size + 1 );

        while( size - 1 != x )
        {
            size = (size - 1) >> 1;
            seq--;
            x = x % size;
        }

        return pow( y, seq );
    }
    
    template<class Settings>
    Answer SATModule<Settings>::checkCore()
    {
//        for( const auto& f : rReceivedFormula() )
//            std::cout << "   " << f.formula().toString() << std::endl;
//        std::cout << ((FormulaT) rReceivedFormula()).toString( false, 1, "", true, false, true, true ) << std::endl;
        #ifdef SMTRAT_DEVOPTION_Statistics
        mpStatistics->rNrTotalVariablesBefore() = (size_t) nVars();
        mpStatistics->rNrClauses() = (size_t) nClauses();
        #endif
        ScopedBool scopedBool( mBusy, true );
        budgetOff();
//        assumptions.clear();
        Module::init();
        processLemmas();

        ++solves;
        // compared to original minisat we add the number of clauses with size 1 (nAssigns()) and learnts, we got after init()
        max_learnts = (nAssigns() + nClauses() + nLearnts() ) * learntsize_factor;
        learntsize_adjust_confl = learntsize_adjust_start_confl;
        learntsize_adjust_cnt = (int)learntsize_adjust_confl;

        if( !ok )
        {
            assert( !mInfeasibleSubsets.empty() );
            #ifdef SMTRAT_DEVOPTION_Statistics
            collectStats();
            #endif
            mBusy = false;
            return UNSAT;
        }
        mReceivedFormulaPurelyPropositional = rReceivedFormula().isOnlyPropositional();
        if( mReceivedFormulaPurelyPropositional )
        {
            mAllActivitiesChanged = false;
            mChangedBooleans.clear();
            mChangedActivities.clear();
        }
        else if( Settings::initiate_activities )
        {
            double highestActivity = 0;
            for( int pos = 0; pos < activity.size(); ++pos )
            {
                double& act = activity[pos];
                act = 1;
                if( Settings::check_active_literal_occurrences )
                {
                    const auto& litActOccs = mLiteralsActivOccurrences[(size_t)pos];
                    act = (double)litActOccs.first + (double)litActOccs.second;
                }
                if( mBooleanConstraintMap[pos].first != nullptr )
                {
                    act /= (double)mBooleanConstraintMap[pos].first->reabstraction.complexity();
                }
                else
                {
                    auto tvfIter = mTseitinVarFormulaMap.find( pos );
                    if( tvfIter != mTseitinVarFormulaMap.end() )
                        act /= (double)tvfIter->second.complexity();
                }
                if( act > highestActivity )
                    highestActivity = act;
            }
            if( highestActivity > 1 )
            {
                for( int pos = 0; pos < activity.size(); ++pos )
                {
                    activity[pos] /= highestActivity;
                }
            }
            rebuildOrderHeap();
        }
        lbool result = l_Undef;
        mUpperBoundOnMinimal = passedFormulaEnd();
        while( true )
        {
            if( Settings::use_restarts )
            {
                mCurr_Restarts = 0;
                int current_restarts = -1;
                while( current_restarts < mCurr_Restarts )
                {
                    current_restarts = mCurr_Restarts;
                    double rest_base = luby_restart ? luby( restart_inc, mCurr_Restarts ) : pow( restart_inc, mCurr_Restarts );
                    result = search( (int)rest_base * restart_first );
                    // if( !withinBudget() ) break;
                }
            }
            else
                result = search();
            
            if (isLemmaLevel(LemmaLevel::ADVANCED))
            {
                assert(result == l_True);
                computeAdvancedLemmas();
            }
            if( !Settings::stop_search_after_first_unknown )
            {
                unknown_excludes.clear();
                mExcludedAssignments = false;
            }
            if( !mMinimizingCheck )
                break;
            std::vector<CRef> excludedAssignments;
            if( result == l_Undef )
                break;
            else if( result == l_False )
            {
                if( mUpperBoundOnMinimal != rPassedFormula().end() )
                {
                    cleanUpAfterOptimizing( excludedAssignments );
                    result = l_True;
                }
                break;
            }
            else
            {
                assert( result == l_True );
                runBackends( true, mFullCheck, true );
                updateModel();
                auto modelIter = mModel.find( objective() );
                assert( modelIter != mModel.end() );
                const ModelValue& mv = modelIter->second;
                if( mv.isMinusInfinity() )
                {
                    cleanUpAfterOptimizing( excludedAssignments );
                    break;
                }
                assert( mv.isRational() ); // @todo: how do we handle the other model value types?
                // Add a new upper bound on the yet computed minimum
                removeUpperBoundOnMinimal();
                FormulaT newUpperBoundOnMinimal( objectiveFunction() - mv.asRational(), carl::Relation::LESS );
                addConstraintToInform_( newUpperBoundOnMinimal );
                mUpperBoundOnMinimal = addSubformulaToPassedFormula( newUpperBoundOnMinimal, newUpperBoundOnMinimal ).first;
                // Exclude the last theory call with a clause.
                vec<Lit> excludeClause;
                for( int k = 0; k < mBooleanConstraintMap.size(); ++k )
                {
                    if( assigns[k] != l_Undef )
                    {
                        if( mBooleanConstraintMap[k].first != nullptr )
                        {
                            assert( mBooleanConstraintMap[k].second != nullptr );
                            const Abstraction& abstr = assigns[k] == l_False ? *mBooleanConstraintMap[k].second : *mBooleanConstraintMap[k].first;
                            if( !abstr.reabstraction.isTrue() && abstr.consistencyRelevant && (abstr.reabstraction.getType() == carl::FormulaType::UEQ || abstr.reabstraction.getType() == carl::FormulaType::BITVECTOR || abstr.reabstraction.constraint().isConsistent() != 1))
                            {
                                excludeClause.push( mkLit( k, assigns[k] != l_False ) ); 
                            }
                        }
                    }
                }
                addClause( excludeClause, PERMANENT_CLAUSE );
                CRef confl = storeLemmas();
                if( confl != CRef_Undef )
                    excludedAssignments.push_back( confl );
                if( !ok || decisionLevel() <= assumptions.size() )
                {
                    cleanUpAfterOptimizing( excludedAssignments );
                    break;
                }
                if( confl != CRef_Undef )
                    handleConflict( confl );
            }
        }
        
        #ifdef SMTRAT_DEVOPTION_Statistics
        collectStats();
        #endif
        if( result == l_True )
        {
            return SAT;
        }
        else if( result == l_False )
        {
			SMTRAT_LOG_DEBUG("smtrat.sat", "ok = false");
            ok = false;
            updateInfeasibleSubset();
            return UNSAT;
        }
        return UNKNOWN;
    }
    
    template<class Settings>
    Minisat::lbool SATModule<Settings>::checkFormula()
    {
        if( Settings::use_restarts )
        {
            mCurr_Restarts = 0;
            int current_restarts = -1;
            lbool result = l_Undef;
            while( current_restarts < mCurr_Restarts )
            {
                current_restarts = mCurr_Restarts;
                double rest_base = luby_restart ? luby( restart_inc, mCurr_Restarts ) : pow( restart_inc, mCurr_Restarts );
                result = search( (int)rest_base * restart_first );
                // if( !withinBudget() ) break;
            }
            return result;
        }
        else
        {
            return search();
        }
    }

    template<class Settings>
    void SATModule<Settings>::computeAdvancedLemmas()
    {
#ifdef DEBUG_SATMODULE
        printCurrentAssignment();
#endif
        SMTRAT_LOG_TRACE("smtrat.sat", "Find all dependent variables");
        clearLemmas();
        int assumptionSizeStart = assumptions.size();
        // Initialize set of all variables which are not tested yet for positive assignment
        std::set<Minisat::Var> testVarsPositive;
        Minisat::Var testCandidate;
        if (getInformationRelevantFormulas().empty())
        {
            // If non are selected, all variables are relevant
            for (BooleanVarMap::const_iterator iterVar = mBooleanVarMap.begin(); iterVar != mBooleanVarMap.end(); ++iterVar)
            {
                testVarsPositive.insert(iterVar->second);
            }
        }
        else
        {
            for (std::set<FormulaT>::const_iterator iterVar = getInformationRelevantFormulas().begin(); iterVar != getInformationRelevantFormulas().end(); ++iterVar)
            {
                testVarsPositive.insert(mBooleanVarMap.at(iterVar->boolean()));
            }
        }

        lbool result = l_Undef;
        while (!testVarsPositive.empty())
        {
            for (int pos = 0; pos < assigns.size(); ++pos)
            {
                if (assigns[pos] == l_True)
                {
                    testVarsPositive.erase(pos);
                }
            }

            // Reset the state until level 0
            cancelUntil(0, true);
            mPropagatedLemmas.clear();

            if (testVarsPositive.empty())
            {
                break;
            }

            // Set new positive assignment
            // TODO matthias: ignore other variables as "Oxxxx"
            testCandidate = *testVarsPositive.begin();
            SMTRAT_LOG_DEBUG("smtrat.sat", "Test candidate: " << mMinisatVarMap.find(testCandidate)->second);
            Lit nextLit = mkLit(testCandidate, false);
            assert(assumptions.size() <= assumptionSizeStart + 1);
            assumptions.shrink(assumptions.size() - assumptionSizeStart);
            assumptions.push(nextLit);

            // Check again
            result = checkFormula();
            if (result == l_False)
            {
                auto mvIter = mMinisatVarMap.find((int)testCandidate);
                assert( mvIter != mMinisatVarMap.end() );
                SMTRAT_LOG_DEBUG("smtrat.sat", "Unsat with variable: " << mvIter->second);
                testVarsPositive.erase(testCandidate);
                //Construct lemma via infeasible subset
                updateInfeasibleSubset();
                FormulaT infeasibleSubset = FormulaT(carl::FormulaType::AND, infeasibleSubsets()[0]);
                FormulaT lemma = FormulaT(carl::FormulaType::IMPLIES, infeasibleSubset, mvIter->second.negated());
                SMTRAT_LOG_DEBUG("smtrat.sat", "Add propagated lemma: " << lemma);
                addLemma(lemma);
            }
            else if (result == l_True)
            {
                SMTRAT_LOG_DEBUG("smtrat.sat", "Sat with variable: " << mMinisatVarMap.find(testCandidate)->second);
#ifdef DEBUG_SATMODULE
                printCurrentAssignment();
#endif
            }
            else
            {
                SMTRAT_LOG_TRACE("smtrat.sat", "UNKNOWN with variable: " << mMinisatVarMap.find(testCandidate)->second);
            }
        }
        //Clear
        assumptions.shrink(assumptions.size() - assumptionSizeStart);
    }

    template<class Settings>
    void SATModule<Settings>::updateModel() const
    {
        if( !mModelComputed && !mOptimumComputed )
        {
            clearModel();
            if( solverState() != UNSAT || mMinimizingCheck )
            {
                for( BooleanVarMap::const_iterator bVar = mBooleanVarMap.begin(); bVar != mBooleanVarMap.end(); ++bVar )
                {
                    ModelValue assignment = assigns[bVar->second] == l_True;
                    mModel.insert(std::make_pair(bVar->first, assignment));
                }
                Module::getBackendsModel();
                if( Settings::check_if_all_clauses_are_satisfied && trail.size() < assigns.size() )
                {
                    getDefaultModel( mModel, (FormulaT)rReceivedFormula(), false );
                }
            }
        }
    }

    template<class Settings>
    void SATModule<Settings>::updateModel( Model& model, bool only_relevant_variables ) const
    {
        model.clear();
        if( solverState() == SAT )
        {
            if ( only_relevant_variables )
            {
                // Set assignment for all relevant variables (might be partial assignment)
                for ( size_t i = 0; i < mRelevantVariables.size(); ++i )
                {
                    int index = mRelevantVariables[ i ];
                    ModelValue assignment = assigns[ index ] == l_True;
                    auto mvIter = mMinisatVarMap.find(index);
                    assert( mvIter != mMinisatVarMap.end() );
                    carl::Variable var = mvIter->second.boolean();
                    model.insert( std::make_pair( var, assignment ) );
                }
            }
            else
            {
                // Set assignment for all defined variables (might be partial assignment)
                for (BooleanVarMap::const_iterator bVar = mBooleanVarMap.begin(); bVar != mBooleanVarMap.end(); ++bVar)
                {
                    ModelValue assignment = assigns[bVar->second] == l_True;
                    model.insert(std::make_pair(bVar->first, assignment));
                }
            }
            Module::getBackendsModel();
            if (Settings::check_if_all_clauses_are_satisfied && trail.size() < assigns.size())
            {
                getDefaultModel(model, (FormulaT)rReceivedFormula(), false);
            }
        }
    }

    template<class Settings>
    void SATModule<Settings>::updateAllModels()
    {
        SMTRAT_LOG_TRACE("smtrat.sat", "Update all models");
        mComputeAllSAT = true;
        clearModels();
        int sizeLearntsStart = learnts.size();
        if( solverState() == SAT )
        {
            // Compute all satisfying assignments
            SMTRAT_LOG_TRACE("smtrat.sat", "Compute more assignments");

            // Construct list of all relevant variables
            mRelevantVariables.clear();
            if (getInformationRelevantFormulas().empty())
            {
                // If non are selected, all variables are relevant
                for ( BooleanVarMap::const_iterator iterVar = mBooleanVarMap.begin(); iterVar != mBooleanVarMap.end(); ++ iterVar)
                {
                    mRelevantVariables.push_back( iterVar->second );
                }
            }
            else
            {
                for ( std::set<FormulaT>::const_iterator iterVar = getInformationRelevantFormulas().begin(); iterVar != getInformationRelevantFormulas().end(); ++iterVar )
                {
                    mRelevantVariables.push_back( mBooleanVarMap.at( iterVar->boolean() ) );
                }
            }
            assert( mRelevantVariables.size() > 0);
            #ifdef DEBUG_SATMODULE
            std::cout << "Relevant variables: ";
            for ( std::size_t i = 0; i < mRelevantVariables.size(); ++i )
            {
                auto mvIter = mMinisatVarMap.find(mRelevantVariables[ i ]);
                assert( mvIter != mMinisatVarMap.end() );
                std::cout << mRelevantVariables[ i ] << " (" << mvIter->second << "), ";
            }
            std::cout << std::endl;
            #endif

            lbool result = l_False;
            Model model;
            do
            {
                // Compute assignment
                #ifdef DEBUG_SATMODULE
                printCurrentAssignment();
                #endif
                updateModel( model, true );
                mAllModels.push_back( model );
                SMTRAT_LOG_TRACE("smtrat.sat", "Model: " << model);
                // Exclude assignment
                vec<Lit> excludeClause;
                int index;
                for ( size_t i = 0; i < mRelevantVariables.size(); ++i )
                {
                    index = mRelevantVariables[ i ];
                    // Add negated literal
                    Lit lit = mkLit( index, assigns[ index ] == l_True);
                    excludeClause.push( lit );
                }
                #ifdef DEBUG_SATMODULE
                std::cout << "Added exclude: " << std::endl;
                printClause( excludeClause );
                #endif
                CRef clause;
                if( addClause( excludeClause, PERMANENT_CLAUSE ) )
                    clause = learnts.last();
                else if( excludeClause.size() == 1)
                    break; // already unsat
                else
                    assert( false );
                if( !ok || decisionLevel() <= assumptions.size() )
                {
                    break;
                }
                handleConflict( clause );

                // Check again
                result = checkFormula();
            } while( result == l_True );
            SMTRAT_LOG_TRACE("smtrat.sat", ( result == l_False ? "UnSAT" : "Undef" ));
        }
        // Remove clauses for excluded assignments
        clearLearnts( sizeLearntsStart );
        mComputeAllSAT = false;
        cancelUntil(0, true);
    }
    
    template<class Settings>
    void SATModule<Settings>::updateInfeasibleSubset()
    {
        assert( isLemmaLevel(LemmaLevel::ADVANCED) || !ok );
        mInfeasibleSubsets.clear();
        // Set the infeasible subset to the set of all clauses.
        FormulaSetT infeasibleSubset;
//        if( mpReceivedFormula->isConstraintConjunction() )
//        {
//            getInfeasibleSubsets();
//        }
//        else
//        {
            // Just add all sub formulas.
            // TODO: compute a better infeasible subset
            for( auto subformula = rReceivedFormula().begin(); subformula != rReceivedFormula().end(); ++subformula )
            {
                infeasibleSubset.insert( subformula->formula() );
            }
//        }
        mInfeasibleSubsets.push_back( std::move(infeasibleSubset) );
    }
    
    template<class Settings>
    void SATModule<Settings>::cleanUpAfterOptimizing( const std::vector<CRef>& _excludedAssignments )
    {
        mModelComputed = true; // fix the last found model
        mOptimumComputed = true;
        removeUpperBoundOnMinimal();
        mUpperBoundOnMinimal = passedFormulaEnd();
        // Remove the added clauses for the exclusion of Boolean assignments.
        for( CRef cl : _excludedAssignments )
        {
            removeClause( cl );
        }
    }
    
    template<class Settings>
    void SATModule<Settings>::removeUpperBoundOnMinimal()
    {
        if( mUpperBoundOnMinimal != passedFormulaEnd() )
        {
            FormulaT bound = mUpperBoundOnMinimal->formula();
            eraseSubformulaFromPassedFormula( mUpperBoundOnMinimal, true );
        }
    }
    
    template<class Settings>
    void SATModule<Settings>::addBooleanAssignments( EvalRationalMap& _rationalAssignment ) const
    {
        for( BooleanVarMap::const_iterator bVar = mBooleanVarMap.begin(); bVar != mBooleanVarMap.end(); ++bVar )
        {
            if( assigns[bVar->second] == l_True )
            {
                assert( _rationalAssignment.find( bVar->first ) == _rationalAssignment.end() );
                _rationalAssignment.insert( std::pair< const carl::Variable, Rational >( bVar->first, ONE_RATIONAL ) );
            }
            else if( assigns[bVar->second] == l_False )
            {
                assert( _rationalAssignment.find( bVar->first ) == _rationalAssignment.end() );
                _rationalAssignment.insert( std::pair< const carl::Variable, Rational >( bVar->first, ZERO_RATIONAL ) );
            }
        }
    }
    
    template<class Settings>
    void SATModule<Settings>::updateCNFInfoCounter( typename FormulaCNFInfosMap::iterator _iter, const FormulaT& _origin, bool _increment )
    {
        assert( _iter != mFormulaCNFInfosMap.end() );
        if( _increment )
            ++_iter->second.mCounter;
        else
            --_iter->second.mCounter;
        for( std::size_t pos = 0; pos < _iter->second.mClauses.size(); )
        {
            Minisat::CRef cr = _iter->second.mClauses[pos];
            assert( cr != CRef_Undef );
            auto ciIter = mClauseInformation.find( cr );
            assert( ciIter != mClauseInformation.end() );
            if( _increment )
            {
                ciIter->second.addOrigin( _origin );
                ++pos;
            }
            else
            {
                ciIter->second.removeOrigin( _origin );
                // if the counter becomes zero, remove the clause
                if( _iter->second.mCounter == 0 )
                {
                    // remove this clause and each information we stored for it
                    assert( ciIter->second.mOrigins.size() == 0 );
                    vec<CRef>& cls = ciIter->second.mStoredInSatisfied ? satisfiedClauses : clauses;
                    if( ciIter->second.mPosition < cls.size() - 1 )
                    {
                        cls[ciIter->second.mPosition] = cls.last();
                        auto ciIterB = mClauseInformation.find( cls[ciIter->second.mPosition] );
                        assert( ciIterB != mClauseInformation.end() );
                        ciIterB->second.mPosition = ciIter->second.mPosition;
                        cls.pop();
                    }
                    else
                    {
                        cls.pop();
                    }
                    mClauseInformation.erase( ciIter );
                    if( Settings::check_if_all_clauses_are_satisfied )
                    {
                        const Clause& c = ca[cr];
                        for( int i = 0; i < c.size(); ++i )
                            mLiteralClausesMap[Minisat::toInt(c[i])].erase( cr );
                    }
                    removeClause( cr );
                    if( pos < _iter->second.mClauses.size() - 1 )
                        _iter->second.mClauses[pos] = _iter->second.mClauses.back();
                    _iter->second.mClauses.pop_back();
                }
                else
                    ++pos;
            }
        }
        // Invoke this procedure recursively on all sub-formulas, which again contain sub-formulas
        if( _iter->first.isNary() )
        {
            for( const FormulaT& formula : _iter->first.subformulas() )
            {
                if( formula.isNary() )
                {
                    auto cnfInfoIter = mFormulaCNFInfosMap.find( formula.removeNegations() );
                    if( cnfInfoIter != mFormulaCNFInfosMap.end() )
                    {
                        updateCNFInfoCounter( cnfInfoIter, _origin, _increment );
                        if( !_increment && cnfInfoIter->second.mClauses.empty() )
                        {
                            mFormulaCNFInfosMap.erase( cnfInfoIter );
                        }
                    }
                }
            }
        }
    }
    
    template<class Settings>
    Lit SATModule<Settings>::addClauses( const FormulaT& _formula, unsigned _type, unsigned _depth, const FormulaT& _original )
    {
        assert( _type < 4 );
        bool everythingDecisionRelevant = !Settings::formula_guided_decision_heuristic;
        unsigned nextDepth = _depth+1;
        switch( _formula.getType() )
        {
            case carl::FormulaType::TRUE:
            case carl::FormulaType::FALSE:
                assert( false );
                break;
            case carl::FormulaType::BOOL:
            case carl::FormulaType::UEQ:
            case carl::FormulaType::CONSTRAINT:
			case carl::FormulaType::VARCOMPARE:
            case carl::FormulaType::BITVECTOR:
                return createLiteral( _formula, _original, everythingDecisionRelevant || _depth <= 1 );
            case carl::FormulaType::NOT:
            {
				SMTRAT_LOG_DEBUG("smtrat.sat", "Adding a negation: " << _formula);
                Lit l = lit_Undef; 
                if( _formula.isLiteral() )
                {
                    l = createLiteral( _formula, _original, everythingDecisionRelevant || _depth <= 1 );
					SMTRAT_LOG_DEBUG("smtrat.sat", "It is a literal: " << l);
                }
                else {
                    l = neg( addClauses( _formula.subformula(), _type, nextDepth, _original ) );
					SMTRAT_LOG_DEBUG("smtrat.sat", "It is not a literal, but now: " << l);
				}
                if( _depth == 0 )
                {
                    assumptions.push( l );
                    assert( mFormulaAssumptionMap.find( _formula ) == mFormulaAssumptionMap.end() );
                    mFormulaAssumptionMap.emplace( _formula, assumptions.last() );
                    return lit_Undef;
                }
                return l;
            }
            default:
            {
                auto cnfInfoIter = mFormulaCNFInfosMap.end();
                if( _type == NORMAL_CLAUSE )
                {
                    cnfInfoIter = mFormulaCNFInfosMap.find( _formula );
                    if( cnfInfoIter != mFormulaCNFInfosMap.end() )
                    {
                        updateCNFInfoCounter( cnfInfoIter, _original, true );
                        return cnfInfoIter->second.mLiteral;
                    }
                    cnfInfoIter = mFormulaCNFInfosMap.emplace( _formula, CNFInfos() ).first;
                }
                vec<Lit> lits;
                FormulaT tsVar = carl::FormulaPool<Poly>::getInstance().createTseitinVar( _formula );
                Lit tsLit = createLiteral( tsVar, _original, everythingDecisionRelevant || _depth <= 1 );
                if( _type == NORMAL_CLAUSE )
                    cnfInfoIter->second.mLiteral = tsLit;
                switch( _formula.getType() )
                {
                case carl::FormulaType::ITE:
                {
                    Lit condLit = addClauses( _formula.condition(), _type, nextDepth, _original );
                    Lit negCondLit = _formula.condition().isLiteral() ? addClauses( _formula.condition().negated(), _type, nextDepth, _original ) : neg( condLit );
                    Lit thenLit = addClauses( _formula.firstCase(), _type, nextDepth, _original );
                    Lit elseLit = addClauses( _formula.secondCase(), _type, nextDepth, _original );
                    if( _depth == 0 )
                    {
                        // (or -cond then)
                        lits.push( negCondLit ); lits.push( thenLit ); addClause_( lits, _type, _original, cnfInfoIter );
                        // (or cond else)
                        lits.clear(); lits.push( condLit ); lits.push( elseLit ); addClause_( lits, _type, _original, cnfInfoIter );
                        return lit_Undef;
                    }
                    Lit negThenLit = _formula.firstCase().isLiteral() ? addClauses( _formula.firstCase().negated(), _type, nextDepth, _original ) : neg( thenLit );
                    Lit negElseLit = _formula.secondCase().isLiteral() ? addClauses( _formula.secondCase().negated(), _type, nextDepth, _original ) : neg( elseLit );
                    if( !mReceivedFormulaPurelyPropositional && Settings::initiate_activities )
                    {
                        mTseitinVarFormulaMap.emplace( (int)var(tsLit), _formula );
                    }
                    if( !mReceivedFormulaPurelyPropositional && Settings::formula_guided_decision_heuristic )
                    {
                        mTseitinVarShadows.emplace( (signed)var(tsLit), std::vector<signed>{ (signed)var(condLit), (signed)var(thenLit), (signed)var(elseLit)} ); 
                    }
                    // (or ts -cond -then)
                    lits.push( tsLit ); lits.push( negCondLit ); lits.push( negThenLit ); addClause_( lits, _type, _original, cnfInfoIter );
                    // (or ts cond -else)
                    lits.clear(); lits.push( tsLit ); lits.push( condLit ); lits.push( negElseLit ); addClause_( lits, _type, _original, cnfInfoIter );
                    // (or -ts -cond then)
                    lits.clear(); lits.push( neg( tsLit ) ); lits.push( negCondLit ); lits.push( thenLit ); addClause_( lits, _type, _original, cnfInfoIter );
                    // (or -ts cond else)
                    lits.clear(); lits.push( neg( tsLit ) ); lits.push( condLit ); lits.push( elseLit ); addClause_( lits, _type, _original, cnfInfoIter );
                    
                    return tsLit;
                }
                case carl::FormulaType::IMPLIES:
                {
                    Lit premLit = addClauses( _formula.premise(), _type, nextDepth, _original );
                    Lit negPremLit = _formula.premise().isLiteral() ? addClauses( _formula.premise().negated(), _type, nextDepth, _original ) : neg( premLit );
                    Lit conLit = addClauses( _formula.conclusion(), _type, nextDepth, _original );
                    if( _depth == 0 )
                    {
                        // (or -premise conclusion)
                        lits.push( neg( premLit ) ); lits.push( conLit ); addClause_( lits, _type, _original, cnfInfoIter );
                        return lit_Undef;
                    }
                    Lit negConLit = _formula.conclusion().isLiteral() ? addClauses( _formula.conclusion().negated(), _type, nextDepth, _original ) : neg( conLit );
                    if( !mReceivedFormulaPurelyPropositional && Settings::initiate_activities )
                    {
                        mTseitinVarFormulaMap.emplace( (int)var(tsLit), _formula );
                    }
                    if( !mReceivedFormulaPurelyPropositional && Settings::formula_guided_decision_heuristic )
                    {
                        mTseitinVarShadows.emplace( (signed)var(tsLit), std::vector<signed>{ (signed)var(premLit), (signed)var(conLit)} ); 
                    }
                    // (or -ts -prem con)
                    lits.push( neg( tsLit ) ); lits.push( negPremLit ); lits.push( conLit ); addClause_( lits, _type, _original, cnfInfoIter );
                    // (or ts prem)
                    lits.clear(); lits.push( tsLit ); lits.push( premLit ); addClause_( lits, _type, _original, cnfInfoIter );
                    // (or ts -con)
                    lits.clear(); lits.push( tsLit ); lits.push( negConLit ); addClause_( lits, _type, _original, cnfInfoIter );
                    return tsLit;
                }
                case carl::FormulaType::OR:
                {
                    for( const auto& sf : _formula.subformulas() )
                        lits.push( addClauses( sf, _type, nextDepth, _original ) );
                    if( _depth == 0 )
                    {
                        // (or a1 .. an)
                        addClause_( lits, _type, _original, cnfInfoIter );
                        return lit_Undef;
                    }
                    if( !mReceivedFormulaPurelyPropositional && Settings::initiate_activities )
                    {
                        mTseitinVarFormulaMap.emplace( (int)var(tsLit), _formula );
                    }
                    if( !mReceivedFormulaPurelyPropositional && Settings::formula_guided_decision_heuristic )
                    {
                        std::vector<signed> vars;
                        for( int pos = 0; pos < lits.size(); ++pos )
                            vars.push_back( (signed)var(lits[pos]) );
                        mTseitinVarShadows.emplace( (signed)var(tsLit), std::move(vars) ); 
                    }
                    // (or -ts a1 .. an)
                    lits.push( neg( tsLit ) );
                    addClause_( lits, _type, _original, cnfInfoIter );
                    // (or ts -a1) .. (or ts -an)
                    vec<Lit> litsTmp;
                    litsTmp.push( tsLit );
                    int i = 0;
                    for( const auto& sf : _formula.subformulas() )
                    {
                        assert( i < lits.size() );
                        litsTmp.push( sf.isLiteral() ? addClauses( sf.negated(), _type, nextDepth, _original ) : neg( lits[i] ) );
                        addClause_( litsTmp, _type, _original, cnfInfoIter );
                        litsTmp.pop();
                        ++i;
                    }
                    return tsLit;
                }
                case carl::FormulaType::AND:
                {
                    assert( _depth != 0 ); // because, this should be split in the module input
                    if( !mReceivedFormulaPurelyPropositional && Settings::initiate_activities )
                    {
                        mTseitinVarFormulaMap.emplace( (int)var(tsLit), _formula );
                    }
                    // (or -ts a1) .. (or -ts an)
                    // (or ts -a1 .. -an)
                    vec<Lit> litsTmp;
                    litsTmp.push( neg( tsLit ) );
                    for( const auto& sf : _formula.subformulas() )
                    {
                        Lit l = addClauses( sf, _type, nextDepth, _original );
                        assert( l != lit_Undef );
                        litsTmp.push( l );
                        addClause_( litsTmp, _type, _original, cnfInfoIter );
                        litsTmp.pop();
                        Lit negL = sf.isLiteral() ? addClauses( sf.negated(), _type, nextDepth, _original ) : neg( l );
                        lits.push( negL );
                    }
                    if( !mReceivedFormulaPurelyPropositional && Settings::formula_guided_decision_heuristic )
                    {
                        std::vector<signed> vars;
                        for( int pos = 0; pos < lits.size(); ++pos )
                            vars.push_back( (signed)var(lits[pos]) );
                        mTseitinVarShadows.emplace( (signed)var(tsLit), std::move(vars) ); 
                    }
                    lits.push( tsLit );
                    addClause_( lits, _type, _original, cnfInfoIter );
                    if( _type == NORMAL_CLAUSE )
                        cnfInfoIter->second.mLiteral = tsLit;
                    return tsLit;
                }
                case carl::FormulaType::IFF: 
                {
                    vec<Lit> tmp;
                    if( _depth == 0 )
                    {
                        auto sfIter = _formula.subformulas().begin();
                        Lit l = addClauses( *sfIter, _type, nextDepth, _original );
                        Lit negL = sfIter->isLiteral() ? addClauses( sfIter->negated(), _type, nextDepth, _original ) : neg( l );
                        ++sfIter;
                        for( ; sfIter != _formula.subformulas().end(); ++sfIter )
                        {
                            Lit k = addClauses( *sfIter, _type, nextDepth, _original );
                            Lit negK = sfIter->isLiteral() ? addClauses( sfIter->negated(), _type, nextDepth, _original ) : neg( k );
                            // (or -l k)
                            tmp.clear(); tmp.push( negL ); tmp.push( k ); addClause_( tmp, _type, _original, cnfInfoIter );
                            // (or l -k)
                            tmp.clear(); tmp.push( l ); tmp.push( negK ); addClause_( tmp, _type, _original, cnfInfoIter );
                            l = k;
                            negL = negK;
                        }
                        return lit_Undef;
                    }
                    for( const auto& sf : _formula.subformulas() )
                    {
                        Lit l = addClauses( sf, _type, nextDepth, _original );
                        Lit negL = sf.isLiteral() ? addClauses( sf.negated(), _type, nextDepth, _original ) : neg( l );
                        lits.push( l );
                        tmp.push( negL );
                    }
                    if( !mReceivedFormulaPurelyPropositional && Settings::initiate_activities )
                    {
                        mTseitinVarFormulaMap.emplace( (int)var(tsLit), _formula );
                    }
                    if( !mReceivedFormulaPurelyPropositional && Settings::formula_guided_decision_heuristic )
                    {
                        std::vector<signed> vars;
                        for( int pos = 0; pos < lits.size(); ++pos )
                            vars.push_back( (signed)var(lits[pos]) );
                        mTseitinVarShadows.emplace( (signed)var(tsLit), std::move(vars) ); 
                    }
                    // (or a1 .. an h)
                    lits.push( tsLit ); addClause_( lits, _type, _original, cnfInfoIter );
                    lits.pop();
                    // (or -a1 .. -an h)
                    tmp.push( tsLit ); addClause_( tmp, _type, _original, cnfInfoIter );
                    // (or -a1 a2 -h) (or a1 -a2 -h) .. (or -a{n-1} an -h) (or a{n-1} -an -h)
                    vec<Lit> tmpB;
                    for( int i = 1; i < lits.size(); ++i )
                    {
                        tmpB.clear(); tmpB.push( tmp[i-1] ); tmpB.push( lits[i] ); tmpB.push( neg( tsLit ) ); addClause_( tmpB, _type, _original, cnfInfoIter );
                        tmpB.clear(); tmpB.push( lits[i-1] ); tmpB.push( tmp[i] ); tmpB.push( neg( tsLit ) ); addClause_( tmpB, _type, _original, cnfInfoIter );
                    }
                    return tsLit;
                }
                case carl::FormulaType::XOR:
                {
                    vec<Lit> negLits;
                    vec<Lit> tmp;
                    for( const auto& sf : _formula.subformulas() )
                    {
                        lits.push( addClauses( sf, _type, nextDepth, _original ) );
                        negLits.push( sf.isLiteral() ? addClauses( sf.negated(), _type, nextDepth, _original ) : neg( lits.last() ) );
                    }
                    if( _type == NORMAL_CLAUSE )
                        cnfInfoIter->second.mLiteral = tsLit;
                    if( _depth == 0 )
                    {
                        addXorClauses( lits, negLits, 0, true, _type, tmp, _original, cnfInfoIter );
                        return lit_Undef;
                    }
                    if( !mReceivedFormulaPurelyPropositional && Settings::initiate_activities )
                    {
                        mTseitinVarFormulaMap.emplace( (int)var(tsLit), _formula );
                    }
                    if( !mReceivedFormulaPurelyPropositional && Settings::formula_guided_decision_heuristic )
                    {
                        std::vector<signed> vars;
                        for( int pos = 0; pos < lits.size(); ++pos )
                            vars.push_back( (signed)var(lits[pos]) );
                        mTseitinVarShadows.emplace( (signed)var(tsLit), std::move(vars) ); 
                    }
                    lits.push( neg( tsLit ) );
                    negLits.push( tsLit );
                    addXorClauses( lits, negLits, 0, true, _type, tmp, _original, cnfInfoIter );
                    return tsLit;
                }
                case carl::FormulaType::EXISTS:
                case carl::FormulaType::FORALL:
                    assert( false );
                    std::cerr << "Formula must be quantifier-free!" << std::endl;
                    break;
                default:
					SMTRAT_LOG_WARN("smtrat.sat", "Unexpected formula type " << _formula.getType());
                    assert( false );
                    std::cerr << "Unexpected type of formula!" << std::endl;
                }
            }
        }
        return lit_Undef;
    }
    
    template<class Settings>
    void SATModule<Settings>::addXorClauses( const vec<Lit>& _literals, const vec<Lit>& _negLiterals, int _from, bool _numOfNegatedLitsEven, unsigned _type, vec<Lit>& _clause, const FormulaT& _original, typename FormulaCNFInfosMap::iterator _formulaCNFInfoIter )
    {
        if( _from == _literals.size() - 1 )
        {
            _clause.push( _numOfNegatedLitsEven ? _literals[_from] : _negLiterals[_from] );
            addClause_( _clause, _type, _original, _formulaCNFInfoIter );
            _clause.pop();
        }
        else
        {
            _clause.push( _literals[_from] );
            addXorClauses( _literals, _negLiterals, _from+1, _numOfNegatedLitsEven, _type, _clause, _original, _formulaCNFInfoIter );
            _clause.pop();
            _clause.push( _negLiterals[_from] );
            addXorClauses( _literals, _negLiterals, _from+1, !_numOfNegatedLitsEven, _type, _clause, _original, _formulaCNFInfoIter );
            _clause.pop();
        }
    }
    
    template<class Settings>
    Lit SATModule<Settings>::createLiteral( const FormulaT& _formula, const FormulaT& _origin, bool _decisionRelevant )
    {
        assert( _formula.propertyHolds( carl::PROP_IS_A_LITERAL ) );
        bool negated = _formula.getType() == carl::FormulaType::NOT;
        const FormulaT& content = negated ? _formula.subformula() : _formula;
        if( content.getType() == carl::FormulaType::BOOL )
        {
            Lit l = lit_Undef;
            BooleanVarMap::iterator booleanVarPair = mBooleanVarMap.find(content.boolean());
            if( booleanVarPair != mBooleanVarMap.end() )
            {
                if( _decisionRelevant )
                    setDecisionVar( booleanVarPair->second, _decisionRelevant );
                l = mkLit( booleanVarPair->second, negated );
            }
            else
            {
                Var var = newVar( true, _decisionRelevant, content.activity() );
                mBooleanVarMap[content.boolean()] = var;
                mMinisatVarMap.emplace((int)var,content);
                mBooleanConstraintMap.push( std::make_pair( nullptr, nullptr ) );
                l = mkLit( var, negated );
            }
            return l;
        }
        else
        {
            assert( supportedConstraintType( content ) );
            double act = fabs( _formula.activity() );
            bool preferredToTSolver = false; //(_formula.activity()<0)
            ConstraintLiteralsMap::iterator constraintLiteralPair = mConstraintLiteralMap.find( _formula );
            if( constraintLiteralPair != mConstraintLiteralMap.end() )
            {
                // Check whether the theory solver wants this literal to assigned as soon as possible.
                int abstractionVar = var(constraintLiteralPair->second.front());
                if( act == numeric_limits<double>::infinity() )
                {
                    activity[abstractionVar] = maxActivity() + 1;
                    polarity[abstractionVar] = false;
                }
                if( _decisionRelevant )
                    setDecisionVar( abstractionVar, _decisionRelevant );
                // add the origin
                auto& abstrPair = mBooleanConstraintMap[abstractionVar];
                assert( abstrPair.first != nullptr && abstrPair.second != nullptr );
                Abstraction& abstr = sign(constraintLiteralPair->second.front()) ? *abstrPair.second : *abstrPair.first;
                if( !_origin.isTrue() || !negated )
                {
                    if( !abstr.consistencyRelevant )
                    {
                        addConstraintToInform_( abstr.reabstraction );
                        if( (sign(constraintLiteralPair->second.front()) && assigns[abstractionVar] == l_False)
                            || (!sign(constraintLiteralPair->second.front()) && assigns[abstractionVar] == l_True) )
                        {
                            if( ++abstr.updateInfo > 0 )
                                mChangedBooleans.push_back( abstractionVar );
                        }
                        abstr.consistencyRelevant = true;
                    }
                    if( !_origin.isTrue() )
                    {
                        if( abstr.origins == nullptr )
                        {
                            abstr.origins = std::shared_ptr<std::vector<FormulaT>>( new std::vector<FormulaT>() );
                        }
                        abstr.origins->push_back( _origin );
                    }
                }
                return constraintLiteralPair->second.front();
            }
            else
            {
                // Add a fresh Boolean variable as an abstraction of the constraint.
                #ifdef SMTRAT_DEVOPTION_Statistics
                if( preferredToTSolver ) mpStatistics->initialTrue();
                #endif
                FormulaT constraint;
                FormulaT invertedConstraint;
                if( content.getType() == carl::FormulaType::CONSTRAINT )
                {
                    constraint = content;
                    const ConstraintT& cons = content.constraint();
                    invertedConstraint = FormulaT( cons.lhs(), carl::invertRelation( cons.relation() ) );
                }
				else if (content.getType() == carl::FormulaType::VARCOMPARE )
				{
					constraint = content;
					invertedConstraint = FormulaT( content.variableComparison().negation() );
				}
                else if( content.getType() == carl::FormulaType::UEQ )
                {
                    constraint = content;
                    const carl::UEquality& ueq = content.uequality();
                    invertedConstraint = FormulaT( ueq.lhs(), ueq.rhs(), !ueq.negated() );
                }
                else if (content.getType() == carl::FormulaType::BITVECTOR)
                {
                    constraint = content;
                    invertedConstraint = FormulaT( carl::FormulaType::NOT, content );
                }
				else
				{
					assert( content.getType() == carl::FormulaType::PBCONSTRAINT );
					constraint = content;
					invertedConstraint = FormulaT( carl::FormulaType::NOT, content );
				}
                Var constraintAbstraction = newVar( !preferredToTSolver, _decisionRelevant, act );
                // map the abstraction variable to the abstraction information for the constraint and it's negation
                mBooleanConstraintMap.push( std::make_pair( new Abstraction( passedFormulaEnd(), constraint ), new Abstraction( passedFormulaEnd(), invertedConstraint ) ) );
                // add the constraint and its negation to the constraints to inform backends about
                if( !_origin.isTrue() )
                {
                    assert( mBooleanConstraintMap.last().first != nullptr && mBooleanConstraintMap.last().second != nullptr );
                    Abstraction& abstr = negated ? *mBooleanConstraintMap.last().second : *mBooleanConstraintMap.last().first;
                    if( abstr.origins == nullptr )
                    {
                        abstr.origins = std::shared_ptr<std::vector<FormulaT>>( new std::vector<FormulaT>() );
                    }
                    if( negated )
                    {
                        abstr.origins->push_back( _origin );
                        abstr.consistencyRelevant = true;
                        addConstraintToInform_( invertedConstraint );
                    }
                    else
                    {
                        abstr.origins->push_back( _origin );
                        abstr.consistencyRelevant = true;
                        addConstraintToInform_( constraint );
                    }
                }
                else if( !negated )
                {
                    assert( mBooleanConstraintMap.last().first != nullptr );
                    mBooleanConstraintMap.last().first->consistencyRelevant = true;
                    addConstraintToInform_( constraint );
                }
                // create a literal for the constraint and its negation
                Lit litPositive = mkLit( constraintAbstraction, false );
                std::vector<Lit> litsA;
                litsA.push_back( litPositive );
                mConstraintLiteralMap.insert( std::make_pair( FormulaT( carl::FormulaType::NOT, invertedConstraint ), litsA ) );
                mConstraintLiteralMap.insert( std::make_pair( constraint, std::move( litsA ) ) );
                Lit litNegative = mkLit( constraintAbstraction, true );
                std::vector<Lit> litsB;
                litsB.push_back( litNegative );
                mConstraintLiteralMap.insert( std::make_pair( negated ? _formula : FormulaT( carl::FormulaType::NOT, constraint ), litsB ) );
                mConstraintLiteralMap.insert( std::make_pair( invertedConstraint, std::move( litsB ) ) );
                // we return the abstraction variable as literal, if the negated flag was negative,
                // otherwise we return the abstraction variable's negation 
                Lit res = negated ? litNegative : litPositive;
                return res;
            }
        }
    }
    
    template<class Settings>
    Lit SATModule<Settings>::getLiteral( const FormulaT& _formula ) const
    {
        bool negated = _formula.getType() == carl::FormulaType::NOT;
        const FormulaT& content = negated ? _formula.subformula() : _formula;
        if( content.getType() == carl::FormulaType::BOOL )
        {
            BooleanVarMap::const_iterator booleanVarPair = mBooleanVarMap.find(content.boolean());
            assert( booleanVarPair != mBooleanVarMap.end() );
            return mkLit( booleanVarPair->second, negated );
        }
        assert( supportedConstraintType( content ) );
        ConstraintLiteralsMap::const_iterator constraintLiteralPair = mConstraintLiteralMap.find( content );
        assert( constraintLiteralPair != mConstraintLiteralMap.end() );
        return negated ? neg( constraintLiteralPair->second.front() ) : constraintLiteralPair->second.front();
    }

    template<class Settings>
    void SATModule<Settings>::adaptPassedFormula()
    {
        // Adapt the constraints in the passed formula for the just assigned Booleans being abstractions of constraints.
        for( signed posInAssigns : mChangedBooleans )
        {
            assert( mBooleanConstraintMap[posInAssigns].first != nullptr && mBooleanConstraintMap[posInAssigns].second != nullptr );
            adaptPassedFormula( *mBooleanConstraintMap[posInAssigns].first );
            adaptPassedFormula( *mBooleanConstraintMap[posInAssigns].second );
        }
        mChangedBooleans.clear();
        // Update the activities of the constraints in the passed formula according to the activity of the SAT solving process.
        if( mAllActivitiesChanged )
        {
            for( int i = 0; i < mBooleanConstraintMap.size(); ++i )
            {
                if( mBooleanConstraintMap[i].first != nullptr )
                {
                    assert( mBooleanConstraintMap[i].second != nullptr );
                    auto posInPasForm = mBooleanConstraintMap[i].first->position;
                    if( posInPasForm != rPassedFormula().end() )
                        posInPasForm->formula().setActivity(activity[i]);
                    posInPasForm = mBooleanConstraintMap[i].second->position;
                    if( posInPasForm != rPassedFormula().end() )
                        posInPasForm->formula().setActivity(activity[i]);
                }
            }
            mAllActivitiesChanged = false;
        }
        else
        {
            for( signed v : mChangedActivities )
            {
                if( mBooleanConstraintMap[v].first != nullptr )
                {
                     assert( mBooleanConstraintMap[v].second != nullptr );
                    auto posInPasForm = mBooleanConstraintMap[v].first->position;
                    if( posInPasForm != rPassedFormula().end() )
                        posInPasForm->formula().setActivity(activity[v]);
                    posInPasForm = mBooleanConstraintMap[v].second->position;
                    if( posInPasForm != rPassedFormula().end() )
                        posInPasForm->formula().setActivity(activity[v]);
                }
            }
        }
        mChangedActivities.clear();
        if( mChangedPassedFormula )
        {
            mCurrentAssignmentConsistent = SAT;
        }
//        assert( passedFormulaCorrect() );
    }
    
    template<class Settings>
    void SATModule<Settings>::adaptPassedFormula( Abstraction& _abstr )
    {
        if( _abstr.updateInfo < 0 )
        {
            assert( !_abstr.reabstraction.isTrue() );
            if( _abstr.position != rPassedFormula().end() )
            {
                removeOrigins( _abstr.position, _abstr.origins );
                _abstr.position = passedFormulaEnd();
                mChangedPassedFormula = true;
            }
        }
        else if( _abstr.updateInfo > 0 )
        {
            assert( !_abstr.reabstraction.isTrue() );
            assert( _abstr.reabstraction.getType() == carl::FormulaType::UEQ || _abstr.reabstraction.getType() == carl::FormulaType::BITVECTOR || (_abstr.reabstraction.getType() == carl::FormulaType::CONSTRAINT && _abstr.reabstraction.constraint().isConsistent() == 2) );
            auto res = addSubformulaToPassedFormula( _abstr.reabstraction, _abstr.origins );
            _abstr.position = res.first;
            _abstr.position->setDeducted( _abstr.isDeduction );
            mChangedPassedFormula = true;
        }
        _abstr.updateInfo = 0;
    }
    
    template<class Settings>
    bool SATModule<Settings>::passedFormulaCorrect() const
    {
        for( int k = 0; k < mBooleanConstraintMap.size(); ++k )
        {
            if( assigns[k] != l_Undef )
            {
                if( mBooleanConstraintMap[k].first != nullptr )
                {
                    assert( mBooleanConstraintMap[k].second != nullptr );
                    const Abstraction& abstr = assigns[k] == l_False ? *mBooleanConstraintMap[k].second : *mBooleanConstraintMap[k].first;
                    if( !abstr.reabstraction.isTrue() && abstr.consistencyRelevant && (abstr.reabstraction.getType() == carl::FormulaType::UEQ || abstr.reabstraction.getType() == carl::FormulaType::BITVECTOR || abstr.reabstraction.constraint().isConsistent() != 1))
                    {
                        if( !rPassedFormula().contains( abstr.reabstraction ) )
                        {
//                            cout << "does not contain  " << abstr.reabstraction << endl;
                            return false;
                        }
                    }
                }
            }
        }
        for( auto subformula = rPassedFormula().begin(); subformula != rPassedFormula().end(); ++subformula )
        {
            if( value( getLiteral( subformula->formula() ) ) != l_True )
            {
//                cout << "should not contain  " << iter->first << endl;
                return false;
            }
        }
        return true;
    }

    template<class Settings>
    Var SATModule<Settings>::newVar( bool sign, bool dvar, double _activity )
    {
        int v = nVars();
        watches.init( mkLit( v, false ) );
        watches.init( mkLit( v, true ) );
        assigns.push( l_Undef );
        vardata.push( VarData( CRef_Undef, -1, -1 ) );
        activity.push( _activity == numeric_limits<double>::infinity() ? maxActivity() + 1 : _activity );
        // activity.push( rnd_init_act ? drand( random_seed ) * 0.00001 : 0 );
        seen.push( 0 );
        polarity.push( sign );
        decision.push();
        trail.capacity( v + 1 );
        if( !mReceivedFormulaPurelyPropositional && Settings::formula_guided_decision_heuristic )
        {
            setDecisionVar( v, dvar );
            mNonTseitinShadowedOccurrences.push( dvar ? 1 : 0 );
        }
        else
            setDecisionVar( v, dvar );
        if( !mReceivedFormulaPurelyPropositional && Settings::check_active_literal_occurrences )
        {
            mLiteralsClausesMap.emplace_back();
            mLiteralsActivOccurrences.emplace_back();
        }
        return v;
    }

    template<class Settings>
    bool SATModule<Settings>::addClause( const vec<Lit>& _clause, unsigned _type  )
    {
		SMTRAT_LOG_DEBUG("smtrat.sat", "Adding clause " << _clause);
        #ifdef DEBUG_SATMODULE_LEMMA_HANDLING
        std::cout << "add clause ";
        printClause(_clause,true);
        #endif
        assert( _clause.size() != 0 );
        assert(_type < 4);
        add_tmp.clear();
        _clause.copyTo( add_tmp );

        #ifdef SMTRAT_DEVOPTION_Statistics
        if( _type != NORMAL_CLAUSE ) mpStatistics->lemmaLearned();
        #endif
        // Check if clause is satisfied and remove false/duplicate literals:true);
        sort( add_tmp );
        
        int falseLiteralsCount = 0;
        // check the clause for tautologies and similar
        // note, that we do not change original clauses, as due to incrementality we
        // want to know the clauses of a formula regardless of the context of other formulas
        if( _type != NORMAL_CLAUSE )
        {
            Lit p;
            int i, j;
            for( i = j = 0, p = lit_Undef; i < add_tmp.size(); ++i )
            {
                // tautologies are ignored
                if( add_tmp[i] == ~p )
                    return true; // clause can be ignored
                // clauses with 0-level true literals are also ignored
                if( value( add_tmp[i] ) == l_True && level( var( add_tmp[i] ) ) == 0 )
                    return true;
                // ignore repeated literals
                if( add_tmp[i] == p )
                    continue;
                // if a literal is false at 0 level (both sat and user level) we also ignore it
                if( value( add_tmp[i] ) == l_False )
                {
                    if( level( var( add_tmp[i] ) ) == 0 )
                        continue;
                    else
                        ++falseLiteralsCount; // if we decide to keep it, we count it into the false literals
                }
                // this literal is a keeper
                add_tmp[j++] = p = add_tmp[i];
            }
            add_tmp.shrink( i - j );
            if( mBusy || decisionLevel() > assumptions.size() )
            {
                #ifdef DEBUG_SATMODULE_LEMMA_HANDLING
                std::cout << "add to mLemmas" << std::endl;
                #endif
                mLemmas.push();
                add_tmp.copyTo( mLemmas.last() );
                mLemmasRemovable.push( _type != NORMAL_CLAUSE );
                return true;
            }
            // if all false, we're in conflict
            if( add_tmp.size() == falseLiteralsCount )
                return ok = false;
        }
        CRef cr = CRef_Undef;
        // if not unit, add the clause
        if( add_tmp.size() > 1 )
        {
            lemma_lt lt( *this );
            sort( add_tmp, lt );
            cr = ca.alloc( add_tmp, NORMAL_CLAUSE );
            clauses.push( cr );
            attachClause( cr );
        }
        // check if it propagates
        if( add_tmp.size() == falseLiteralsCount + 1 )
        {
            if( assigns[var(add_tmp[0])] == l_Undef )
            {
                assert( assigns[var(add_tmp[0])] != l_False );
                uncheckedEnqueue( add_tmp[0], cr );
                propagateConsistently( false );
                return ok;
            }
            else
                return ok;
        }
        return true;
    }

    template<class Settings>
    int SATModule<Settings>::level( const vec< Lit >& _clause ) const
    {
        int result = 0;
        for( int i = 0; i < _clause.size(); ++i )
        {
            if( value( _clause[i] ) != l_Undef )
            {
                int varLevel = level( var( _clause[i] ) );
                if( varLevel > result ) result = varLevel;
            }
        }
        return result;
    }
    
    template<class Settings>
    CRef SATModule<Settings>::storeLemmas()
    {
		SMTRAT_LOG_DEBUG("smtrat.sat", "Storing lemmas");
        #ifdef DEBUG_SATMODULE_LEMMA_HANDLING
        std::cout << __func__ << std::endl;
        #endif
        CRef conflict = CRef_Undef;
        // decision level to backtrack to
        int backtrackLevel = decisionLevel();
        // we use this comparison operator
        lemma_lt lt( *this );
        // check for propagation and level to backtrack to
        #ifdef DEBUG_SATMODULE_LEMMA_HANDLING
        std::cout << "mLemmas.size() = " << mLemmas.size() << std::endl;
        #endif
        int i = 0;
        while( i < mLemmas.size() )
        {
            // we need this loop as when we backtrack, due to registration more lemmas could be added
            for( ; i < mLemmas.size(); ++i )
            {
                // The current lemma
                vec<Lit>& lemma = mLemmas[i];
				SMTRAT_LOG_DEBUG("smtrat.sat", "Adding a lemma " << lemma);
                #ifdef DEBUG_SATMODULE_LEMMA_HANDLING
                std::cout << "add the lemma  ";
                printClause(lemma,true);
                #endif
                // if it's an empty lemma, we have a conflict at zero level
                if( lemma.size() == 0 )
                {
                    backtrackLevel = 0;
                    continue;
                }
                // sort the lemma to be able to attach
                sort( lemma, lt );
                // see if the lemma propagates something
                if( lemma.size() == 1 || value(lemma[1]) == l_False )
                {
                    // this lemma propagates, see which level we need to backtrack to
                    int currentBacktrackLevel = lemma.size() == 1 ? 0 : level(var(lemma[1]));
                    // even if the first literal is true, we should propagate it at this level (unless it's set at a lower level)
                    if( value(lemma[0]) != l_True || level(var(lemma[0])) > currentBacktrackLevel )
                    {
                        if( currentBacktrackLevel < backtrackLevel )
                            backtrackLevel = currentBacktrackLevel;
                    }
                }
            }
            // pop so that propagation would be current
            cancelUntil( backtrackLevel, true );
            #ifdef DEBUG_SATMODULE_LEMMA_HANDLING
            std::cout << "backtrack to " << backtrackLevel << std::endl;
            #endif
        }
        // last index in the trail
        int backtrack_index = trail.size();
        // attach all the clauses and enqueue all the propagations
        for( int i = 0; i < mLemmas.size(); ++i )
        {
            // the current lemma
            vec<Lit>& lemma = mLemmas[i];
            if( lemma.size() == 0 )
            {
				SMTRAT_LOG_DEBUG("smtrat.sat", "ok = false");
                ok = false;
                return CRef_Undef;
            }
            #ifdef DEBUG_SATMODULE_LEMMA_HANDLING
            std::cout << "use the lemma  ";
            printClause(lemma,true);
            #endif
            bool removable = mLemmasRemovable[i];
            // attach it if non-unit
            CRef lemma_ref = CRef_Undef;
            if( lemma.size() > 1 )
            {
                lemma_ref = ca.alloc( lemma, removable );
                if( removable )
                    learnts.push( lemma_ref );
                else
                    clauses.push( lemma_ref );
                attachClause( lemma_ref );
            }
            // if the lemma is propagating enqueue its literal (or set the conflict)
	        #ifdef DEBUG_SATMODULE
	        cout << "######################################################################" << endl;
			cout << "###" << endl; printBooleanConstraintMap(cout, "###");
	        cout << "###" << endl; printClauses( clauses, "Clauses", cout, "### ", 0, false, false );
	        cout << "###" << endl; printClauses( learnts, "Learnts", cout, "### ", 0, false, false );
	        cout << "###" << endl; printCurrentAssignment( cout, "### " );
	        cout << "###" << endl; printDecisions( cout, "### " );
	        cout << "###" << endl;
	        #endif
            if( conflict == CRef_Undef && value(lemma[0]) != l_True )
            {
                if( lemma.size() == 1 || (value(lemma[1]) == l_False && trailIndex(var(lemma[1])) < backtrack_index) )
                {
                    if( value(lemma[0]) == l_False )
                    {
                        // we have a conflict
                        if( lemma.size() > 1 )
                        {
                            #ifdef DEBUG_SATMODULE_LEMMA_HANDLING
                            std::cout << "lemma is better as conflict" << std::endl;
                            #endif
                            conflict = lemma_ref;
                        }
                    }
                    else
                    {
                        uncheckedEnqueue(lemma[0], lemma_ref);
                    }
                }
            }
        }
        // clear the lemmas
        mLemmas.clear();
        mLemmasRemovable.clear();
		SMTRAT_LOG_DEBUG("smtrat.sat", "Stored lemmas, returning conflict " << conflict);
        return conflict;
    }

    template<class Settings>
    void SATModule<Settings>::attachClause( CRef cr )
    {
        Clause& c = ca[cr];
        assert( c.size() > 1 );
        watches[~c[0]].push( Watcher( cr, c[1] ) );
        watches[~c[1]].push( Watcher( cr, c[0] ) );
        if( c.learnt() )
        {
            learnts_literals += (uint64_t)c.size();
        }
        else
            clauses_literals += (uint64_t)c.size();
        if( !mReceivedFormulaPurelyPropositional && Settings::check_active_literal_occurrences )
        {
            bool clauseSatisfied = satisfied(c);
            for( int i = 0; i < c.size(); ++i )
            {
                size_t v = (size_t)var(c[i]);
                if( sign(c[i]) )
                {
                    if( !clauseSatisfied )
                        ++(mLiteralsActivOccurrences[v].second);
                    mLiteralsClausesMap[v].addNegative( cr );
                }
                else
                {
                    if( !clauseSatisfied )
                        ++(mLiteralsActivOccurrences[v].first);
                    mLiteralsClausesMap[v].addPositive( cr );
                }
            }
        }
    }

    template<class Settings>
    void SATModule<Settings>::detachClause( CRef cr, bool strict )
    {
        const Clause& c = ca[cr];
        assert( c.size() > 1 );

        if( strict )
        {
            Minisat::remove( watches[~c[0]], Watcher( cr, c[1] ) );
            Minisat::remove( watches[~c[1]], Watcher( cr, c[0] ) );
        }
        else
        {
            // Lazy detaching: (NOTE! Must clean all watcher lists before garbage collecting this clause)
            watches.smudge( ~c[0] );
            watches.smudge( ~c[1] );
        }

        if( c.learnt() )
            learnts_literals -= (uint64_t)c.size();
        else
            clauses_literals -= (uint64_t)c.size();
        if( !mReceivedFormulaPurelyPropositional && Settings::check_active_literal_occurrences )
        {
            bool clauseSatisfied = satisfied(c);
            for( int i = 0; i < c.size(); ++i )
            {
                size_t v = (size_t)var(c[i]);
                if( sign(c[i]) )
                {
                    if( !clauseSatisfied )
                    {
                        assert( mLiteralsActivOccurrences[v].second > 0 );
                        --(mLiteralsActivOccurrences[v].second);
                    }
                    mLiteralsClausesMap[v].removeNegative( cr );
                }
                else
                {
                    if( !clauseSatisfied )
                    {
                        assert( mLiteralsActivOccurrences[v].first > 0 );
                        --(mLiteralsActivOccurrences[v].first);
                    }
                    mLiteralsClausesMap[v].removePositive( cr );
                }
            }
        }
    }

    template<class Settings>
    void SATModule<Settings>::removeClause( CRef cr )
    {
        Clause& c = ca[cr];
        detachClause( cr );
        // Don't leave pointers to free'd memory!
        if( locked( c ) )
            vardata[var( c[0] )].reason = CRef_Undef;
        c.mark( 1 );
        ca.free( cr );
    }

    template<class Settings>
    bool SATModule<Settings>::satisfied( const Clause& c ) const
    {
        for( int i = 0; i < c.size(); i++ )
        {
            if( value( c[i] ) == l_True )
                return true;
        }
        return false;
    }
    
    template<class Settings>
    void SATModule<Settings>::cancelUntil( int level, bool force )
    {
        if( level < assumptions.size() && !force )
            level = assumptions.size();
        #ifdef DEBUG_SATMODULE
	std::cout << "### cancel until " << level << std::endl;
        #endif
        if( decisionLevel() > level )
        {
            cancelAssignmentUntil( level );
            qhead = trail_lim[level];
			SMTRAT_LOG_TRACE("smtrat.sat", "Reset qhead to " << qhead << " from " << trail_lim);
            trail.shrink( trail.size() - trail_lim[level] );
            trail_lim.shrink( trail_lim.size() - level );
            ok = true;
        }
    }

    template<class Settings>
    void SATModule<Settings>::cancelAssignmentUntil( int level )
    {
        for( int c = trail.size() - 1; c >= trail_lim[level]; --c )
        {
            Var x = var( trail[c] );
            resetVariableAssignment( x );
            VarData& vd = vardata[x];
            if( vd.mExpPos > 0 )
            {
                removeTheoryPropagation( vd.mExpPos );
                vd.mExpPos = -1;
            }
            vd.reason = CRef_Undef;
            vd.mTrailIndex = -1;
            if( (phase_saving > 1 || (phase_saving == 1)) && c > trail_lim.last() )
                polarity[x] = sign( trail[c] );
            insertVarOrder( x );
        }
    }
    
    template<class Settings>
    void SATModule<Settings>::resetVariableAssignment( Var _var )
    {
        lbool& ass = assigns[_var];
        bool wasAssignedToFalse = ass == l_False;
        if( !mReceivedFormulaPurelyPropositional && mBooleanConstraintMap[_var].first != nullptr )
        {
            assert( mBooleanConstraintMap[_var].second != nullptr );
            Abstraction& abstr = wasAssignedToFalse ? *mBooleanConstraintMap[_var].second : *mBooleanConstraintMap[_var].first;
            if( abstr.position != rPassedFormula().end() )
            {
                if( abstr.updateInfo >=0 && --abstr.updateInfo < 0 )
                {
                    mChangedBooleans.push_back( _var );
                }
            }
            else if( abstr.consistencyRelevant )
            {
                abstr.updateInfo = 0;
            }
        }

        if( !mReceivedFormulaPurelyPropositional && Settings::formula_guided_decision_heuristic )
        {
            auto iter = mTseitinVarShadows.find( (signed) _var );
            if( iter != mTseitinVarShadows.end() )
            {
                for( signed var : iter->second )
                {
                    decrementTseitinShadowOccurrences(var);
                }
            }
        }
        ass = l_Undef;
        if( !mReceivedFormulaPurelyPropositional && Settings::check_active_literal_occurrences )
        {
            // Check clauses which are going to be satisfied by this assignment.
            size_t v = (size_t)_var;
            const std::vector<CRef>& satisfiedClauses = wasAssignedToFalse ? mLiteralsClausesMap[v].negatives() : mLiteralsClausesMap[v].positives();
            for( CRef cr : satisfiedClauses )
            {
                const Clause& c = ca[cr];
                // Check if clause is not yet satisfied.
                if( !satisfied(c) )
                {
                    for( int i = 0; i < c.size(); ++i )
                    {
                        size_t v = (size_t)var(c[i]);
                        std::pair<size_t,size_t>& litActOccs = mLiteralsActivOccurrences[v];
                        Var x = var(c[i]);
                        if( litActOccs.first == 0 )
                        {
                            if( litActOccs.second == 0  )
                            {
                                decision[x] = true;
                                insertVarOrder( x );
                            }
                            else
                            {
                                auto pfdIter = std::find( mPropagationFreeDecisions.begin(), mPropagationFreeDecisions.end(), mkLit( x, true ) );
                                if( pfdIter != mPropagationFreeDecisions.end() )
                                {
                                    *pfdIter = mPropagationFreeDecisions.back();
                                    mPropagationFreeDecisions.pop_back();
                                }
                            }
                        }
                        else if( litActOccs.second == 0 )
                        {
                            auto pfdIter = std::find( mPropagationFreeDecisions.begin(), mPropagationFreeDecisions.end(), mkLit( x, false ) );
                            if( pfdIter != mPropagationFreeDecisions.end() )
                            {
                                *pfdIter = mPropagationFreeDecisions.back();
                                mPropagationFreeDecisions.pop_back();
                            }
                        }
                        if( sign(c[i]) )
                        {
                            ++(litActOccs.second);
                        }
                        else
                        {
                            ++(litActOccs.first);
                        }
                    }
                }
            }
        }
        if( Settings::check_if_all_clauses_are_satisfied && !mReceivedFormulaPurelyPropositional && mNumberOfSatisfiedClauses > 0 )
        {
            auto litClausesIter = mLiteralClausesMap.find( (int) _var );
            if( litClausesIter != mLiteralClausesMap.end() )
            {
                for( CRef cl : litClausesIter->second )
                {
                    if( !satisfied( ca[cl] ) )
                    {
                        assert( mNumberOfSatisfiedClauses > 0 );
                        --mNumberOfSatisfiedClauses;
                    }
                }
            }
        }
    }
    
    template<class Settings>
    CRef SATModule<Settings>::propagateConsistently( bool _checkWithTheory )
    {
        CRef confl = CRef_Undef;
        
        ScopedBool scopedBool( mBusy, true );
        
        // add lemmas that we're left behind
        if( mLemmas.size() > 0 )
        {
			SMTRAT_LOG_DEBUG("smtrat.sat", "Storing lemmas");
            confl = storeLemmas();
            if( confl != CRef_Undef )
                return confl;
            if( !ok )
                return CRef_Undef;
        }
        // keep running until we have checked everything, we have no conflict and no new literals have been asserted
        do
        {
            // Propagate on the clauses
            confl = propagate();
            // If no conflict, do the theory check
            if( confl == CRef_Undef && _checkWithTheory )
            {
                // do the theory check
                theoryCall();
                if( mCurrentAssignmentConsistent == ABORTED )
                {
                    mCurrentAssignmentConsistent = UNKNOWN;
                    return CRef_Undef;
                }
                // propagate theory
                propagateTheory();
                // if there are lemmas (or conflicts) update them
                if( mLemmas.size() > 0 )
                    confl = storeLemmas();
            }
            else
            {   
                // even though in conflict, we still need to discharge the lemmas
                if( mLemmas.size() > 0 )
                {
                    // remember the trail size
                    int oldLevel = decisionLevel();
                    // update the lemmas
                    CRef lemmaConflict = storeLemmas();
                    // if we get a conflict, we prefer it since it's earlier in the trail
                    if( lemmaConflict != CRef_Undef )
                        confl = lemmaConflict; // lemma conflict takes precedence, since it's earlier in the trail
                    else if( oldLevel > decisionLevel() )
                        confl = CRef_Undef; // Otherwise, the Boolean conflict is canceled in the case we popped the trail
                }
            }
            if( !ok ) {
				SMTRAT_LOG_DEBUG("smtrat.sat", "Aborting due to !ok");
                return CRef_Undef;
			}
            assert( mChangedBooleans.empty() || _checkWithTheory );
        }
        while( confl == CRef_Undef && (qhead < trail.size() || (decisionLevel() >= assumptions.size() && mCurrentAssignmentConsistent != SAT && !mChangedBooleans.empty())) );
		SMTRAT_LOG_TRACE("smtrat.sat", "Returning " << confl);
        return confl;
    }
    
    template<class Settings>
    void SATModule<Settings>::propagateTheory()
    {
        carl::uint pos = mTheoryPropagations.size();
        collectTheoryPropagations();
        while( pos < mTheoryPropagations.size() )
        {
            TheoryPropagation& tp = mTheoryPropagations[pos];
            Lit conclLit = createLiteral( tp.mConclusion );
            if( value(conclLit) == l_Undef )
            {
                uncheckedEnqueue( conclLit, CRef_Lazy );
                vardata[var(conclLit)].mExpPos = (int)pos;
                ++pos;
            }
            else
            {
                if( value(conclLit) == l_False )
                {
                    vec<Lit> explanation;
                    for( const auto& subformula : tp.mPremise )
                        explanation.push( neg( getLiteral( subformula ) ) );
                    explanation.push( conclLit );
                    addClause( explanation, LEMMA_CLAUSE );
                }
                if( (std::size_t) pos != mTheoryPropagations.size()-1 )
                    tp = std::move( mTheoryPropagations.back() );
                mTheoryPropagations.pop_back();
            }
        }
    }
    
    template<class Settings>
    CRef SATModule<Settings>::reason( Var x )
    {
        VarData& vd = vardata[x];
        // if we already have a reason, just return it
        if( vd.reason != CRef_Lazy )
            return vd.reason;

        // what's the literal we are trying to explain
        Lit l = mkLit(x, value(x) != l_True);

        // get the explanation
        assert( vd.mExpPos >= 0 && (std::size_t)vd.mExpPos < mTheoryPropagations.size() );
        TheoryPropagation& tp = mTheoryPropagations[(std::size_t)vd.mExpPos];
        vec<Lit> explanation;
        assert( getLiteral( tp.mConclusion ) == l );
        explanation.push( l );
        for( const auto& subformula : tp.mPremise )
            explanation.push( neg( getLiteral( subformula ) ) );
        
        // remove theory propagation
        removeTheoryPropagation( vd.mExpPos );

        // sort the literals by trail index level
        lemma_lt lt(*this);
        sort( explanation, lt );
        assert( explanation[0] == l );

        // compute the assertion level for this clause
        int i, j;
        Lit prev = lit_Undef;
        for( i = 0, j = 0; i < explanation.size(); ++i )
        {
            assert( value(explanation[i]) != l_Undef );
            assert( i == 0 || trailIndex(var(explanation[0])) > trailIndex(var(explanation[i])) );

            // always keep the first literal
            if( i == 0 )
            {
                prev = explanation[j++] = explanation[i];
                continue;
            }
            // ignore duplicate literals
            if( explanation[i] == prev )
                continue;
            // ignore zero level literals
            if( level(var(explanation[i])) == 0 )
                continue;
            // keep this literal
            prev = explanation[j++] = explanation[i];
        }
        explanation.shrink(i - j);

        // we need an explanation clause so we add a fake literal
        if( j == 1 )
        {
            // add not TRUE to the clause
            explanation.push( mkLit( mTrueVar, true ) );
        }

        // construct the reason
        CRef real_reason = ca.alloc( explanation, LEMMA_CLAUSE );
        vardata[x] = VarData( real_reason, level(x), trailIndex(x) );
        learnts.push(real_reason);
        attachClause(real_reason);
        return real_reason;
    }
    
    template<class Settings>
    void SATModule<Settings>::removeTheoryPropagation( int _position )
    {
        assert( _position >= 0 );
        assert( (std::size_t)_position < mTheoryPropagations.size() );
        if( (std::size_t) _position != mTheoryPropagations.size()-1 )
        {
            TheoryPropagation& tp = mTheoryPropagations.back();
            VarData& vd = vardata[var(getLiteral( tp.mConclusion ))];
            assert( (std::size_t) vd.mExpPos == mTheoryPropagations.size()-1 );
            vd.mExpPos = _position;
            mTheoryPropagations[(std::size_t)_position] = std::move( tp );
        }
        mTheoryPropagations.pop_back();
    }
    
    template<class Settings>
    void SATModule<Settings>::theoryCall()
    {
        #ifdef DEBUG_SATMODULE
        cout << "### Sat iteration" << endl;
        cout << "######################################################################" << endl;
		cout << "###" << endl; printBooleanConstraintMap(cout, "###");
        cout << "###" << endl; printClauses( clauses, "Clauses", cout, "### ", 0, false, false );
        cout << "###" << endl; printClauses( learnts, "Learnts", cout, "### ", 0, false, false );
        cout << "###" << endl; printCurrentAssignment( cout, "### " );
        cout << "###" << endl; printDecisions( cout, "### " );
        cout << "###" << endl;
        #endif
        if( !mReceivedFormulaPurelyPropositional && decisionLevel() >= assumptions.size() && 
            (!Settings::try_full_lazy_call_first || mNumberOfFullLazyCalls > 0 || trail.size() == assigns.size()) )
        {
            if( Settings::try_full_lazy_call_first && trail.size() == assigns.size() )
                ++mNumberOfFullLazyCalls;
            // Check constraints corresponding to the positively assigned Boolean variables for consistency.
            if( mCurrentAssignmentConsistent != SAT )
            {
                adaptPassedFormula();
            }
            bool finalCheck = fullAssignment();
            if( mChangedPassedFormula || finalCheck )
            {
                #ifdef DEBUG_SATMODULE
                cout << "### Check the constraints: { "; for( auto& subformula : rPassedFormula() ) cout << subformula.formula() << " "; cout << "}" << endl;
                #endif
                mChangedPassedFormula = false;
                mCurrentAssignmentConsistent = runBackends( finalCheck, mFullCheck, false );
                #ifdef DEBUG_SATMODULE
                cout << "### Result: " << ANSWER_TO_STRING( mCurrentAssignmentConsistent ) << "!" << endl;
                #endif
                switch( mCurrentAssignmentConsistent )
                {
                    case SAT:
                    {
                        if( Settings::allow_theory_propagation )
                            processLemmas();
                        break;
                    }
                    case UNSAT:
                    {
                        learnTheoryConflicts();
                        if( Settings::allow_theory_propagation )
                            processLemmas();
                        break;
                    }
                    case UNKNOWN:
                    {
                        if( Settings::allow_theory_propagation )
                            processLemmas();
                        break;
                    }
                    default:
                    {
                        break;
                    }
                }
            }
        }
    }
    
    template<class Settings>
    bool SATModule<Settings>::expPositionsCorrect() const
    {
        for( int i = 0; i < vardata.size(); ++i )
        {
            if( vardata[i].reason == CRef_Lazy && vardata[i].mExpPos < 0 )
                return false;
        }
        return true;
    }
    
    template<class Settings>
    void SATModule<Settings>::constructLemmas()
    {
        for( VarLemmaMap::const_iterator iter = mPropagatedLemmas.begin(); iter != mPropagatedLemmas.end(); ++iter )
        {
            // Construct formula
            FormulaT premise( carl::FormulaType::AND, std::move( iter->second ) );
            auto mvIter = mMinisatVarMap.find(iter->first);
            assert( mvIter != mMinisatVarMap.end() );
            if( assigns[ iter->first ] == l_False )
            {
                addLemma( FormulaT( carl::FormulaType::IMPLIES, premise, mvIter->second.negated() ) );
            }
            else
            {
                assert( assigns[ iter->first ] == l_True );
                FormulaT lemma = FormulaT( carl::FormulaType::IMPLIES, premise, mvIter->second );
                addLemma( lemma );
            }
        }
    }

    template<class Settings>
    lbool SATModule<Settings>::search( int nof_conflicts )
    {
        #ifdef DEBUG_SATMODULE
        cout << "### search()" << endl;
		cout << "###" << endl; printBooleanConstraintMap(cout, "###");
        cout << "###" << endl; printClauses( clauses, "Clauses", cout, "### " );
        cout << "###" << endl; printClauses( learnts, "Learnts", cout, "### " );
        cout << "###" << endl; printBooleanConstraintMap( cout, "###" );
        cout << "###" << endl; printBooleanVarMap( cout, "###" );
        cout << "###" << endl;
        #endif
        assert( ok );
        int conflictC = 0;
        starts++;
        mCurrentAssignmentConsistent = SAT;
        for( ; ; )
        {
            if( !mComputeAllSAT && anAnswerFound() )
                return l_Undef;
            CRef confl = propagateConsistently();
            if( !mComputeAllSAT && anAnswerFound() )
                return l_Undef;
            if( !ok )
            {
                if( !mReceivedFormulaPurelyPropositional && !Settings::stop_search_after_first_unknown && mExcludedAssignments )
                    return l_Undef;
                return l_False;
            }

            if( confl == CRef_Undef )
            {
                // NO CONFLICT
                if( Settings::check_if_all_clauses_are_satisfied && !mReceivedFormulaPurelyPropositional )
                {
                    if( decisionLevel() >= assumptions.size() && mNumberOfSatisfiedClauses == (size_t)clauses.size() )
                    {
                        return l_True;
                    }
                }
                if( Settings::use_restarts && nof_conflicts >= 0 && (conflictC >= nof_conflicts) ) // ||!withinBudget()) )
                {
                    #ifdef DEBUG_SATMODULE
                    cout << "###" << endl << "### Restart." << endl << "###" << endl;
                    #endif
                    // Reached bound on number of conflicts:
                    progress_estimate = progressEstimate();
                    cancelUntil( 0 );
                    ++mCurr_Restarts;
                    #ifdef SMTRAT_DEVOPTION_Statistics
                    mpStatistics->restart();
                    #endif
                    return l_Undef;
                }
                if( learnts.size() - nAssigns() >= max_learnts && rReceivedFormula().isOnlyPropositional() )
                {
                     // Reduce the set of learned clauses:
                     reduceDB();
                }
                
                Lit next = lit_Undef;
                while( decisionLevel() < assumptions.size() )
                {
                    // Perform user provided assumption:
                    Lit p = assumptions[decisionLevel()];
                    if( value( p ) == l_True )
                    {
                        // Dummy decision level:
                        newDecisionLevel();
                    }
                    else if( value( p ) == l_False )
                    {
                        if( !mReceivedFormulaPurelyPropositional && !Settings::stop_search_after_first_unknown && mExcludedAssignments )
                            return l_Undef;
                        return l_False;
                    }
                    else
                    {
                        next = p;
                        break;
                    }
                }
                // If we do not already have a branching literal, we pick one
                if( next == lit_Undef )
                {
                    // New variable decision:
                    decisions++;
                    #ifdef SMTRAT_DEVOPTION_Statistics
                    mpStatistics->decide();
                    #endif
                    next = pickBranchLit();

                    if( next == lit_Undef )
                    {
                        if( mReceivedFormulaPurelyPropositional || mCurrentAssignmentConsistent == SAT )
                        {
                            // Model found:
                            return l_True;
                        }
                        else
                        {
                            assert( mCurrentAssignmentConsistent == UNKNOWN );
                            if( Settings::stop_search_after_first_unknown )
                                return l_Undef;
                            else
                            {
                                mExcludedAssignments = true;
                                learnt_clause.clear();
                                for( auto subformula = rPassedFormula().begin(); subformula != rPassedFormula().end(); ++subformula )
                                    learnt_clause.push( neg( getLiteral( subformula->formula() ) ) );
                                addClause( learnt_clause, LEMMA_CLAUSE );
								SMTRAT_LOG_DEBUG("smtrat.sat", "Storing lemmas");
                                confl = storeLemmas();
                                if( confl != CRef_Undef )
                                    unknown_excludes.push( confl );
                            }
                        }
                    }
                }
                if( mReceivedFormulaPurelyPropositional || Settings::stop_search_after_first_unknown || next != lit_Undef )
                {
                    // Increase decision level and enqueue 'next'
                    newDecisionLevel();
                    assert( value( next ) == l_Undef );
                    #ifdef DEBUG_SATMODULE
                    std::cout << "### Decide " <<  (sign(next) ? "-" : "" ) << var(next) << std::endl;
                    #endif
                    uncheckedEnqueue( next );
                }
            }
            if( confl != CRef_Undef )
            {
                // CONFLICT
                conflicts++;
                conflictC++;
                
                if( decisionLevel() <= assumptions.size() )
                {
                    if( !mReceivedFormulaPurelyPropositional && !Settings::stop_search_after_first_unknown && mExcludedAssignments )
                        return l_Undef;
                    return l_False;
                }

                handleConflict( confl );
            }
        }
    }
    
    template<class Settings>
    void SATModule<Settings>::handleConflict( CRef _confl )
    {
        learnt_clause.clear();
        assert( _confl != CRef_Undef );
		SMTRAT_LOG_DEBUG("smtrat.sat", "Conflict clause: " << _confl);

        int backtrack_level;
//        bool conflictClauseNotAsserting = analyze( _confl, learnt_clause, backtrack_level );
        analyze( _confl, learnt_clause, backtrack_level );
        assert( learnt_clause.size() > 0 );

        #ifdef DEBUG_SATMODULE
        printClause( learnt_clause, true, cout, "### Asserting clause: " );
        cout << "### Backtrack to level " << backtrack_level << endl;
        cout << "###" << endl;
        #endif
        cancelUntil( backtrack_level );

        #ifdef SMTRAT_DEVOPTION_Validation // this is often an indication that something is wrong with our theory, so we do store our assumptions.
        if( value( learnt_clause[0] ) != l_Undef ) Module::storeAssumptionsToCheck( *mpManager );
        #endif
        assert( value( learnt_clause[0] ) == l_Undef );
        if( learnt_clause.size() == 1 )
        {
            uncheckedEnqueue( learnt_clause[0] );
        }
        else
        {
            // learnt clause is the asserting clause.
            _confl = ca.alloc( learnt_clause, CONFLICT_CLAUSE );
            learnts.push( _confl );
            attachClause( _confl );
            claBumpActivity( ca[_confl] );
            uncheckedEnqueue( learnt_clause[0], _confl );
            decrementLearntSizeAdjustCnt();
        }

        varDecayActivity();
        claDecayActivity();
    }
    
    template<class Settings>
    void SATModule<Settings>::decrementLearntSizeAdjustCnt()
    {
        if( --learntsize_adjust_cnt == 0 )
        {
            learntsize_adjust_confl *= learntsize_adjust_inc;
            learntsize_adjust_cnt   = (int)learntsize_adjust_confl;
            max_learnts             *= learntsize_inc;

            if( verbosity >= 1 )
                printf( "| %9d | %7d %8d %8d | %8d %8d %6.0f | %6.3f %% |\n",
                        (int)conflicts,
                        (int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]),
                        nClauses(),
                        (int)clauses_literals,
                        (int)max_learnts,
                        nLearnts(),
                        (double)learnts_literals / nLearnts(),
                        progressEstimate() * 100 );
        }
    }
    
    template<class Settings>
    bool SATModule<Settings>::fullAssignment()
    {
        Var next = pickSplittingVar();
        if( next != var_Undef )
            return false;
        while( !order_heap.empty() && ((next = order_heap[0]) == var_Undef || value( next ) != l_Undef || !decision[next]) )
            order_heap.removeMin();
        return order_heap.empty();
    }
        
    template<class Settings>
    Var SATModule<Settings>::pickSplittingVar()
    {
        Var next = var_Undef;
        while( !mNewSplittingVars.empty() )
        {
            if( value( mNewSplittingVars.back() ) == l_Undef )
            {
                next = mNewSplittingVars.back();
                assert( decision[next] );
                return next;
            }
            mNewSplittingVars.pop_back();
        }
        return next;
    }

    template<class Settings>
    Lit SATModule<Settings>::pickBranchLit()
    {
        Var next = var_Undef;
        // Random decision:
        //        if( drand( random_seed ) < random_var_freq &&!order_heap.empty() )
        //        {
        //            next = order_heap[irand( random_seed, order_heap.size() )];
        //            if( value( next ) == l_Undef && decision[next] )
        //                rnd_decisions++;
        //        }
        // Check first, if a splitting decision has to be made.
        next = pickSplittingVar();
        if( next != var_Undef )
            mNewSplittingVars.pop_back();
        else
        {
            if( !mReceivedFormulaPurelyPropositional && Settings::check_active_literal_occurrences )
            {
                while( next == var_Undef && !mPropagationFreeDecisions.empty() )
                {
                    Lit l = mPropagationFreeDecisions.back();
                    mPropagationFreeDecisions.pop_back();
                    if( assigns[var(l)] == l_Undef )
                        return l;
                }
            }
            if( mReceivedFormulaPurelyPropositional || Settings::theory_conflict_guided_decision_heuristic == TheoryGuidedDecisionHeuristicLevel::DISABLED || mCurrentAssignmentConsistent != SAT )
            {
                // Activity based decision:
                while( next == var_Undef || value( next ) != l_Undef || !decision[next] )
                {
                    if( order_heap.empty() )
                    {
                        next = var_Undef;
                        break;
                    }
                    else
                        next = order_heap.removeMin();
                }
            }
            else
                return bestBranchLit();
        }
        return next == var_Undef ? lit_Undef : mkLit( next, polarity[next] );
        //return next == var_Undef ? lit_Undef : mkLit( next, rnd_pol ? drand( random_seed ) < 0.5 : polarity[next] );
    }
    
    template<class Settings>
    Lit SATModule<Settings>::bestBranchLit()
    {
        #ifdef DEBUG_SATMODULE_DECISION_HEURISTIC
        std::cout << __func__ << std::endl;
        #endif
        Var next = var_Undef;
        vec<Var> varsToRestore;
        #ifdef DEBUG_SATMODULE_DECISION_HEURISTIC
        Model bModel = backendsModel();
        std::cout << "Backend's model: " << std::endl << bModel << std::endl;
        #endif
        while( next == var_Undef || value( next ) != l_Undef || !decision[next] )
        {
            if( order_heap.empty() )
            {
                #ifdef DEBUG_SATMODULE_DECISION_HEURISTIC
                std::cout << "heap empty" << std::endl;
                #endif
                next = var_Undef;
                break;
            }
            else
            {
                next = order_heap.removeMin();
                #ifdef DEBUG_SATMODULE_DECISION_HEURISTIC
                std::cout << "consider variable " << next << std::endl;
                std::cout << "value( next ) == l_Undef: " << (value( next ) == l_Undef) << std::endl;
                std::cout << "decision[next] = " << (decision[next] ? "true" : "false") << std::endl;
                #endif
                if( value( next ) == l_Undef && decision[next] )
                {
                    const auto& abstrPair = mBooleanConstraintMap[next];
                    if( abstrPair.first != nullptr )
                    {
                        assert( abstrPair.second != nullptr );
                        if( Settings::check_active_literal_occurrences )
                        {
//                            const auto& litActOccs = mLiteralsActivOccurrences[(size_t)next];
//                            takeNegation = litActOccs.second > litActOccs.first;
                        }
                        const Abstraction& abstr = *abstrPair.first;
                        #ifdef DEBUG_SATMODULE_DECISION_HEURISTIC
                        std::cout << "corresponds to constraint: " << abstr.reabstraction << std::endl;
                        #endif
                        unsigned consistency = currentlySatisfiedByBackend( abstr.reabstraction );
                        #ifdef DEBUG_SATMODULE_DECISION_HEURISTIC
                        std::cout << "consistency = " << consistency << std::endl;
                        #endif
                        bool skipVariable = false;
                        switch( Settings::theory_conflict_guided_decision_heuristic )
                        {
                            case TheoryGuidedDecisionHeuristicLevel::CONFLICT_FIRST:
                            {
                                switch( consistency )
                                {
                                    case 0:
                                        polarity[next] = false;
                                        break;
                                    case 1:
                                        polarity[next] = true;
                                        break;
                                    default:
                                        skipVariable = true;
                                        break;
                                }
                                break;
                            }
                            case TheoryGuidedDecisionHeuristicLevel::SATISFIED_FIRST:
                            {
                                switch( consistency )
                                {
                                    case 0:
                                        polarity[next] = true;
                                        break;
                                    case 1:
                                        polarity[next] = false;
                                        break;
                                    default:
                                        skipVariable = true;
                                        break;
                                }
                                break;
                            }
                            default:
                                assert( Settings::theory_conflict_guided_decision_heuristic == TheoryGuidedDecisionHeuristicLevel::DISABLED );
                                break;
                        }
                        if( skipVariable )
                        {
                            #ifdef DEBUG_SATMODULE_DECISION_HEURISTIC
                            std::cout << "store variable for restorage" << std::endl;
                            #endif
                            varsToRestore.push(next);
                            next = var_Undef;
                        }
                    }
                }
            }
        }
        for( int pos = 0; pos < varsToRestore.size(); ++pos )
        {
            #ifdef DEBUG_SATMODULE_DECISION_HEURISTIC
            std::cout << "restore to heap: " << varsToRestore[pos] << std::endl;
            #endif
            insertVarOrder( varsToRestore[pos] );
        }
        if( next == var_Undef )
        {
            if( !order_heap.empty() )
            {
                next = order_heap.removeMin();
                assert( value( next ) == l_Undef );
                assert( decision[next] );
            }
        }
        return next == var_Undef ? lit_Undef : mkLit( next, polarity[next] );
    }
    
    template<class Settings>
    bool SATModule<Settings>::analyze( CRef confl, vec<Lit>& out_learnt, int& out_btlevel )
    {
		assert( confl != CRef_Undef );
        int pathC = 0;
        int resolutionSteps = -1;
        Lit p = lit_Undef;

        // Generate conflict clause:
        //
        out_learnt.push();    // (leave room for the asserting literal)
        int index = trail.size() - 1;

        do
        {
            assert( confl != CRef_Undef );    // (otherwise should be UIP)
            Clause& c = ca[confl];
            if( c.learnt() )
                claBumpActivity( c );

            for( int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++ )
            {
                Lit q = c[j];
                
                if( !seen[var( q )] && level( var( q ) ) > 0 )
                {
                    varBumpActivity( var( q ) );
                    seen[var( q )] = 1;
                    if( level( var( q ) ) >= decisionLevel() )
                        pathC++;
                    else
                        out_learnt.push( q );
                }
            }

            // Select next clause to look at:
            while( !seen[var( trail[index--] )] );
            p              = trail[index + 1];
            confl          = reason( var( p ) );
            seen[var( p )] = 0;
            pathC--;
            ++resolutionSteps;
        }
        while( pathC > 0 );
        out_learnt[0] = ~p;

        // Simplify conflict clause:
        //
        int i, j;
        out_learnt.copyTo( analyze_toclear );
        if( ccmin_mode == 2 )
        {
            uint32_t abstract_level = 0;
            for( i = 1; i < out_learnt.size(); i++ )
                abstract_level |= abstractLevel( var( out_learnt[i] ) );    // (maintain an abstraction of levels involved in conflict)

            for( i = j = 1; i < out_learnt.size(); i++ )
                if( reason( var( out_learnt[i] ) ) == CRef_Undef ||!litRedundant( out_learnt[i], abstract_level ) )
                    out_learnt[j++] = out_learnt[i];

        }
        else if( ccmin_mode == 1 )
        {
            for( i = j = 1; i < out_learnt.size(); i++ )
            {
                Var x = var( out_learnt[i] );

                if( reason( x ) == CRef_Undef )
                    out_learnt[j++] = out_learnt[i];
                else
                {
                    Clause& c = ca[reason( var( out_learnt[i] ) )];
                    for( int k = 1; k < c.size(); k++ )
                        if( !seen[var( c[k] )] && level( var( c[k] ) ) > 0 )
                        {
                            out_learnt[j++] = out_learnt[i];
                            break;
                        }
                }
            }
        }
        else
            i = j = out_learnt.size();

        max_literals += (uint64_t)out_learnt.size();
        out_learnt.shrink( i - j );
        tot_literals += (uint64_t)out_learnt.size();

        // Find correct backtrack level:
        //
        if( out_learnt.size() == 1 )
            out_btlevel = 0;
        else
        {
            int max_i = 1;
            // Find the first literal assigned at the next-highest level:
            for( int i = 2; i < out_learnt.size(); i++ )
                if( level( var( out_learnt[i] ) ) > level( var( out_learnt[max_i] ) ) )
                    max_i = i;
            // Swap-in this literal at index 1:
            Lit p             = out_learnt[max_i];
            out_learnt[max_i] = out_learnt[1];
            out_learnt[1]     = p;
            out_btlevel       = level( var( p ) );
        }

        for( int j = 0; j < analyze_toclear.size(); j++ )
            seen[var( analyze_toclear[j] )] = 0;    // ('seen[]' is now cleared)
        return resolutionSteps > 0;
    }

    template<class Settings>
    bool SATModule<Settings>::litRedundant( Lit p, uint32_t abstract_levels )
    {
        analyze_stack.clear();
        analyze_stack.push( p );
        int top = analyze_toclear.size();
        while( analyze_stack.size() > 0 )
        {
            CRef c_reason = reason(var(analyze_stack.last()));
            assert( c_reason != CRef_Undef );
            Clause& c = ca[c_reason];
            int c_size = c.size();
            analyze_stack.pop();

            for( int i = 1; i < c_size; i++ )
            {
                Lit p  = ca[c_reason][i];
                if( !seen[var( p )] && level( var( p ) ) > 0 )
                {
                    if( reason( var( p ) ) != CRef_Undef && (abstractLevel( var( p ) ) & abstract_levels) != 0 )
                    {
                        seen[var( p )] = 1;
                        analyze_stack.push( p );
                        analyze_toclear.push( p );
                    }
                    else
                    {
                        for( int j = top; j < analyze_toclear.size(); j++ )
                            seen[var( analyze_toclear[j] )] = 0;
                        analyze_toclear.shrink( analyze_toclear.size() - top );
                        return false;
                    }
                }
            }
        }

        return true;
    }

    template<class Settings>
    void SATModule<Settings>::uncheckedEnqueue( Lit p, CRef from )
    {
        #ifdef DEBUG_SATMODULE
        cout << __func__ << " " << (sign(p) ? "-" : "") << var(p) << "  from " << from << endl;
        #endif
        assert( value( p ) == l_Undef );
        if( Settings::check_if_all_clauses_are_satisfied && !mReceivedFormulaPurelyPropositional && mNumberOfSatisfiedClauses < (size_t)clauses.size() )
        {
            auto litClausesIter = mLiteralClausesMap.find( Minisat::toInt( p ) );
            if( litClausesIter != mLiteralClausesMap.end() )
            {
                for( CRef cl : litClausesIter->second )
                {
                    if( !satisfied( ca[cl] ) )
                    {
                        assert( mNumberOfSatisfiedClauses < (size_t)clauses.size() );
                        ++mNumberOfSatisfiedClauses;
                    }
                }
            }
        }
        if( !mReceivedFormulaPurelyPropositional && Settings::check_active_literal_occurrences )
        {
            // Check clauses which are going to be satisfied by this assignment.
            size_t v = (size_t)var(p);
            const std::vector<CRef>& nowSatisfiedClauses = sign(p) ? mLiteralsClausesMap[v].negatives() : mLiteralsClausesMap[v].positives();
            for( CRef cr : nowSatisfiedClauses )
            {
                const Clause& c = ca[cr];
                // Check if clause is not yet satisfied.
                if( !satisfied(c) )
                {
                    for( int i = 0; i < c.size(); ++i )
                    {
                        size_t v = (size_t)var(c[i]);
                        std::pair<size_t,size_t>& litActOccs = mLiteralsActivOccurrences[v];
                        if( sign(c[i]) )
                        {
                            assert( litActOccs.second > 0 );
                            --(litActOccs.second);
                        }
                        else
                        {
                            assert( litActOccs.first > 0 );
                            --(litActOccs.first);
                        }
                        if( litActOccs.first == 0 )
                        {
                            if( litActOccs.second == 0 )
                                decision[var(c[i])] = false;
                            else
                                mPropagationFreeDecisions.push_back( mkLit( var(c[i]), true ) );
                        }
                        else
                        {
                            if( litActOccs.second == 0 )
                                mPropagationFreeDecisions.push_back( mkLit( var(c[i]), false ) );
                        }
                    }
                }
            }
        }
        assigns[var( p )] = lbool( !sign( p ) );
        if( !mReceivedFormulaPurelyPropositional && mBooleanConstraintMap[var( p )].first != nullptr )
        {
            assert( mBooleanConstraintMap[var( p )].second != nullptr );
            Abstraction& abstr = sign( p ) ? *mBooleanConstraintMap[var( p )].second : *mBooleanConstraintMap[var( p )].first;
            if( !abstr.reabstraction.isTrue() && abstr.consistencyRelevant && (abstr.reabstraction.getType() == carl::FormulaType::UEQ || abstr.reabstraction.getType() == carl::FormulaType::BITVECTOR || abstr.reabstraction.constraint().isConsistent() != 1)) 
            {
                if( ++abstr.updateInfo > 0 )
                {
                    unsigned res = currentlySatisfiedByBackend( abstr.reabstraction );
                    if( res != 1 )
                    {
                        mCurrentAssignmentConsistent = UNKNOWN;
                    }
                    mChangedBooleans.push_back( var( p ) );
                }
            }
            vardata[var( p )] = VarData( from, decisionLevel(), trail.size() );
            trail.push_( p );
        }
        else
        {
            vardata[var( p )] = VarData( from, decisionLevel(), trail.size() );
            trail.push_( p );
        }

        // Save reasons (clauses) implicating a variable value
        if (isLemmaLevel(LemmaLevel::NORMAL) && decisionLevel() == 0 && !mComputeAllSAT)
        {
            if ( from != CRef_Undef) {
                // Find corresponding formula
                auto iter = mClauseInformation.find( from );
                assert( iter != mClauseInformation.end() );
                FormulaT formula = iter->second.mOrigins.back();
                assert( formula.propertyHolds(carl::PROP_IS_A_CLAUSE) && formula.propertyHolds(carl::PROP_CONTAINS_BOOLEAN) );

                // Get lemmas for variable
                // Notice: new pair is inserted if not already contained
                FormulasT* pFormulas = &mPropagatedLemmas[ var(p) ];
                // Insert reason for variable
                pFormulas->push_back( formula );

                // Find formulas for contained variables
                carl::Variables vars;
                formula.booleanVars(vars);
                for ( carl::Variables::const_iterator iter = vars.begin(); iter != vars.end(); ++iter )
                {
                    BooleanVarMap::const_iterator itVar = mBooleanVarMap.find( *iter );
                    assert( itVar != mBooleanVarMap.end() );
                    Minisat::Var var = itVar->second;
                    // Find possible formulas for variable
                    VarLemmaMap::const_iterator itFormulas = mPropagatedLemmas.find( var );
                    if ( itFormulas != mPropagatedLemmas.end() )
                    {
                        // Insert formulas from contained variable into set for current variable
                        pFormulas->insert( pFormulas->end(), itFormulas->second.begin(), itFormulas->second.end() );
                    }
                }
            }
        }
        if( !mReceivedFormulaPurelyPropositional && Settings::formula_guided_decision_heuristic )
        {
            auto iter = mTseitinVarShadows.find( (signed) var(p) );
            if( iter != mTseitinVarShadows.end() )
            {
                for( signed var : iter->second )
                {
                    incrementTseitinShadowOccurrences(var);
                }
            }
        }
    }

    template<class Settings>
    CRef SATModule<Settings>::propagate()
    {
        #ifdef DEBUG_SATMODULE
		cout << "######################################################################" << endl;
        cout << "### Propagate" << endl;
        cout << "### qhead = " << qhead << endl;
		cout << "### trail = " << trail << endl;
        cout << "### trail.size() = " << trail.size() << endl;
		cout << "### trail_lim = " << trail_lim << endl;
		//cout << "### theory stack = " << mTheoryVariableStack << endl;
		cout << "###" << endl; printBooleanConstraintMap(cout, "###");
		cout << "###" << endl; printClauses( clauses, "Clauses", cout, "### ", 0, false, false );
		cout << "###" << endl; printClauses( learnts, "Learnts", cout, "### ", 0, false, false );
		cout << "###" << endl; printCurrentAssignment( cout, "### " );
		cout << "###" << endl; printDecisions( cout, "### " );
		cout << "###" << endl;
        #endif
        CRef confl = CRef_Undef;
        int num_props = 0;
        watches.cleanAll();

        while( qhead < trail.size() )
        {
            Lit p = trail[qhead++];    // 'p' is enqueued fact to propagate.
            vec<Watcher>& ws = watches[p];
            Watcher * i, *j, *end;
            num_props++;
			SMTRAT_LOG_DEBUG("smtrat.sat", "Current literal: " << p);

            for( i = j = (Watcher*)ws, end = i + ws.size(); i != end; )
            {
                // Try to avoid inspecting the clause:
                Lit blocker = i->blocker;
                if( value( blocker ) == l_True )
                {
                    *j++ = *i++;
                    continue;
                }

                // Make sure the false literal is data[1]:
                CRef cr = i->cref;
                Clause& c = ca[cr];
                Lit false_lit = ~p;
                if( c[0] == false_lit )
                    c[0]              = c[1], c[1] = false_lit;
                assert( c[1] == false_lit );
                i++;

                // If 0th watch is true, then clause is already satisfied.
                Lit first = c[0];
                Watcher w = Watcher( cr, first );
                if( first != blocker && value( first ) == l_True )
                {
                    *j++ = w;
                    continue;
                }

                // Look for new watch:
                for( int k = 2; k < c.size(); k++ )
                    if( value( c[k] ) != l_False )
                    {
                        c[1] = c[k];
                        c[k] = false_lit;
                        watches[~c[1]].push( w );
                        goto NextClause;
                    }

                // Did not find watch -- clause is unit under assignment:
                *j++ = w;
                if( value( first ) == l_False )
                {
                    confl = cr;
                    qhead = trail.size();
                    // Copy the remaining watches:
                    while( i < end )
                        *j++ = *i++;
                }
                else
                {
                    assert( value( first ) == l_Undef );
                    uncheckedEnqueue( first, cr );
                    #ifdef SMTRAT_DEVOPTION_Statistics
                    mpStatistics->propagate();
                    #endif
                }

NextClause:
                ;
            }
            ws.shrink( (int) (i - j) );
        }
        propagations += (uint64_t)num_props;
//        simpDB_props -= (uint64_t)num_props;
        return confl;
    }

    struct reduceDB_lt
    {
        ClauseAllocator& ca;

        reduceDB_lt( ClauseAllocator& ca_ ):
            ca( ca_ )
        {}
        bool operator ()( CRef x, CRef y )
        {
            return ca[x].size() > 2 && (ca[y].size() == 2 || ca[x].activity() < ca[y].activity());
        }
    };

    template<class Settings>
    void SATModule<Settings>::reduceDB()
    {
        int    i, j;
        double extra_lim = cla_inc / learnts.size();    // Remove any clause below this activity

        sort( learnts, reduceDB_lt( ca ) );
        // Don't delete binary or locked clauses. From the rest, delete clauses from the first half
        // and clauses with activity smaller than 'extra_lim':
        for( i = j = 0; i < learnts.size(); i++ )
        {
            Clause& c = ca[learnts[i]];
            if( c.type() != PERMANENT_CLAUSE && c.size() > 2 && !locked( c ) && (i < learnts.size() / 2 || c.activity() < extra_lim) )
//            if( c.size() > 2 && !locked( c ) && (i < learnts.size() / 2 || c.activity() < extra_lim) )
            {
                removeClause( learnts[i] );
            }
            else
                learnts[j++] = learnts[i];
        }
        learnts.shrink( i - j );
        checkGarbage();
    }
	
    template<class Settings>
    void SATModule<Settings>::clearLearnts( int n )
    {
        for( int i = n; i < learnts.size(); ++i )
        {
            removeClause( learnts[i] );
        }
        learnts.shrink( learnts.size() - n );
    }

    template<class Settings>
    void SATModule<Settings>::removeSatisfied( vec<CRef>& cs )
    {
        int i, j;
        for( i = j = 0; i < cs.size(); i++ )
        {
            Clause& c = ca[cs[i]];
            if( satisfied( c ) )
                removeClause( cs[i] );
            else
                cs[j++] = cs[i];
        }
        cs.shrink( i - j );
    }

    template<class Settings>
    void SATModule<Settings>::rebuildOrderHeap()
    {
        vec<Var> vs;
        for( Var v = 0; v < nVars(); v++ )
            if( decision[v] && value( v ) == l_Undef )
                vs.push( v );
        order_heap.build( vs );
    }

    template<class Settings>
    void SATModule<Settings>::simplify()
    {
        assert( decisionLevel() == assumptions.size() );
        #ifdef DEBUG_SATMODULE
        std::cout << __func__ << std::endl;
        #endif
        while( ok )
        {
            if( propagate() != CRef_Undef )
            {
				SMTRAT_LOG_DEBUG("smtrat.sat", "ok = false");
                ok = false;
                return;
            }
            if( nAssigns() == simpDB_assigns )// || (simpDB_props > 0) )
            {
                return;
            }
            // Remove satisfied clauses:
            removeSatisfied( learnts );
            if( remove_satisfied )    // Can be turned off.
                removeSatisfied( clauses );
            // @todo: free somehow splitting variables, which are assigned in decision level 0 (aka assumption.size())
            checkGarbage();
            rebuildOrderHeap();
            simpDB_assigns = nAssigns();
//            simpDB_props   = (int64_t)(clauses_literals + learnts_literals);    // (shouldn't depend on stats really, but it will do for now)
            processLemmas();
        }
    }

    template<class Settings>
    bool SATModule<Settings>::processLemmas()
    {
        bool lemmasLearned = false;
        std::vector<Module*>::const_iterator backend = usedBackends().begin();
        while( backend != usedBackends().end() )
        {
            // Learn the lemmas.
            (*backend)->updateLemmas();
            if( !(mCurrentAssignmentConsistent == SAT && fullAssignment()) )
            {
                for( const auto& lem : (*backend)->lemmas() )
                {
                    if( lem.mLemma.getType() != carl::FormulaType::TRUE )
                    {
                        #ifdef DEBUG_SATMODULE_THEORY_PROPAGATION
                        cout << "Learned a theory lemma from a backend module!" << endl;
                        cout << lem.mLemma.toString( false, 0, "", true, true, true ) << endl;
                        #endif
                        #ifdef SMTRAT_DEVOPTION_Validation
                        if( validationSettings->logLemmata() )
                            addAssumptionToCheck( FormulaT( carl::FormulaType::NOT, lem.mLemma ), false, (*backend)->moduleName() + "_lemma" );
                        #endif
                        int numOfLearnts = mLemmas.size();
                        /*{
                            std::lock_guard<std::mutex> lock( Module::mOldSplittingVarMutex );
                            std::cout << __func__ << ":" << __LINE__ << ": " << (*backend)->moduleName() << " (" <<(*backend)->id() << ")" << std::endl;
                            std::cout << lem.mLemma << std::endl;
                        }*/
                        addClauses( lem.mLemma, lem.mLemmaType == LemmaType::PERMANENT ? PERMANENT_CLAUSE : LEMMA_CLAUSE );
                        if( numOfLearnts < mLemmas.size() )
                            lemmasLearned = true;
                    }
                }
            }
            (*backend)->clearLemmas();
            ++backend;
        }
        return lemmasLearned;
    }
    
    template<class Settings>
    void SATModule<Settings>::learnTheoryConflicts()
    {
        std::vector<Module*>::const_iterator backend = usedBackends().begin();
        while( backend != usedBackends().end() )
        {
            const std::vector<FormulaSetT>& infSubsets = (*backend)->infeasibleSubsets();
            assert( (*backend)->solverState() != UNSAT || !infSubsets.empty() );
            for( auto infsubset = infSubsets.begin(); infsubset != infSubsets.end(); ++infsubset )
            {
                assert( !infsubset->empty() );
                #ifdef SMTRAT_DEVOPTION_Validation
                if( validationSettings->logInfSubsets() )
                    addAssumptionToCheck( *infsubset, false, (*backend)->moduleName() + "_infeasible_subset" );
                #endif
                #ifdef DEBUG_SATMODULE
                for( const auto& iss : (*backend)->infeasibleSubsets() )
                {
                    cout << " {";
                    for( const auto& infSubFormula : iss )
                        cout << " " << infSubFormula.toString( false, 0, "", true, true, true ) << std::endl;
                    cout << " }";
                }
                std::cout << std::endl;
                #endif
                // Add the according literals to the conflict clause.
                vec<Lit> explanation;
                bool containsUpperBoundOnMinimal = false;
                for( auto subformula = infsubset->begin(); subformula != infsubset->end(); ++subformula )
                {
                    if( mUpperBoundOnMinimal != passedFormulaEnd() && mUpperBoundOnMinimal->formula() == *subformula )
                    {
                        containsUpperBoundOnMinimal = true;
                        continue;
                    }
                    // add literal to clause
                    explanation.push( neg( getLiteral( *subformula ) ) );
                }
                addClause( explanation, containsUpperBoundOnMinimal ? PERMANENT_CLAUSE : CONFLICT_CLAUSE );
            }
            ++backend;
        }
    }
    
    template<class Settings>
    void SATModule<Settings>::adaptConflictEvaluation( size_t& _clauseEvaluation, Lit _lit, bool _firstLiteral )
    {
        switch( Settings::conflict_clause_evaluation_strategy )
        {
            case CCES::SECOND_LEVEL_MINIMIZER:
            {
                size_t litLevel = (size_t) level( var( _lit ) );
                if( _firstLiteral || litLevel > _clauseEvaluation )
                    _clauseEvaluation = litLevel;
                break;
            }
            case CCES::LITERALS_BLOCKS_DISTANCE:
            {
                if( _firstLiteral )
                {
                    mLevelCounter.clear();
                    _clauseEvaluation = 0;
                }
                if( mLevelCounter.insert( level( var( _lit ) ) ).second )
                    ++_clauseEvaluation;
                break;
            }
            case CCES::SECOND_LEVEL_MINIMIZER_PLUS_LBD:
            {
                size_t litLevel = (size_t) level( var( _lit ) ) * (size_t) decisionLevel();
                if( _firstLiteral )
                {
                    mLevelCounter.clear();
                    mLevelCounter.insert( level( var( _lit ) ) );
                    _clauseEvaluation = litLevel + 1;
                }
                else
                {
                    bool levelAdded = mLevelCounter.insert( level( var( _lit ) ) ).second;
                    if( litLevel > _clauseEvaluation )
                        _clauseEvaluation = litLevel + mLevelCounter.size();
                    else if( levelAdded )
                        ++_clauseEvaluation;
                }
                break;
            }
            default:
            {
                assert( false );
            }
        }
    }

    template<class Settings>
    double SATModule<Settings>::progressEstimate() const
    {
        double progress = 0;
        double F        = 1.0 / nVars();

        for( int i = 0; i <= decisionLevel(); i++ )
        {
            int beg = i == 0 ? 0 : trail_lim[i - 1];
            int end = i == decisionLevel() ? trail.size() : trail_lim[i];
            progress += pow( F, i ) * (end - beg);
        }

        return progress / nVars();
    }

    template<class Settings>
    void SATModule<Settings>::relocAll( ClauseAllocator& to )
    {
        // relocate clauses in mFormulaClausesMap
        for( auto& iter : mFormulaCNFInfosMap )
        {
            std::vector<CRef> tmp;
            for( CRef c : iter.second.mClauses )
            {
                ca.reloc( c, to );
                tmp.insert( tmp.end(), c );
            }
            iter.second.mClauses = std::move( tmp );
        }
        
        carl::FastMap<Minisat::CRef,ClauseInformation> tmp;
        for( auto& ciPair : mClauseInformation )
        {
            CRef c = ciPair.first;
            ca.reloc( c, to );
            tmp.emplace( c, ciPair.second );
        }
        mClauseInformation = std::move( tmp );
        
        if( Settings::check_if_all_clauses_are_satisfied )
        {
            for( auto& lcsPair : mLiteralClausesMap )
            {
                std::unordered_set<CRef>& cls = lcsPair.second;
                std::unordered_set<CRef> tmp;
                for( CRef c : cls )
                {
                    ca.reloc( c, to );
                    tmp.insert( tmp.end(), c );
                }
                cls = std::move(tmp);
            }
        }
        
        if( !mReceivedFormulaPurelyPropositional && Settings::check_active_literal_occurrences )
        {
            for( auto& cls : mLiteralsClausesMap )
            {
                cls.reloc( ca, to );
            }
        }
        
        // All watchers:
        //
        // for (int i = 0; i < watches.size(); i++)
        watches.cleanAll();
        for( int v = 0; v < nVars(); v++ )
            for( int s = 0; s < 2; s++ )
            {
                Lit p = mkLit( v, s );
                // printf(" >>> RELOCING: %s%d\n", sign(p)?"-":"", var(p)+1);
                vec<Watcher>& ws = watches[p];
                for( int j = 0; j < ws.size(); j++ )
                    ca.reloc( ws[j].cref, to );
            }

        // All reasons:
        //
        for( int i = 0; i < trail.size(); i++ )
        {
            Var v = var( trail[i] );

            if( reason( v ) != CRef_Undef && (ca[reason( v )].reloced() || locked( ca[reason( v )] )) )
                ca.reloc( vardata[v].reason, to );
        }

        // All learnt:
        //
        for( int i = 0; i < learnts.size(); i++ )
            ca.reloc( learnts[i], to );

        // All original:
        //
        for( int i = 0; i < clauses.size(); i++ )
            ca.reloc( clauses[i], to );
    }

    template<class Settings>
    void SATModule<Settings>::garbageCollect()
    {
        // Initialize the next region to a size corresponding to the estimated utilization degree. This
        // is not precise but should avoid some unnecessary reallocations for the new region:
        ClauseAllocator to(ca.size() > ca.wasted() ? ca.size() - ca.wasted() : 0 );

        relocAll( to );
        if( verbosity >= 2 )
            printf( "|  Garbage collection:   %12d bytes => %12d bytes             |\n",
                    ca.size() * ClauseAllocator::Unit_Size,
                    to.size() * ClauseAllocator::Unit_Size );
        to.moveTo( ca );
    }

    template<class Settings>
    Var SATModule<Settings>::mapVar( Var x, vec<Var>& map, Var& max )
    {
        if( map.size() <= x || map[x] == -1 )
        {
            map.growTo( x + 1, -1 );
            map[x] = max++;
        }
        return map[x];
    }
    
    #ifdef DEBUG_METHODS_SATMODULE
    template<class Settings>
    void SATModule<Settings>::print( ostream& _out, const string _init ) const
    {
        printConstraintLiteralMap( _out, _init );
        printBooleanVarMap( _out, _init );
        printBooleanConstraintMap( _out, _init );
        printConstraintLiteralMap( _out, _init );
        printBooleanConstraintMap( _out, _init );
        printBooleanVarMap( _out, _init );
        printClauses( clauses, "Clauses", _out, _init );
        printClauses( learnts, "Learnts", _out, _init );
        printDecisions( _out, _init );
        printPassedFormula( _init );
        for(int i = 0; i < vardata.size(); i++ )
            _out << _init << i << " -> " << ((uint32_t) vardata[i].reason) << endl;
    }

    template<class Settings>
    void SATModule<Settings>::printConstraintLiteralMap( ostream& _out, const string _init ) const
    {
        _out << _init << " ConstraintLiteralMap" << endl;
        for( ConstraintLiteralsMap::const_iterator clPair = mConstraintLiteralMap.begin(); clPair != mConstraintLiteralMap.end(); ++clPair )
        {
            _out << _init << "    " << clPair->first.toString() << "  ->  [";
            for( auto litIter = clPair->second.begin(); litIter != clPair->second.end(); ++litIter )
            {
                _out << " ";
                if( sign( *litIter ) )
                {
                    _out << "-";
                }
                _out << var( *litIter );
            }
            _out << " ]" << endl;
        }
    }
    
    template<class Settings>
    void SATModule<Settings>::printFormulaCNFInfosMap( ostream& _out, const string _init ) const
    {
        _out << _init << " FormulaCNFInfosMap" << endl;
        for( const auto& fcsPair : mFormulaCNFInfosMap )
        {
            _out << _init << "    " << fcsPair.first << std::endl;
            _out << _init << "        Literal: ";
            toString( _out, fcsPair.second.mLiteral );
            _out << std::endl;
            _out << _init << "        Counter: " << fcsPair.second.mCounter << std::endl;
            _out << _init << "        {";
            for( auto cref : fcsPair.second.mClauses )
                _out << " " << cref;
            _out << " }" << std::endl;
        }
    }
    
    template<class Settings>
    void SATModule<Settings>::printClauseInformation( ostream& _out, const string _init ) const
    {
        _out << _init << " ClauseInformation" << endl;
        for( auto& ciPair : mClauseInformation )
        {
            _out << _init << "    " << ciPair.first << " -> (stored in satisfied: " << (ciPair.second.mStoredInSatisfied ? "yes" : "no") << ", position: " << ciPair.second.mPosition << ")" << std::endl;
        }
    }

    template<class Settings>
    void SATModule<Settings>::printBooleanVarMap( ostream& _out, const string _init ) const
    {
        _out << _init << " BooleanVarMap" << endl;
        for( BooleanVarMap::const_iterator clPair = mBooleanVarMap.begin(); clPair != mBooleanVarMap.end(); ++clPair )
        {
            _out << _init << "    " << clPair->first << "  ->  " << clPair->second;
            auto tvfIter = mTseitinVarFormulaMap.find( (int)clPair->second );
            if( tvfIter != mTseitinVarFormulaMap.end() )
                _out << "   ( " << tvfIter->second << " )";
            _out << endl;
        }
    }

    template<class Settings>
    void SATModule<Settings>::printBooleanConstraintMap( ostream& _out, const string _init ) const
    {
        _out << _init << " BooleanConstraintMap" << endl;
        for( int k = 0; k < mBooleanConstraintMap.size(); ++k )
        {
            if( mBooleanConstraintMap[k].first != nullptr )
            {
                assert( mBooleanConstraintMap[k].second != nullptr );
                _out << _init << "   " << k << "  ->  " << mBooleanConstraintMap[k].first->reabstraction;
                _out << "  (" << setw( 7 ) << activity[k] << ") [" << mBooleanConstraintMap[k].first->updateInfo << "]" << endl;
                _out << _init << "  ~" << k << "  ->  " << mBooleanConstraintMap[k].second->reabstraction;
                _out << "  (" << setw( 7 ) << activity[k] << ") [" << mBooleanConstraintMap[k].second->updateInfo << "]" << endl;
            }
        }
    }

    template<class Settings>
    void SATModule<Settings>::printClause( const vec<Lit>& _clause, bool _withAssignment, ostream& _out, const string& _init ) const
    {
        _out << _init;
        for( int pos = 0; pos < _clause.size(); ++pos )
        {
            _out << " ";
            toString( _out, _clause[pos] );
            if( _withAssignment )
                _out << "(" << (value( _clause[pos] ) == l_True ? "true" : (value( _clause[pos] ) == l_False ? "false" : "undef")) << "@" << level( var( _clause[pos] ) ) << ")";
        }
        _out << endl;
    }

    template<class Settings>
    void SATModule<Settings>::printClause( CRef _clause, bool _withAssignment, ostream& _out, const string& _init ) const
    {
        const Clause& c = ca[_clause];
        _out << _init;
        for( int pos = 0; pos < c.size(); ++pos )
        {
            _out << " ";
            toString( _out, c[pos] );
            if( _withAssignment )
            {
                _out << " [" << (value( c[pos] ) == l_True ? "true@" : (value( c[pos] ) == l_False ? "false@" : "undef"));
                if( value( c[pos] ) != l_Undef )
                {
                    _out << level( var( c[pos] ) );
                }
                _out << "]";
            }
        }
        _out << "  [" << ((uint32_t) _clause) << "]" << endl;
    }

    template<class Settings>
    void SATModule<Settings>::printClauses( const vec<CRef>& _clauses, const string _name, ostream& _out, const string _init, int _from, bool _withAssignment, bool _onlyNotSatisfied ) const
    {
        _out << _init << " " << _name << ":" << endl;
        // Handle case when solver is in contradictory state:
        if( !ok )
        {
            _out << _init << "  p cnf 1 2" << endl;
            _out << _init << "  1 0" << endl;
            _out << _init << "  -1 0" << endl;
            return;
        }

        vec<Var> map;
        Var max = 0;

        // Cannot use removeClauses here because it is not safe
        // to deallocate them at this point. Could be improved.
        int cnt = 0;
        for( int i = _from; i < _clauses.size(); i++ )
            if( !satisfied( ca[_clauses[i]] ) )
                cnt++;

        for( int i = _from; i < _clauses.size(); i++ )
            if( !satisfied( ca[_clauses[i]] ) )
            {
                const Clause& c = ca[_clauses[i]];
                for( int j = 0; j < c.size(); j++ )
                    if( value( c[j] ) != l_False )
                        mapVar( var( c[j] ), map, max );
            }

        // Assumptions are added as unit clauses:
        cnt += assumptions.size();

        _out << _init << "  p cnf " << max << " " << cnt << std::endl;

        for( int i = 0; i < assumptions.size(); i++ )
        {
//            assert( isLemmaLevel(LemmaLevel::ADVANCED) || value( assumptions[i] ) != l_False );
            _out << _init << "  " << (sign( assumptions[i] ) ? "-" : "") << var( assumptions[i] ) << std::endl;//(mapVar( var( assumptions[i] ), map, max )) << endl;
        }

        for( int i = _from; i < _clauses.size(); i++ )
        {
            if( !_onlyNotSatisfied || !satisfied(ca[_clauses[i]]) )
            {
                _out << _init << i;
                if( !_onlyNotSatisfied )
                    _out << (satisfied(ca[_clauses[i]]) ? " (ok)" : "     ");
                _out << ": ";
                printClause( _clauses[i], _withAssignment, _out, ""  );
                
            }
        }

        if( verbosity > 0 )
            _out << _init << "  Wrote " << cnt << " clauses with " << max << " variables." << std::endl;
    }

    template<class Settings>
    void SATModule<Settings>::printCurrentAssignment( ostream& _out, string _init ) const
    {
        _out << _init << " Assignments:  ";
        for( int pos = 0; pos < assigns.size(); ++pos )
        {
            if( pos > 0 )
            {
                _out << _init << "               ";
            }
            _out << setw( 5 ) << pos;
            _out << "  (" << setw( 7 ) << activity[pos] << ") " << " -> ";
            if( assigns[pos] == l_True )
            {
                _out << "l_True";
                // if it is not a Boolean variable
                if( mBooleanConstraintMap[pos].first != nullptr && mBooleanConstraintMap[pos].first->consistencyRelevant )
                    _out << "   ( " << mBooleanConstraintMap[pos].first->reabstraction << " )";
                else
                {
                    auto tvfIter = mTseitinVarFormulaMap.find( pos );
                    if( tvfIter != mTseitinVarFormulaMap.end() )
                        _out << "   ( " << tvfIter->second << " )";
                }
                _out << endl;
            }
            else if( assigns[pos] == l_False )
            {
                _out << "l_False";
                // if it is not a Boolean variable
                if( mBooleanConstraintMap[pos].second != nullptr && mBooleanConstraintMap[pos].second->consistencyRelevant )
                    _out << "   ( " << mBooleanConstraintMap[pos].second->reabstraction << " )";
                else
                {
                    auto tvfIter = mTseitinVarFormulaMap.find( pos );
                    if( tvfIter != mTseitinVarFormulaMap.end() )
                        _out << "   ( " << tvfIter->second.negated() << " )";
                }
                _out << endl;
            }
            else
            {
                _out << "l_Undef" << endl;
            }
        }
    }

    template<class Settings>
    void SATModule<Settings>::printDecisions( ostream& _out, string _init ) const
    {
        _out << _init << " Decisions:  ";
        int level = 0;
        for( int pos = 0; pos < trail.size(); ++pos )
        {
            if( level < trail_lim.size() )
            {
                if( pos == trail_lim[level] )
                {
                    ++level;
                }
            }
            if( pos > 0 )
            {
                _out << _init << "             ";
            }
            stringstream tmpStream;
            tmpStream << (sign( trail[pos] ) ? "-" : "") << var( trail[pos] );
            _out << setw( 6 ) << tmpStream.str() << " @ " << level;
            // if it is not a Boolean variable
            if( assigns[var(trail[pos])] == l_True && mBooleanConstraintMap[var(trail[pos])].first != nullptr && mBooleanConstraintMap[var(trail[pos])].first->consistencyRelevant  )
            {
                _out << "   ( " << mBooleanConstraintMap[var(trail[pos])].first->reabstraction << " )";
                _out << " [" << mBooleanConstraintMap[var(trail[pos])].first->updateInfo << "]";
            }
            else if( assigns[var(trail[pos])] == l_False && mBooleanConstraintMap[var(trail[pos])].second != nullptr && mBooleanConstraintMap[var(trail[pos])].second->consistencyRelevant  )
            {
                _out << "   ( " << mBooleanConstraintMap[var(trail[pos])].second->reabstraction << " )";
                _out << " [" << mBooleanConstraintMap[var(trail[pos])].second->updateInfo << "]";
            }
            _out << endl;
        }
    }
    #endif

    template<class Settings>
    void SATModule<Settings>::printPropagatedLemmas( ostream& _out, string _init ) const
    {
        _out << _init << " Propagated lemmas:" << endl;
        for( VarLemmaMap::const_iterator itFormulas = mPropagatedLemmas.begin(); itFormulas != mPropagatedLemmas.end(); ++itFormulas )
        {
            auto mvIter = mMinisatVarMap.find(itFormulas->first);
            assert( mvIter != mMinisatVarMap.end() );
            _out << _init << " " << mvIter->second << " <- { ";
            FormulasT formulas = itFormulas->second;
            for ( FormulasT::iterator iter = formulas.begin(); iter != formulas.end(); ++iter )
            {
                if ( iter != formulas.begin() )
                {
                    _out << ", ";
                }
                _out << *iter;
            }
            _out << " }" << endl;
        }
    }
    
    template<class Settings>
    void SATModule<Settings>::printLiteralsActiveOccurrences( ostream& _out, string _init ) const
    {
        _out << _init << "Literals' active occurrences:" << std::endl;
        for( std::size_t pos = 0; pos < mLiteralsActivOccurrences.size(); ++pos )
            _out << _init << "   " << pos << " -> " << mLiteralsActivOccurrences[pos] << std::endl;
    }

    template<class Settings>
    void SATModule<Settings>::collectStats()
    {
        #ifdef SMTRAT_DEVOPTION_Statistics
        mpStatistics->rNrTotalVariablesAfter() = (size_t) nVars();
        mpStatistics->rNrClauses() = (size_t) nClauses();
        #endif
    }
}    // namespace smtrat

#include "Instantiation.h"
