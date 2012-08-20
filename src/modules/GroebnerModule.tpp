/*
 *  SMT-RAT - Satisfiability-Modulo-Theories Real Algebra Toolbox
 * Copyright (C) 2012 Florian Corzilius, Ulrich Loup, Erika Abraham, Sebastian Junges
 *
 * This file is part of SMT-RAT.
 *
 * SMT-RAT is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMT-RAT is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with SMT-RAT.  If not, see <http://www.gnu.org/licenses/>.
 *
 */


/**
 * @file   GroebnerModule.cpp
 * 
 * @author Sebastian Junges
 * @author Ulrich Loup
 *
 * @version 2012-03-20
 */
#include "../config.h"


#include "NSSModule/definitions.h"
#include "GroebnerModule.h"
#include "GBModule/GBModuleStatistics.h"
#ifdef USE_NSS
#include "NSSModule/GroebnerToSDP.h"
#endif


using std::set;
using GiNaC::ex_to;

using GiNaCRA::VariableListPool;
using GiNaCRA::MultivariatePolynomialMR;

namespace smtrat
{

template<class Settings>
GroebnerModule<Settings>::GroebnerModule( Manager * const _tsManager, const Formula * const _formula ) :
Module( _tsManager, _formula ),

mBasis( ),
mInequalities( this ),
mStateHistory( )
#ifdef GATHER_STATS
    , mStats(GroebnerModuleStats::getInstance(Settings::identifier))
#endif

{
    mModuleType = MT_GroebnerModule;
    mPopCausesRecalc = false;
    pushBacktrackPoint( mpReceivedFormula->end( ) );
}

template<class Settings>
GroebnerModule<Settings>::~GroebnerModule( )
{
}

/**
 * Adds the constraint to the known constraints of the module. 
 * This includes scanning variables as well as transforming inequalities, if this is enabled.
 * @param _formula A REALCONSTRAINT which should be regarded by the next theory call.
 * @return true
 */
template<class Settings>
bool GroebnerModule<Settings>::assertSubformula( Formula::const_iterator _formula )
{
    assert( (*_formula)->getType( ) == REALCONSTRAINT );
    Module::assertSubformula( _formula );

    const Constraint& constraint = (*_formula)->constraint( );

    for( GiNaC::symtab::const_iterator it = constraint.variables( ).begin( ); it != constraint.variables( ).end( ); ++it )
    {
        VariableListPool::addVariable( ex_to<symbol > (it->second) );
        mListOfVariables.insert( *it );
    }
    
    #ifdef GATHER_STATS
    mStats->constraintAdded(constraint.relation());
    #endif
    //only equalities should be added to the gb
    if( constraint.relation( ) == CR_EQ )
    {
        pushBacktrackPoint( _formula );
        mBasis.addPolynomial( Polynomial( constraint.lhs( ) ) );
        saveState( );

        if( !Settings::passGB )
        {
            addReceivedSubformulaToPassedFormula( _formula );
        }
    }
    else 
    {
        
        if( Settings::transformIntoEqualities == ALL_INEQUALITIES ||
                (Settings::transformIntoEqualities == ONLY_NONSTRICT && (constraint.relation( ) == CR_GEQ || constraint.relation( ) == CR_LEQ)) )
        {
            assert( Settings::transformIntoEqualities != NO_INEQUALITIES );
            pushBacktrackPoint( _formula );
            mBasis.addPolynomial( transformIntoEquality( _formula ) );
            saveState( );

            if( !Settings::passGB )
            {
                addReceivedSubformulaToPassedFormula( _formula );
            }
        }
        else if( Settings::checkInequalities == NEVER )
        {
            addReceivedSubformulaToPassedFormula( _formula );
        }
        else
        {
            mNewInequalities.push_back( mInequalities.InsertReceivedFormula( _formula ) );
        }
    }
    return true;
}

/**
 * A theory call to the GroebnerModule. The exact working of this module depends on the settings in GBSettings.
 * @return (TRUE,FALSE,UNKNOWN) dependent on the asserted constraints.
 */
template<class Settings>
Answer GroebnerModule<Settings>::isConsistent( )
{
    // This check asserts that all the conflicts are handled by the SAT solver. (workaround)
    if( !mInfeasibleSubsets.empty() ) return False;
    
    #ifdef GATHER_STATS
    mStats->called();
    #endif
    
    assert( mBacktrackPoints.size( ) - 1 == mBasis.nrOriginalConstraints( ) );
    assert( mInfeasibleSubsets.empty( ) );
 
    if( !mBasis.inputEmpty( ) )
    {
        //first, we interreduce the input!
        mBasis.reduceInput( );
    }

    //If no equalities are added, we do not know anything 
    if( !mBasis.inputEmpty( ) || (mPopCausesRecalc && mBasis.nrOriginalConstraints( ) > 0) )
    {
        mPopCausesRecalc = false;
        //now, we calculate the groebner basis
        mBasis.calculate( );
        
        Polynomial witness;

#ifdef USE_NSS
        // On linear systems, all solutions lie in Q. So we do not have to check for a solution.
        if( Settings::applyNSS && !mBasis.isConstant( ) && !mBasis.getGbIdeal( ).isLinear( ) )
        {
            std::cout << "NSS?";
            // Lets search for a witness. We only have to do this if the gb is non-constant.

            std::set<unsigned> variables;
            std::set<unsigned> allVars = mBasis.getGbIdeal( ).gatherVariables( );
            std::set<unsigned> superfluous = mBasis.getGbIdeal( ).getSuperfluousVariables( );
            std::set_difference( allVars.begin( ), allVars.end( ),
                                 superfluous.begin( ), superfluous.end( ),
                                 std::inserter( variables, variables.end( ) ) );

            unsigned vars = variables.size( );
            // We currently only try with a low nr of variables.
            if( vars < Settings::SDPupperBoundNrVariables )
            {
                std::cout << " Run SDP";

                GroebnerToSDP<typename Settings::Order> sdp( mBasis.getGbIdeal( ), MonomialIterator( variables, Settings::maxSDPdegree ) );
                witness = sdp.findWitness( );
            }
            std::cout << std::endl;
            if( !witness.isZero( ) ) std::cout << "Found witness: " << witness << std::endl;
        }
        // We have found an infeasible subset. Generate it.
#endif
        if( mBasis.isConstant( ) || (Settings::applyNSS && !witness.isZero( )) )
        {
            if( mBasis.isConstant( ) )
            {
                #ifdef GATHER_STATS
                mStats->constantGB();
                #endif
                witness = mBasis.getGb( ).front( );
            }
            else
            {
                typename Settings::Reductor red( mBasis.getGbIdeal( ), witness );
                witness = red.fullReduce( );
                std::cout << witness << std::endl;
                assert( witness.isZero( ) );
            }
            mInfeasibleSubsets.push_back( set<const Formula*>() );
            // The equalities we used for the basis-computation are the infeasible subset

            GiNaCRA::BitVector::const_iterator origIt = witness.getOrigins( ).getBitVector( ).begin( );
            auto it = mBacktrackPoints.begin( );
            for( ++it; it != mBacktrackPoints.end( ); ++it )
            {
                assert( (**it)->getType( ) == REALCONSTRAINT );
                assert( Settings::transformIntoEqualities != NO_INEQUALITIES || (**it)->constraint( ).relation( ) == CR_EQ );
                               
                if( Settings::getReasonsForInfeasibility )
                {
                    if( origIt.get( ) )
                    {
                        mInfeasibleSubsets.back( ).insert( **it );
                    }
                    origIt++;
                }
                else
                {
                    mInfeasibleSubsets.back( ).insert( **it );
                }
            }
            
            #ifdef GATHER_STATS
            mStats->EffectivenessOfConflicts(mInfeasibleSubsets.back().size()/mpReceivedFormula->size());
            #endif
            return False;
        }
        saveState( );

        if( Settings::checkInequalities != NEVER )
        {
            Answer ans = mInequalities.reduceWRTGroebnerBasis( mBasis.getGbIdeal( ) );
            mNewInequalities.clear( );
            if( ans != Unknown )
            {
                return ans;
            }
        }
        assert( mInfeasibleSubsets.empty( ) );

        if( Settings::passGB )
        {
            for( Formula::iterator i = mpPassedFormula->begin( ); i != mpPassedFormula->end( ); )
            {
                assert( (*i)->getType( ) == REALCONSTRAINT );
                if( (*i)->constraint( ).relation( ) == CR_EQ )
                {
                    i = super::removeSubformulaFromPassedFormula( i );
                }
                else
                {
                    ++i;
                }
            }
            passGB( );
        }
    }
    else if( Settings::checkInequalities == ALWAYS )
    {
        Answer ans = mInequalities.reduceWRTGroebnerBasis( mNewInequalities, mBasis.getGbIdeal( ) );
        mNewInequalities.clear( );
        if( ans != Unknown ) return ans;
    }

    Answer ans = runBackends( );
    if( ans == False )
    {
        #ifdef GATHER_STATS
        mStats->backendFalse();
        #endif
        getInfeasibleSubsets( );

        assert( !mInfeasibleSubsets.empty( ) );
    }

    return ans;
}

/**
 * Removes the constraint from the GBModule.
 * Notice: Whenever a constraint is removed which was not asserted before, this leads to an unwanted error.
 *    A general approach for this has to be found.
 * @param _formula the constraint which should be removed.
 */
template<class Settings>
void GroebnerModule<Settings>::removeSubformula( Formula::const_iterator _formula )
{
    #ifdef GATHER_STATS
    mStats->constraintRemoved((*_formula)->constraint().relation());
    #endif
    if( Settings::transformIntoEqualities == ALL_INEQUALITIES )
    {
        popBacktrackPoint( _formula );
    }
    else if( Settings::transformIntoEqualities == ONLY_NONSTRICT && (*_formula)->constraint( ).relation( ) != CR_GREATER && (*_formula)->constraint( ).relation( ) != CR_LESS )
    {
        popBacktrackPoint( _formula );
    }
    else if( (*_formula)->constraint( ).relation( ) == CR_EQ )
    {
        popBacktrackPoint( _formula );
    }
    else
    {
        if( Settings::checkInequalities != NEVER )
        {
            mInequalities.removeInequality( _formula );
        }
    }
    super::removeSubformula( _formula );
}

/**
 * To implement backtrackability, we save the current state after each equality we add.
 * @param btpoint The equality we have removed
 */
template<class Settings>
void GroebnerModule<Settings>::pushBacktrackPoint( Formula::const_iterator btpoint )
{
    assert( mBacktrackPoints.empty( ) || (*btpoint)->getType( ) == REALCONSTRAINT );
    assert( mBacktrackPoints.size( ) == mStateHistory.size( ) );
  
    if( !mBacktrackPoints.empty( ) )
    {
        saveState( );
    }
    mBacktrackPoints.push_back( btpoint );
    mStateHistory.push_back( GroebnerModuleState<Settings>( mBasis ) );
    assert( mBacktrackPoints.size( ) == mStateHistory.size( ) );

    if( Settings::checkInequalities != NEVER )
    {
        mInequalities.pushBacktrackPoint( );
    }
}


/**
 * Pops all states from the stack until the state which we had before the constraint was added. 
 * Then, we make new states with all equalities which were added afterwards.
 * @param a pointer in the received formula to the constraint which will be removed. 
 */
template<class Settings>
void GroebnerModule<Settings>::popBacktrackPoint( Formula::const_iterator btpoint )
{
    assert( validityCheck( ) );
    assert( mBacktrackPoints.size( ) == mStateHistory.size( ) );
    assert( !mBacktrackPoints.empty( ) );

    // We have to do a consistency check
    mPopCausesRecalc = true;

    //We first count how far we have to backtrack.
    unsigned nrOfBacktracks = 1;
    while( !mBacktrackPoints.empty( ) )
    {
        if( mBacktrackPoints.back( ) == btpoint )
        {
            mBacktrackPoints.pop_back( );
            break;
        }
        ++nrOfBacktracks;
        mBacktrackPoints.pop_back( );
    }
    
    #ifdef GATHER_STATS
    mStats->PopLevel(nrOfBacktracks);
    #endif 

    for( unsigned i = 0; i < nrOfBacktracks; ++i )
    {
        assert( !mStateHistory.empty( ) );
        mStateHistory.pop_back( );
    }
    assert( mBacktrackPoints.size( ) == mStateHistory.size( ) );
    assert( !mStateHistory.empty( ) );

    // Load the state to be restored;
    mBasis = mStateHistory.back( ).getBasis( );
    assert( mBasis.nrOriginalConstraints( ) == mBacktrackPoints.size( ) - 1 );

    if( Settings::checkInequalities != NEVER )
    {
        mInequalities.popBacktrackPoint( nrOfBacktracks );
    }

    //We should not add this one again (it is the end)
    btpoint++;
    //Add all others
    for( Formula::const_iterator it = btpoint; it != mpReceivedFormula->end( ); ++it )
    {
        assert( (*it)->getType( ) == REALCONSTRAINT );
        Constraint_Relation relation = (*it)->constraint( ).relation( );
        bool isInGb = Settings::transformIntoEqualities == ALL_INEQUALITIES || relation == CR_EQ
                || (Settings::transformIntoEqualities == ONLY_NONSTRICT && relation != CR_GREATER && relation != CR_LESS);
        if( isInGb )
        {
            pushBacktrackPoint( it );
            mBasis.addPolynomial( relation == CR_EQ ? Polynomial( (*it)->constraint( ).lhs( ) ) : transformIntoEquality( it ) );
            // and save them
            saveState( );
        }
    }
    assert( mBasis.nrOriginalConstraints( ) == mBacktrackPoints.size( ) - 1 );
}

/**
 * Transforms a given inequality to a polynomial such that p = 0 is equivalent to the given constraint.
 * This is done by inserting an additional variable which has an index which is given by the id of the given inequality.
 * @param constraint a pointer to the inequality
 * @return The polynomial which represents the equality.
 */
template<class Settings>
typename GroebnerModule<Settings>::Polynomial GroebnerModule<Settings>::transformIntoEquality( Formula::const_iterator constraint )
{
    Polynomial result( (*constraint)->constraint( ).lhs( ) );
    unsigned constrId = (*constraint)->constraint( ).id( );
    std::map<unsigned, unsigned>::const_iterator mapentry = mAdditionalVarMap.find( constrId );
    unsigned varNr;
    if( mapentry == mAdditionalVarMap.end( ) )
    {
        std::stringstream stream;
        stream << "_AddVarGB_" << constrId;
        GiNaC::symbol varSym = ex_to<symbol > (Formula::newVariable( stream.str( ) ));
        mListOfVariables[stream.str()] = varSym;
        varNr = VariableListPool::addVariable( varSym );
        mAdditionalVarMap.insert(std::pair<unsigned, unsigned>(constrId, varNr));
    }
    else
    {
        varNr = mapentry->second;
    }
    
    switch( (*constraint)->constraint( ).relation( ) )
    {
    case CR_GEQ:
        result = result + GiNaCRA::MultivariateTermMR( -1, varNr, 2 );
        break;
    case CR_LEQ:
        result = result + GiNaCRA::MultivariateTermMR( 1, varNr, 2 );
        break;
    case CR_GREATER:
        result = result * GiNaCRA::MultivariateTermMR( 1, varNr, 2 );
        result = result + GiNaCRA::MultivariateTermMR( -1 );
        break;
    case CR_LESS:
        result = result * GiNaCRA::MultivariateTermMR( 1, varNr, 2 );
        result = result + GiNaCRA::MultivariateTermMR( 1 );
        break;
    default:
        assert( false );
    }
    return result;
}

/**
 * 
 * @return 
 */
template<class Settings>
bool GroebnerModule<Settings>::saveState( )
{
    assert( mStateHistory.size( ) == mBacktrackPoints.size( ) );
    mStateHistory.pop_back( );
    mStateHistory.push_back( GroebnerModuleState<Settings>( mBasis ) );

    return true;
}

/**
 * Add the equalities from the Groebner basis to the passed formula. Adds the reason vector.
 */
template<class Settings>
void GroebnerModule<Settings>::passGB( )
{
    assert( Settings::passGB );
    vec_set_const_pFormula originals;
    originals.push_back( set<const Formula*>() );

    if( !Settings::passWithMinimalReasons )
    {
        // find original constraints which made the gb.
        for( Formula::const_iterator it = mpReceivedFormula->begin( ); it != mpReceivedFormula->end( ); ++it )
        {
            if( Settings::transformIntoEqualities == ALL_INEQUALITIES )
            {
                originals.front( ).insert( *it );
            }
            else if( Settings::transformIntoEqualities == ONLY_NONSTRICT && (*it)->constraint( ).relation( ) != CR_GREATER && (*it)->constraint( ).relation( ) != CR_LESS )
            {
                originals.front( ).insert( *it );
            }
            else if( (*it)->constraint( ).relation( ) == CR_EQ )
            {
                originals.front( ).insert( *it );
            }
        }
    }

    // The gb should be passed
    std::list<Polynomial> simplified = mBasis.getGb( );
    for( typename std::list<Polynomial>::const_iterator simplIt = simplified.begin( ); simplIt != simplified.end( ); ++simplIt )
    {
        if( Settings::checkEqualitiesForTrivialSumOfSquares && simplIt->isTrivialSumOfSquares( ) ) std::cout << "Found trivial sum of square" << std::endl;
        if( Settings::passWithMinimalReasons )
        {
            originals.front( ) = generateReasons( simplIt->getOrigins( ).getBitVector( ) );
        }
        assert( !originals.front( ).empty( ) );
        addSubformulaToPassedFormula( new Formula( Formula::newConstraint( simplIt->toEx( ), CR_EQ ) ), originals );
    }
}

/**
 * Generate reason sets from reason vectors
 * @param reasons The reasons vector.
 * @return The reason set.
 */

template<class Settings>
std::set<const Formula*> GroebnerModule<Settings>::generateReasons( const GiNaCRA::BitVector& reasons )
{
    GiNaCRA::BitVector::const_iterator origIt = reasons.begin( );
    std::set<const Formula*> origins;

    auto it = mBacktrackPoints.begin( );
    for( ++it; it != mBacktrackPoints.end( ); ++it )
    {
        assert( (**it)->getType( ) == REALCONSTRAINT );
        assert( Settings::transformIntoEqualities != NO_INEQUALITIES || (**it)->constraint( ).relation( ) == CR_EQ );
        //                    
        if( origIt.get( ) )
        {
            origins.insert( **it );
        }
        origIt++;
    }
    return origins;

}

/**
 *  Prints the state history.
 */

template<class Settings>
void GroebnerModule<Settings>::printStateHistory( )
{
    std::cout << "[";
    auto btp = mBacktrackPoints.begin( );
    for( auto it = mStateHistory.begin( ); it != mStateHistory.end( ); ++it )
    {
        std::cout << **btp << ": ";
        it->getBasis( ).getGbIdeal( ).print( );
        std::cout << "," << std::endl;
        btp++;
    }
    std::cout << "]" << std::endl;
}

/**
 * A validity check of the data structures which can be used to assert valid behaviour.
 * @return true, iff the backtrackpoints are valid.
 */

template<class Settings>
bool GroebnerModule<Settings>::validityCheck( )
{
    auto btp = mBacktrackPoints.begin( );
    ++btp;
    for( auto it = mpReceivedFormula->begin( ); it != mpReceivedFormula->end( ); ++it )
    {
        bool isInGb = Settings::transformIntoEqualities == ALL_INEQUALITIES || (*it)->constraint( ).relation( ) == CR_EQ
                || (Settings::transformIntoEqualities == ONLY_NONSTRICT && (*it)->constraint( ).relation( ) != CR_GREATER && (*it)->constraint( ).relation( ) != CR_LESS);

        if( isInGb )
        {
            if( it != *btp )
            {
                print( );
                printStateHistory( );
                std::cout << *it << " != " << **btp << std::endl;
                return false;
            }
            ++btp;
        }
    }
    return true;
}

/**
 * This function is overwritten such that it is visible to the InequalitiesTable. For more details take a look at Module::removeSubformulaFromPassedFormula()
 * @param _formula
 */

template<class Settings>
void GroebnerModule<Settings>::removeSubformulaFromPassedFormula( Formula::iterator _formula )
{
    super::removeSubformulaFromPassedFormula( _formula );
}

/**
 * Initializes the inequalities table
 * @param module
 */
template<class Settings>
InequalitiesTable<Settings>::InequalitiesTable( GroebnerModule<Settings>* module ) : mModule( module )
{
    mBtnumber = 0;
    mNewConstraints = mReducedInequalities.begin( );
    #ifdef GATHER_STATS
    mStats = GroebnerModuleStats::getInstance(Settings::identifier);
    #endif 
}

/**
 * Adds the constraint as a row to the inequalities table.
 * @param received A pointer from the receivedFormula to the inequality.
 * @return The position in the inequalities table.
 */

template<class Settings>
typename InequalitiesTable<Settings>::Rows::iterator InequalitiesTable<Settings>::InsertReceivedFormula( Formula::const_iterator received )
{
    assert( (*received)->constraint().relation() != CR_EQ );
    mModule->addReceivedSubformulaToPassedFormula( received );
    // We assume that the just added formula is the last one.
    const Formula::iterator passedEntry = mModule->mpPassedFormula->last( );
    // And we add a row to our table
    return mReducedInequalities.insert( Row( received, RowEntry( passedEntry, (*received)->constraint( ).relation( ), std::list<CellEntry > (1, CellEntry( 0, Polynomial( (*received)->constraint( ).lhs( ) ) )) ) ) ).first;

}

/**
 * Informs the inequalities table that new reductions are with respect to the GB with the latest btpoint.
 */

template<class Settings>
void InequalitiesTable<Settings>::pushBacktrackPoint( )
{
    ++mBtnumber;
    if( Settings::setCheckInequalitiesToBeginAfter > 1 )
    {
        if( mLastRestart + Settings::setCheckInequalitiesToBeginAfter == mBtnumber )
        {
            mNewConstraints = mReducedInequalities.begin( );
        }
    }
}

/**
 * Clears cells from the inequalities table with backtrack points from the latest nrOfBacktracks many backtrackpoints.
 * Also updates the new backtracknumber.
 * @param nrOfBacktracks How many backtrack points are popped.
 */

template<class Settings>
void InequalitiesTable<Settings>::popBacktrackPoint( unsigned nrOfBacktracks )
{
    assert( mBtnumber >= nrOfBacktracks );
    mBtnumber -= nrOfBacktracks;
    for( auto it = mReducedInequalities.begin( ); it != mReducedInequalities.end( ); ++it )
    {
        typename std::list<CellEntry>::iterator listEnd = std::get < 2 > (it->second).end( );
        for( typename std::list<CellEntry>::iterator jt = std::get < 2 > (it->second).begin( ); jt != listEnd; ++jt )
        {
            if( jt->first > mBtnumber )
            {
                std::get < 2 > (it->second).erase( jt, listEnd );
                bool pass;
                if( Settings::passInequalities == FULL_REDUCED_IF )
                {
                    pass = Settings::passPolynomial::evaluate( std::get < 2 > (it->second).front( ).second, std::get < 2 > (it->second).back( ).second );
                }

                // what shall we pass
                if( Settings::passInequalities == AS_RECEIVED )
                {
                    if( std::get < 0 > (it->second) == mModule->mpPassedFormula->end( ) )
                    {
                        // we had reduced it to true, therefore not passed it, but now we have to pass the original one again.
                        mModule->addReceivedSubformulaToPassedFormula( it->first );
                        std::get < 0 > (it->second) = mModule->mpPassedFormula->last( );
                    }
                }
                else
                {
                    if( std::get < 0 > (it->second) != mModule->mpPassedFormula->end( ) )
                    {
                        // we can of course only remove something which is in the formula.
                        mModule->removeSubformulaFromPassedFormula( std::get < 0 > (it->second) );
                    }
                    if( Settings::passInequalities == FULL_REDUCED || (Settings::passInequalities == FULL_REDUCED_IF && pass) )
                    {
                        std::vector<std::set<const Formula*> > originals;
                        originals.push_back( mModule->generateReasons( std::get < 2 > (it->second).back( ).second.getOrigins( ).getBitVector( ) ) );
                        originals.front( ).insert( *(it->first) );
                        mModule->addSubformulaToPassedFormula( new Formula( Formula::newConstraint( std::get < 2 > (it->second).back( ).second.toEx( ), std::get < 1 > (it->second) ) ), originals );

                    }
                    else
                    {
                        assert( Settings::passInequalities == FULL_REDUCED_IF );
                        //we pass the original one.
                        mModule->addReceivedSubformulaToPassedFormula( it->first );
                    }
                    //update the reference to the passed formula again
                    std::get < 0 > (it->second) = mModule->mpPassedFormula->last( );
                }
                break;
            }
        }
    }
}

/**
 * Reduce all rows with respect to the given Groebner basis.
 * @param gb The groebner basis
 * @return If one of the inequalities yields a contradiction, False, else Unknown.
 */

template<class Settings>
Answer InequalitiesTable<Settings>::reduceWRTGroebnerBasis( const Ideal& gb )
{
    for( auto it = mReducedInequalities.begin( ); it != mReducedInequalities.end( ); ++it )
    {
        if( !reduceWRTGroebnerBasis( it, gb ) ) {
            #ifdef GATHER_STATS
            mStats->infeasibleInequality();
            #endif
            return False;   
        }
    }
    if( Settings::withInfeasibleSubset != RETURN_DIRECTLY )
    {
        if( mModule->mInfeasibleSubsets.empty( ) )
        {
            return Unknown;
        }
        else
        {
            #ifdef GATHER_STATS
            mStats->infeasibleInequality();
            #endif
            return False;
        }
    }
    else
    {
        return Unknown;
    }

}

/**
 * Reduce the given rows with respect to the given Groebner basis.
 * @param ineqToBeReduced A list of rows which should be updated.
 * @param gb The Groebner basis.
 * @return If one of the inequalities yields a contradiction, False, else Unknown.
 */

template<class Settings>
Answer InequalitiesTable<Settings>::reduceWRTGroebnerBasis( const std::list<typename Rows::iterator>& ineqToBeReduced, const Ideal& gb )
{
    for( auto it = ineqToBeReduced.begin( ); it != ineqToBeReduced.end( ); ++it )
    {
        assert( std::get < 1 > ((*it)->second) != CR_EQ );
        if( !reduceWRTGroebnerBasis( *it, gb ) ) {
            #ifdef GATHER_STATS
            mStats->infeasibleInequality();
            #endif
            return False;
        }
    }
    if( Settings::withInfeasibleSubset != RETURN_DIRECTLY )
    {
        if( mModule->mInfeasibleSubsets.empty( ) )
        {
            return Unknown;
        }
        else
        {
            #ifdef GATHER_STATS
            mStats->infeasibleInequality();
            #endif
            return False;
        }
    }
    else
    {
        return Unknown;
    }
}

/**
 * Reduce the given row with respect to the given Groebner basis.
 * @param ineqToBeReduced A pointer to the row which should be updated.
 * @param gb The Groebner basis.
 * @return If one of the inequalities yields a contradiction, False, else Unknown.
 */

template<class Settings>
bool InequalitiesTable<Settings>::reduceWRTGroebnerBasis( typename Rows::iterator it, const Ideal& gb )
{
    assert( std::get < 1 > (it->second) != CR_EQ );
    Polynomial& p = std::get < 2 > (it->second).back( ).second;
    Polynomial reduced;

    bool reductionOccured = false;
    if( !p.isZero( ) && !p.isConstant( ) )
    {
        GiNaCRA::BaseReductor<typename Settings::Order> reductor( gb, p );
        reduced = reductor.fullReduce( );
        reductionOccured = reductor.reductionOccured( );
    }

    Constraint_Relation relation = std::get < 1 > (it->second);
    if( reductionOccured )
    {
        if( reduced.isZero( ) || reduced.isConstant( ) )
        {
            bool satisfied = false;
            if( reduced.isZero( ) && !constraintRelationIsStrict( relation ) )
            {
                assert( !constraintRelationIsStrict( relation ) );
                satisfied = true;
            }
            else if( !reduced.isZero( ) )
            { // non zero
                assert( reduced.nrOfTerms( ) > 0 );
                assert( reduced.lcoeff( ) != 0 );

                const Rational reducedConstant = reduced.lcoeff( );
                assert( reducedConstant != 0 );
                if( reducedConstant < 0 )
                {
                    if( relation == CR_LESS || relation == CR_LEQ || relation == CR_NEQ )
                    {
                        satisfied = true;
                    }
                }
                else
                {
                    if( relation == CR_GREATER || relation == CR_GEQ || relation == CR_NEQ )
                    {
                        satisfied = true;
                    }
                }
            }

            if( satisfied )
            {
                mModule->removeSubformulaFromPassedFormula( std::get < 0 > (it->second) );

                std::get < 2 > (it->second).push_back( CellEntry( mBtnumber, reduced ) );
                std::set<const Formula*> originals( mModule->generateReasons( reduced.getOrigins( ).getBitVector( ) ) );

                std::get < 0 > (it->second) = mModule->mpPassedFormula->end( );
                if( Settings::addTheoryDeductions != NO_CONSTRAINTS )
                {
                    mModule->addDeduction( originals, &((*(it->first))->constraint( )) );
                }
            }
            else // we have a conflict
            {
                
                std::set<const Formula*> infeasibleSubset( mModule->generateReasons( reduced.getOrigins( ).getBitVector( ) ) );
                infeasibleSubset.insert( *(it->first) );
                #ifdef GATHER_STATS
                mStats->EffectivenessOfConflicts(infeasibleSubset.size()/mModule->mpReceivedFormula->size());
                #endif //GATHER_STATS
                mModule->mInfeasibleSubsets.push_back( infeasibleSubset );
                if( Settings::withInfeasibleSubset == RETURN_DIRECTLY )
                {
                    return false;
                }
            }
        }
        else if( Settings::withInfeasibleSubset == PROCEED_ALLINEQUALITIES || mModule->mInfeasibleSubsets.empty( ) )
        {
            if( Settings::checkEqualitiesForTrivialSumOfSquares && reduced.isTrivialSumOfSquares( ) ) std::cout << "Found trivial sum of square inequality" << std::endl;

            bool pass;
            if( Settings::passInequalities == FULL_REDUCED_IF )
            {
                pass = Settings::passPolynomial::evaluate( std::get < 2 > (it->second).front( ).second, reduced );
            }

            if( Settings::passInequalities == FULL_REDUCED || (Settings::passInequalities == FULL_REDUCED_IF && pass) )
            {
                //remove the last one
                mModule->removeSubformulaFromPassedFormula( std::get < 0 > (it->second) );
            }
            //add a new cell
            std::get < 2 > (it->second).push_back( CellEntry( mBtnumber, reduced ) );
            if( Settings::passInequalities == FULL_REDUCED || (Settings::passInequalities == FULL_REDUCED_IF && pass) )
            {
                // get the reason set for the reduced polynomial
                std::vector<std::set<const Formula*> > originals;
                originals.push_back( mModule->generateReasons( reduced.getOrigins( ).getBitVector( ) ) );
                originals.front( ).insert( *(it->first) );

                //pass the result
                mModule->addSubformulaToPassedFormula( new Formula( Formula::newConstraint( reduced.toEx( ), relation ) ), originals );
                //set the pointer to the passed formula accordingly.
                std::get < 0 > (it->second) = mModule->mpPassedFormula->last( );
            }
        }
    }
    return true;
}

/**
 * Removes the row corresponding to this constraint from the inequalities table.
 * @param _formula A pointer to the constraint in the receivedFormula which has to be removed.
 */

template<class Settings>
void InequalitiesTable<Settings>::removeInequality( Formula::const_iterator _formula )
{
    mReducedInequalities.erase( _formula );
    if( mNewConstraints != mReducedInequalities.end( ) && _formula == mNewConstraints->first )
    {
        ++mNewConstraints;
    }
}

/**
 * A print function for the inequalitiestable
 * @param os
 */

template<class Settings>
void InequalitiesTable<Settings>::print( std::ostream& os ) const
{
    std::cout << "Bt: " << mBtnumber << std::endl;
    for( auto it = mReducedInequalities.begin( ); it != mReducedInequalities.end( ); ++it )
    {
        typename std::list<CellEntry>::const_iterator listEnd = std::get < 2 > (it->second).end( );
        std::cout << *(it->first) << " -> " << *(std::get < 0 > (it->second)) << std::endl;
        for(typename std::list<CellEntry>::const_iterator jt = std::get < 2 > (it->second).begin( ); jt != listEnd; ++jt )
        {
            std::cout << "\t(" << jt->first << ") " << jt->second << std::endl;
        }
    }
}

} // namespace smtrat




