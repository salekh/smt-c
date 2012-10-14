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
 * @file Module.cpp
 *
 * @author Florian Corzilius
 * @author Ulrich Loup
 * @author Sebastian Junges
 * @since: 2012-01-18
 * @version: 2012-08-13
 */

#include "Module.h"
#include "ModuleFactory.h"
#include "Manager.h"
#include <limits.h>
#include <iostream>
#include <fstream>

/// Flag activating some informative and not exaggerated output about module calls.
//#define MODULE_VERBOSE

using namespace std;


namespace smtrat
{
    vector<string> Module::mAssumptionToCheck = vector<string>();
    set<string, strcomp> Module::mVariablesInAssumptionToCheck = set<string, strcomp>();

    Module::Module( Manager* const _tsManager, const Formula* const _formula ):
        mInfeasibleSubsets(),
        mpManager( _tsManager ),
        mModuleType( MT_Module ),
        mConstraintsToInform(),
        mpReceivedFormula( _formula ),
        mpPassedFormula( new Formula( AND ) ),
        mUsedBackends(),
        mAllBackends(),
        mPassedformulaOrigins(),
        mDeductions(),
        mFirstSubformulaToPass( mpPassedFormula->end() ),
        mFirstUncheckedReceivedSubformula( mpReceivedFormula->end() ),
        mSmallerMusesCheckCounter(0)
    {}

    Module::~Module()
    {
        delete mpPassedFormula;
    }

    /**
     * Checks the received formula for consistency.
     *
     * @return  TS_True,    if the received formula is consistent;
     *          TS_False,   if the received formula is inconsistent;
     *          TS_Unknown, otherwise.
     */
    Answer Module::isConsistent()
    {
        assert( mInfeasibleSubsets.empty() );

        Formula::const_iterator subformula = mpReceivedFormula->begin();
        for( Formula::const_iterator passedSubformula = mpPassedFormula->begin(); passedSubformula != mpPassedFormula->end(); ++passedSubformula )
        {
            assert( subformula != mpReceivedFormula->end() );
            ++subformula;
        }
        while( subformula != mpReceivedFormula->end() )
        {
            addReceivedSubformulaToPassedFormula( subformula++ );
        }

        Answer a = runBackends();
        if( a == False )
        {
            getInfeasibleSubsets();
        }
        return a;
    }

    /**
     * Removes a everything related to a sub formula of the received formula.
     *
     * @param _subformula The sub formula of the received formula to remove.
     */
    void Module::removeSubformula( Formula::const_iterator _receivedSubformula )
    {
        if( mFirstUncheckedReceivedSubformula == _receivedSubformula )
        {
            ++mFirstUncheckedReceivedSubformula;
        }

        /*
         * Check if the constraint to delete is an original constraint of constraints in the vector
         * of passed constraints.
         */
        for( Formula::iterator passedSubformula = mpPassedFormula->begin(); passedSubformula != mpPassedFormula->end(); )
        {
            /*
             * Remove the received formula from the set of origins.
             */
            vec_set_const_pFormula&          formulaOrigins = mPassedformulaOrigins[*passedSubformula];
            vec_set_const_pFormula::iterator formulaOrigin  = formulaOrigins.begin();
            while( formulaOrigin != formulaOrigins.end() )
            {
                /*
                 * If the received formula is in the set of origins, erase it.
                 */
                if( formulaOrigin->find( *_receivedSubformula ) != formulaOrigin->end() )
                {
                    // Erase the changed set.
                    formulaOrigin = formulaOrigins.erase( formulaOrigin );
                }
                else
                {
                    ++formulaOrigin;
                }
            }

            if( formulaOrigins.empty() )
            {
                passedSubformula = removeSubformulaFromPassedFormula( passedSubformula );
            }
            else
            {
                ++passedSubformula;
            }
        }

        /*
         * Delete all infeasible subsets in which the constraint to delete occurs.
         */
        vec_set_const_pFormula::iterator infSubSet = mInfeasibleSubsets.begin();
        while( infSubSet != mInfeasibleSubsets.end() )
        {
            set<const Formula*>::iterator infSubformula = infSubSet->begin();
            while( infSubformula != infSubSet->end() )
            {
                if( *infSubformula == *_receivedSubformula )
                {
                    break;
                }
                ++infSubformula;
            }
            if( infSubformula != infSubSet->end() )
            {
                infSubSet = mInfeasibleSubsets.erase( infSubSet );
            }
            else
            {
                ++infSubSet;
            }
        }
    }

    /**
     *
     * @param _subformula
     */
    void Module::addReceivedSubformulaToPassedFormula( Formula::const_iterator _subformula )
    {
        addSubformulaToPassedFormula( new Formula( **_subformula ), *_subformula );
    }

    /**
     *
     * @param _formula
     * @param _origins
     */
    void Module::addSubformulaToPassedFormula( Formula* _formula, const vec_set_const_pFormula& _origins )
    {
        assert( mpReceivedFormula->size() != UINT_MAX );
        mpPassedFormula->addSubformula( _formula );
        mPassedformulaOrigins[_formula] = _origins;
        if( mFirstSubformulaToPass == mpPassedFormula->end() )
        {
            mFirstSubformulaToPass = mpPassedFormula->last();
            assert( checkFirstSubformulaToPassValidity() );

        }
    }

    /**
     *
     * @param _formula
     * @param _origin
     */
    void Module::addSubformulaToPassedFormula( Formula* _formula, const Formula* _origin )
    {
        assert( mpReceivedFormula->size() != UINT_MAX );
        mpPassedFormula->addSubformula( _formula );
        vec_set_const_pFormula originals;
        originals.push_back( set<const Formula*>() );
        originals.front().insert( _origin );
        mPassedformulaOrigins[_formula] = originals;
        if( mFirstSubformulaToPass == mpPassedFormula->end() )
        {
            mFirstSubformulaToPass = mpPassedFormula->last();

            assert( checkFirstSubformulaToPassValidity() );
        }
    }

    /**
     *
     * @param _formula
     * @param _origins
     */
    void Module::setOrigins( const Formula* const _formula, vec_set_const_pFormula& _origins )
    {
        mPassedformulaOrigins[_formula] = _origins;
    }

    /**
     *
     * @param _subformula
     * @return
     */
    const std::set<const Formula*>& Module::getOrigins( Formula::const_iterator _subformula ) const
    {
        FormulaOrigins::const_iterator origins = mPassedformulaOrigins.find( *_subformula );
        assert( origins != mPassedformulaOrigins.end() );
        assert( origins->second.size() == 1 );
        return origins->second.front();
    }

    /**
     *
     * @param _subformula
     * @param _origins
     */
    void Module::getOrigins( const Formula* const _subformula, vec_set_const_pFormula& _origins ) const
    {
        FormulaOrigins::const_iterator origins = mPassedformulaOrigins.find( _subformula );
        assert( origins != mPassedformulaOrigins.end() );
        _origins = origins->second;
    }

    /**
     * Merges the two vectors of sets into the first one.
     *
     * ({a,b},{a,c}) and ({b,d},{b}) -> ({a,b,d},{a,b},{a,b,c,d},{a,b,c})
     *
     * @param _vecSetA  A vector of sets of constraints.
     * @param _vecSetB  A vector of sets of constraints.
     *
     * @result The vector being the two given vectors merged.
     */
    vec_set_const_pFormula Module::merge( const vec_set_const_pFormula& _vecSetA, const vec_set_const_pFormula& _vecSetB ) const
    {
        vec_set_const_pFormula result = vec_set_const_pFormula();
        vec_set_const_pFormula::const_iterator originSetA = _vecSetA.begin();
        while( originSetA != _vecSetA.end() )
        {
            vec_set_const_pFormula::const_iterator originSetB = _vecSetB.begin();
            while( originSetB != _vecSetB.end() )
            {
                result.push_back( set<const Formula*>( originSetA->begin(), originSetA->end() ) );
                result.back().insert( originSetB->begin(), originSetB->end() );
                ++originSetB;
            }
            ++originSetA;
        }
        return result;
    }

    /**
     * Provides some special case checks which can be executed at the start.
     *
     * @return
     */
    Answer Module::specialCaseConsistencyCheck() const
    {
        if( mpReceivedFormula->empty() )
        {
            return True;
        }
        return Unknown;
    }

    /**
     *
     */
    void Module::getInfeasibleSubsets()
    {
        vector<Module*>::const_iterator backend = mUsedBackends.begin();
        while( backend != mUsedBackends.end() )
        {
            if( !(*backend)->rInfeasibleSubsets().empty() )
            {
                mInfeasibleSubsets = getInfeasibleSubsets( **backend );
                return;
            }
            ++backend;
        }
    }

    /**
     * Get the infeasible subsets the given backend provides. Note, that an infeasible subset
     * in a backend contains sub formulas of the passed formula and an infeasible subset of
     * this module contains sub formulas of the received formula. In this method the LATTER is
     * returned.
     *
     * @param _backend  The backend from which to obtain the infeasible subsets.
     *
     * @return  The infeasible subsets the given backend provides.
     */
    vec_set_const_pFormula Module::getInfeasibleSubsets( const Module& _backend ) const
    {
        vec_set_const_pFormula result = vec_set_const_pFormula();
        const vec_set_const_pFormula& backendsInfsubsets = _backend.rInfeasibleSubsets();
        assert( !backendsInfsubsets.empty() );
        for( vec_set_const_pFormula::const_iterator infSubSet = backendsInfsubsets.begin(); infSubSet != backendsInfsubsets.end(); ++infSubSet )
        {
            assert( !infSubSet->empty() );
            #ifdef LOG_INFEASIBLE_SUBSETS
            addAssumptionToCheck( *infSubSet, false, moduleName( _backend.type() ) + "_infeasible_subset" );
            #endif
            result.push_back( set<const Formula*>() );
            for( set<const Formula*>::const_iterator cons = infSubSet->begin(); cons != infSubSet->end(); ++cons )
            {
                vec_set_const_pFormula formOrigins = vec_set_const_pFormula();
                getOrigins( *cons, formOrigins );

                /*
                 * Find the smallest set of origins.
                 */
                vec_set_const_pFormula::const_iterator smallestOriginSet = formOrigins.begin();
                vec_set_const_pFormula::const_iterator originSet         = formOrigins.begin();
                while( originSet != formOrigins.end() )
                {
                    if( originSet->size() == 1 )
                    {
                        smallestOriginSet = originSet;
                        break;
                    }
                    else if( originSet->size() < smallestOriginSet->size() )
                    {
                        smallestOriginSet = originSet;
                    }
                    ++originSet;
                }
                assert( smallestOriginSet != formOrigins.end() );

                /*
                 * Add its formulas to the infeasible subset.
                 */
                for( set<const Formula*>::const_iterator originFormula = smallestOriginSet->begin(); originFormula != smallestOriginSet->end();
                        ++originFormula )
                {
                    result.back().insert( *originFormula );
                }
            }
        }
        return result;
    }

    /**
     * Runs the backend solvers on the passed formula.
     *
     * @return  TS_True,    if the passed formula is consistent;
     *          TS_False,   if the passed formula is inconsistent;
     *          TS_Unknown, otherwise.
     */
    Answer Module::runBackends()
    {
        passedFormulaCannotBeSolved();

        mUsedBackends = mpManager->getBackends( mpPassedFormula, this );

        if( mFirstSubformulaToPass != mpPassedFormula->end() )
        {
            assert( checkFirstSubformulaToPassValidity() );
            bool assertionFailed = false;
            for( vector<Module*>::iterator module = mUsedBackends.begin(); module != mUsedBackends.end(); ++module )
            {
                for( Formula::const_iterator subformula = mFirstSubformulaToPass; subformula != mpPassedFormula->end(); ++subformula )
                {
                    if( !(*module)->assertSubformula( subformula ) )
                    {
                        assertionFailed = true;
                    }
                }
            }
            if( assertionFailed )
            {
                return False;
            }
        }
        mFirstSubformulaToPass = mpPassedFormula->end();
        Answer result          = Unknown;

        /*
         * Run the backend solver sequentially until the first answers true or false.
         */
        vector<Module*>::iterator module = mUsedBackends.begin();
        while( module != mUsedBackends.end() && result == Unknown )
        {
            #ifdef MODULE_VERBOSE
            cout << endl << "Call to module " << moduleName( (*module)->type() ) << endl;
            (*module)->print( cout, " ");
            #endif
            result = (*module)->isConsistent();
            (*module)->receivedFormulaChecked();
            #ifdef LOG_THEORY_CALLS
            if( result != Unknown )
            {
                addAssumptionToCheck( *mpPassedFormula, result == True, moduleName( (*module)->type() ) );
            }
            #endif
            ++module;
        }
        #ifdef MODULE_VERBOSE
        cout << "Result:   " << (result == True ? "True" : (result == False ? "False" : "Unknown")) << endl;
        #endif
        return result;
    }

    /**
     *
     * @param _subformula
     * @return
     */
    Formula::iterator Module::removeSubformulaFromPassedFormula( Formula::iterator _subformula )
    {
        assert( _subformula != mpPassedFormula->end() );
        if( _subformula == mFirstSubformulaToPass )
        {
            mFirstSubformulaToPass++;
        }

        /*
         * Delete the sub formula from the passed formula.
         */
        mAllBackends = mpManager->getAllBackends( this );
        for( vector<Module*>::iterator module = mAllBackends.begin(); module != mAllBackends.end(); ++module )
        {
            (*module)->removeSubformula( _subformula );
        }
        mPassedformulaOrigins.erase( *_subformula );
        return mpPassedFormula->erase( _subformula );
    }

    /**
     *
     * @param _subformula
     * @return
     */
    Formula::iterator Module::pruneSubformulaFromPassedFormula( Formula::iterator _subformula )
    {
        assert( _subformula != mpPassedFormula->end() );

        /*
         * Delete the sub formula from the passed formula.
         */
        mAllBackends = mpManager->getAllBackends( this );
        for( vector<Module*>::iterator module = mAllBackends.begin(); module != mAllBackends.end(); ++module )
        {
            (*module)->removeSubformula( _subformula );
        }
        mPassedformulaOrigins.erase( *_subformula );
        return mpPassedFormula->prune( _subformula );
    }

    /**
     *
     */
    void Module::updateDeductions()
    {
        for( vector<Module*>::iterator module = mUsedBackends.begin(); module != mUsedBackends.end(); ++module )
        {
            (*module)->updateDeductions();
            
            while( !(*module)->deductions().empty() )
            {
                addDeduction( (*module)->rDeductions().back() );
                #ifdef LOG_LEMMATA
                Formula notLemma = Formula( NOT );
                notLemma.addSubformula( new Formula( *(*module)->rDeductions().back() ) );
                addAssumptionToCheck( notLemma, false, moduleName( (*module)->type() ) + "_lemma" );
                notLemma.pruneBack();
                #endif
                (*module)->rDeductions().pop_back();
            }
        }
    }

    /**
     *
     * @return
     */
    bool Module::checkFirstSubformulaToPassValidity() const
    {
        for( Formula::const_iterator it = mpPassedFormula->begin(); it != mpPassedFormula->end(); ++it )
        {
            if( mFirstSubformulaToPass == it )
            {
                return true;
            }
        }
        return false;
    }

    /**
     * Add a formula to the assumption vector and its predetermined consistency status.
     * @param _formula
     * @param _consistent
     * @see Module::storeAssumptionsToCheck
     */
    void Module::addAssumptionToCheck( const Formula& _formula, bool _consistent, const string _moduleName )
    {
        string assumption = "";
        assumption += ( _consistent ? "(set-info :status sat)\n" : "(set-info :status unsat)\n");
        assumption += "(assert (and ";
        assumption += _formula.toString();
        assumption += " " + _moduleName;
        assumption += "))\n";
        assumption += "(get-assertions)\n";
        assumption += "(check-sat)\n";
        mAssumptionToCheck.push_back( assumption );
        mVariablesInAssumptionToCheck.insert( _moduleName );
    }

    /**
     * Add a conjunction of _constraints to the assumption vector and its predetermined consistency status.
     * @param _constraints
     * @param _consistent
     * @see Module::storeAssumptionsToCheck
     */
    void Module::addAssumptionToCheck( const set<const Formula*>& _formulas, bool _consistent, const string _moduleName )
    {
        string assumption = "";
        assumption += ( _consistent ? "(set-info :status sat)\n" : "(set-info :status unsat)\n");
        assumption += "(assert (and";
        for( set<const Formula*>::const_iterator formula = _formulas.begin();
             formula != _formulas.end(); ++formula )
        {
            assumption += " " + (*formula)->toString();
        }
        assumption += " " + _moduleName;
        assumption += "))\n";
        assumption += "(get-assertions)\n";
        assumption += "(check-sat)\n";
        mAssumptionToCheck.push_back( assumption );
        mVariablesInAssumptionToCheck.insert( _moduleName );
    }

    /**
     * Add a conjunction of _constraints to the assumption vector and its predetermined consistency status.
     * @param _constraints
     * @param _consistent
     * @see Module::storeAssumptionsToCheck
     */
    void Module::addAssumptionToCheck( const set<const Constraint*>& _constraints, bool _consistent, const string _moduleName )
    {
        string assumption = "";
        assumption += ( _consistent ? "(set-info :status sat)\n" : "(set-info :status unsat)\n");
        assumption += "(assert (and";
        for( set<const Constraint*>::const_iterator constraint = _constraints.begin();
             constraint != _constraints.end(); ++constraint )
        {
            assumption += " " + (*constraint)->smtlibString();
        }
        assumption += " " + _moduleName;
        assumption += "))\n";
        assumption += "(get-assertions)\n";
        assumption += "(check-sat)\n";
        mAssumptionToCheck.push_back( assumption );
        mVariablesInAssumptionToCheck.insert( _moduleName );
    }

    /**
     * Prints the collected assumptions in the assumption vector into _filename with an appropriate smt2 header including all variables used.
     * @param _filename
     */
    void Module::storeAssumptionsToCheck( const Manager& _manager, const string _filename )
    {
        if( !Module::mAssumptionToCheck.empty() )
        {
            ofstream smtlibFile;
            smtlibFile.open( _filename );
            for( vector< string >::const_iterator assum = Module::mAssumptionToCheck.begin();
                 assum != Module::mAssumptionToCheck.end(); ++assum )
            { // for each assumption add a new solver-call by resetting the search state
                smtlibFile << "(reset)\n";
                smtlibFile << "(set-logic QF_NRA)\n";
                smtlibFile << "(set-option :interactive-mode true)\n";
                smtlibFile << "(set-info :smt-lib-version 2.0)\n";
                // add all real-valued variables
                for( GiNaC::symtab::const_iterator var = Formula::mConstraintPool.variables().begin();
                    var != Formula::mConstraintPool.variables().end(); ++var )
                {
                    smtlibFile << "(declare-fun " << var->first << " () Real)\n";
                }
                // add all Boolean variables
                for( auto var = _manager.formula().booleanVars().begin(); var != _manager.formula().booleanVars().end(); ++var )
                {
                    smtlibFile << "(declare-fun " << *var << " () Bool)\n";
                }
                // add all Boolean auxiliary variables
                for( unsigned auxIndex = 0; auxIndex < Formula::mAuxiliaryBooleanCounter; ++auxIndex )
                {
                    smtlibFile << "(declare-fun " << Formula::mAuxiliaryBooleanNamePrefix << auxIndex << " () Bool)\n";
                }
                // add module name variables
                for( set<string, strcomp>::const_iterator involvedModule = Module::mVariablesInAssumptionToCheck.begin();
                     involvedModule != Module::mVariablesInAssumptionToCheck.end(); ++involvedModule )
                {
                    smtlibFile << "(declare-fun " << *involvedModule << " () Bool)\n";
                }
                smtlibFile << *assum;
            }
            smtlibFile << "(exit)";
            smtlibFile.close();
        }
    }

    /**
     * Store subsets as smt2 files in order to check them later.
     * @param
     * @param
     */
    void Module::storeSmallerInfeasibleSubsetsCheck(const std::vector<Formula> & subformulae, const std::string filename) const {
        stringstream _filename;
        _filename << filename << "_" << moduleName(mModuleType) << "_" << mSmallerMusesCheckCounter << ".smt2";
        ofstream smtlibFile;
        smtlibFile.open( _filename.str() );
        for( vector< Formula >::const_iterator subformula = subformulae.begin();
             subformula != subformulae.end(); ++subformula )
        { // for each assumption add a new solver-call by resetting the search state
            smtlibFile << "(reset)\n";
            smtlibFile << "(set-logic QF_NRA)\n";
            smtlibFile << "(set-option :interactive-mode true)\n";
            smtlibFile << "(set-info :smt-lib-version 2.0)\n";
            // add all real-valued variables
            for( GiNaC::symtab::const_iterator var = Formula::mConstraintPool.variables().begin();
                var != Formula::mConstraintPool.variables().end(); ++var )
            {
                smtlibFile << "(declare-fun " << var->first << " () Real)\n";
            }
            string assumption = "";
            assumption += "(set-info :status sat)\n";
            assumption += "(assert (and ";
            assumption += subformula->toString();
            assumption += "))\n";
            assumption += "(get-assertions)\n";
            assumption += "(check-sat)\n";
            smtlibFile << assumption;
        }
        smtlibFile << "(exit)";
        smtlibFile.close();
        ++mSmallerMusesCheckCounter;
    }

     /**
     * Generates all subformulae of the given size
     * @param size the number of constraints
     * @return A set of subformulae
     */
    std::vector<Formula> Module::generateSubformulaeOfInfeasibleSubset(unsigned infeasibleset, unsigned size ) const {
        assert(size < mInfeasibleSubsets[infeasibleset].size());

        //000000....000011111 (size-many ones)
        unsigned bitvector = (1 << size) - 1;
        //000000....100000000
        unsigned limit = (1 << mInfeasibleSubsets[infeasibleset].size());
        unsigned nextbitvector;

        std::vector<Formula> subformulae;
        while(bitvector < limit) {
            Formula formula(AND);
            // compute lexicographical successor of the bitvector
            unsigned int tmp = (bitvector | (bitvector - 1)) + 1;
            nextbitvector = tmp | ((((tmp & -tmp) / (bitvector & -bitvector)) >> 1) - 1);

            // fill formula
            for(auto it = mInfeasibleSubsets[infeasibleset].begin(); it != mInfeasibleSubsets[infeasibleset].end(); ++it) {
                if(bitvector & 1) {
                    formula.addSubformula((*it)->pConstraint());
                }
                bitvector >>= 1;
            }
            // add subformulae
            subformulae.push_back(formula);
            bitvector = nextbitvector;
        }
        return subformulae;
    }
    /**
     *
     * @param _moduleType
     * @return
     */
    const string Module::moduleName( const ModuleType _moduleType )
    {
        switch( _moduleType )
        {
            case MT_Module:
            {
                return "Module";
            }
            case MT_SmartSimplifier:
            {
                return "SmartSimplifier";
            }
            case MT_GroebnerModule:
            {
                return "GroebnerModule";
            }
            case MT_VSModule:
            {
                return "VSModule";
            }
            case MT_CADModule:
            {
                return "CADModule";
            }
            case MT_UnivariateCADModule:
            {
                return "UnivariateCADModule";
            }
            case MT_SATModule:
            {
                return "SATModule";
            }
            case MT_LRAModule:
            {
                return "LRAModule";
            }
            case MT_PreProModule:
            {
                return "PreProModule";
            }
            case MT_CNFerModule:
            {
                return "CNFerModule";
            }
            case MT_SingleVSModule:
            {
                return "SingleVSModule";
            }
            case MT_FourierMotzkinSimplifier:
            {
                return "FourierMotzkinSimplifier";
            }
            case MT_NoModule:
            {
                return "NoModule";
            }
            default:
            {
                return "UnknownModule";
            }
        }
    }

    /**
     * Prints everything relevant of the solver.
     *
     * @param _out  The output stream where the answer should be printed.
     * @param _initiation   The line initiation.
     */
    void Module::print( ostream& _out, const string _initiation ) const
    {
        _out << _initiation << "********************************************************************************" << endl;
        _out << _initiation << " Solver with stored at " << this << " with name " << moduleName( type() ) << endl;
        _out << _initiation << endl;
        _out << _initiation << " Current solver state" << endl;
        _out << _initiation << endl;
        printReceivedFormula( _out, _initiation + " " );
        _out << _initiation << endl;
        printPassedFormula( _out, _initiation + " " );
        _out << _initiation << endl;
        printInfeasibleSubsets( _out, _initiation + " " );
        _out << _initiation << endl;
        _out << _initiation << "********************************************************************************" << endl;
    }

    /**
     * Prints the vector of the received formula.
     *
     * @param _out          The output stream where the answer should be printed.
     * @param _initiation   The line initiation.
     */
    void Module::printReceivedFormula( ostream& _out, const string _initiation ) const
    {
        _out << _initiation << "Received formula:" << endl;
        for( Formula::const_iterator receivedSubformula = mpReceivedFormula->begin(); receivedSubformula != mpReceivedFormula->end();
                ++receivedSubformula )
        {
            _out << _initiation << "  ";
            _out << setw( 30 ) << (*receivedSubformula)->toString( true );
            stringstream out;
            out << "  [" << *receivedSubformula << "]";
            _out << setw( 15 ) << out.str() << endl;
        }
    }

    /**
     * Prints the vector of passed formula.
     *
     * @param _out          The output stream where the answer should be printed.
     * @param _initiation   The line initiation.
     */
    void Module::printPassedFormula( ostream& _out, const string _initiation ) const
    {
        _out << _initiation << "Passed formula:" << endl;
        for( Formula::const_iterator passedSubformula = mpPassedFormula->begin(); passedSubformula != mpPassedFormula->end(); ++passedSubformula )
        {
            FormulaOrigins::const_iterator formulaOrigins = mPassedformulaOrigins.find( *passedSubformula );
            assert( formulaOrigins != mPassedformulaOrigins.end() );
            _out << _initiation << "  ";
            _out << setw( 30 ) << (*passedSubformula)->toString( true );
            stringstream out;
            out << "  [" << *passedSubformula << "]" << " from " << "(";
            _out << setw( 22 ) << out.str();
            for( vec_set_const_pFormula::const_iterator oSubformulas = formulaOrigins->second.begin(); oSubformulas != formulaOrigins->second.end();
                    ++oSubformulas )
            {
                _out << " {";
                for( set<const Formula*>::const_iterator oSubformula = oSubformulas->begin(); oSubformula != oSubformulas->end(); ++oSubformula )
                {
                    _out << " [" << *oSubformula << "]";
                }
                _out << " }";
            }
            _out << " )" << endl;
        }
    }

    /**
     * Prints the infeasible subsets.
     *
     * @param _out          The output stream where the answer should be printed.
     * @param _initiation   The line initiation.
     */
    void Module::printInfeasibleSubsets( ostream& _out, const string _initiation ) const
    {
        _out << _initiation << "Infeasible subsets:" << endl;
        _out << _initiation << "   {";
        for( vec_set_const_pFormula::const_iterator infSubSet = mInfeasibleSubsets.begin(); infSubSet != mInfeasibleSubsets.end(); ++infSubSet )
        {
            if( infSubSet != mInfeasibleSubsets.begin() )
            {
                _out << endl << _initiation << "    ";
            }
            _out << " {";
            for( set<const Formula*>::const_iterator infSubFormula = infSubSet->begin(); infSubFormula != infSubSet->end(); ++infSubFormula )
            {
                _out << " " << **infSubFormula;
            }
            _out << " }";
        }
        _out << " }" << endl;
    }

}    // namespace smtrat
