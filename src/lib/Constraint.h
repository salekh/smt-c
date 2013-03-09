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
 * Constraint.h
 * @author Florian Corzilius
 * @author Sebastian Junges
 * @since 2010-04-26
 * @version 2012-10-12
 */


#ifndef SMTRAT_TS_CONSTRAINT_H
#define SMTRAT_TS_CONSTRAINT_H

//#define SMTRAT_TS_CONSTRAINT_SIMPLIFIER
//#define NDEBUG
#define VS_USE_GINAC_EXPAND
//#define VS_USE_GINAC_NORMAL


#include <ginac/ginac.h>
#include <ginac/flags.h>
#include <vector>
#include <iostream>
#include <cstring>
#include <string.h>
#include <sstream>
#include <assert.h>
#include <mutex>
#include <atomic>
#include <ginacra/utilities.h>
#include "config.h"

namespace smtrat
{
    //
    // Type and object definitions
    //

    enum Constraint_Relation
    {
        CR_EQ = 0, CR_NEQ = 1, CR_LESS = 2, CR_GREATER = 3, CR_LEQ = 4, CR_GEQ = 5
    };

    enum Variable_Domain { REAL_DOMAIN = 0, INTEGER_DOMAIN = 1 };

    bool constraintRelationIsStrict( Constraint_Relation rel );
    std::string relationToString( const Constraint_Relation rel );

    struct strCmp
    {
        bool operator ()( const std::string& _stringA, const std::string& _stringB ) const
        {
            return _stringA.compare( _stringB ) < 0;
        }
    };

    struct VarInfo
    {
        unsigned maxDegree;
        unsigned minDegree;
        unsigned occurences;
    };

    typedef std::map< const GiNaC::ex, VarInfo, GiNaC::ex_is_less > VarInfoMap;

    typedef std::pair< const GiNaC::ex, signed > VarDegree;

    struct varDegreeCmp
    {
        bool operator ()( const VarDegree& varDegreeA, const VarDegree& varDegreeB ) const
        {
            signed result = varDegreeA.first.compare( varDegreeB.first );
            if( result < 0 )
            {
                return true;
            }
            else if ( result == 0 )
            {
                return varDegreeA.second < varDegreeB.second;
            }
            return false;
        }
    };

    typedef std::map< VarDegree, const GiNaC::ex, varDegreeCmp > Coefficients;

    /**
     * Class to create a constraint object.
     * @author Florian Corzilius
     * @since 2010-04-26
     * @version 2011-12-05
     */
    class Constraint
    {
        private:
            /*
             * Attributes:
             */
            unsigned             mID;
            unsigned             mFirstHash;
            unsigned             mSecondHash;
            bool                 mIsNeverPositive;
            bool                 mIsNeverNegative;
            bool                 mIsNeverZero;
            bool                 mContainsRealValuedVariables;
            bool                 mContainsIntegerValuedVariables;
            unsigned             mNumMonomials;
            unsigned             mMaxMonomeDegree;
            unsigned             mMinMonomeDegree;
            Constraint_Relation  mRelation;
            GiNaC::ex            mLhs;
            GiNaC::ex            mMultiRootLessLhs;
            GiNaC::ex            mFactorization;
            Coefficients*        mpCoefficients;
            mutable std::mutex   mMutexCoefficients;
            GiNaC::numeric       mConstantPart;
            GiNaC::symtab        mVariables;
            VarInfoMap           mVarInfoMap;

        public:

            static std::recursive_mutex mMutex;

            /*
             * Constructors:
             */
            Constraint();
            Constraint( const GiNaC::ex&, const Constraint_Relation, const GiNaC::symtab&, unsigned = 0 );
            Constraint( const GiNaC::ex&, const GiNaC::ex&, const Constraint_Relation&, const GiNaC::symtab&, unsigned = 0 );
            Constraint( const Constraint&, bool = false );

            /*
             * Destructor:
             */
            ~Constraint();

            /*
             * Methods:
             */
            const GiNaC::ex lhs() const
            {
                return mLhs;
            }

            const GiNaC::symtab variables() const
            {
                return mVariables;
            }

            Constraint_Relation relation() const
            {
                return mRelation;
            }

            unsigned id() const
            {
                return mID;
            }

            unsigned& rId() // TODO: Only the constraint pool should have access to this method (friend)
            {
                return mID;
            }

            unsigned firstHash() const
            {
                return mFirstHash;
            }

            unsigned secondHash() const
            {
                return mSecondHash;
            }

            const GiNaC::ex multiRootLessLhs() const
            {
                if( mMultiRootLessLhs != 0 ) return mMultiRootLessLhs;
                else return mLhs;
            }

            bool hasFactorization() const
            {
                return (mFactorization != 0);
            }

            const GiNaC::ex factorization() const
            {
                if( mFactorization != 0 ) return mFactorization;
                else return mLhs;
            }

            bool containsIntegerValuedVariable() const
            {
                return mContainsIntegerValuedVariables;
            }

            bool containsRealValuedVariable() const
            {
                return mContainsRealValuedVariables;
            }

            unsigned numMonomials() const
            {
                return mNumMonomials;
            }

            unsigned minMonomeDegree() const
            {
                return mMinMonomeDegree;
            }

            unsigned maxMonomeDegree() const
            {
                return mMaxMonomeDegree;
            }

            const GiNaC::numeric constantPart() const
            {
                return mConstantPart;
            }

            static void normalize( GiNaC::ex& _exp )
            {
//                std::lock_guard<std::mutex> lock( mMutexNormalize );
                GiNaC::numeric commonDenom = GiNaC::mdenom( _exp );
                if( commonDenom != 1 ) _exp *= commonDenom;
                _exp = _exp.expand();
            }

            unsigned maxDegree( const ex& _variable ) const
            {
                VarInfoMap::const_iterator varInfo = mVarInfoMap.find( _variable );
                if( varInfo != mVarInfoMap.end() )
                {
                    return varInfo->second.maxDegree;
                }
                else
                {
                    return 0;
                }
            }

            unsigned minDegree( const ex& _variable ) const
            {
                VarInfoMap::const_iterator varInfo = mVarInfoMap.find( _variable );
                if( varInfo != mVarInfoMap.end() )
                {
                    return varInfo->second.minDegree;
                }
                else
                {
                    return 0;
                }
            }

            unsigned occurences( const ex& _variable ) const
            {
                VarInfoMap::const_iterator varInfo = mVarInfoMap.find( _variable );
                if( varInfo != mVarInfoMap.end() )
                {
                    return varInfo->second.occurences;
                }
                else
                {
                    return 0;
                }
            }

            const VarInfo varInfo( const ex& _variable ) const
            {
                VarInfoMap::const_iterator varInfo = mVarInfoMap.find( _variable );
                assert( varInfo != mVarInfoMap.end() ); // variable not in constraint.
                return varInfo->second;
            }

            bool constraintRelationIsStrict( Constraint_Relation rel ) const
            {
                return (rel == CR_NEQ || rel == CR_LESS || rel == CR_GREATER);
            }

            unsigned maxDegree() const
            {
                return mMaxMonomeDegree;
            }

            bool isLinear() const
            {
                return mMaxMonomeDegree < 2;
            }

            // Data access methods (read only).
            GiNaC::ex variable( const std::string& ) const;
            bool hasVariable( const std::string& ) const;
            unsigned isConsistent() const;
            unsigned satisfiedBy( GiNaC::exmap& ) const;
            bool hasFinitelyManySolutionsIn( const std::string& ) const;
            GiNaC::ex coefficient( const GiNaC::ex&, int ) const;
            signed highestDegree() const;
            std::map<const std::string, GiNaC::numeric, strCmp> linearAndConstantCoefficients() const;
            static int exCompare( const GiNaC::ex&, const GiNaC::symtab&, const GiNaC::ex&, const GiNaC::symtab& );

            // Operators.
            bool operator <( const Constraint& ) const;
            bool operator ==( const Constraint& ) const;
            friend std::ostream& operator <<( std::ostream&, const Constraint& );

            // Manipulating methods.
            void collectProperties();
            Constraint* simplify();
            void init();

            // Printing methods.
            std::string toString( bool = false ) const;
            void print( std::ostream& _out = std::cout ) const;
            void print2( std::ostream& _out = std::cout ) const;
            void printInPrefix( std::ostream& _out = std::cout ) const;
            const std::string prefixStringOf( const GiNaC::ex& ) const;
            void printProperties( std::ostream& = std::cout ) const;
            std::string smtlibString() const;

            //
            static signed compare( std::atomic<const Constraint*>*, std::atomic<const Constraint*>* );
            static std::atomic<const Constraint*>* mergeConstraints( std::atomic<const Constraint*>*, std::atomic<const Constraint*>* );
            static bool combineConstraints( std::atomic<const Constraint*>*, std::atomic<const Constraint*>*, std::atomic<const Constraint*>* );
    };

    typedef std::vector<std::atomic<const Constraint*>*>                                vec_const_pConstraint;
    typedef std::vector<std::set<std::atomic<const Constraint*>*> >                     vec_set_const_pConstraint;
    typedef std::map<std::atomic<const Constraint*>* , vec_set_const_pConstraint> constraintOriginsMap;
    struct constraintPointerComp
    {
        bool operator ()( std::atomic<const Constraint*>* pConstraintA, std::atomic<const Constraint*>* pConstraintB ) const
        {
            return (*pConstraintA->load()) < (*pConstraintB->load());
        }
    };

    struct constraintIdComp
    {
        bool operator() (std::atomic<const Constraint*>* pConstraintA, std::atomic<const Constraint*>* pConstraintB ) const
        {
            return pConstraintA->load()->id() < pConstraintB->load()->id();
        }
    };

    typedef std::set< std::atomic<const Constraint*>*, constraintPointerComp > ConstraintSet;
}    // namespace smtrat

#ifdef SMTRAT_STRAT_PARALLEL_MODE
#define CONSTRAINT_LOCK_GUARD std::lock_guard<std::recursive_mutex> lock( smtrat::Constraint::mMutex );
#define CONSTRAINT_LOCK smtrat::Constraint::mMutex.lock();
#define CONSTRAINT_UNLOCK smtrat::Constraint::mMutex.unlock();
typedef std::atomic< const smtrat::Constraint* >* Constraint_Atom;
#else
#define CONSTRAINT_LOCK_GUARD
#define CONSTRAINT_LOCK
#define CONSTRAINT_UNLOCK
typedef std::atomic< const smtrat::Constraint* >* Constraint_Atom;
#endif

#endif
