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
 * @file Bound.h
 * @author Florian Corzilius <corzilius@cs.rwth-aachen.de>
 * @since 2012-04-05
 * @version 2014-10-01
 */

#pragma once

#include "Value.h"
#include "../../Formula.h"
#include <stddef.h>
#include <set>

namespace smtrat
{
    namespace lra
    {
        // Forward declaration.
        template<class T1, class T2>
        class Variable;

        // Forward declaration.
        template<typename T1, typename T2>
        class Bound;

        /**
         * 
         */
        template<typename T1, typename T2>
        class Bound
        {
            public:
            ///
            enum Type{ LOWER, UPPER, EQUAL };

            /**
             * 
             */
            struct boundComp
            {
                /**
                 * @param pBoundA
                 * @param pBoundB
                 * @return 
                 */
                bool operator ()( const Bound<T1, T2>* const _pBoundA, const Bound<T1, T2>* const _pBoundB ) const
                {
                    return (*_pBoundA) < (*_pBoundB);
                }
            };

            ///
            typedef std::set<const Bound<T1, T2>*, boundComp > BoundSet;

            /**
             * 
             */
            struct Info
            {
                ///
                int updated;
                ///
                std::list<const smtrat::Formula*>::iterator position;
                ///
                const smtrat::Formula* neqRepresentation;
                ///
                bool exists;
            };

            private:

                ///
                bool mDeduced;
                ///
                Type mType;
                ///
                const Value<T1>* mLimit;
                ///
                Variable<T1, T2>* const mVar;
                ///
                const smtrat::Formula* mpAsConstraint;
                ///
                std::vector<PointerSet<Formula> >* mpOrigins;
                ///
                Info* mpInfo;

            public:
                /**
                 * 
                 */
                Bound();
                
                /**
                 * 
                 * @param _limit
                 * @param _var
                 * @param _type
                 * @param _constraint
                 * @param _boundInfo
                 * @param _deduced
                 */
                Bound( const Value<T1>* const _limit, Variable<T1, T2>* const _var, Type _type, const smtrat::Formula* _constraint, Bound<T1, T2>::Info* _boundInfo = NULL, bool _deduced = false );
                
                /**
                 * 
                 */
                ~Bound();

                /**
                 * 
                 * @param _value
                 * @return 
                 */
                bool operator >( const Value<T1>& _value ) const;
                
                /**
                 * 
                 * @param _value
                 * @return 
                 */
                bool operator ==( const Value<T1>& _value ) const;
                
                /**
                 * 
                 * @param _value
                 * @return 
                 */
                bool operator <( const Value<T1>& _value ) const;
                
                /**
                 * 
                 * @param _bound
                 * @return 
                 */
                bool operator <( const Bound& _bound ) const;
                
                /**
                 * 
                 * @param _bound
                 * @return 
                 */
                bool operator >( const Bound& _bound ) const;
                
                /**
                 * 
                 * @param _a
                 * @return 
                 */
                bool operator ==( const T1& _a ) const;
                
                /**
                 * 
                 * @param _a
                 * @return 
                 */
                bool operator >( const T1& _a ) const;
                
                /**
                 * 
                 * @param _a
                 * @return 
                 */
                bool operator <( const T1& _a ) const;
                
                /**
                 * 
                 * @param _a
                 * @return 
                 */
                bool operator >=( const T1& _a ) const;
                
                /**
                 * 
                 * @param _a
                 * @return 
                 */
                bool operator <=( const T1& _a ) const;
                
                /**
                 * 
                 * @return 
                 */
                const std::string toString() const;
                
                /**
                 * 
                 * @param _withOrigins
                 * @param _out
                 * @param _printTypebool
                 */
                template <typename T3, typename T4> friend std::ostream& operator <<( std::ostream& _ostream, const Bound<T3, T4>& _bound );
                
                /**
                 * 
                 * @param _withOrigins
                 * @param _out
                 * @param _printTypebool
                 */
                void print( bool _withOrigins = false,  std::ostream& _out = std::cout, bool _printTypebool = false ) const;

                /**
                 * @return 
                 */
                bool deduced() const
                {
                    return mDeduced;
                }

                /**
                 * @return 
                 */
                const Value<T1>& limit() const
                {
                    return *mLimit;
                }

                /**
                 * @return 
                 */
                const Value<T1>* pLimit() const
                {
                    return mLimit;
                }

                /**
                 * @return 
                 */
                bool isInfinite() const
                {
                    return mLimit == NULL;
                }

                /**
                 * @return 
                 */
                Variable<T1, T2>* pVariable() const
                {
                    return mVar;
                }

                /**
                 * @return 
                 */
                const Variable<T1, T2>& variable() const
                {
                    return *mVar;
                }

                /**
                 * @return 
                 */
                Type type() const
                {
                    return mType;
                }

                /**
                 * @return 
                 */
                bool isWeak() const
                {
                    return mLimit->deltaPart() == 0;
                }

                /**
                 * @return 
                 */
                bool isUpperBound() const
                {
                    return mType != LOWER;
                }

                /**
                 * @return 
                 */
                bool isLowerBound() const
                {
                    return mType != UPPER;
                }

                /**
                 * @return 
                 */
                const smtrat::Formula* pAsConstraint() const
                {
                    return mpAsConstraint;
                }
                
                /**
                 * @return 
                 */
                const smtrat::Formula* neqRepresentation() const
                {
                    return mpInfo->neqRepresentation;
                }
                
                /**
                 * 
                 * @param _constraint
                 */
                void setNeqRepresentation( const smtrat::Formula* _constraint ) const
                {
                    assert( _constraint->getType() == smtrat::CONSTRAINT && _constraint->constraint().relation() == smtrat::Relation::NEQ );
                    if( mpInfo->neqRepresentation == NULL )
                    {
                        mpInfo->neqRepresentation = _constraint;
                    }
                }
                
                /**
                 * 
                 */
                void boundExists() const
                {
                    mpInfo->exists = true;
                }

                /**
                 * @return 
                 */
                std::vector<PointerSet<Formula> >* pOrigins() const
                {
                    return mpOrigins;
                }

                /**
                 * @return 
                 */
                const std::vector<PointerSet<Formula> >& origins() const
                {
                    return *mpOrigins;
                }

                /**
                 * @return 
                 */
                bool isActive() const
                {
                    return !mpOrigins->empty();
                }

                /**
                 * @return 
                 */
                Info* pInfo() const
                {
                    return mpInfo;
                }

                /**
                 * @return 
                 */
                bool operator >=( const Value<T1>& v ) const
                {
                    return !((*this) < v);
                }

                /**
                 * @return 
                 */
                bool operator <=( const Value<T1>& v ) const
                {
                    return !((*this) > v);
                }
        };
    }    // end namspace lra
}    // end namspace smtrat

#include "Bound.tpp"
