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
 * Class containing a method applying a virtual substitution.
 * @author Florian Corzilius
 * @since 2011-05-23
 * @version 2011-12-05
 */

#include "Substitute.h"

//#define VS_DEBUG_METHODS
//#define VS_DEBUG_SUBSTITUTION

//#define VS_SUBSTITUTION_ACCORDING_PAPER

namespace vs
{
    using namespace std;
    using namespace GiNaC;

    /**
     * Applies a substitution to a constraint and stores the results in the given vector.
     *
     * @param _constraint           The constraint to substitute in.
     * @param _substitution         The substitution to apply.
     * @param _substitutionResults  The vector, in which to store the results of this substitution.
     *
     */
    void substitute( Constraint_Atom _constraint,
                     const Substitution& _substitution,
                     DisjunctionOfConstraintConjunctions& _substitutionResults )
    {
        #ifdef VS_DEBUG_METHODS
        cout << "substitute" << endl;
        #endif
        #ifdef VS_DEBUG_SUBSTITUTION
        cout << "substitute: ( " << _constraint << " )" << _substitution << endl;
        #endif

        CONSTRAINT_LOCK_GUARD
        /*
         * Apply the substitution according to its type.
         */
        switch( _substitution.type() )
        {
            case ST_NORMAL:
            {
                substituteNormal( _constraint, _substitution, _substitutionResults );
                break;
            }
            case ST_PLUS_EPSILON:
            {
                substitutePlusEps( _constraint, _substitution, _substitutionResults );
                break;
            }
            case ST_MINUS_INFINITY:
            {
                substituteMinusInf( _constraint, _substitution, _substitutionResults );
                break;
            }
            default:
            {
                cout << "Error in substitute: unexpected type of substitution." << endl;
            }
        }
        #ifdef SMTRAT_DEVOPTION_Statistics
        splitProducts( _substitutionResults );
        #endif
        #ifdef VS_DEBUG_SUBSTITUTION
        print( _substitutionResults );
        #endif
    }

    /**
     * Applies ...
     *
     * @param _constraint           The constraint to substitute in.
     * @param _substitution         The substitution to apply.
     * @param _substitutionResults  The vector, in which to store the results of this substitution.
     */
    void substituteNormal( Constraint_Atom _constraint,
                           const Substitution& _substitution,
                           DisjunctionOfConstraintConjunctions& _substitutionResults )
    {
        ex sym = _constraint->load()->variable( _substitution.variable() );
        if( sym == 0 )
        {
            _substitutionResults.push_back( TS_ConstraintConjunction() );
            _substitutionResults.back().push_back( _constraint );
            return;
        }
        /*
         * Get the variables of the constraint merged with those of the substitution.
         */
        symtab variables = symtab();
        symtab variablesA = _constraint->load()->variables();
        for( symtab::const_iterator var = variablesA.begin(); var != variablesA.end(); ++var )
        {
            variables.insert( *var );
        }
        for( symtab::const_iterator var = _substitution.termVariables().begin(); var != _substitution.termVariables().end(); ++var )
        {
            variables.insert( *var );
        }

        /*
        * Collect all necessary left hand sides to create the new conditions of all cases
        * referring to the virtual substitution.
        */
        SqrtEx substituted = SqrtEx::subBySqrtEx( _constraint->load()->lhs(), sym, _substitution.term(), variables );

        #ifdef VS_DEBUG_SUBSTITUTION
        cout << "Result of common substitution:" << substituted << endl;
        #endif

        /*
        *                               q
        * The term then looks like:    ---
        *                               s
        */
        if( !substituted.hasSqrt() )
        {
            /*
            * Create the new decision tuples.
            */
            if( _constraint->load()->relation() == smtrat::CR_EQ || _constraint->load()->relation() == smtrat::CR_NEQ )
            {
                ex q = simplify( substituted.constantPart(), variables );
                /*
                * Add conjunction (q = 0) to the substitution result.
                */
                _substitutionResults.push_back( TS_ConstraintConjunction() );
                _substitutionResults.back().push_back( smtrat::Formula::newConstraint( q, _constraint->load()->relation(), variables ) );
            }
            else
            {
                ex q = simplify( substituted.constantPart(), variables );
                if( fmod( _constraint->load()->maxDegree( sym ), 2.0 ) != 0.0 )
                {
                    ex s = simplify( substituted.denominator(), variables );
                    /*
                    * Add conjunction (s>0 and q </>/<=/>= 0) to the substitution result.
                    */
                    _substitutionResults.push_back( TS_ConstraintConjunction() );
                    _substitutionResults.back().push_back( smtrat::Formula::newConstraint( s, smtrat::CR_GREATER, variables ) );
                    _substitutionResults.back().push_back( smtrat::Formula::newConstraint( q, _constraint->load()->relation(), variables ) );

                    /*
                    * Add conjunction (s<0 and q >/</>=/<= 0) to the substitution result.
                    */
                    smtrat::Constraint_Relation inverseRelation;
                    switch( _constraint->load()->relation() )
                    {
                        case smtrat::CR_LESS:
                            inverseRelation = smtrat::CR_GREATER;
                            break;
                        case smtrat::CR_GREATER:
                            inverseRelation = smtrat::CR_LESS;
                            break;
                        case smtrat::CR_LEQ:
                            inverseRelation = smtrat::CR_GEQ;
                            break;
                        case smtrat::CR_GEQ:
                            inverseRelation = smtrat::CR_LEQ;
                            break;
                        default:
                            assert( false );
                            inverseRelation = smtrat::CR_EQ;
                    }
                    _substitutionResults.push_back( TS_ConstraintConjunction() );
                    _substitutionResults.back().push_back( smtrat::Formula::newConstraint( s, smtrat::CR_LESS, variables ) );
                    _substitutionResults.back().push_back( smtrat::Formula::newConstraint( q, inverseRelation, variables ) );
                }
                else
                {
                    /*
                    * Add conjunction (f(-c/b)*b^k </>/<=/>= 0) to the substitution result.
                    */
                    _substitutionResults.push_back( TS_ConstraintConjunction() );
                    _substitutionResults.back().push_back( smtrat::Formula::newConstraint( q, _constraint->load()->relation(), variables ) );
                }
            }
        }

        /*
        *                              q+r*sqrt(b^2-4ac)
        * The term then looks like:    -----------------
        *                                     s
        */
        else
        {
            ex s = 1;
            if( fmod( _constraint->load()->maxDegree( sym ), 2.0 ) != 0.0 )
            {
                s = substituted.denominator();
            }

            switch( _constraint->load()->relation() )
            {
                case smtrat::CR_EQ:
                {
                    substituteNormalSqrtEq( _constraint,
                                            _substitution,
                                            substituted.radicand(),
                                            substituted.constantPart(),
                                            substituted.factor(),
                                            variables,
                                            _substitutionResults );
                    break;
                }
                case smtrat::CR_NEQ:
                {
                    substituteNormalSqrtNeq( _constraint,
                                                _substitution,
                                                substituted.radicand(),
                                                substituted.constantPart(),
                                                substituted.factor(),
                                                variables,
                                                _substitutionResults );
                    break;
                }
                case smtrat::CR_LESS:
                {
                    substituteNormalSqrtLess( _constraint,
                                                _substitution,
                                                substituted.radicand(),
                                                substituted.constantPart(),
                                                substituted.factor(),
                                                s,
                                                variables,
                                                _substitutionResults );
                    break;
                }
                case smtrat::CR_GREATER:
                {
                    substituteNormalSqrtLess( _constraint,
                                                _substitution,
                                                substituted.radicand(),
                                                substituted.constantPart(),
                                                substituted.factor(),
                                                -s,
                                                variables,
                                                _substitutionResults );
                    break;
                }
                case smtrat::CR_LEQ:
                {
                    substituteNormalSqrtLeq( _constraint,
                                                _substitution,
                                                substituted.radicand(),
                                                substituted.constantPart(),
                                                substituted.factor(),
                                                s,
                                                variables,
                                                _substitutionResults );
                    break;
                }
                case smtrat::CR_GEQ:
                {
                    substituteNormalSqrtLeq( _constraint,
                                                _substitution,
                                                substituted.radicand(),
                                                substituted.constantPart(),
                                                substituted.factor(),
                                                -s,
                                                variables,
                                                _substitutionResults );
                    break;
                }
                default:
                    cout << "Error in substituteNormal: Unexpected relation symbol" << endl;
                    assert( false );
            }
        }
        simplify( _substitutionResults );
    }

    /**
     * Sub-method of substituteNormalSqrt, where applying the substitution led to a term
     * containing a square root. The relation symbol of the constraint to substitute is "=".
     *
     *                              (_q+_r*sqrt(_radicand))
     * The term then looks like:    ------------------
     *                                      _s
     *
     * @param _constraint           The constraint to substitute in.
     * @param _substitution         The substitution to apply.
     * @param _radicand             The radicand of the square root.
     * @param _q                    The summand not containing the square root.
     * @param _r                    The coefficient of the radicand.
     * @param _substitutionResults  The vector, in which to store the results of this substitution.
     * @param _variables            The variables, which the substitution term and the condition to
     *                              substitute in contain.
     */
    void substituteNormalSqrtEq( Constraint_Atom _constraint,
                                 const Substitution& _substitution,
                                 const ex& _radicand,
                                 const ex& _q,
                                 const ex& _r,
                                 const symtab& _variables,
                                 DisjunctionOfConstraintConjunctions& _substitutionResults )
    {
        #ifdef VS_DEBUG_METHODS
        cout << "substituteNormalSqrtEq" << endl;
        #endif
        ex lhs = pow( _q, 2 ) - pow( _r, 2 ) * _radicand;
        _constraint->load()->normalize( lhs );
        lhs = simplify( lhs, _variables );
        ex q = simplify( _q, _variables );
        ex r = simplify( _r, _variables );
        ex t = simplify( _radicand, _variables );
        #ifndef VS_SUBSTITUTION_ACCORDING_PAPER
        /*
         * Add conjunction (q=0 and r=0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( q, smtrat::CR_EQ, _variables ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( r, smtrat::CR_EQ, _variables ) );
        /*
         * Add conjunction (q=0 and radicand=0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( q, smtrat::CR_EQ, _variables ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( t, smtrat::CR_EQ, _variables ) );
        /*
         * Add conjunction (q<0 and r>0 and q^2-r^2*radicand=0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( q, smtrat::CR_LESS, _variables ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( r, smtrat::CR_GREATER, _variables ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_EQ, _variables ) );
        /*
         * Add conjunction (q>0 and r<0 and q^2-r^2*radicand=0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( q, smtrat::CR_GREATER, _variables ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( r, smtrat::CR_LESS, _variables ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_EQ, _variables ) );
        #else
        ex qr = _q * _r;
        smtrat::Constraint::normalize( qr );
        qr = simplify( qr, _variables );
        /*
         * Add conjunction (q*r<=0 and q^2-r^2*radicand=0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( qr, smtrat::CR_LEQ, _variables ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_EQ, _variables ) );
        #endif
    }

    /**
     * Sub-method of substituteNormalSqrt, where applying the substitution led to a term
     * containing a square root. The relation symbol of the constraint to substitute is "!=".
     *
     *                              (_q+_r*sqrt(_radicand))
     * The term then looks like:    -----------------------
     *                                      _s
     *
     * @param _constraint           The constraint to substitute in.
     * @param _substitution         The substitution to apply.
     * @param _radicand             The radicand of the square root.
     * @param _q                    The summand not containing the square root.
     * @param _r                    The coefficient of the radicand.
     * @param _substitutionResults  The vector, in which to store the results of this substitution.
     * @param _variables            The variables, which the substitution term and the condition to
     *                              substitute in contain.
     */
    void substituteNormalSqrtNeq( Constraint_Atom _constraint,
                                  const Substitution& _substitution,
                                  const ex& _radicand,
                                  const ex& _q,
                                  const ex& _r,
                                  const symtab& _variables,
                                  DisjunctionOfConstraintConjunctions& _substitutionResults )
    {
        #ifdef VS_DEBUG_METHODS
        cout << "substituteNormalSqrtNeq" << endl;
        #endif
        ex lhs = pow( _q, 2 ) - pow( _r, 2 ) * _radicand;
        _constraint->load()->normalize( lhs );
        lhs = simplify( lhs, _variables );
        ex q = simplify( _q, _variables );
        ex r = simplify( _r, _variables );
        #ifndef VS_SUBSTITUTION_ACCORDING_PAPER
        /*
         * Add conjunction (q>0 and r>0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( q, smtrat::CR_GREATER, _variables ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( r, smtrat::CR_GREATER, _variables ) );
        /*
         * Add conjunction (q<0 and r<0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( q, smtrat::CR_LESS, _variables ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( r, smtrat::CR_LESS, _variables ) );
        /*
         * Add conjunction (q^2-r^2*radicand!=0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_NEQ, _variables ) );
        #else
        ex qr = _q * _r;
        smtrat::Constraint::normalize( qr );
        qr = simplify( qr, _variables );
        /*
         * Add conjunction (q*r>0 and q^2-r^2*radicand!=0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( qr, smtrat::CR_GREATER, _variables ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_NEQ, _variables ) );
        #endif
    }

    /**
     * Sub-method of substituteNormalSqrt, where applying the substitution led to a term
     * containing a square root. The relation symbol of the constraint to substitute is "<".
     *
     *                              (_q+_r*sqrt(_radicand))
     * The term then looks like:    ------------------
     *                                      _s
     *
     * @param _constraint           The constraint to substitute in.
     * @param _substitution         The substitution to apply.
     * @param _radicand             The radicand of the square root.
     * @param _q                    The summand not containing the square root.
     * @param _r                    The coefficient of the radicand.
     * @param _s                    The denominator of the expression containing the square root.
     * @param _substitutionResults  The vector, in which to store the results of this substitution.
     * @param _variables            The variables, which the substitution term and the condition to
     *                              substitute in contain.
     */
    void substituteNormalSqrtLess( Constraint_Atom _constraint,
                                   const Substitution& _substitution,
                                   const ex& _radicand,
                                   const ex& _q,
                                   const ex& _r,
                                   const ex& _s,
                                   const symtab& _variables,
                                   DisjunctionOfConstraintConjunctions& _substitutionResults )
    {
        #ifdef VS_DEBUG_METHODS
        cout << "substituteNormalSqrtLess" << endl;
        #endif
        ex lhs = pow( _q, 2 ) - pow( _r, 2 ) * _radicand;
        _constraint->load()->normalize( lhs );
        lhs = simplify( lhs, _variables );
        ex s = simplify( _s, _variables );
        ex q = simplify( _q, _variables );
        ex r = simplify( _r, _variables );
        #ifndef VS_SUBSTITUTION_ACCORDING_PAPER
        /*
         * Add conjunction (q<0 and s>0 and q^2-r^2*radicand>0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( q, smtrat::CR_LESS, _variables ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( s, smtrat::CR_GREATER, _variables ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_GREATER, _variables ) );
        /*
         * Add conjunction (q>0 and s<0 and q^2-r^2*radicand>0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( q, smtrat::CR_GREATER, _variables ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( s, smtrat::CR_LESS, _variables ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_GREATER, _variables ) );
        /*
         * Add conjunction (r>0 and s<0 and q^2-r^2*radicand<0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( r, smtrat::CR_GREATER, _variables ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( s, smtrat::CR_LESS, _variables ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_LESS, _variables ) );
        /*
         * Add conjunction (r<0 and s>0 and q^2-r^2*radicand<0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( r, smtrat::CR_LESS, _variables ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( s, smtrat::CR_GREATER, _variables ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_LESS, _variables ) );
        /*
         * Add conjunction (r>=0 and q<0 and s>0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( r, smtrat::CR_GEQ, _variables ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( q, smtrat::CR_GREATER, _variables ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( s, smtrat::CR_LESS, _variables ) );
        /*
         * Add conjunction (r<=0 and q>0 and s<0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( r, smtrat::CR_LEQ, _variables ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( q, smtrat::CR_LESS, _variables ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( s, smtrat::CR_GREATER, _variables ) );
        #else
        ex qs = _q * _s;
        smtrat::Constraint::normalize( qs );
        qs = simplify( qs, _variables );
        ex rs = _r * _s;
        smtrat::Constraint::normalize( rs );
        rs = simplify( rs, _variables );
        /*
         * Add conjunction (q*s<0 and q^2-r^2*radicand>0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( qs, smtrat::CR_LESS, _variables ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_GREATER, _variables ) );
        /*
         * Add conjunction (r*s<=0 and q*s<0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( rs, smtrat::CR_LEQ, _variables ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( qs, smtrat::CR_LESS, _variables ) );
        /*
         * Add conjunction (r*s<=0 and q^2-r^2*radicand<0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( rs, smtrat::CR_LEQ, _variables ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_LESS, _variables ) );
        #endif
    }

    /**
     * Sub-method of substituteNormalSqrt, where applying the substitution led to a term
     * containing a square root. The relation symbol of the constraint to substitute is "<=".
     *
     *                              (_q+_r*sqrt(_radicand))
     * The term then looks like:    ------------------
     *                                      _s
     *
     * @param _constraint           The constraint to substitute in.
     * @param _substitution         The substitution to apply.
     * @param _radicand             The radicand of the square root.
     * @param _q                    The summand not containing the square root.
     * @param _r                    The coefficient of the radicand.
     * @param _s                    The denominator of the expression containing the square root.
     * @param _substitutionResults  The vector, in which to store the results of this substitution.
     * @param _variables            The variables, which the substitution term and the condition to
     *                              substitute in contain.
     */
    void substituteNormalSqrtLeq( Constraint_Atom _constraint,
                                  const Substitution& _substitution,
                                  const ex& _radicand,
                                  const ex& _q,
                                  const ex& _r,
                                  const ex& _s,
                                  const symtab& _variables,
                                  DisjunctionOfConstraintConjunctions& _substitutionResults )
    {
        #ifdef VS_DEBUG_METHODS
        cout << "substituteNormalSqrtLeq" << endl;
        #endif
        ex lhs = pow( _q, 2 ) - pow( _r, 2 ) * _radicand;
        _constraint->load()->normalize( lhs );
        lhs = simplify( lhs, _variables );
        ex s = simplify( _s, _variables );
        ex q = simplify( _q, _variables );
        ex r = simplify( _r, _variables );
        ex t = simplify( _radicand, _variables );
        #ifndef VS_SUBSTITUTION_ACCORDING_PAPER
        /*
         * Add conjunction (q<0 and s>0 and q^2-r^2*radicand>=0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( q, smtrat::CR_LESS, _variables ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( s, smtrat::CR_GREATER, _variables ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_GEQ, _variables ) );
        /*
         * Add conjunction (q>0 and s<0 and q^2-r^2*radicand>=0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( q, smtrat::CR_GREATER, _variables ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( s, smtrat::CR_LESS, _variables ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_GEQ, _variables ) );
        /*
         * Add conjunction (r>0 and s<0 and q^2-r^2*radicand<=0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( r, smtrat::CR_GREATER, _variables ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( s, smtrat::CR_LESS, _variables ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_LEQ, _variables ) );
        /*
         * Add conjunction (r<0 and s>0 and q^2-r^2*radicand<=0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( r, smtrat::CR_LESS, _variables ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( s, smtrat::CR_GREATER, _variables ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_LEQ, _variables ) );
        /*
         * Add conjunction (r=0 and q=0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( r, smtrat::CR_EQ, _variables ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( q, smtrat::CR_EQ, _variables ) );
        /*
         * Add conjunction (radicand=0 and q=0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( t, smtrat::CR_EQ, _variables ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( q, smtrat::CR_EQ, _variables ) );
        #else
        ex qs = _q * _s;
        smtrat::Constraint::normalize( qs );
        qs = simplify( qs, _variables );
        ex rs = _r * _s;
        smtrat::Constraint::normalize( rs );
        rs = simplify( rs, _variables );
        /*
         * Add conjunction (q*s<=0 and q^2-r^2*radicand>=0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( qs, smtrat::CR_LEQ, _variables ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_GEQ, _variables ) );
        /*
         * Add conjunction (r*s<=0 and q^2-r^2*radicand<=0) to the substitution result.
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( rs, smtrat::CR_LEQ, _variables ) );
        _substitutionResults.back().push_back( smtrat::Formula::newConstraint( lhs, smtrat::CR_LEQ, _variables ) );
        #endif
    }

    /**
     * Applies the given substitution to the given constraint, where the substitution
     * is of the form [x -> t+epsilon] with x as the variable and c and b polynomials in
     * the real theory excluding x. The constraint is of the form "f(x) \rho 0" with
     * \rho element of {=,!=,<,>,<=,>=} and k as the maximum degree of x in f.
     *
     * @param _constraint           The constraint to substitute in.
     * @param _substitution         The substitution to apply.
     * @param _substitutionResults  The vector, in which to store the results of this substitution.
     */
    void substitutePlusEps( Constraint_Atom _constraint,
                            const Substitution& _substitution,
                            DisjunctionOfConstraintConjunctions& _substitutionResults )
    {
        #ifdef VS_DEBUG_METHODS
        cout << "substitutePlusEps" << endl;
        #endif
        symtab variables = _constraint->load()->variables();
        if( !variables.empty() )
        {
            if( variables.find( _substitution.variable() ) != variables.end() )
            {
                switch( _constraint->load()->relation() )
                {
                    case smtrat::CR_EQ:
                    {
                        substituteTrivialCase( _constraint, _substitution, _substitutionResults );
                        break;
                    }
                    case smtrat::CR_NEQ:
                    {
                        substituteNotTrivialCase( _constraint, _substitution, _substitutionResults );
                        break;
                    }
                    case smtrat::CR_LESS:
                    {
                        substituteEpsGradients( _constraint, _substitution, smtrat::CR_LESS, _substitutionResults );
                        break;
                    }
                    case smtrat::CR_GREATER:
                    {
                        substituteEpsGradients( _constraint, _substitution, smtrat::CR_GREATER, _substitutionResults );
                        break;
                    }
                    case smtrat::CR_LEQ:
                    {
                        substituteTrivialCase( _constraint, _substitution, _substitutionResults );
                        substituteEpsGradients( _constraint, _substitution, smtrat::CR_LESS, _substitutionResults );
                        break;
                    }
                    case smtrat::CR_GEQ:
                    {
                        substituteTrivialCase( _constraint, _substitution, _substitutionResults );
                        substituteEpsGradients( _constraint, _substitution, smtrat::CR_GREATER, _substitutionResults );
                        break;
                    }
                    default:
                        assert( false );
                }
                simplify( _substitutionResults );
            }
            else
            {
                _substitutionResults.push_back( TS_ConstraintConjunction() );
                _substitutionResults.back().push_back( _constraint );
            }
        }
        else
        {
            cout << "Warning in substitutePlusEps: The chosen constraint has no variable" << endl;
        }
    }

    /**
     * Sub-method of substituteEps and substituteMinusEps, where one of the gradients in the
     * point represented by the substitution must be negative if the parameter relation is <
     * or positive if the parameter relation is >. The constraint is of the form:
     *
     *  f(x)~0, with ~ being < in the case of +epsilon and > in the case of -epsilon
     *
     * and the substitution of the form [x -> t +/- epsilon]
     *
     * @param _constraint           The constraint to substitute in.
     * @param _substitution         The substitution to apply.
     * @param _relation1            The relation symbol, which compares a even derivative with zero.
     * @param _relation2            The relation symbol, which compares a odd derivative with zero.
     * @param _substitutionResults  The vector, in which to store the results of this substitution.
     */
    void substituteEpsGradients( Constraint_Atom _constraint,
                                 const Substitution& _substitution,
                                 const smtrat::Constraint_Relation _relation,
                                 DisjunctionOfConstraintConjunctions& _substitutionResults )
    {
        #ifdef VS_DEBUG_METHODS
        cout << "substituteEpsGradients" << endl;
        #endif

        ex sym = _constraint->load()->variable( _substitution.variable() );
        symtab variables = _constraint->load()->variables();

        // Create a substitution formed by the given one without an addition of epsilon.
        Substitution substitution = Substitution( _substitution.variable(), sym, _substitution.term(), ST_NORMAL, _substitution.originalConditions() );

        /*
         * Create the vector of constraints which serves as a collection of the necessary constraints.
         * It represents the current conjunction created by substituting by an epsilon term, which
         * results in a disjunction of conjunctions.
         */
        TS_ConstraintConjunction collection = TS_ConstraintConjunction();

        /*
         * Call the method substituteNormal with the constraint f(x)~0 and the substitution [x -> t],
         * where the parameter relation is ~.
         */
        collection.push_back( smtrat::Formula::newConstraint( _constraint->load()->lhs(), _relation, variables ) );

        // Check:  (f(x)~0) [x -> t]
        substituteNormal( collection.back(), substitution, _substitutionResults );

        // Create a vector to store the results of each single substitution.
        vector<DisjunctionOfConstraintConjunctions> substitutionResultsVector;
        substitutionResultsVector = vector<DisjunctionOfConstraintConjunctions>();

        /*
         * Let k be the maximum degree of x in f, then call for every 1<=i<=k substituteNormal with:
         *
         *      f^0(x)=0 and ... and f^i-1(x)=0 and f^i(x)~0     as constraints and
         *      [x -> t]                                         as substitution,
         *
         * where the relation is ~.
         */
        unsigned pos = 0;
        ex derivative = ex( _constraint->load()->lhs() );
        while( derivative.has( sym ) )
        {
            // Change the relation symbol of the last added constraint to "=".
            Constraint_Atom constraint = smtrat::Formula::newConstraint( derivative, smtrat::CR_EQ, variables );
            collection.pop_back();
            collection.push_back( constraint );

            // Form the derivate of the left hand side of the last added constraint.
            derivative = constraint->load()->lhs().diff( ex_to<symbol>( sym ), 1 );
            SqrtEx::simplify( derivative, sym );

            assert( derivative.degree( sym ) < (signed) collection.back()->load()->maxDegree( sym ) );

            // Add the constraint f^i(x)~0.
            collection.push_back( smtrat::Formula::newConstraint( derivative, _relation, variables ) );

            // Apply the substitution (without epsilon) to each constraint in the collection.
            for( unsigned i = pos; i < collection.size(); ++i )
            {
                substitutionResultsVector.push_back( DisjunctionOfConstraintConjunctions() );
                substituteNormal( collection[i], substitution, substitutionResultsVector.back() );
            }

            combine( substitutionResultsVector, _substitutionResults );

            // Remove the last substitution result.
            substitutionResultsVector.pop_back();
            ++pos;
        }
    }

    /**
     * Applies the given substitution to the given constraint, where the substitution
     * is of the form [x -> -infinity] with x as the variable and c and b polynomials in
     * the real theory excluding x. The constraint is of the form "f(x) \rho 0" with
     * \rho element of {=,!=,<,>,<=,>=} and k as the maximum degree of x in f.
     *
     * @param _constraint           The constraint to substitute in.
     * @param _substitution         The substitution to apply.
     * @param _substitutionResults  The vector, in which to store the results of this substitution.
     */
    void substituteMinusInf( Constraint_Atom _constraint,
                             const Substitution& _substitution,
                             DisjunctionOfConstraintConjunctions& _substitutionResults )
    {
        #ifdef VS_DEBUG_METHODS
        cout << "substituteMinusInf: " << endl;
        #endif
        symtab variables = _constraint->load()->variables();
        if( !variables.empty() )
        {
            if( variables.find( _substitution.variable() ) != variables.end() )
            {
                if( _constraint->load()->relation() == smtrat::CR_EQ )
                {
                    substituteTrivialCase( _constraint, _substitution, _substitutionResults );
                }
                else if( _constraint->load()->relation() == smtrat::CR_NEQ )
                {
                    substituteNotTrivialCase( _constraint, _substitution, _substitutionResults );
                }
                else
                {
                    substituteInfLessGreater( _constraint, _substitution, _substitutionResults );
                }
                simplify( _substitutionResults );
            }
            else
            {
                _substitutionResults.push_back( TS_ConstraintConjunction() );
                _substitutionResults.back().push_back( _constraint );
            }
        }
        else
        {
            cout << "Warning in substituteInf: The chosen constraint has no variable" << endl;
        }
    }

    /**
     * Applies the given substitution to the given constraint, where the substitution
     * is of the form [x -> +/-infinity] with x as the variable and c and b polynomials in
     * the real theory excluding x. The constraint is of the form "a*x^2+bx+c \rho 0",
     * where \rho is < or >.
     *
     * @param _constraint           The constraint to substitute in.
     * @param _substitution         The substitution to apply.
     * @param _substitutionResults  The vector, in which to store the results of this substitution.
     */
    void substituteInfLessGreater( Constraint_Atom _constraint,
                                   const Substitution& _substitution,
                                   DisjunctionOfConstraintConjunctions& _substitutionResults )
    {
        #ifdef VS_DEBUG_METHODS
        cout << "substituteInfLessGreater: " << endl;
        #endif
        /*
         * Check whether the relation is not "=" or "!=".
         */
        assert( _constraint->load()->relation() != smtrat::CR_EQ );
        assert( _constraint->load()->relation() != smtrat::CR_NEQ );
        ex sym = _constraint->load()->variable( _substitution.variable() );
        symtab variables = _constraint->load()->variables();
        /*
         * Determine the relation for the coefficients of the odd and even degrees.
         */
        smtrat::Constraint_Relation oddRelationType  = smtrat::CR_GREATER;
        smtrat::Constraint_Relation evenRelationType = smtrat::CR_LESS;
        if( _constraint->load()->relation() == smtrat::CR_GREATER || _constraint->load()->relation() == smtrat::CR_GEQ )
        {
            oddRelationType  = smtrat::CR_LESS;
            evenRelationType = smtrat::CR_GREATER;
        }
        /*
         * Check all cases according to the substitution rules.
         */
        unsigned varDegree = _constraint->load()->maxDegree( sym );
        assert( varDegree > 0 );
        for( unsigned i = varDegree + 1; i > 0; --i )
        {
            /*
             * Check, whether the variable to substitute, does not occur in the
             * conditions we substituted in.
             */
            assert( !_constraint->load()->coefficient( sym, i - 1 ).has( sym ) );

            /*
             * Add conjunction (a_n=0 and ... and a_i~0) to the substitution result.
             */

            _substitutionResults.push_back( TS_ConstraintConjunction() );

            for( unsigned j = varDegree; j > i - 1; --j )
            {
                _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _constraint->load()->coefficient( sym, j ), smtrat::CR_EQ, variables ) );
            }
            if( i > 1 )
            {
                if( fmod( i - 1, 2.0 ) != 0.0 )
                {
                    _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _constraint->load()->coefficient( sym, i - 1 ), oddRelationType, variables ) );
                }
                else
                {
                    _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _constraint->load()->coefficient( sym, i - 1 ), evenRelationType, variables ) );
                }
            }
            else
            {
                _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _constraint->load()->coefficient( sym, i - 1 ), _constraint->load()->relation(), variables ) );
            }
        }
    }

    /**
     * Deals with the case, that the left hand side of the constraint to substitute is
     * a trivial polynomial in the variable to substitute.
     *
     * The constraints left hand side then should looks like:   ax^2+bx+c
     *
     * @param _constraint           The constraint to substitute in.
     * @param _substitution         The substitution to apply.
     * @param _substitutionResults  The vector, in which to store the results of this substitution.
     */
    void substituteTrivialCase( Constraint_Atom _constraint,
                                const Substitution& _substitution,
                                DisjunctionOfConstraintConjunctions& _substitutionResults )
    {
        #ifdef VS_DEBUG_METHODS
        cout << "substituteTrivialCase" << endl;
        #endif
        /*
         * Check whether the relation is "=", "<=" or ">=".
         */
        assert( _constraint->load()->relation() == smtrat::CR_EQ || _constraint->load()->relation() == smtrat::CR_LEQ || _constraint->load()->relation() == smtrat::CR_GEQ );
        ex sym = _constraint->load()->variable( _substitution.variable() );
        symtab variables = _constraint->load()->variables();
        unsigned varDegree = _constraint->load()->maxDegree( sym );
        /*
         * Check the cases (a_0=0 and ... and a_n=0)
         */
        _substitutionResults.push_back( TS_ConstraintConjunction() );
        for( unsigned i = 0; i <= varDegree; ++i )
        {
            /*
             * Check, whether the variable to substitute, does not occur in the
             * conditions we substituted in.
             */
            assert( !_constraint->load()->coefficient( sym, i ).has( sym ) );
            _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _constraint->load()->coefficient( sym, i ), smtrat::CR_EQ, variables ) );
        }
    }

    /**
     * Deals with the case, that the left hand side of the constraint to substitute is
     * not a trivial polynomial in the variable to substitute.
     *
     * The constraints left hand side then should looks like:   ax^2+bx+c
     *
     * @param _constraint           The constraint to substitute in.
     * @param _substitution         The substitution to apply.
     * @param _substitutionResults  The vector, in which to store the results of this substitution.
     */
    void substituteNotTrivialCase( Constraint_Atom _constraint,
                                   const Substitution& _substitution,
                                   DisjunctionOfConstraintConjunctions& _substitutionResults )
    {
        #ifdef VS_DEBUG_METHODS
        cout << "substituteNotTrivialCase" << endl;
        #endif
        /*
         * Check whether the relation is "!=".
         */
        assert( _constraint->load()->relation() == smtrat::CR_NEQ );
        ex sym = _constraint->load()->variable( _substitution.variable() );
        symtab variables = _constraint->load()->variables();
        unsigned varDegree = _constraint->load()->maxDegree( sym );
        for( unsigned i = 0; i <= varDegree; ++i )
        {
            assert( !_constraint->load()->coefficient( sym, i ).has( sym ) );
            /*
             * Add conjunction (a_i!=0) to the substitution result.
             */
            _substitutionResults.push_back( TS_ConstraintConjunction() );
            _substitutionResults.back().push_back( smtrat::Formula::newConstraint( _constraint->load()->coefficient( sym, i ), smtrat::CR_NEQ, variables ) );
        }
    }

    /**
     * Simplifies a disjunction of conjunctions of constraints by deleting consistent
     * constraint and inconsistent conjunctions of constraints. If a conjunction of
     * only consistent constraints exists, the simplified disjunction contains one
     * empty conjunction.
     *
     * @param _toSimplify   The disjunction of conjunctions to simplify.
     */
    void simplify( DisjunctionOfConstraintConjunctions& _toSimplify )
    {
        #ifdef VS_DEBUG_METHODS
        cout << "simplify" << endl;
        #endif
        bool                                          containsEmptyDisjunction = false;
        DisjunctionOfConstraintConjunctions::iterator conj                     = _toSimplify.begin();
        while( conj != _toSimplify.end() )
        {
            bool                               conjInconsistent = false;
            TS_ConstraintConjunction::iterator cons             = (*conj).begin();
            while( cons != (*conj).end() )
            {
                unsigned consConsistent = (*cons)->load()->isConsistent();
                if( consConsistent == 0 )
                {
                    conjInconsistent = true;
                    break;
                }
                else if( consConsistent == 1 )
                {
                    // Delete the constraint.
                    cons = (*conj).erase( cons );
                }
                else
                {
                    cons++;
                }
            }
            bool conjEmpty = (*conj).empty();
            if( conjInconsistent || (containsEmptyDisjunction && conjEmpty) )
            {
                // Delete the conjunction.
                (*conj).clear();
                conj = _toSimplify.erase( conj );
            }
            else
            {
                conj++;
            }
            if( !containsEmptyDisjunction && conjEmpty )
            {
                containsEmptyDisjunction = true;
            }
        }
    }

    /**
     *
     * @param _toSimplify
     */
    void splitProducts( DisjunctionOfConstraintConjunctions& _toSimplify )
    {
        unsigned toSimpSize = _toSimplify.size();
        for( unsigned pos = 0; pos < toSimpSize; )
        {
            if( !_toSimplify.begin()->empty() )
            {
                DisjunctionOfConstraintConjunctions temp = splitProducts( _toSimplify[pos] );
                _toSimplify.erase( _toSimplify.begin() );
                _toSimplify.insert( _toSimplify.end(), temp.begin(), temp.end() );
                --toSimpSize;
            }
            else
            {
                ++pos;
            }
        }
    }

    /**
     *
     * @param _constraintConjunction
     * @return
     */
    DisjunctionOfConstraintConjunctions splitProducts( const TS_ConstraintConjunction& _constraintConjunction )
    {
        DisjunctionOfConstraintConjunctions result = DisjunctionOfConstraintConjunctions();
        vector<DisjunctionOfConstraintConjunctions> toCombine = vector<DisjunctionOfConstraintConjunctions>();
        for( auto constraint = _constraintConjunction.begin(); constraint != _constraintConjunction.end(); ++constraint )
        {
            if( (*constraint)->load()->hasFactorization() )
            {
                switch( (*constraint)->load()->relation() )
                {
                    case smtrat::CR_EQ:
                    {
                        toCombine.push_back( DisjunctionOfConstraintConjunctions() );
                        const ex factorization = (*constraint)->load()->factorization();
                        for( GiNaC::const_iterator summand = factorization.begin(); summand != factorization.end(); ++summand )
                        {
                            Constraint_Atom cons = smtrat::Formula::newConstraint( *summand, smtrat::CR_EQ, (*constraint)->load()->variables() );
                            toCombine.back().push_back( TS_ConstraintConjunction() );
                            toCombine.back().back().push_back( cons );
                        }
                        break;
                    }
                    case smtrat::CR_NEQ:
                    {
                        toCombine.push_back( DisjunctionOfConstraintConjunctions() );
                        toCombine.back().push_back( TS_ConstraintConjunction() );
                        const ex factorization = (*constraint)->load()->factorization();
                        for( GiNaC::const_iterator summand = factorization.begin(); summand != factorization.end(); ++summand )
                        {
                            Constraint_Atom cons = smtrat::Formula::newConstraint( *summand, smtrat::CR_NEQ, (*constraint)->load()->variables() );
                            toCombine.back().back().push_back( cons );
                        }
                        break;
                    }
                    default:
                    {
//                        cout << "getSignCombinations: " << **constraint << endl;
                        toCombine.push_back( getSignCombinations( *constraint ) );
//                        print( toCombine.back() );
                    }
                    simplify( toCombine.back() );
                }
            }
            else
            {
                toCombine.push_back( DisjunctionOfConstraintConjunctions() );
                toCombine.back().push_back( TS_ConstraintConjunction() );
                toCombine.back().back().push_back( *constraint );
            }
        }
        combine( toCombine, result );
        simplify( result );
        return result;
    }

    /**
     *
     * @param _product
     * @param _positive
     * @param _zero
     * @param _variables
     * @return
     */
    DisjunctionOfConstraintConjunctions getSignCombinations( Constraint_Atom _constraint )
    {
        DisjunctionOfConstraintConjunctions combinations = DisjunctionOfConstraintConjunctions();
        if( _constraint->load()->hasFactorization() && _constraint->load()->factorization().nops() <= MAX_PRODUCT_SPLIT_NUMBER )
        {
            assert( _constraint->load()->relation() == smtrat::CR_GREATER || _constraint->load()->relation() == smtrat::CR_LESS
                    || _constraint->load()->relation() == smtrat::CR_GEQ || _constraint->load()->relation() == smtrat::CR_LEQ );
            smtrat::Constraint_Relation relPos = smtrat::CR_GREATER;
            smtrat::Constraint_Relation relNeg = smtrat::CR_LESS;
            if( _constraint->load()->relation() == smtrat::CR_GEQ || _constraint->load()->relation() == smtrat::CR_LEQ )
            {
                relPos = smtrat::CR_GEQ;
                relNeg = smtrat::CR_LEQ;
            }
            bool positive = (_constraint->load()->relation() == smtrat::CR_GEQ || _constraint->load()->relation() == smtrat::CR_GREATER);
            TS_ConstraintConjunction positives = TS_ConstraintConjunction();
            TS_ConstraintConjunction alwayspositives = TS_ConstraintConjunction();
            TS_ConstraintConjunction negatives = TS_ConstraintConjunction();
            TS_ConstraintConjunction alwaysnegatives = TS_ConstraintConjunction();
            unsigned numOfAlwaysNegatives = 0;
            const ex product = _constraint->load()->factorization();
        symtab variables = _constraint->load()->variables();
            for( GiNaC::const_iterator summand = product.begin(); summand != product.end(); ++summand )
            {
                Constraint_Atom consPos = smtrat::Formula::newConstraint( *summand, relPos, variables );
                unsigned posConsistent = consPos->load()->isConsistent();
                if( posConsistent != 0 )
                {
                    positives.push_back( consPos );
                }
                Constraint_Atom consNeg = smtrat::Formula::newConstraint( *summand, relNeg, variables );
                unsigned negConsistent = consNeg->load()->isConsistent();
                if( negConsistent == 0 )
                {
                    if( posConsistent == 0 )
                    {
                        combinations.push_back( TS_ConstraintConjunction() );
                        combinations.back().push_back( consNeg );
                        return combinations;
                    }
                    if( posConsistent != 1 ) alwayspositives.push_back( positives.back() );
                    positives.pop_back();
                }
                else
                {
                    if( posConsistent == 0 )
                    {
                        ++numOfAlwaysNegatives;
                        if( negConsistent != 1 ) alwaysnegatives.push_back( consNeg );
                    }
                    else negatives.push_back( consNeg );
                }
            }
            assert( positives.size() == negatives.size() );
            if( positives.size() > 0 )
            {
                vector< bitset<MAX_PRODUCT_SPLIT_NUMBER> > combSelector = vector< bitset<MAX_PRODUCT_SPLIT_NUMBER> >();
                if( fmod( numOfAlwaysNegatives, 2.0 ) != 0.0 )
                {
                    if( positive ) getOddBitStrings( positives.size(), combSelector );
                    else getEvenBitStrings( positives.size(), combSelector );
                }
                else
                {
                    if( positive ) getEvenBitStrings( positives.size(), combSelector );
                    else getOddBitStrings( positives.size(), combSelector );
                }
                for( auto comb = combSelector.begin(); comb != combSelector.end(); ++comb )
                {
                    combinations.push_back( TS_ConstraintConjunction( alwaysnegatives ) );
                    combinations.back().insert( combinations.back().end(), alwayspositives.begin(), alwayspositives.end() );
                    for( unsigned pos = 0; pos < positives.size(); ++pos )
                    {
                        if( (*comb)[pos] ) combinations.back().push_back( negatives[pos] );
                        else combinations.back().push_back( positives[pos] );
                    }
                }
            }
            else
            {
                combinations.push_back( TS_ConstraintConjunction( alwaysnegatives ) );
                combinations.back().insert( combinations.back().end(), alwayspositives.begin(), alwayspositives.end() );
            }
        }
        else
        {
            combinations.push_back( TS_ConstraintConjunction() );
            combinations.back().push_back( _constraint );
        }
        return combinations;
    }

    /**
     *
     * @param _length
     * @param _strings
     */
    void getOddBitStrings( unsigned _length, vector< bitset<MAX_PRODUCT_SPLIT_NUMBER> >& _strings, unsigned _pos  )
    {
        assert( _length > 0 );
        if( _length == 1 )  _strings.push_back( bitset<MAX_PRODUCT_SPLIT_NUMBER>( 1 ) );
        else
        {
            getEvenBitStrings( _length - 1, _strings, _pos );
            for( ; _pos < _strings.size(); ++_pos )
            {
                _strings[_pos] <<= 1;
                _strings[_pos].flip(0);
            }
            getOddBitStrings( _length - 1, _strings, _pos );
            for( ; _pos < _strings.size(); ++_pos ) _strings[_pos] <<= 1;
        }
    }

    /**
     *
     * @param _length
     * @param _strings
     */
    void getEvenBitStrings( unsigned _length, vector< bitset<MAX_PRODUCT_SPLIT_NUMBER> >& _strings, unsigned _pos )
    {
        assert( _length > 0 );
        if( _length == 1 ) _strings.push_back( bitset<MAX_PRODUCT_SPLIT_NUMBER>( 0 ) );
        else
        {
            getEvenBitStrings( _length - 1, _strings );
            for( ; _pos < _strings.size(); ++_pos ) _strings[_pos] <<= 1;
            getOddBitStrings( _length - 1, _strings );
            for( ; _pos < _strings.size(); ++_pos )
            {
                _strings[_pos] <<= 1;
                _strings[_pos].flip(0);
            }
        }
    }

    /**
     *
     * @param _expression
     * @param _variables
     * @return
     */
    ex simplify( const ex& _expression, const symtab& _variables )
    {
        for( symtab::const_iterator var = _variables.begin(); var != _variables.end(); ++var )
        {
            if( _expression.has( var->second ) )
            {
                ex un, con, prim;
                _expression.unitcontprim( var->second, un, con, prim );
                if( con.info( info_flags::rational ) )
                {
                    return prim * un;
                }
                return _expression;
            }
        }
        return _expression;
    }

    /**
     *
     * @param _substitutionResults
     */
    void print( DisjunctionOfConstraintConjunctions& _substitutionResults )
    {
        DisjunctionOfConstraintConjunctions::const_iterator conj = _substitutionResults.begin();
        while( conj != _substitutionResults.end() )
        {
            if( conj != _substitutionResults.begin() )
            {
                cout << " or (";
            }
            else
            {
                cout << "    (";
            }
            TS_ConstraintConjunction::const_iterator cons = (*conj).begin();
            while( cons != (*conj).end() )
            {
                if( cons != (*conj).begin() )
                {
                    cout << " and ";
                }
                (*cons)->load()->print( cout );
                cons++;
            }
            cout << ")" << endl;
            conj++;
        }
        cout << endl;
    }
}    // end namspace vs

