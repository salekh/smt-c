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
 * Class to create a square root expression object.
 * @author Florian Corzilius
 * @since 2011-05-26
 * @version 2013-10-07
 */

#include "SqrtEx.h"

namespace vs
{
    using namespace std;

    /**
     * Constructors:
     */
    SqrtEx::SqrtEx():
        mConstantPart( smtrat::ZERO_RATIONAL ),
        mFactor( smtrat::ZERO_RATIONAL ),
        mDenominator( smtrat::ONE_RATIONAL ),
        mRadicand( smtrat::ZERO_RATIONAL )
    {}

    SqrtEx::SqrtEx( const smtrat::Polynomial& _poly ):
        mConstantPart( _poly ),
        mFactor( smtrat::ZERO_RATIONAL ),
        mDenominator( smtrat::ONE_RATIONAL ),
        mRadicand( smtrat::ZERO_RATIONAL )
    {
        normalize();
    }

    SqrtEx::SqrtEx( const smtrat::Polynomial& _constantPart, const smtrat::Polynomial& _factor, const smtrat::Polynomial& _denominator, const smtrat::Polynomial& _radicand ):
        mConstantPart( _constantPart ),
        mFactor( _radicand == smtrat::ZERO_POLYNOMIAL ? smtrat::ZERO_POLYNOMIAL : _factor ),
        mDenominator( ((mFactor == smtrat::ZERO_POLYNOMIAL) && (_constantPart == smtrat::ZERO_POLYNOMIAL)) ? smtrat::ONE_POLYNOMIAL : _denominator ),
        mRadicand( ( _factor == smtrat::ZERO_POLYNOMIAL ) ? smtrat::ZERO_POLYNOMIAL : _radicand )
    {
        assert( _denominator != smtrat::ZERO_POLYNOMIAL );
        assert( !_radicand.isConstant() || smtrat::ZERO_RATIONAL <= _radicand.trailingTerm()->coeff() );
        normalize();
    }

    SqrtEx::SqrtEx( const SqrtEx& _sqrtEx ):
        mConstantPart( _sqrtEx.constantPart() ),
        mFactor( _sqrtEx.factor() ),
        mDenominator( _sqrtEx.denominator() ),
        mRadicand( _sqrtEx.radicand() )
    {}

    SqrtEx::~SqrtEx()
    {}

    void SqrtEx::normalize()
    {
        //TODO: implement this method
    }

    bool SqrtEx::operator==( const SqrtEx& _toCompareWith ) const
    {
        return    mRadicand == _toCompareWith.radicand() && mDenominator == _toCompareWith.denominator() 
               && mFactor == _toCompareWith.factor() && mConstantPart == _toCompareWith.constantPart();
    }

    SqrtEx& SqrtEx::operator=( const SqrtEx& _sqrtEx )
    {
        if( this != &_sqrtEx )
        {
            mConstantPart = _sqrtEx.constantPart();
            mFactor       = _sqrtEx.factor();
            mDenominator  = _sqrtEx.denominator();
            if( factor() == smtrat::ZERO_POLYNOMIAL )
                mRadicand = smtrat::ZERO_POLYNOMIAL;
            else
                mRadicand = _sqrtEx.radicand();
        }
        return *this;
    }

    SqrtEx& SqrtEx::operator=( const smtrat::Polynomial& _poly )
    {
        mConstantPart = _poly;
        mFactor       = smtrat::ZERO_POLYNOMIAL;
        mDenominator  = smtrat::ONE_POLYNOMIAL;
        mRadicand     = smtrat::ZERO_POLYNOMIAL;
        return *this;
    }

    SqrtEx operator+( const SqrtEx& _summandA, const SqrtEx& _summandB )
    {
        assert( !_summandA.hasSqrt() ||!_summandB.hasSqrt() || _summandA.radicand() == _summandB.radicand() );
        SqrtEx result = SqrtEx( _summandB.denominator() * _summandA.constantPart() + _summandB.constantPart() * _summandA.denominator(),
                         _summandB.denominator() * _summandA.factor() + _summandB.factor() * _summandA.denominator(),
                         _summandA.denominator() * _summandB.denominator(), _summandA.radicand() );
        return result;
    }

    SqrtEx operator-( const SqrtEx& _minuend, const SqrtEx& _subtrahend )
    {
        assert( !_minuend.hasSqrt() || !_subtrahend.hasSqrt() || _minuend.radicand() == _subtrahend.radicand() );
        SqrtEx result = SqrtEx( _subtrahend.denominator() * _minuend.constantPart() - _subtrahend.constantPart() * _minuend.denominator(),
                         _subtrahend.denominator() * _minuend.factor() - _subtrahend.factor() * _minuend.denominator(),
                         _minuend.denominator() * _subtrahend.denominator(), _minuend.radicand() );
        return result;
    }

    SqrtEx operator*( const SqrtEx& _factorA, const SqrtEx& _factorB )
    {
        assert( !_factorA.hasSqrt() || !_factorB.hasSqrt() || _factorA.radicand() == _factorB.radicand() );
        SqrtEx result = SqrtEx( _factorB.constantPart() * _factorA.constantPart() + _factorB.factor() * _factorA.factor() * _factorA.radicand(),
                         _factorB.constantPart() * _factorA.factor() + _factorB.factor() * _factorA.constantPart(),
                         _factorA.denominator() * _factorB.denominator(), _factorA.radicand() );
        return result;
    }

    SqrtEx operator/( const SqrtEx& _dividend, const SqrtEx& _divisor )
    {
        assert( !_divisor.hasSqrt() );
        SqrtEx result = SqrtEx( _dividend.constantPart() * _divisor.denominator(), _dividend.factor() * _divisor.denominator(),
                         _dividend.denominator() * _divisor.factor(), _dividend.radicand() );
        return result;
    }
    
    ostream& operator<<( ostream& _out, const SqrtEx& _substitution )
    {
        return (_out << _substitution.toString( true ) );
    }
    
    string SqrtEx::toString( bool _infix, bool _friendlyNames ) const
    {
        if( _infix )
        {
            string result = "((";
            result += mConstantPart.toString( true, _friendlyNames );
            result +=  ")+(";
            result +=  mFactor.toString( true, _friendlyNames );
            result +=  ")*";
            result +=  "sqrt(";
            result +=  mRadicand.toString( true, _friendlyNames );
            result +=  "))";
            result +=  "/(";
            result +=  mDenominator.toString( true, _friendlyNames );
            result +=  ")";
            return result;
        }
        else
        {
            string result = "(/ (+";
            result += mConstantPart.toString( false, _friendlyNames );
            result +=  " (*";
            result +=  mFactor.toString( false, _friendlyNames );
            result +=  " ";
            result +=  "(sqrt ";
            result +=  mRadicand.toString( false, _friendlyNames );
            result +=  "))) ";
            result +=  mDenominator.toString( false, _friendlyNames );
            result +=  ")";
            return result;
        }
    }

    SqrtEx SqrtEx::subBySqrtEx( const smtrat::Polynomial& _substituteIn, const carl::Variable& _varToSubstitute, const SqrtEx& _substituteBy )
    {
        /*
         * We have to calculate the result of the substitution:
         *
         *                           q+r*sqrt{t}
         *        (a_n*x^n+...+a_0)[------------ / x]
         *                               s
         * being:
         *
         *      sum_{k=0}^n (a_k * (q+r*sqrt{t})^k * s^{n-k})
         *      ----------------------------------------------
         *                           s^n
         */
//        carl::VariableInformation<true,smtrat::Polynomial> varInfo = _poly.getVarInfo( _varToSubstitute ); //TODO: implement this line
        unsigned n = 0; // varInfo.maxDegree(); //TODO: implement this line
        if( n == 0 )
        {
            SqrtEx result = SqrtEx( _substituteIn );
            return result;
        }
        // Calculate the s^k:   (0<=k<=n)
        vector<smtrat::Polynomial> sk = vector<smtrat::Polynomial>( n + 1 );
        sk[0] = smtrat::Polynomial( 1 );
        for( unsigned i = 1; i <= n; ++i )
            sk[i] = sk[i - 1] * _substituteBy.denominator();
        // Calculate the constant part and factor of the square root of (q+r*sqrt{t})^k:   (1<=k<=n)
        vector<smtrat::Polynomial> qk = vector<smtrat::Polynomial>( n );
        vector<smtrat::Polynomial> rk = vector<smtrat::Polynomial>( n );
        qk[0] = smtrat::Polynomial( _substituteBy.constantPart() );
        rk[0] = smtrat::Polynomial( _substituteBy.factor() );
        for( unsigned i = 1; i < n; ++i )
        {
            qk[i] = _substituteBy.constantPart() * qk[i - 1] + _substituteBy.factor() * rk[i - 1] * _substituteBy.radicand();
            rk[i] = _substituteBy.constantPart() * rk[i - 1] + _substituteBy.factor() * qk[i - 1];
        }
        // Calculate the result:
        smtrat::Polynomial resConstantPart = sk[n]; // * varInfo.coeffs( 0 ); //TODO: implement this line
        smtrat::Polynomial resFactor       = smtrat::ZERO_POLYNOMIAL;
        for( unsigned i = 1; i <= n; ++i )
        {
//            resConstantPart += varInfo.coeffs( i ) * qk[i - 1] * sk[n - i]; //TODO: implement this line
//            resFactor       += varInfo.coeffs( i ) * rk[i - 1] * sk[n - i]; //TODO: implement this line
        }
        SqrtEx result = SqrtEx( resConstantPart, resFactor, sk[n], _substituteBy.radicand() );
        return result;
    }
}    // end namspace vs
