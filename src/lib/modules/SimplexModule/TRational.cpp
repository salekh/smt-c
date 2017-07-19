/**
 * @file TRational.h
 * @author Sanchit Alekh <sanchit.alekh@rwth-aachen.de>
 * @author Karsten Jungnitsch <karsten.jungnitsch@rwth-aachen.de>
 * @author Alexander Reeh <alexander.reeh@rwth-aachen.de>
 *
 */
#pragma once

#include "TRational.h"

namespace smtrat {

	/**************************************
				CONSTRUCTORS
	**************************************/

    //Constructor for "zero" object

	TRational::TRational():
		rationalPart(0),
		deltaPart(0),
        inf(0),
        upperBound(false)
	{}

    TRational::TRational(const Rational& rational):
        rationalPart(rational),
        deltaPart(0),
        inf(0),
        upperBound(false)
    {}


    //Constructor for objects without strict inequalities

	TRational::TRational(const Rational& rational, const Rational& inf, bool bound):
		rationalPart(rational),
		deltaPart(0),
        infPart(inf),
        upperBound(bound)
	{}

    //Constructor for objects with strict equalities

	TRational::TRational(const Rational& rational, const Rational& delta, const Rational& inf, bool bound):
		rationalPart(rational),
		deltaPart(delta),
        infPart(inf),
        upperBound(bound)
	{}

    //Empty constructor

	TRational::~TRational(){}

	
	/**************************************
			OVERLOAD OPERATORS
	**************************************/

    /** Checking for infinity
    * since the inf parts can't be anything else
    * then -1, 0, +1
    */

    Rational checkInf(const TRational& _a, const TRational& _b) {
        if (a.getInfPart() + b.getInfPart() == 2) {
            return Rational(1);
        }
        else if (a.getInfPart() + b.getInfPart() == -2) {
            return Rational(-1);
        }
        else
            return a.getInfPart() + b.getInfPart();
    }

	/**
	 * Equals operation
	 * @param _trational
	 * @return
	*/
	TRational& TRational::operator=(const TRational& _trational){
		rationalPart = _trational.getRationalPart();
        deltaPart = _trational.getDeltaPart();
        infPart = _trational.getInfPart();
        return *this;
	}

	/**
     * Addition TRationals
     * @param _trational
     * @return
    */
    TRational TRational::operator +( const TRational& _trational) const{
		Rational first = rationalPart + _trational.getRationalPart();
        Rational second = deltaPart + _trational.getDeltaPart();
        Rational third = checkInf(this,_trational);

        return TRational(first, second, third, upperBound);
    }

    /**
     * Addition of two TRationals
     * @param _trational
    */
 	void TRational::operator +=( const TRational& _trational ){
 		this->rationalPart += _trational.getRationalPart();
        this->deltaPart += _trational.getDeltaPart();
        this->infPart = checkInf(this,_trational)
 	}

	/**
     * Subtraction of two TRationals
     * @param _trational
     * @return
    */
    TRational TRational::operator -( const TRational& _trational) const{
		Rational first = rationalPart - _trational.getRationalPart();
        Rational second = deltaPart - _trational.getDeltaPart();
        Rational third = checkInf(this,_trational);
        return TRational(first, second, third, upperBound);
    }

    /**
     * Subtraction of two TRationals
     * @param _trational
    */
 	void TRational::operator -=( const TRational& _trational ){
 		this->rationalPart -= _trational.getRationalPart();
        this->deltaPart -= _trational.getDeltaPart();
        this->infPart = checkInf(this,_trational)
 	}

 	/**
     * Multiplication by value _a
     * @param _a
     * @return
    */
    TRational TRational::operator *( const Rational& _a) const{
		Rational first = _a * rationalPart;
        Rational second = _a * deltaPart;
        Rational third = infPart;
        return TRational(first, second, third, upperBound);
    }

    /**
     * Multiplication of two TRational values
     * @param _trational
    */
 	void TRational::operator *=( const TRational& _trational ){
 		this->rationalPart *= _trational.getRationalPart();
        this->deltaPart *= _trational.getDeltaPart();
        this->infPart *= _trational.getInfPart();
 	} 	


 	/**
     * Multiplication by value _a
     * @param _a
     * @return
    */
    void TRational::operator *=( const Rational& _a) {
		this->rationalPart *= _a;
		this->deltaPart *= _a;
        this->infPart = infPart;
    }

	/**
     * Division by value _a
     * @param _a
     * @return
    */
 	TRational TRational::operator /( const Rational& _a) const {
		Rational first = rationalPart / _a;
        Rational second = deltaPart / _a;
        Ration third = infPart;
        return TRational(first, second, third, upperBound);
    }

 	/**
     * Division by value _a
     * @param _a
     * @return
    */
    void TRational::operator /=( const Rational& _a) {
		this->rationalPart /= _a;
		this->deltaPart /= _a;
        this->infPart = infPart;
    }

    /**
     * Strictly smaller as comparison
     * @param _trational
     * @return
    */

    bool TRational::operator <(const TRational& _trational) const {
        if (this->infPart < _trational.getInfPart()) {
            return true;
        }
    	else if( this->rationalPart < _trational.getRationalPart() ) {
            return true;
        } else if( this->rationalPart == _trational.getRationalPart() ) {
            if( this->deltaPart < _trational.getDeltaPart() ) {
            	return true;
			}
        }
        return false;
    }

    /**
     * Smaller equals as comparison
     * @param _trational
     * @return
    */

    bool TRational::operator <=(const TRational& _trational) const {
    	bool b = false;
        if( (this->infPart <= _trational.getInfPart() || this->rationalPart < _trational.getRationalPart()) || (this->rationalPart == _trational.getRationalPart() && this->deltaPart <= _trational.getDeltaPart()) )
            b = true;
        return b;
    }

    /**
     * Equality comparison
     * @param _trational
     * @return
    */

    bool TRational::operator ==(const TRational& _trational) const {
    	bool b = false;
        //TODO I found that the deltaPart comparison was <= beforehand. Is that supposed to be that way or was that a bug?
        if((this->infPart == _trational.getInfPart() && this->rationalPart == _trational.getRationalPart() && this->deltaPart == _trational.getDeltaPart()))
            b = true;
        return b;
    }

    /**
     * Equality comparison for objects without strict inequalities
     * @param _a
     * @return
    */

    bool TRational::operator ==(const Rational& _a) const {
    	if (this->infPart == -1 || this->infPart == 1)
            return false;
        return (this->rationalPart == _a && this->deltaPart == 0);
    }

    /**
     * Strictly smaller comparison with Rational _a
     * @param _a
     * @return
    */

    bool TRational::operator <(const Rational& _a) const {
        if (this->infPart == -1)
            return true;
        else if (this->infPart == 1) 
            return false;
    	return ((this->rationalPart < _a) || (this->rationalPart == _a && this->deltaPart < 0));
    }

    /**
     * Strictly greater comparison with Rational _a
     * @param _a
     * @return
    */

    bool TRational::operator >(const Rational& _a) const {
        if (this->infPart == -1)
            return false;
        else if (this->infPart == 1) 
            return true;
    	return ((this->rationalPart > _a) || (this->rationalPart == _a && this->deltaPart > 0));
    }

    /**
     * Smaller equals comparison with Rational _a
     * @param _a
     * @return
    */

    bool TRational::operator <=(const Rational& _a) const {
        if (this->infPart == -1)
            return true;
        else if (this->infPart == 1) 
            return false;
    	return ((this->rationalPart < _a) || (this->rationalPart == _a && this->deltaPart <= 0));
    }

    /**
     * Greater equals comparison with Rational _a
     * @param _a
     * @return
    */

    bool TRational::operator >=(const Rational& _a) const {
        if (this->infPart == -1)
            return false;
        else if (this->infPart == 1) 
            return true;
    	return ((this->rationalPart > _a) || (this->rationalPart == _a && this->deltaPart >= 0));
    }

    /**
     * Print function
     * @param t
     * @return
    */

	std::ostream& operator<<( std::ostream& stream, const TRational& t)
	{
		stream << t.getRationalPart() << "(" << t.getDeltaPart() << "," << t.getInfPart() ")";
		return stream;
	}
} // smtrat


