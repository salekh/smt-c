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
		deltaPart(0)
	{}

    //Constructor for objects without strict inequalities

	TRational::TRational(const Rational& rational):
		rationalPart(rational),
		deltaPart(0)
	{}

    //Constructor for objects with strict equalities

	TRational::TRational(const Rational& rational, const Rational& delta):
		rationalPart(rational),
		deltaPart(delta)
	{}

    //Empty constructor

	TRational::~TRational(){}

	
	/**************************************
			OVERLOAD OPERATORS
	**************************************/

	/**
	 * Equals operation
	 * @param _trational
	 * @return
	*/
	TRational& TRational::operator=(const TRational& _trational){
		rationalPart = _trational.getRationalPart();
        deltaPart = _trational.getDeltaPart();
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
        return TRational(first, second);
    }

    /**
     * Addition of two TRationals
     * @param _trational
    */
 	void TRational::operator +=( const TRational& _trational ){
 		this->rationalPart += _trational.getRationalPart();
        this->deltaPart += _trational.getDeltaPart();
 	}

	/**
     * Subtraction of two TRationals
     * @param _trational
     * @return
    */
    TRational TRational::operator -( const TRational& _trational) const{
		Rational first = rationalPart - _trational.getRationalPart();
        Rational second = deltaPart - _trational.getDeltaPart();
        return TRational(first, second);
    }

    /**
     * Subtraction of two TRationals
     * @param _trational
    */
 	void TRational::operator -=( const TRational& _trational ){
 		this->rationalPart -= _trational.getRationalPart();
        this->deltaPart -= _trational.getDeltaPart();
 	}

 	/**
     * Multiplication by value _a
     * @param _a
     * @return
    */
    TRational TRational::operator *( const Rational& _a) const{
		Rational first = _a * rationalPart;
        Rational second = _a * deltaPart;
        return TRational(first, second);
    }

    /**
     * Multiplication of two TRational values
     * @param _trational
    */
 	void TRational::operator *=( const TRational& _trational ){
 		this->rationalPart *= _trational.getRationalPart();
        this->deltaPart *= _trational.getDeltaPart();
 	} 	


 	/**
     * Multiplication by value _a
     * @param _a
     * @return
    */
    void TRational::operator *=( const Rational& _a) {
		this->rationalPart *= _a;
		this->deltaPart *= _a;
    }

	/**
     * Division by value _a
     * @param _a
     * @return
    */
 	TRational TRational::operator /( const Rational& _a) const {
		Rational first = rationalPart / _a;
        Rational second = deltaPart / _a;
        return TRational(first, second);
    }

 	/**
     * Division by value _a
     * @param _a
     * @return
    */
    void TRational::operator /=( const Rational& _a) {
		this->rationalPart /= _a;
		this->deltaPart /= _a;
    }

    /**
     * Strictly smaller as comparison
     * @param _trational
     * @return
    */

    bool TRational::operator <(const TRational& _trational) const {
    	if( this->rationalPart < _trational.getRationalPart() ) {
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
        if( (this->rationalPart < _trational.getRationalPart()) || (this->rationalPart == _trational.getRationalPart() && this->deltaPart <= _trational.getDeltaPart()) )
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
        if((this->rationalPart == _trational.getRationalPart() && this->deltaPart <= _trational.getDeltaPart()))
            b = true;
        return b;
    }

    /**
     * Equality comparison for objects without strict inequalities
     * @param _a
     * @return
    */

    bool TRational::operator ==(const Rational& _a) const {
    	return (this->rationalPart == _a && this->deltaPart == 0);
    }

    /**
     * Strictly smaller comparison with Rational _a
     * @param _a
     * @return
    */

    bool TRational::operator <(const Rational& _a) const {
    	return ((this->rationalPart < _a) || (this->rationalPart == _a && this->deltaPart < 0));
    }

    /**
     * Strictly greater comparison with Rational _a
     * @param _a
     * @return
    */

    bool TRational::operator >(const Rational& _a) const {
    	return ((this->rationalPart > _a) || (this->rationalPart == _a && this->deltaPart > 0));
    }

    /**
     * Smaller equals comparison with Rational _a
     * @param _a
     * @return
    */

    bool TRational::operator <=(const Rational& _a) const {
    	return ((this->rationalPart < _a) || (this->rationalPart == _a && this->deltaPart <= 0));
    }

    /**
     * Greater equals comparison with Rational _a
     * @param _a
     * @return
    */

    bool TRational::operator >=(const Rational& _a) const {
    	return ((this->rationalPart > _a) || (this->rationalPart == _a && this->deltaPart >= 0));
    }

    /**
     * Print function
     * @param t
     * @return
    */

	std::ostream& operator<<( std::ostream& stream, const TRational& t)
	{
		stream << t.getRationalPart() << "(" << t.getDeltaPart() << ")";
		return stream;
	}
} // smtrat


